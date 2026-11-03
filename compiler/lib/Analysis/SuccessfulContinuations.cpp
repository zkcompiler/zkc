#include "zkc/Analysis/SuccessfulContinuations.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dominance.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Analysis/ProtocolConstants.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/SelectedControl.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
using Status = SuccessfulContinuationAnalysis::Status;
} // namespace

struct SuccessfulContinuationAnalysis::Impl {
  Operation *owner;
  Limits limits;
  std::unique_ptr<InteractionAnalysis> ownedInteractions;
  std::unique_ptr<MathematicalFactAnalysis> ownedMathematics;
  InteractionAnalysis &interactions;
  MathematicalFactAnalysis &mathematics;
  DominanceInfo dominance;

  Impl(Operation *owner, Limits limits)
      : owner(owner),
        limits{std::min(limits.depth, 64u), std::min(limits.actions, 100000u)},
        ownedInteractions(std::make_unique<InteractionAnalysis>(
            owner, InteractionAnalysis::Limits{this->limits.depth,
                                               this->limits.actions})),
        ownedMathematics(std::make_unique<MathematicalFactAnalysis>(owner)),
        interactions(*ownedInteractions), mathematics(*ownedMathematics) {}
  Impl(Operation *owner, AnalysisManager &manager)
      : owner(owner), interactions(manager.getAnalysis<InteractionAnalysis>()),
        mathematics(manager.getAnalysis<MathematicalFactAnalysis>()) {}

  bool enter(facts::Work &work, unsigned depth) const {
    if (depth >= limits.depth)
      work.exhaust();
    return work.charge();
  }
  bool member(ArrayAttr roles, StringRef participant, facts::Work &work) const {
    for (auto role : roles) {
      if (!work.charge())
        return false;
      if (cast<StringAttr>(role).getValue() == participant)
        return true;
    }
    return false;
  }
  // Validate closed Protocol ancestry without a second lexical traversal.
  bool contains(Value value, Operation *declaration, facts::Work &work) const {
    if (!work.charge() || !value)
      return false;
    auto *scope = value.getParentRegion()->getParentOp();
    for (unsigned depth = 0; enter(work, depth); ++depth) {
      if (scope == declaration)
        return true;
      if (!isa_and_nonnull<pir::RepeatOp, pir::BranchOp>(scope))
        return false;
      scope = scope->getParentOp();
    }
    return false;
  }
  Value normalize(Value value, Operation *declaration, StringRef participant,
                  facts::Work &work) const {
    for (unsigned depth = 0; enter(work, depth); ++depth) {
      if (!contains(value, declaration, work))
        return {};
      if (auto restriction = value.getDefiningOp<pir::RestrictRolesOp>()) {
        if (!member(restriction.getRoles(), participant, work))
          return {};
        value = restriction.getInput();
        continue;
      }
      if (auto assembly = value.getDefiningOp<pir::AssembleRolesOp>()) {
        if (!member(assembly.getRoles(), participant, work))
          return {};
        value = assembly.getComponent(participant);
        continue;
      }
      if (auto argument = dyn_cast<BlockArgument>(value)) {
        if (auto capture = selectedCapture(argument)) {
          value = capture;
          continue;
        }
        auto repeat =
            dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
        if (repeat && !member(repeat.getRoles(), participant, work))
          return {};
        if (repeat && argument.getArgNumber() > uint64_t(repeat.getCarried())) {
          value = repeat.getInputs()[argument.getArgNumber()];
          continue;
        }
      }
      return value;
    }
    return {};
  }

  Expected<Status> prefix(const InteractionDeclaration &view,
                          const InteractionSequence &sequence, unsigned end,
                          StringRef participant, Value index, Value upper,
                          std::optional<uint64_t> constantUpper,
                          facts::Work &work, unsigned depth, bool proven) {
    if (!enter(work, depth))
      return Status::Capacity;
    auto missing = [&] {
      return work.exhausted() ? Status::Capacity : Status::Unknown;
    };
    for (unsigned i = 0; i < end; ++i) {
      if (!work.charge())
        return Status::Capacity;
      const auto &action = view.getActions()[sequence.getActions()[i]];
      auto *operation = action.getOperation();
      if (auto branch = dyn_cast<pir::BranchOp>(operation)) {
        if (!member(branch.getRoles(), participant, work)) {
          if (work.exhausted())
            return Status::Capacity;
          continue;
        }
        std::optional<unsigned> selected;
        if (branch.getInputs()[0].getType().isSignlessInteger(1)) {
          auto selector = observeProtocolConstant(
              branch.getInputs()[0], participant, mathematics, work, depth);
          if (selector.status == facts::Status::Capacity)
            return Status::Capacity;
          if (selector.value)
            selected = *selector.value ? 0 : 1;
        }
        bool continuing = false, common = true;
        for (const auto &edge : action.getRegions()) {
          if (selected && *selected != edge.ordinal)
            continue;
          const auto &arm = view.getSequence(edge.sequence);
          auto state =
              prefix(view, arm, arm.getActions().size(), participant, index,
                     upper, constantUpper, work, depth + 1, proven);
          if (!state)
            return state.takeError();
          if (*state == Status::Capacity)
            return Status::Capacity;
          if (*state == Status::Unreachable)
            continue;
          continuing = true;
          common &= *state == Status::Proven;
        }
        if (!continuing)
          return Status::Unreachable;
        proven = common;
        continue;
      }
      Value condition;
      bool guard = false;
      if (auto check = dyn_cast<pir::GuardOp>(operation)) {
        if (check.getOwner() == participant) {
          condition = check.getCondition();
          guard = true;
        }
      } else if (auto finish = dyn_cast<pir::FinishIfOp>(operation)) {
        if (finish.getOwner() == participant)
          condition = finish.getCondition();
      }
      if (!condition)
        continue;
      condition =
          normalize(condition, view.getDeclaration(), participant, work);
      if (!condition)
        return missing();
      // Literal/condition lookup, even on repeated queries.
      if (!work.charge())
        return Status::Capacity;
      auto literal = observeProtocolConstant(condition, participant,
                                             mathematics, work, depth);
      if (literal.status == facts::Status::Capacity)
        return Status::Capacity;
      if (literal.value && (bool(*literal.value) != guard))
        return Status::Unreachable;
      if (!guard)
        continue;
      auto less = condition.getDefiningOp<data::LessOp>();
      if (!less)
        continue;
      auto lhs =
          normalize(less.getLhs(), view.getDeclaration(), participant, work);
      auto rhs =
          normalize(less.getRhs(), view.getDeclaration(), participant, work);
      if (work.exhausted())
        return Status::Capacity;
      // Exact fact lookup, with no shape/origin substitution.
      if (!work.charge())
        return Status::Capacity;
      if (!lhs || !rhs || lhs != index)
        continue;
      if (!constantUpper) {
        proven |= rhs == upper;
      } else {
        auto integer =
            observeProtocolConstant(rhs, participant, mathematics, work, depth);
        if (integer.status == facts::Status::Capacity)
          return Status::Capacity;
        proven |= integer.status == facts::Status::Proven && integer.value &&
                  *integer.value <= *constantUpper;
      }
    }
    return proven ? Status::Proven : missing();
  }

  Expected<Status> bound(Operation *declaration, Operation *point,
                         StringRef participant, Value index, Value upper,
                         std::optional<uint64_t> constantUpper,
                         facts::Work &work) {
    if (!work.charge())
      return Status::Capacity;
    auto extracted = interactions.get(declaration, work);
    if (!extracted) {
      auto failure = extracted.takeError();
      if (!work.exhausted())
        return std::move(failure);
      consumeError(std::move(failure));
      return Status::Capacity;
    }
    auto missing = [&] {
      return work.exhausted() ? Status::Capacity : Status::Unknown;
    };
    auto program = dyn_cast<pir::MathematicalOp>(declaration);
    if (!program || !member(program.getRoles(), participant, work) || !point ||
        point->getName().getDialectNamespace() != "protocol" ||
        mathematical::isProtocolValueExpression(point) ||
        point->hasTrait<OpTrait::IsTerminator>() || !index ||
        !index.getType().isUnsignedInteger(64) ||
        (!constantUpper && (!upper || !upper.getType().isUnsignedInteger(64))))
      return missing();

    const auto &view = **extracted;
    const InteractionAction *selected = nullptr;
    for (const auto &action : view.getActions()) {
      if (!work.charge())
        return Status::Capacity;
      if (action.getOperation() == point) {
        selected = &action;
        break;
      }
    }
    if (!selected)
      return Status::Unknown;
    // The profile contains only single-block Protocol regions. Its retained
    // inventory bounds the dominance query as well as lexical extraction.
    // Check the original values: normalizing a capture first could import a
    // value from an unrelated or already exited repeat occurrence.
    if (!work.charge(view.getActions().size() + 1))
      return Status::Capacity;
    if (!contains(index, declaration, work) ||
        !dominance.properlyDominates(index, point) ||
        (!constantUpper && (!contains(upper, declaration, work) ||
                            !dominance.properlyDominates(upper, point))))
      return missing();
    index = normalize(index, declaration, participant, work);
    if (!constantUpper)
      upper = normalize(upper, declaration, participant, work);
    if (!index || (!constantUpper && !upper))
      return missing();

    bool proven = false;
    const auto *sequence = &view.getBody();
    auto path = selected->getPath();
    unsigned depth = 0;
    for (unsigned coordinate = 0; coordinate < path.size();
         ++coordinate, ++depth) {
      unsigned ordinal = path[coordinate];
      if (!enter(work, depth))
        return Status::Capacity;
      // Prefixes are interpreted outer-to-inner. A preceding repeat remains
      // opaque: neither its body guards nor its stops escape to this block.
      auto state = prefix(view, *sequence, ordinal, participant, index, upper,
                          constantUpper, work, depth, proven);
      if (!state)
        return state.takeError();
      if (*state == Status::Capacity || *state == Status::Unreachable)
        return *state;
      proven = *state == Status::Proven;
      if (!work.charge())
        return Status::Capacity;
      const auto &action = view.getActions()[sequence->getActions()[ordinal]];
      if (coordinate + 1 == path.size())
        break;
      if (auto branch = dyn_cast<pir::BranchOp>(action.getOperation())) {
        if (!member(branch.getRoles(), participant, work) ||
            coordinate + 1 >= path.size())
          return missing();
        unsigned arm = path[++coordinate];
        if (arm >= action.getRegions().size())
          return missing();
        if (branch.getInputs()[0].getType().isSignlessInteger(1)) {
          auto selector = observeProtocolConstant(
              branch.getInputs()[0], participant, mathematics, work, depth);
          if (selector.status == facts::Status::Capacity)
            return Status::Capacity;
          if (selector.value && arm != (*selector.value ? 0u : 1u))
            return Status::Unreachable;
        }
        sequence = &view.getSequence(action.getRegions()[arm].sequence);
        continue;
      }
      auto repeat = dyn_cast<pir::RepeatOp>(action.getOperation());
      if (!repeat || !action.getRepeatBody() ||
          !member(repeat.getRoles(), participant, work))
        return missing();
      auto count =
          normalize(repeat.getInputs().front(), declaration, participant, work);
      if (!count)
        return missing();
      auto trips =
          observeProtocolConstant(count, participant, mathematics, work, depth);
      if (trips.status == facts::Status::Capacity)
        return Status::Capacity;
      if (!repeat.getMaximum() ||
          (trips.status == facts::Status::Proven && trips.value &&
           (!*trips.value || *trips.value > uint64_t(repeat.getMaximum()))))
        return Status::Unreachable;
      sequence = &view.getSequence(*action.getRepeatBody());
    }
    return proven ? Status::Proven : Status::Unknown;
  }
};

SuccessfulContinuationAnalysis::SuccessfulContinuationAnalysis(Operation *owner)
    : SuccessfulContinuationAnalysis(owner, Limits{}) {}
SuccessfulContinuationAnalysis::SuccessfulContinuationAnalysis(Operation *owner,
                                                               Limits limits)
    : impl_(std::make_unique<Impl>(owner, limits)) {}
SuccessfulContinuationAnalysis::SuccessfulContinuationAnalysis(
    Operation *owner, AnalysisManager &manager)
    : impl_(std::make_unique<Impl>(owner, manager)) {}
SuccessfulContinuationAnalysis::~SuccessfulContinuationAnalysis() = default;
bool SuccessfulContinuationAnalysis::isInvalidated(
    const AnalysisManager::PreservedAnalyses &preserved) {
  return !preserved.isPreserved<SuccessfulContinuationAnalysis>() ||
         !preserved.isPreserved<InteractionAnalysis>() ||
         !preserved.isPreserved<MathematicalFactAnalysis>() ||
         !preserved.isPreserved<SymbolClosureAnalysis>();
}
void SuccessfulContinuationAnalysis::clear() {
  impl_->dominance.invalidate();
  impl_->interactions.clear();
  impl_->mathematics.clear();
}
Operation *SuccessfulContinuationAnalysis::getOwner() const {
  return impl_->owner;
}
Expected<SuccessfulContinuationAnalysis::Status>
SuccessfulContinuationAnalysis::bound(Operation *declaration, Operation *point,
                                      StringRef participant, Value index,
                                      Value upper, facts::Work &work) {
  return impl_->bound(declaration, point, participant, index, upper,
                      std::nullopt, work);
}
Expected<SuccessfulContinuationAnalysis::Status>
SuccessfulContinuationAnalysis::bound(Operation *declaration, Operation *point,
                                      StringRef participant, Value index,
                                      uint64_t upper, facts::Work &work) {
  return impl_->bound(declaration, point, participant, index, {}, upper, work);
}
} // namespace zkc
