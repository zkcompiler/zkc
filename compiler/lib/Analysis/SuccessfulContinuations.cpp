#include "zkc/Analysis/SuccessfulContinuations.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dominance.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
using Status = SuccessfulContinuationAnalysis::Status;
std::optional<bool> boolean(Value value) {
  auto constant = value.getDefiningOp<arith::ConstantOp>();
  auto literal =
      constant ? dyn_cast<IntegerAttr>(constant.getValue()) : IntegerAttr();
  if (literal && literal.getType().isSignlessInteger(1))
    return !literal.getValue().isZero();
  return std::nullopt;
}
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
  // Only the declaration body and its owned repeat bodies are supported.
  // This validates ancestry, not a second lexical operation traversal.
  bool contains(Value value, Operation *declaration, facts::Work &work) const {
    if (!work.charge() || !value)
      return false;
    auto *scope = value.getParentRegion()->getParentOp();
    for (unsigned depth = 0; enter(work, depth); ++depth) {
      if (scope == declaration)
        return true;
      if (!isa_and_nonnull<pir::RepeatOp>(scope))
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
      if (auto argument = dyn_cast<BlockArgument>(value)) {
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
    for (auto [depth, ordinal] : enumerate(path)) {
      if (!enter(work, depth))
        return Status::Capacity;
      // Prefixes are interpreted outer-to-inner. A preceding repeat remains
      // opaque: neither its body guards nor its stops escape to this block.
      for (unsigned i = 0; i < ordinal; ++i) {
        if (!work.charge())
          return Status::Capacity;
        auto *operation =
            view.getActions()[sequence->getActions()[i]].getOperation();
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
        condition = normalize(condition, declaration, participant, work);
        if (!condition)
          return missing();
        // Literal/condition lookup, even on repeated queries.
        if (!work.charge())
          return Status::Capacity;
        auto literal = boolean(condition);
        if (literal && (*literal != guard))
          return Status::Unreachable;
        if (!guard)
          continue;
        auto less = condition.getDefiningOp<data::LessOp>();
        if (!less)
          continue;
        auto lhs = normalize(less.getLhs(), declaration, participant, work);
        auto rhs = normalize(less.getRhs(), declaration, participant, work);
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
          auto integer = mathematics.integer(rhs, work, depth);
          if (integer.status == facts::Status::Capacity)
            return Status::Capacity;
          proven |= integer.status == facts::Status::Proven && integer.value &&
                    *integer.value <= *constantUpper;
        }
      }
      if (!work.charge())
        return Status::Capacity;
      const auto &action = view.getActions()[sequence->getActions()[ordinal]];
      if (depth + 1 == path.size())
        break;
      auto repeat = dyn_cast<pir::RepeatOp>(action.getOperation());
      if (!repeat || !action.getRepeatBody() ||
          !member(repeat.getRoles(), participant, work))
        return missing();
      auto count =
          normalize(repeat.getInputs().front(), declaration, participant, work);
      if (!count)
        return missing();
      auto trips = mathematics.integer(count, work, depth);
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
