#include "zkc/Analysis/Interactions.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include <algorithm>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
Error capacity(facts::Work &work) {
  work.exhaust();
  return error("interaction-analysis-capacity");
}
} // namespace

Expected<const InteractionAction *>
InteractionDeclaration::lookup(ArrayRef<unsigned> path,
                               facts::Work &work) const {
  if (!work.charge())
    return capacity(work);
  const auto *sequence = &getBody();
  const InteractionAction *action = nullptr;
  for (unsigned index = 0; index < path.size(); ++index) {
    unsigned component = path[index];
    if (!work.charge())
      return capacity(work);
    if (!sequence || component >= sequence->getActions().size())
      return nullptr;
    action = &actions_[sequence->getActions()[component]];
    sequence = nullptr;
    if (auto repeat = action->getRepeatBody())
      sequence = &getSequence(*repeat);
    else if (!action->getRegions().empty() && index + 1 < path.size()) {
      if (!work.charge())
        return capacity(work);
      unsigned arm = path[++index];
      for (const auto &region : action->getRegions())
        if (region.ordinal == arm)
          sequence = &getSequence(region.sequence);
      if (!sequence || index + 1 == path.size())
        return nullptr;
    }
  }
  return action;
}

struct InteractionAnalysis::Impl {
  Operation *owner;
  Limits limits;
  std::unique_ptr<SymbolClosureAnalysis> ownedSymbols;
  SymbolClosureAnalysis &symbols;
  llvm::DenseMap<Operation *, std::unique_ptr<InteractionDeclaration>>
      declarations;

  Impl(Operation *owner, Limits limits)
      : owner(owner),
        limits{std::min(limits.depth, 64u), std::min(limits.actions, 100000u)},
        ownedSymbols(std::make_unique<SymbolClosureAnalysis>(owner)),
        symbols(*ownedSymbols) {}
  Impl(Operation *owner, SymbolClosureAnalysis &symbols)
      : owner(owner), symbols(symbols) {}

  Error charge(InteractionDeclaration &view, facts::Work &work) {
    if (!work.charge())
      return capacity(work);
    ++view.extractionWork_;
    return Error::success();
  }
  Expected<unsigned> sequence(InteractionDeclaration &view, Block &body,
                              SmallVector<unsigned> &path, facts::Work &work,
                              unsigned depth = 0) {
    if (depth >= limits.depth)
      return capacity(work);
    if (auto failure = charge(view, work))
      return std::move(failure);
    unsigned sequenceIndex = view.sequences_.size();
    view.sequences_.emplace_back();
    view.sequences_[sequenceIndex].block_ = &body;
    unsigned ordinal = 0;
    for (Operation &operation : body) {
      if (view.actions_.size() >= limits.actions)
        return capacity(work);
      if (auto failure = charge(view, work))
        return std::move(failure);
      path.push_back(ordinal++);
      // Pay for retained coordinates and actual operand/result associations.
      uint64_t associations = path.size() + operation.getNumOperands() +
                              uint64_t(operation.getNumResults());
      for (uint64_t i = 0; i < associations; ++i)
        if (auto failure = charge(view, work))
          return std::move(failure);
      unsigned actionIndex = view.actions_.size();
      view.sequences_[sequenceIndex].actions_.push_back(actionIndex);
      view.actions_.emplace_back();
      view.actions_[actionIndex].operation_ = &operation;
      view.actions_[actionIndex].declaration_ = view.declaration_;
      view.actions_[actionIndex].path_ = path;
      SymbolRefAttr target;
      if (auto apply = dyn_cast<protocol_ir::ApplyOp>(operation))
        target = apply.getCalleeAttr();
      else if (auto call = dyn_cast<protocol_ir::LocalCallOp>(operation))
        target = call.getCalleeAttr();
      else if (auto call = dyn_cast<func::CallOp>(operation))
        target = call.getCalleeAttr();
      else if (auto created = dyn_cast<protocol_ir::OracleVirtualOp>(operation))
        target = created.getCalleeAttr();
      if (target) {
        if (auto failure = charge(view, work))
          return std::move(failure);
        auto *referenced = symbols.lookup(&operation, target);
        if (!referenced)
          return error("interaction-analysis-unsupported");
        view.actions_[actionIndex].referencedSymbol_ = referenced;
      }
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(operation)) {
        if (!hasSingleElement(repeat.getBody()))
          return error("interaction-analysis-unsupported");
        auto nested =
            sequence(view, repeat.getBody().front(), path, work, depth + 1);
        if (!nested)
          return nested.takeError();
        view.actions_[actionIndex].children_.push_back(
            {InteractionRegion::Kind::Repeat,
             0,
             *nested,
             {},
             repeat.getRoles()});
      } else if (auto branch = dyn_cast<protocol_ir::BranchOp>(operation)) {
        for (auto [index, region] : enumerate(branch.getArms())) {
          if (!hasSingleElement(region) || region.front().empty())
            return error("interaction-analysis-unsupported");
          uint64_t associations = 1 + region.front().getNumArguments() +
                                  region.front().back().getNumOperands() +
                                  branch.getRoles().size();
          for (uint64_t i = 0; i < associations; ++i)
            if (auto failure = charge(view, work))
              return std::move(failure);
          path.push_back(index);
          auto nested = sequence(view, region.front(), path, work, depth + 1);
          path.pop_back();
          if (!nested)
            return nested.takeError();
          view.actions_[actionIndex].children_.push_back(
              {InteractionRegion::Kind::BranchArm, unsigned(index), *nested,
               cast<StringAttr>(branch.getAlternatives()[index]),
               branch.getRoles()});
        }
      } else if (operation.getNumRegions() &&
                 !mathematical::isTotal(&operation)) {
        return error("interaction-analysis-unsupported");
      }
      path.pop_back();
    }
    return sequenceIndex;
  }
};

InteractionAnalysis::InteractionAnalysis(Operation *owner)
    : InteractionAnalysis(owner, Limits{}) {}
InteractionAnalysis::InteractionAnalysis(Operation *owner, Limits limits)
    : impl_(std::make_unique<Impl>(owner, limits)) {}
InteractionAnalysis::InteractionAnalysis(Operation *owner, AnalysisManager &am)
    : impl_(std::make_unique<Impl>(owner,
                                   am.getAnalysis<SymbolClosureAnalysis>())) {}
InteractionAnalysis::~InteractionAnalysis() = default;
bool InteractionAnalysis::isInvalidated(
    const AnalysisManager::PreservedAnalyses &preserved) {
  return !preserved.isPreserved<InteractionAnalysis>() ||
         !preserved.isPreserved<SymbolClosureAnalysis>();
}
void InteractionAnalysis::clear() {
  impl_->declarations.clear();
  impl_->symbols.clear();
}
Operation *InteractionAnalysis::getOwner() const { return impl_->owner; }
Expected<const InteractionDeclaration *>
InteractionAnalysis::get(Operation *declaration, facts::Work &work) {
  // This debit is identical on cold, warm, invalid and exhausted requests.
  if (!work.charge())
    return capacity(work);
  if (!isa_and_nonnull<ModuleOp>(impl_->owner) || !declaration ||
      declaration->getParentOfType<ModuleOp>().getOperation() != impl_->owner)
    return error("interaction-analysis-owner");
  auto program = dyn_cast<protocol_ir::MathematicalOp>(declaration);
  auto oracle = dyn_cast<protocol_ir::OracleDefinitionOp>(declaration);
  auto module = dyn_cast_or_null<protocol_ir::ProtocolModuleOp>(
      declaration->getParentOp());
  Region *body = program  ? &program.getBody()
                 : oracle ? &oracle.getBody()
                          : nullptr;
  if (!body || !module ||
      module.getProfile() != protocol_ir::Profile::Protocol ||
      !hasSingleElement(*body))
    return error("interaction-analysis-unsupported");
  auto found = impl_->declarations.find(declaration);
  if (found != impl_->declarations.end()) {
    for (uint64_t i = 0; i < found->second->extractionWork_; ++i)
      if (!work.charge())
        return capacity(work);
    return found->second.get();
  }
  auto view =
      std::unique_ptr<InteractionDeclaration>(new InteractionDeclaration);
  view->declaration_ = declaration;
  SmallVector<unsigned> path;
  auto extracted = impl_->sequence(*view, body->front(), path, work);
  if (!extracted)
    return extracted.takeError();
  auto *result = view.get();
  impl_->declarations.try_emplace(declaration, std::move(view));
  return result;
}
} // namespace zkc
