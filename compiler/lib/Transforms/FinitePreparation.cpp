#include "FinitePreparation.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>
#include <cassert>

using namespace mlir;
namespace zkc::finite {
CallbackStructuralWork::CallbackStructuralWork(ComputationWork &shared,
                                               OptimizationOutcome &outcome)
    : shared(shared), outcome(outcome),
      initial(std::min(shared.structural, callbackStructuralLimit)),
      limitedByCallback(shared.structural > callbackStructuralLimit),
      remaining(shared) {
  remaining.structural = initial;
}
CallbackStructuralWork::~CallbackStructuralWork() {
  assert(remaining.structural <= initial && "optional work cannot be refilled");
  shared.structural -= initial - remaining.structural;
  shared.equations = remaining.equations;
  shared.evidence = remaining.evidence;
  if (limitedByCallback && outcome.capacity &&
      outcome.capacity->owner == WorkOwner::Structural)
    outcome.capacity->owner = WorkOwner::FiniteCallbackStructural;
}

namespace {
constexpr uint64_t exceededSize = callbackStructuralLimit + 1;
uint64_t addSize(uint64_t left, uint64_t right) {
  return left >= exceededSize || right >= exceededSize - left ? exceededSize
                                                              : left + right;
}
uint64_t operationWork(Operation *op) {
  return 1 + uint64_t(op->getNumOperands()) + op->getNumResults();
}
struct HelperSize {
  // Includes intermediate call operations, even though inlining erases them.
  uint64_t copying = 0;
  uint64_t expandedOperations = 0;
  // Only the root clone copies its function operation and terminator.
  uint64_t rootOverhead = 0;
  unsigned depth = 1;
  bool arrayProjections = false;
};
class CallbackSizer {
  Operation *root;
  bool singleResultCalls;
  uint64_t &structural;
  OptimizationOutcome &outcome;
  SymbolTableCollection symbols;
  llvm::DenseMap<Operation *, HelperSize> summaries;
  llvm::DenseSet<Operation *> active;

  bool charge(uint64_t amount) {
    return consumeComputationWork(structural, amount, WorkOwner::Structural,
                                  &outcome);
  }
  std::optional<HelperSize> decline(OptimizationReason reason) {
    outcome = {OptimizationStatus::Unsupported, reason};
    return std::nullopt;
  }

public:
  CallbackSizer(Operation *root, uint64_t &structural,
                OptimizationOutcome &outcome, bool singleResultCalls)
      : root(root), singleResultCalls(singleResultCalls),
        structural(structural), outcome(outcome) {}

  std::optional<HelperSize> read(func::FuncOp helper) {
    // Match admitted helper depth, including paths through memoized children.
    if (active.size() >= 64)
      return decline(OptimizationReason::Depth);
    if (auto found = summaries.find(helper); found != summaries.end()) {
      if (active.size() + found->second.depth > 64)
        return decline(OptimizationReason::Depth);
      return found->second;
    }
    if (!active.insert(helper).second)
      return decline(OptimizationReason::Cycle);
    auto leave = llvm::scope_exit([&] { active.erase(helper); });
    if (helper.isExternal() || !helper.getBody().hasOneBlock() ||
        helper.front().empty())
      return decline(OptimizationReason::ImplementationRestriction);
    if (!charge(operationWork(helper) + helper.getNumArguments()))
      return std::nullopt;
    HelperSize size;
    size.rootOverhead = operationWork(helper);
    for (auto &op : helper.front()) {
      if (!charge(operationWork(&op)))
        return std::nullopt;
      // Do not expand away conditional admission, including unused results.
      if (isComputation(&op) || op.getNumRegions())
        return decline(OptimizationReason::ImplementationRestriction);
      if (&op == &helper.front().back()) {
        if (!isa<func::ReturnOp>(op))
          return decline(OptimizationReason::ImplementationRestriction);
        size.rootOverhead = addSize(size.rootOverhead, operationWork(&op));
        break;
      }
      size.copying = addSize(size.copying, operationWork(&op));
      if (auto call = dyn_cast<func::CallOp>(op)) {
        // The independent module reader follows single-result source calls.
        // Keep other valid calls ordered; normalization must not hide them.
        if (singleResultCalls && call.getNumResults() != 1)
          return decline(OptimizationReason::ImplementationRestriction);
        // Every edge is charged, including edges to an already sized helper.
        if (!charge(1))
          return std::nullopt;
        auto callee =
            symbols.lookupSymbolIn<func::FuncOp>(root, call.getCalleeAttr());
        if (!callee)
          return decline(OptimizationReason::ImplementationRestriction);
        auto child = read(callee);
        if (!child)
          return std::nullopt;
        size.copying = addSize(size.copying, child->copying);
        size.expandedOperations =
            addSize(size.expandedOperations, child->expandedOperations);
        size.depth = std::max(size.depth, child->depth + 1);
        size.arrayProjections |= child->arrayProjections;
      } else {
        size.expandedOperations = addSize(size.expandedOperations, 1);
        size.arrayProjections |= isa<algebra::ArrayAtOp>(op);
      }
      // This is a proved fixed-threshold result, not temporary exhaustion.
      // Its partial operation/overhead counts are never used as exact costs.
      if (size.copying == exceededSize)
        break;
    }
    summaries[helper] = size;
    return size;
  }
};
} // namespace

std::optional<CallbackPreparation>
sizeCallbackPreparation(const Computation &computation, Operation *root,
                        uint64_t &structural, OptimizationOutcome &outcome) {
  auto helper = dyn_cast<func::FuncOp>(computation.helper);
  if (!helper) {
    outcome = {OptimizationStatus::Unsupported,
               OptimizationReason::ImplementationRestriction};
    return std::nullopt;
  }
  auto signature = computation.signature;
  bool module = signature.getNumResults() == 1 &&
                isa<algebra::GroupType>(signature.getResult(0));
  CallbackSizer sizer(root, structural, outcome, module);
  auto size = sizer.read(helper);
  if (!size)
    return std::nullopt;
  uint64_t context = 4 + 2 * uint64_t(computation.signature.getNumInputs()) +
                     2 * uint64_t(computation.signature.getNumResults());
  // Every callback needs admission scanning. Only helpers containing array
  // projections need the two folding scans (including their terminator).
  auto scans = size->expandedOperations;
  if (size->arrayProjections)
    scans = addSize(scans, addSize(scans, addSize(scans, 2)));
  return CallbackPreparation{addSize(addSize(size->copying, size->rootOverhead),
                                     addSize(scans, context)),
                             size->arrayProjections};
}
} // namespace zkc::finite
