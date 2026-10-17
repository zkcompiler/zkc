#include "zkc/Analysis/TotalClosure.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", detail);
}
using Dependencies = llvm::DenseMap<Value, BitVector>;
} // namespace
struct TotalClosure::Impl {
  Operation *unit;
  SymbolTableCollection &tables;
  NativeTypePolicies types;
  func::FuncOp entry;
  llvm::DenseMap<Operation *, std::unique_ptr<TotalSummary>> summaries;
  bool refused = false;
  llvm::DenseSet<Operation *> active;
  uint64_t remainingDependencyWork = 1000000;
  unsigned remainingOperations = 100000;
  uint64_t remainingObservationWork = 1000000;

  LogicalResult charge(Operation *op, uint64_t work) {
    if (work > remainingDependencyWork)
      return limit(op, "helper dependency work exceeds 1000000 words/indices");
    remainingDependencyWork -= work;
    return success();
  }
  LogicalResult limit(Operation *op, StringRef detail) {
    return diagnostics::emit(op->emitOpError(), "mathematical-analysis-limit",
                             detail);
  }
  static std::vector<unsigned> indices(const BitVector &bits) {
    std::vector<unsigned> result;
    for (int bit = bits.find_first(); bit >= 0; bit = bits.find_next(bit))
      result.push_back(bit);
    return result;
  }
  static BitVector substitute(const BitVector &dependencies, ValueRange inputs,
                              const Dependencies &environment, unsigned size) {
    BitVector result(size);
    for (int index = dependencies.find_first(); index >= 0;
         index = dependencies.find_next(index))
      result |= environment.lookup(inputs[index]);
    return result;
  }

  LogicalResult checkObservations(func::FuncOp function) {
    auto chargeObservation = [&](Operation *op) -> LogicalResult {
      uint64_t work = 1 + op->getNumOperands() + op->getNumResults();
      if (work > remainingObservationWork)
        return limit(function,
                     "polynomial observation expansion exceeds 1000000 slots");
      remainingObservationWork -= work;
      return success();
    };
    for (auto &op : function.front())
      if (failed(chargeObservation(&op)))
        return failure();
    OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(function->clone()));
    SmallVector<func::CallOp> pending;
    scratch->walk([&](func::CallOp call) { pending.push_back(call); });
    while (!pending.empty()) {
      auto call = pending.pop_back_val();
      auto helper =
          tables.lookupSymbolIn<func::FuncOp>(unit, call.getCalleeAttr());
      // Signatures and the acyclic closure were checked before this replay.
      if (!helper || helper.isExternal())
        return refuse(function, "missing polynomial observation helper");
      IRMapping mapping;
      for (auto [argument, value] :
           zip(helper.getArguments(), call.getOperands()))
        mapping.map(argument, value);
      OpBuilder builder(call);
      for (auto &op : helper.front().without_terminator()) {
        if (failed(chargeObservation(&op)))
          return failure();
        auto *copy = builder.clone(op, mapping);
        if (auto nested = dyn_cast<func::CallOp>(copy))
          pending.push_back(nested);
      }
      for (auto [value, returned] :
           zip(call.getResults(), helper.front().back().getOperands()))
        value.replaceAllUsesWith(mapping.lookup(returned));
      call.erase();
    }
    bool formalPolynomial = any_of(function.getArgumentTypes(), [](Type type) {
      return isa<poly::PolynomialType>(type);
    });
    poly::Degrees degrees;
    return poly::deriveDegrees(scratch->front(), degrees, formalPolynomial);
  }

public:
  Impl(Operation *unit, SymbolTableCollection &tables, func::FuncOp entry)
      : unit(unit), tables(tables), types(unit), entry(entry) {}
  LogicalResult get(func::FuncOp function, const TotalSummary *&result) {
    if (!function)
      return refuse(unit, "missing pure helper definition");
    if (failed(function->getName().verifyInvariants(function)))
      return failure();
    auto dataType = [&](Type type) {
      auto policy = types.get(type);
      return policy && policy->total;
    };
    if (function->getParentOp() != unit || function.isExternal() ||
        (function == entry ? !function.isPublic() : !function.isPrivate()) ||
        !hasSingleElement(function.getBody()) || function.front().empty() ||
        !isa<func::ReturnOp>(function.front().back()) ||
        function.front().getArgumentTypes() != function.getArgumentTypes() ||
        function.front().back().getOperandTypes() !=
            function.getResultTypes() ||
        !all_of(function.getArgumentTypes(), dataType) ||
        !all_of(function.getResultTypes(), dataType))
      return refuse(function,
                    "requires a defined entry or private helper with closed "
                    "mathematical signatures");
    for (auto attr : function->getAttrs())
      if (!is_contained(ArrayRef<StringRef>{"sym_name", "sym_visibility",
                                            "function_type",
                                            "data.preconditions"},
                        attr.getName().getValue()))
        return refuse(function, "unsupported pure helper attribute");
    if (auto found = summaries.find(function); found != summaries.end()) {
      result = found->second.get();
      return success();
    }
    if (!active.insert(function).second)
      return refuse(function, "pure helper calls must be acyclic");
    if (active.size() > 64)
      return limit(function, "helper depth exceeds 64");
    if (function.getNumArguments() > 100000)
      return limit(function, "helper signature exceeds analysis work bound");
    TotalSummary summary;
    Dependencies environment;
    const unsigned size = function.getNumArguments();
    const uint64_t words = (uint64_t(size) + 63) / 64;
    if (failed(charge(function, words * size)))
      return failure();
    for (auto [index, argument] : enumerate(function.getArguments())) {
      BitVector dependency(size);
      dependency.set(index);
      environment[argument] = std::move(dependency);
    }
    for (auto &operation : function.front()) {
      auto *op = &operation;
      if (failed(op->getName().verifyInvariants(op)))
        return failure();
      if (failed(verifyOperation(op, Helper)))
        return failure();
      if (!remainingOperations || ++summary.expandedOperations > 100000)
        return limit(op, "helper analysis exceeds 100000 operations");
      --remainingOperations;
      if (failed(
              charge(op, uint64_t(op->getNumResults() + op->getNumOperands()) *
                             words)))
        return failure();
      for (auto operand : op->getOperands())
        if (!environment.count(operand))
          return refuse(op, "helper operand is outside its closed body");
      if (auto returned = dyn_cast<func::ReturnOp>(op)) {
        if (op != &function.front().back())
          return refuse(op, "helper return must terminate its body");
        for (auto value : returned.getOperands())
          summary.results.push_back(environment.lookup(value));
      } else if (isTotal(op)) {
        summary.observesPolynomial |= isa<poly::PolynomialCoefficientsOp>(op);
        if (failed(verifyTotalTypes(op, types)))
          return failure();
        finite::Summary finiteSummary;
        if (finite::isComputation(op) &&
            failed(finite::summarize(op, finiteSummary)))
          return failure();
        for (auto [index, value] : enumerate(op->getResults())) {
          BitVector dependency(size);
          auto inputs = operandDependencies(op, index);
          if (failed(inputs))
            return failure();
          for (unsigned input : *inputs)
            dependency |= environment.lookup(op->getOperand(input));
          if (failed(charge(op, dependency.count())))
            return failure();
          summary.requirements.insert(indices(dependency));
          environment[value] = std::move(dependency);
        }
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        const TotalSummary *callee;
        if (failed(get(call, callee)))
          return failure();
        if (callee->expandedOperations > 100000 - summary.expandedOperations)
          return limit(call, "expanded analysis exceeds 100000 operations");
        summary.expandedOperations += callee->expandedOperations;
        summary.observesPolynomial |= callee->observesPolynomial;
        summary.depth = std::max(summary.depth, callee->depth + 1);
        if (summary.depth > 64)
          return limit(call, "helper depth exceeds 64");
        for (const auto &requirement : callee->requirements) {
          if (failed(charge(op, uint64_t(requirement.size()) * words)))
            return failure();
          BitVector dependency(size);
          for (unsigned input : requirement)
            dependency |= environment.lookup(call.getOperand(input));
          if (failed(charge(op, dependency.count())))
            return failure();
          summary.requirements.insert(indices(dependency));
        }
        for (auto [value, dependency] :
             zip(call.getResults(), callee->results)) {
          if (failed(charge(op, uint64_t(dependency.count()) * words)))
            return failure();
          environment[value] =
              substitute(dependency, call.getOperands(), environment, size);
        }
      } else {
        return refuse(op,
                      "helper contains an operation without total semantics");
      }
    }
    if (summary.observesPolynomial && failed(checkObservations(function)))
      return failure();
    for (const auto &requirement : summary.requirements)
      summary.replayIndices += requirement.size();
    for (const auto &dependency : summary.results)
      summary.replayIndices += dependency.count();
    active.erase(function);
    result =
        summaries
            .try_emplace(function,
                         std::make_unique<TotalSummary>(std::move(summary)))
            .first->second.get();
    return success();
  }
  LogicalResult get(func::CallOp call, const TotalSummary *&result) {
    auto function = tables.lookupNearestSymbolFrom<func::FuncOp>(
        call, call.getCalleeAttr());
    if (!function ||
        !llvm::equal(function.getArgumentTypes(), call.getOperandTypes()) ||
        !llvm::equal(function.getResultTypes(), call.getResultTypes()))
      return refuse(call, "requires a matching pure helper");
    return get(function, result);
  }
  LogicalResult verify() {
    auto *owner = unit;
    if (!owner->hasTrait<OpTrait::SymbolTable>() ||
        owner->getNumRegions() != 1 || !hasSingleElement(owner->getRegion(0)))
      return refuse(owner, "expected a single-block symbol-table owner");
    if (entry && (entry->getParentOp() != owner || !entry.isPublic()))
      return refuse(owner,
                    "entry must be a public function owned by this closure");
    if (failed(finite::verifyClosure(owner)))
      return failure();
    for (auto function : owner->getRegion(0).front().getOps<func::FuncOp>()) {
      const TotalSummary *summary;
      if (failed(get(function, summary)))
        return failure();
    }
    return success();
  }
};

TotalClosure::TotalClosure(Operation *owner, SymbolTableCollection &symbols,
                           func::FuncOp entry)
    : impl(std::make_unique<Impl>(owner, symbols, entry)) {}
TotalClosure::~TotalClosure() = default;
LogicalResult TotalClosure::verify() {
  if (impl->refused)
    return failure();
  auto result = impl->verify();
  impl->refused = failed(result);
  return result;
}
LogicalResult TotalClosure::get(func::FuncOp function,
                                const TotalSummary *&result) {
  result = nullptr;
  if (impl->refused)
    return failure();
  auto status = impl->get(function, result);
  impl->refused = failed(status);
  return status;
}
LogicalResult TotalClosure::get(func::CallOp call,
                                const TotalSummary *&result) {
  result = nullptr;
  if (impl->refused)
    return failure();
  auto status = impl->get(call, result);
  impl->refused = failed(status);
  return status;
}
LogicalResult verifyTotalClosure(Operation *owner, func::FuncOp entry) {
  SymbolTableCollection symbols;
  return TotalClosure(owner, symbols, entry).verify();
}
} // namespace zkc::mathematical
