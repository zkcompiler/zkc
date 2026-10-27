#include "../RealizationSubject.h"
#include "../ScopedCandidate.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
using Values = SmallVector<Value>;
using mathematical::CandidatePorts;
using mathematical::ScopedCandidate;
class ScopedReader {
  protocol_ir::ProtocolModuleOp original, candidate;
  const protocol::SourceExecutionClosure &source;
  const ScopedCandidate &actual;
  CandidatePorts ports;
  SymbolTable targetSymbols, originalDeclarations;
  MathematicalSelectionPolicy fallback;
  mathematical::RealizationWork &work;
  mathematical::VerificationDecision &outcome;
  llvm::DenseSet<Operation *> usedBindings, visitedFunctions;
  uint64_t &remaining, &bytes;

  LogicalResult refuse(StringRef reason) {
    if (outcome.outcome !=
            mathematical::VerificationObservation::RequiredCapacity &&
        outcome.outcome !=
            mathematical::VerificationObservation::OptionalCapacity)
      outcome = {mathematical::VerificationObservation::Mismatch, reason.str()};
    return diagnostics::emit(candidate.emitOpError(),
                             "numerical-lowering-correspondence", reason);
  }
  bool charge(uint64_t cost) {
    if (cost > remaining) {
      outcome = {mathematical::VerificationObservation::RequiredCapacity,
                 "scoped numerical context comparison capacity"};
      return false;
    }
    remaining -= cost;
    return true;
  }
  bool account(Operation *op) {
    if (!charge(1 + ports.inputs(op).size() + ports.outputs(op).size()))
      return false;
    visitedFunctions.insert(op->getParentOp());
    if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding")) {
      auto binding =
          targetSymbols.lookup<runtime::BindingOp>(reference.getValue());
      if (!binding)
        return false;
      usedBindings.insert(binding);
    }
    return true;
  }
  LogicalResult body(func::FuncOp before, func::FuncOp after,
                     ArrayRef<unsigned> capturePositions = {},
                     unsigned capturePrefix = 0, unsigned depth = 0) {
    if (depth > 64 || !before || !after ||
        !charge(before.getNumArguments() + after.getNumArguments() + 1))
      return refuse("scoped body or comparison depth changed");
    visitedFunctions.insert(after);
    NamedAttrList expected(before->getAttrs()), attributes(after->getAttrs());
    IRMapping values;
    if (capturePositions.empty()) {
      if (before.getFunctionType() != after.getFunctionType())
        return refuse("scoped numerical function interface changed");
      values.map(before.getArguments(), after.getArguments());
    } else {
      // Positions refer only to the trailing captured data. Scope, induction,
      // state and matched payload prefixes retain separate coordinates.
      if (before.getNumArguments() != capturePrefix + capturePositions.size())
        return refuse("source capture partition changed");
      SmallVector<unsigned> positions;
      for (unsigned i = 0; i < capturePrefix; ++i)
        positions.push_back(i);
      for (unsigned position : capturePositions)
        positions.push_back(capturePrefix + position);
      unsigned width = 0;
      for (auto [argument, position] : zip(before.getArguments(), positions)) {
        if (position >= after.getNumArguments() ||
            argument.getType() != after.getArgument(position).getType())
          return refuse("scoped numerical capture type changed");
        values.map(argument, after.getArgument(position));
        width = std::max(width, position + 1);
      }
      if (width != after.getNumArguments() ||
          before.getResultTypes() != after.getResultTypes())
        return refuse("scoped numerical capture width changed");
      expected.set("function_type", after->getAttr("function_type"));
      if (auto premises =
              before->getAttrOfType<ArrayAttr>("data.preconditions")) {
        SmallVector<Attribute> transported;
        for (Attribute premise : premises) {
          if (!charge(1))
            return failure();
          if (auto bound = dyn_cast<data::IndexBoundAttr>(premise))
            transported.push_back(data::IndexBoundAttr::get(
                before.getContext(), positions[bound.getIndexArg()],
                positions[bound.getContainerArg()], bound.getAxis()));
          else {
            auto equal = cast<data::EqualExtentAttr>(premise);
            transported.push_back(data::EqualExtentAttr::get(
                before.getContext(), positions[equal.getLeftArg()],
                equal.getLeftAxis(), positions[equal.getRightArg()],
                equal.getRightAxis()));
          }
        }
        expected.set("data.preconditions",
                     ArrayAttr::get(before.getContext(), transported));
      }
    }
    if (depth)
      expected.set("sym_name", after.getSymNameAttr());
    if (expected.getDictionary(before.getContext()) !=
        after->getAttrDictionary())
      return refuse("scoped declaration, origin or premises changed");
    auto found = source.bodies.find(before.getSymName().str());
    if (found == source.bodies.end())
      return refuse("source scoped body missing");
    auto *cursor = ports.first(&after.front());
    for (const auto &step : found->second) {
      auto *op = step.operation;
      if (!charge(1 + step.inputs.size() + step.outputs.size()))
        return failure();
      Values inputs;
      for (Value input : step.inputs) {
        auto mapped = values.lookupOrNull(input);
        if (!mapped)
          return refuse("lost an actual source payload operand");
        inputs.push_back(mapped);
      }
      if (auto compute = dyn_cast<exec::ComputeOp>(op)) {
        SymbolTableCollection symbols;
        auto entry = compute.resolveCallee(symbols);
        auto policy = effectiveSelectionPolicy(compute, fallback);
        if (!entry || failed(policy))
          return refuse("unresolved source computation");
        finite::VerificationLimits limits;
        limits.sharedReader = &work.requiredFiniteChecking;
        limits.sharedComparison = &work.optionalFiniteChecking;
        limits.candidate = &actual;
        finite::VerificationResult result{finite::VerificationStatus::Mismatch,
                                          {}};
        auto *begin = cursor;
        auto outputs = verifyComputationRecipes(
            entry, candidate, compute.getSite(), inputs, cursor, remaining,
            bytes, *policy, limits, result);
        if (failed(outputs)) {
          outcome = mathematical::verificationDecision(result);
          outcome.invocation = mathematical::realizationSubject(compute);
          return refuse("actual scoped numerical recipe differs");
        }
        if (outputs->size() != step.outputs.size())
          return refuse("numerical return arity changed");
        for (auto [expected, output] : zip(step.outputs, *outputs)) {
          if (expected.getType() != output.getType())
            return refuse("numerical return coordinate changed type");
          values.map(expected, output);
        }
        for (auto *at = begin; at != cursor; at = ports.next(at)) {
          if (!at || ports
                         .walk(at,
                               [&](Operation *nested) {
                                 return account(nested)
                                            ? WalkResult::advance()
                                            : WalkResult::interrupt();
                               })
                         .wasInterrupted())
            return refuse(
                "numerical span contains an unaccounted body or binding");
        }
        continue;
      }
      if (!cursor || op->getName() != cursor->getName() ||
          op->getAttrDictionary() != cursor->getAttrDictionary() ||
          step.outputs.size() != ports.outputs(cursor).size() ||
          !equal(ValueRange(step.outputs).getTypes(),
                 ports.outputs(cursor).getTypes()) ||
          step.regions.size() != ports.bodies(cursor) ||
          step.conditional != actual.get(cursor)->conditional ||
          !account(cursor))
        return refuse("ordered scoped context, site or result changed");
      SmallVector<unsigned> captures;
      unsigned prefix = 0;
      if (!step.regions.empty()) {
        prefix = isa<exec::RangeOp>(op) ? 2 + step.outputs.size() : 1;
        if (inputs.size() < prefix)
          return refuse("invalid control capture prefix");
        Values canonical(ArrayRef(inputs).take_front(prefix));
        llvm::DenseMap<Value, unsigned> seen;
        for (Value input : ArrayRef(inputs).drop_front(prefix)) {
          auto [position, inserted] = seen.try_emplace(input, seen.size());
          captures.push_back(position->second);
          if (inserted)
            canonical.push_back(input);
        }
        inputs = std::move(canonical);
      }
      if (ports.inputs(cursor) != ValueRange(inputs))
        return refuse("ordered scoped operand or capture changed");
      for (unsigned i = 0; i < step.regions.size(); ++i) {
        auto beforeBody = step.regions[i];
        auto *block = ports.body(cursor, i);
        auto afterBody = block ? dyn_cast<func::FuncOp>(block->getParentOp())
                               : func::FuncOp();
        if (beforeBody.getNumArguments() < captures.size())
          return refuse("invalid outlined source signature");
        unsigned fixed = beforeBody.getNumArguments() - captures.size();
        if (failed(body(beforeBody, afterBody, captures, fixed, depth + 1)))
          return failure();
      }
      values.map(step.outputs, ports.outputs(cursor));
      cursor = ports.next(cursor);
    }
    return cursor ? refuse("extra executable work after source body")
                  : success();
  }

public:
  ScopedReader(protocol_ir::ProtocolModuleOp original,
               protocol_ir::ProtocolModuleOp candidate,
               protocol_ir::ProtocolModuleOp declarations,
               const protocol::SourceExecutionClosure &source,
               const ScopedCandidate &actual,
               MathematicalSelectionPolicy fallback,
               mathematical::RealizationWork &work,
               mathematical::VerificationDecision &outcome)
      : original(original), candidate(candidate), source(source),
        actual(actual), ports(&actual), targetSymbols(candidate),
        originalDeclarations(declarations), fallback(fallback), work(work),
        outcome(outcome), remaining(work.numericalContextChecking),
        bytes(work.numericalCheckSiteBytes) {}
  LogicalResult run() {
    bool retainedFinite = false;
    candidate.walk([&](Operation *op) {
      retainedFinite |= isa<exec::CollectOp, exec::FoldOp>(op);
    });
    auto next = candidate.getBody().front().begin();
    SymbolTable sourceSymbols(original);
    auto generated = [&](Operation &op) {
      return (isa<func::FuncOp>(op) && op.hasAttr("runtime.region")) ||
             (isa<runtime::BindingOp>(op) &&
              !sourceSymbols.lookup(SymbolTable::getSymbolName(&op)));
    };
    for (auto &op : original.getBody().front()) {
      auto function = dyn_cast<func::FuncOp>(op);
      bool mathematical =
          isa<data::DomainOp>(op) ||
          (function && !protocol::isScopedExecutionFunction(function));
      if (isa<mlir::ModuleOp>(op) || (mathematical && !retainedFinite) ||
          (function && function->hasAttr("runtime.region")))
        continue;
      while (next != candidate.getBody().front().end() && generated(*next))
        ++next;
      if (next == candidate.getBody().front().end())
        return refuse("missing original declaration");
      auto *target = &*next++;
      if (function && !mathematical) {
        if (failed(body(function, dyn_cast<func::FuncOp>(target))))
          return failure();
      } else {
        Operation *expected = &op;
        if (auto binding = dyn_cast<runtime::BindingOp>(op))
          expected = originalDeclarations.lookup(binding.getSymName());
        if (!expected ||
            !OperationEquivalence::isEquivalentTo(
                expected, target, OperationEquivalence::IgnoreLocations))
          return refuse("retained declaration or participant order changed");
        if (function)
          visitedFunctions.insert(target);
      }
    }
    while (next != candidate.getBody().front().end())
      if (!generated(*next++))
        return refuse("extra unaccounted declaration");
    for (auto &op : candidate.getBody().front()) {
      if (isa<func::FuncOp>(op) && !visitedFunctions.contains(&op))
        return refuse("unaccounted scoped function");
      if (isa<runtime::BindingOp>(op) &&
          !sourceSymbols.lookup(SymbolTable::getSymbolName(&op)) &&
          !usedBindings.contains(&op))
        return refuse("unaccounted numerical binding");
    }
    outcome = {mathematical::VerificationObservation::Verified, {}};
    return success();
  }
};
} // namespace
LogicalResult
verifyScopedNumericalContext(protocol_ir::ProtocolModuleOp original,
                             protocol_ir::ProtocolModuleOp candidate,
                             protocol_ir::ProtocolModuleOp declarations,
                             MathematicalSelectionPolicy policy,
                             mathematical::RealizationWork &work,
                             mathematical::VerificationDecision &outcome) {
  if (original->getAttrDictionary() != candidate->getAttrDictionary())
    return failure();
  auto source = protocol::readSourceExecutionClosure(original);
  // Finite requests remain pending until physical selection. This edge
  // accounts for their actual operands, attributes and unchanged mathematical
  // declarations while checking each numerical replacement independently.
  auto actual =
      ScopedCandidate::read(candidate, ScopedCandidate::Requests::Retained);
  if (!source || !actual) {
    if (!source)
      diagnostics::emit(original.emitOpError(), source.takeError());
    if (!actual)
      diagnostics::emit(candidate.emitOpError(), actual.takeError());
    return failure();
  }
  if (!chargeCopy(original, work.numericalContextChecking) ||
      !chargeCopy(candidate, work.numericalContextChecking)) {
    outcome = {mathematical::VerificationObservation::RequiredCapacity,
               "scoped numerical context copy capacity"};
    return failure();
  }
  return ScopedReader(original, candidate, declarations, *source, **actual,
                      policy, work, outcome)
      .run();
}
} // namespace zkc::computation
