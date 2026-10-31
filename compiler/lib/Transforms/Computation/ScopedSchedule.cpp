#include "../ScopedCandidate.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
using Values = SmallVector<Value>;
using mathematical::ScopedCandidate;
bool chargeComparison(uint64_t amount, uint64_t &remaining,
                      finite::VerificationResult &outcome) {
  if (amount > remaining) {
    outcome = {finite::VerificationStatus::RequiredCapacity,
               "schedule comparison capacity",
               CapacityCause{WorkOwner::AlgorithmChecking, amount, remaining}};
    return false;
  }
  remaining -= amount;
  return true;
}
// Bound actual nesting before any recursive MLIR walk or formation check.
// Native readers allow depth 64 within a definition; the two enclosing module
// operations account for the additional levels here. Charge all operations,
// regions, blocks and raw SSA slots, including empty malformed structures.
bool inspectForComparison(Operation *root, uint64_t &remaining,
                          finite::VerificationResult &outcome) {
  SmallVector<std::pair<Operation *, unsigned>> pending{{root, 0}};
  while (!pending.empty()) {
    auto [op, depth] = pending.pop_back_val();
    if (depth > 66) {
      outcome = {finite::VerificationStatus::RequiredCapacity,
                 "schedule inspection depth",
                 CapacityCause{WorkOwner::AlgorithmChecking}};
      return false;
    }
    if (!chargeComparison(1 + op->getNumOperands() + op->getNumResults(),
                          remaining, outcome))
      return false;
    for (auto &region : op->getRegions()) {
      if (!chargeComparison(1, remaining, outcome))
        return false;
      for (auto &block : region) {
        if (!chargeComparison(1 + block.getNumArguments(), remaining, outcome))
          return false;
        for (auto &child : block) {
          // Every pending operation still needs at least one unit. Refuse
          // before allocating a worklist larger than the remaining allowance.
          if (pending.size() >= remaining) {
            chargeComparison(pending.size() + 1, remaining, outcome);
            return false;
          }
          pending.emplace_back(&child, depth + 1);
        }
      }
    }
  }
  return true;
}
// Consume only the admitted association read from the actual immutable SCF
// schedule. Mathematical source, optional selection and recipe producers are
// absent from this transition. Outlined functions retain their exact inventory.
class Consumer {
  const ScopedCandidate &source;
  OpBuilder &builder;
  uint64_t &remaining;
  std::optional<CapacityCause> *capacity;
  llvm::DenseMap<Operation *, func::FuncOp> functions;

  bool charge(uint64_t amount) {
    if (amount > remaining) {
      if (capacity)
        *capacity =
            CapacityCause{WorkOwner::AlgorithmExpansion, amount, remaining};
      return false;
    }
    remaining -= amount;
    return true;
  }
  LogicalResult body(func::FuncOp input, func::FuncOp output) {
    builder.setInsertionPointToEnd(output.addEntryBlock());
    exec::ScopedExecutionBuilder control(builder, output);
    IRMapping values;
    values.map(input.getArguments().drop_front(),
               output.getArguments().drop_front());
    for (auto *op = source.first(&input.front()); op; op = source.next(op)) {
      auto *step = source.get(op);
      if (!step)
        return failure();
      // Only range/branch/match steps construct scopes and transfers. Charge
      // scalar invocations for their invocation/dispatch pair and slots,
      // including the shared failure continuation on its first use.
      bool structured = isa<exec::RangeOp, exec::TestOp, exec::MatchOp>(op);
      uint64_t width = step->inputs.size() + step->outputs.size();
      if (!charge(structured ? 64 + 16 * width : 16 + 2 * width))
        return failure();
      Values inputs;
      for (Value value : step->inputs) {
        auto actual = values.lookupOrNull(value);
        if (!actual)
          return failure();
        inputs.push_back(actual);
      }
      control.setLocation(op->getLoc());
      auto args = ValueRange(inputs);
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        if (source.next(op))
          return failure();
        if (isa<exec::ReturnOp>(op))
          control.returned(args);
        else
          control.complete(args);
        return success();
      }
      if (auto reject = dyn_cast<exec::RejectOp>(op)) {
        if (source.next(op))
          return failure();
        control.reject(reject.getReason(), reject.getSite());
        return success();
      }
      if (isa<runtime::ReleaseBindingsOp>(op)) {
        control.release(args);
        continue;
      }
      Values outputs;
      auto types = ValueRange(step->outputs).getTypes();
      auto outline = [&](unsigned index) {
        return index < step->regions.size()
                   ? functions.lookup(step->regions[index])
                   : func::FuncOp();
      };
      if (auto range = dyn_cast<exec::RangeOp>(op)) {
        unsigned states = step->outputs.size();
        outputs = control.loop(args[0], args[1], args.slice(2, states),
                               args.drop_front(2 + states), types,
                               step->conditional, range.getSite(), outline);
      } else if (auto test = dyn_cast<exec::TestOp>(op))
        outputs = control.conditional(args[0], args.drop_front(), types,
                                      test.getSite(), outline);
      else if (auto match = dyn_cast<exec::MatchOp>(op)) {
        SmallVector<std::string> alternatives;
        for (auto alternative : match.getAlternatives())
          alternatives.push_back(
              cast<StringAttr>(alternative).getValue().str());
        outputs = control.match(args[0], args.drop_front(), types, alternatives,
                                match.getSite(), outline);
      } else if (isa<exec::ApplyOp, exec::BooleanOp, exec::VariantOp>(op))
        outputs = control.invoke(op->getName().getStringRef(), types,
                                 control.scoped(args), op->getAttrs());
      else
        return failure();
      if (outputs.size() != step->outputs.size())
        return failure();
      values.map(step->outputs, outputs);
    }
    return failure();
  }

public:
  Consumer(const ScopedCandidate &source, OpBuilder &builder,
           uint64_t &remaining, std::optional<CapacityCause> *capacity)
      : source(source), builder(builder), remaining(remaining),
        capacity(capacity) {}
  LogicalResult run(protocol_ir::ProtocolModuleOp input,
                    protocol_ir::ProtocolModuleOp output) {
    for (auto &definition : input.getBody().front()) {
      builder.setInsertionPointToEnd(&output.getBody().front());
      if (isa<runtime::BindingOp>(definition)) {
        builder.clone(definition);
        continue;
      }
      auto function = cast<func::FuncOp>(definition);
      if (!charge(16 + function.getNumArguments() + function.getNumResults()))
        return failure();
      auto target = func::FuncOp::create(builder, function.getLoc(),
                                         function.getSymName(),
                                         function.getFunctionType());
      target->setAttrs(function->getAttrs());
      functions[function] = target;
    }
    for (auto function : input.getBody().front().getOps<func::FuncOp>())
      if (failed(body(function, functions.lookup(function))))
        return failure();
    return success();
  }
};

// Compare the two admitted native associations, not an exported byte model or
// a replay of Consumer. Each reader owns its actual administrative CFG/SCF,
// custody and closure checks. Here every declaration and semantic step must
// agree, including unused roots and the identity/order of outlined children.
// Iterating definitions once avoids expanding shared control bodies again.
class NativeScheduleComparison {
  const protocol::SourceExecutionClosure &source, &actual;
  uint64_t &remaining;
  finite::VerificationResult &outcome;
  llvm::DenseMap<Operation *, Operation *> definitions;

  bool charge(uint64_t amount = 1) {
    return chargeComparison(amount, remaining, outcome);
  }
  bool body(func::FuncOp before, func::FuncOp after,
            ArrayRef<protocol::SourceExecutionStep> expected,
            ArrayRef<protocol::SourceExecutionStep> observed) {
    if (expected.size() != observed.size() ||
        before.getNumArguments() != after.getNumArguments())
      return false;
    // Associate data definitions bijectively. Uses must select the same
    // positional formal or preceding result; equal types alone do not suffice.
    llvm::DenseMap<Value, Value> values, inverse;
    auto associate = [&](Value left, Value right) {
      return charge() && left.getType() == right.getType() &&
             values.try_emplace(left, right).second &&
             inverse.try_emplace(right, left).second;
    };
    for (auto [left, right] : zip(before.getArguments(), after.getArguments()))
      if (!associate(left, right))
        return false;
    for (auto [left, right] : zip(expected, observed)) {
      if (!charge() || !left.operation || !right.operation ||
          left.operation->getName() != right.operation->getName() ||
          left.operation->getAttrDictionary() !=
              right.operation->getAttrDictionary() ||
          left.operation->getOperandTypes() !=
              right.operation->getOperandTypes() ||
          left.operation->getResultTypes() !=
              right.operation->getResultTypes() ||
          left.inputs.size() != right.inputs.size() ||
          left.outputs.size() != right.outputs.size() ||
          left.regions.size() != right.regions.size() ||
          left.conditional != right.conditional)
        return false;
      // Exact native attributes include binding references, typed invocation
      // parameters, sites, variant labels, Boolean values and stop reasons.
      for (auto [input, observedInput] : zip(left.inputs, right.inputs))
        if (!charge() || input.getType() != observedInput.getType() ||
            values.lookup(input) != observedInput)
          return false;
      for (auto [output, observedOutput] : zip(left.outputs, right.outputs))
        if (!associate(output, observedOutput))
          return false;
      for (auto [region, observedRegion] : zip(left.regions, right.regions)) {
        func::FuncOp expectedRegion = region, actualRegion = observedRegion;
        if (!charge() || definitions.lookup(expectedRegion.getOperation()) !=
                             actualRegion.getOperation())
          return false;
      }
    }
    return true;
  }

public:
  NativeScheduleComparison(const protocol::SourceExecutionClosure &source,
                           const protocol::SourceExecutionClosure &actual,
                           uint64_t &remaining,
                           finite::VerificationResult &outcome)
      : source(source), actual(actual), remaining(remaining), outcome(outcome) {
  }
  bool run(protocol_ir::ProtocolModuleOp before,
           protocol_ir::ProtocolModuleOp after) {
    if (!source.computations.empty() || !actual.computations.empty() ||
        source.bodies.size() != actual.bodies.size() ||
        before.getBody().front().getOperations().size() !=
            after.getBody().front().getOperations().size())
      return false;
    SymbolTable symbols(after);
    for (auto &definition : before.getBody().front()) {
      if (!charge())
        return false;
      auto *observed =
          symbols.lookup(SymbolTable::getSymbolName(&definition).getValue());
      // Includes exact callable types, native binding arguments, selected
      // implementations, ABI annotations, origin and region markers.
      if (!observed || observed->getName() != definition.getName() ||
          observed->getAttrDictionary() != definition.getAttrDictionary())
        return false;
      definitions[&definition] = observed;
    }
    for (auto function : before.getBody().front().getOps<func::FuncOp>()) {
      auto observed = cast<func::FuncOp>(definitions.lookup(function));
      auto expectedBody = source.bodies.find(function.getSymName().str());
      auto observedBody = actual.bodies.find(observed.getSymName().str());
      if (expectedBody == source.bodies.end() ||
          observedBody == actual.bodies.end() ||
          !body(function, observed, expectedBody->second, observedBody->second))
        return false;
    }
    return true;
  }
};
} // namespace

OwningOpRef<mlir::ModuleOp>
consumeSchedule(mlir::ModuleOp source, uint64_t &remaining,
                std::optional<CapacityCause> *capacity) {
  if (!source || !chargeCopy(source, remaining, capacity) ||
      failed(verifyScheduledRecipeOutput(source)))
    return {};
  auto input = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  auto view = ScopedCandidate::readSchedule(input);
  if (!view) {
    consumeError(view.takeError());
    return {};
  }
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(result->getBody(), result->getBody()->end());
  auto output = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(), protocol_ir::Profile::Exec, mlir::ArrayAttr{});
  output.getBody().emplaceBlock();
  if (failed(
          Consumer(**view, builder, remaining, capacity).run(input, output)) ||
      failed(verifyRecipeOutput(*result)))
    return {};
  return result;
}

LogicalResult verifyScheduleLowering(mlir::ModuleOp schedule,
                                     mlir::ModuleOp candidate, uint64_t *shared,
                                     finite::VerificationResult *reported) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                     "schedule lowering differs"};
  auto finish = [&](bool valid) {
    if (valid)
      outcome = {finite::VerificationStatus::Verified, {}};
    if (reported)
      *reported = outcome;
    return success(valid);
  };
  if (!schedule || !candidate)
    return finish(false);
  uint64_t standalone = 1000000;
  auto &remaining = shared ? *shared : standalone;
  if (!inspectForComparison(schedule, remaining, outcome) ||
      !inspectForComparison(candidate, remaining, outcome))
    return finish(false);
  if (failed(verifyScheduledRecipeOutput(schedule)) ||
      failed(verifyRecipeOutput(candidate)))
    return finish(false);
  auto before =
      cast<protocol_ir::ProtocolModuleOp>(schedule.getBody()->front());
  auto after =
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  auto expected = protocol::readScheduledExecutionClosure(before);
  if (!expected) {
    consumeError(expected.takeError());
    return finish(false);
  }
  // Numerical candidates still use source completion (exec.returned). Final
  // executable publication introduces exec.complete at the owning boundary.
  // verifyRecipeOutput above separately requires all requests to be resolved.
  auto actual = protocol::readSourceExecutionClosure(after);
  if (!actual) {
    consumeError(actual.takeError());
    return finish(false);
  }
  return finish(NativeScheduleComparison(*expected, *actual, remaining, outcome)
                    .run(before, after));
}
} // namespace zkc::computation
