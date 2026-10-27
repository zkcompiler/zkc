#include "../ScopedCandidate.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
using Values = SmallVector<Value>;
using mathematical::ScopedCandidate;
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
      if (!step ||
          !charge(64 + 16 * (step->inputs.size() + step->outputs.size())))
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
      builder, source.getLoc(), protocol_ir::Profile::Exec);
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
  if (!chargeCopy(schedule, remaining) || !chargeCopy(candidate, remaining)) {
    outcome = {finite::VerificationStatus::RequiredCapacity,
               "schedule checking capacity",
               CapacityCause{WorkOwner::AlgorithmChecking}};
    return finish(false);
  }
  if (failed(verifyScheduledRecipeOutput(schedule)) ||
      failed(verifyRecipeOutput(candidate)))
    return finish(false);
  auto before =
      cast<protocol_ir::ProtocolModuleOp>(schedule.getBody()->front());
  auto after =
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  SymbolTable symbols(after);
  if (before.getBody().front().getOperations().size() !=
      after.getBody().front().getOperations().size())
    return finish(false);
  for (auto &definition : before.getBody().front()) {
    auto *actual =
        symbols.lookup(SymbolTable::getSymbolName(&definition).getValue());
    if (!actual || actual->getName() != definition.getName() ||
        actual->getAttrDictionary() != definition.getAttrDictionary())
      return finish(false);
  }
  auto expected = protocol::readScheduledExecutionClosure(before);
  if (!expected) {
    consumeError(expected.takeError());
    return finish(false);
  }
  if (auto error = protocol::verifySourceExecutionDefinitions(
          after, expected->definitions)) {
    consumeError(std::move(error));
    return finish(false);
  }
  return finish(true);
}
} // namespace zkc::kernel
