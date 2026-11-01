#include "SourceView.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
std::vector<Type> types(TypeRange values) {
  return {values.begin(), values.end()};
}
std::vector<std::string> roles(ArrayAttr values) {
  std::vector<std::string> result;
  for (Attribute value : values)
    result.push_back(cast<StringAttr>(value).str());
  return result;
}
class Reader {
  const SourceExecutionClosure &closure;
  unsigned remaining = 4096;

  Expected<SourceBlock> read(Block &body, TypeRange inputs, TypeRange outputs,
                             ArrayRef<SourceExecutionStep> steps,
                             SourceTerminator terminator, unsigned forwarded,
                             unsigned depth, bool scoped) {
    if (depth > 64 || inputs.size() > 512)
      return error("structured-source-limit");
    SourceBlock result;
    result.inputs = types(inputs);
    result.outputs = types(outputs);
    result.terminator = terminator;
    auto arguments =
        scoped ? body.getArguments().drop_front() : body.getArguments();
    llvm::DenseMap<Value, unsigned> coordinates;
    for (auto [i, argument] : enumerate(arguments))
      coordinates[argument] = i;
    auto indices = [&](ValueRange values) -> Expected<std::vector<unsigned>> {
      std::vector<unsigned> result;
      for (Value value : values) {
        auto found = coordinates.find(value);
        if (found == coordinates.end() || found->second > 4096)
          return error("structured-source-reference");
        result.push_back(found->second);
      }
      return result;
    };
    for (const auto &step : steps) {
      Operation *op = step.operation;
      bool terminal =
          scoped ? isa<exec::ReturnOp, exec::CompleteOp, exec::RejectOp>(op)
                 : op == &body.back();
      if (terminal) {
        result.terminal = op;
        if (isa<exec::RejectOp>(op)) {
          result.terminator = SourceTerminator::Stop;
          return result;
        }
        SmallVector<Value> returned(step.inputs);
        if (scoped)
          append_range(returned, arguments.take_back(forwarded));
        auto actual = indices(returned);
        if (!actual)
          return actual.takeError();
        result.returned = std::move(*actual);
        return result;
      }
      if (!remaining)
        return error("structured-source-limit");
      --remaining;
      SourceInstruction instruction;
      instruction.operation = op;
      auto operands = indices(step.inputs);
      if (!operands)
        return operands.takeError();
      instruction.operands = std::move(*operands);
      instruction.results = types(ValueRange(step.outputs).getTypes());
      auto site = op->getAttrOfType<StringAttr>(
          isa<func::CallOp>(op) ? "runtime.site" : "site");
      if (site)
        instruction.site = site.str();
      if (scoped) {
        for (auto nested : step.regions) {
          unsigned captures = isa<exec::RangeOp>(op)
                                  ? step.inputs.size() - 2 - step.outputs.size()
                                  : 0;
          auto inner = scopedBody(nested,
                                  step.conditional ? SourceTerminator::Condition
                                                   : SourceTerminator::Yield,
                                  captures, depth + 1);
          if (!inner)
            return inner.takeError();
          instruction.regions.push_back(std::move(*inner));
        }
      } else {
        for (Region &region : op->getRegions()) {
          auto inner = ordinary(region.front(), op->getResultTypes(),
                                SourceTerminator::Yield, depth + 1);
          if (!inner)
            return inner.takeError();
          instruction.regions.push_back(std::move(*inner));
        }
      }
      result.instructions.push_back(std::move(instruction));
      for (auto &coordinate : coordinates)
        coordinate.second += step.outputs.size();
      for (auto [i, output] : enumerate(step.outputs))
        coordinates[output] = i;
    }
    return error("structured-source-region");
  }

public:
  explicit Reader(const SourceExecutionClosure &closure) : closure(closure) {}
  Expected<SourceBlock> ordinary(Block &body, TypeRange outputs,
                                 SourceTerminator terminator, unsigned depth) {
    SmallVector<SourceExecutionStep> steps;
    for (Operation &op : body)
      steps.push_back({&op,
                       SmallVector<Value>(op.getOperands()),
                       SmallVector<Value>(op.getResults()),
                       {},
                       false});
    return read(body, body.getArgumentTypes(), outputs, steps, terminator, 0,
                depth, false);
  }
  Expected<SourceBlock> scopedBody(func::FuncOp function,
                                   SourceTerminator terminator,
                                   unsigned forwarded, unsigned depth) {
    auto found = closure.bodies.find(function.getSymName().str());
    if (found == closure.bodies.end())
      return error("structured-source-region");
    // Outlined region signatures include the same scope/outcome ABI, but the
    // public helper-signature query intentionally excludes outlined regions.
    auto outcome = cast<exec::OutcomeType>(function.getResultTypes()[0]);
    SmallVector<Type> outputs(outcome.getPayload());
    append_range(outputs, function.getArgumentTypes().take_back(forwarded));
    return read(function.getBody().front(),
                function.getArgumentTypes().drop_front(), outputs,
                found->second, terminator, forwarded, depth, true);
  }
};
} // namespace

const SourceDefinition *SourceView::find(StringRef name) const {
  auto found = names.find(name.str());
  return found == names.end() ? nullptr : &definitions[found->second];
}
Expected<SourceDefinition>
buildSourceDefinition(Operation &op, StringRef name, StringRef kind,
                      const SourceExecutionClosure &closure) {
  SourceDefinition result;
  result.operation = &op;
  result.name = name.str();
  result.kind = kind.str();
  if (kind != "protocol" && kind != "local" && kind != "math" &&
      kind != "oracle")
    return result;
  result.hasBody = true;
  if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
    result.roles = roles(protocol.getRoles());
    for (auto scope : protocol.getInputRoles())
      result.inputRoles.push_back(roles(cast<ArrayAttr>(scope)));
    for (auto scope : protocol.getOutputRoles())
      result.outputRoles.push_back(roles(cast<ArrayAttr>(scope)));
  }
  Reader reader(closure);
  auto function = dyn_cast<func::FuncOp>(op);
  auto body =
      function && isScopedExecutionFunction(function)
          ? reader.scopedBody(function, SourceTerminator::Return, 0, 0)
          : reader.ordinary(
                op.getRegion(0).front(),
                cast<FunctionType>(
                    op.getAttrOfType<TypeAttr>("function_type").getValue())
                    .getResults(),
                SourceTerminator::Return, 0);
  if (!body)
    return body.takeError();
  result.body = std::move(*body);
  return result;
}
} // namespace zkc::protocol
