#include "SourceView.h"
#include "SourceCoordinates.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/AsmParser/AsmParserState.h"
#include "mlir/Bytecode/BytecodeReader.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"

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
  SourceAllowance &allowance;

  Expected<SourceBlock> read(Block &body, TypeRange inputs, TypeRange outputs,
                             ArrayRef<SourceExecutionStep> steps,
                             SourceTerminator terminator, unsigned forwarded,
                             unsigned depth, bool scoped) {
    if (depth > 128 || !allowance.charge(1 + inputs.size() + outputs.size()))
      return error("source-view-limit");
    SourceBlock result;
    result.inputs = types(inputs);
    result.outputs = types(outputs);
    result.terminator = terminator;
    auto arguments =
        scoped ? body.getArguments().drop_front() : body.getArguments();
    SourceCoordinates coordinates(arguments);
    auto indices = [&](ValueRange values) -> Expected<std::vector<unsigned>> {
      std::vector<unsigned> result;
      for (Value value : values) {
        auto coordinate = coordinates.lookup(value);
        if (!coordinate)
          return error("structured-source-reference");
        result.push_back(*coordinate);
      }
      return result;
    };
    for (const auto &step : steps) {
      Operation *op = step.operation;
      bool terminal =
          scoped ? isa<exec::ReturnOp, exec::CompleteOp, exec::RejectOp>(op)
                 : op == &body.back();
      if (terminal) {
        if (!allowance.charge(1 + step.inputs.size() + forwarded))
          return error("source-view-limit");
        result.terminal = op;
        if (isa<exec::RejectOp>(op)) {
          result.terminator = SourceTerminator::Stop;
          return result;
        }
        SmallVector<Value> returned(step.inputs);
        if (scoped)
          append_range(returned, arguments.take_back(forwarded));
        if (ValueRange(returned).getTypes() != outputs)
          return error("structured-source-region");
        if (!scoped) {
          bool valid =
              terminator == SourceTerminator::Return
                  ? isa<func::ReturnOp, protocol_ir::MathematicalReturnOp,
                        protocol_ir::OracleYieldOp>(op)
                  : terminator == SourceTerminator::Yield &&
                        isa<data::YieldOp, protocol_ir::ProtocolYieldOp>(op);
          if (!valid)
            return error("structured-source-region");
        }
        auto actual = indices(returned);
        if (!actual)
          return actual.takeError();
        result.returned = std::move(*actual);
        return result;
      }
      if (!allowance.charge(1 + step.inputs.size() + step.outputs.size()))
        return error("source-view-limit");
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
        for (auto [arm, region] : llvm::enumerate(op->getRegions())) {
          if (!llvm::hasSingleElement(region) || region.front().empty())
            return error("structured-source-region");
          if (isSelectedControl(op)) {
            auto payloads = selectedPayloadTypes(op, arm);
            if (!payloads)
              return payloads.takeError();
            SmallVector<Type> expected(*payloads);
            append_range(expected, op->getOperands().drop_front().getTypes());
            if (region.front().getArgumentTypes() != TypeRange(expected))
              return error("structured-source-region");
          }
          auto inner = ordinary(region.front(), op->getResultTypes(),
                                SourceTerminator::Yield, depth + 1);
          if (!inner)
            return inner.takeError();
          instruction.regions.push_back(std::move(*inner));
        }
      }
      result.instructions.push_back(std::move(instruction));
      coordinates.prepend(step.outputs);
    }
    return error("structured-source-region");
  }

public:
  Reader(const SourceExecutionClosure &closure, SourceAllowance &allowance)
      : closure(closure), allowance(allowance) {}
  Expected<SourceBlock> ordinary(Block &body, TypeRange outputs,
                                 SourceTerminator terminator, unsigned depth) {
    if (body.empty())
      return error("structured-source-region");
    if (!allowance.charge(body.getOperations().size()))
      return error("source-view-limit");
    SmallVector<SourceExecutionStep> steps;
    for (Operation &op : body) {
      if (!allowance.charge(op.getNumOperands() + op.getNumResults()))
        return error("source-view-limit");
      steps.push_back({&op,
                       SmallVector<Value>(op.getOperands()),
                       SmallVector<Value>(op.getResults()),
                       {},
                       false});
    }
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
                      const SourceExecutionClosure &closure,
                      SourceAllowance &allowance) {
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
  Reader reader(closure, allowance);
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
Expected<SourceView> readSourceView(StringRef bytes, StringRef name,
                                    MLIRContext &context,
                                    StructuredSourceProfile profile) {
  bool bytecode = isBytecode(MemoryBufferRef(bytes, "original"));
  if (bytes.size() > 16 * 1024 * 1024 ||
      (!bytecode && !mlirNestingWithinLimit(bytes)))
    return error("structured-source-limit");
  SourceMgr manager;
  manager.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(bytes, "original"),
                             SMLoc());
  if (bytecode) {
    // The const SourceMgr overload copies any retained resources into context
    // ownership. No operation range is invented from bytecode loc attributes.
    auto original =
        parseSourceFile<ModuleOp>(manager, ParserConfig(&context, false));
    if (!original)
      return error("structured-source-original");
    return readSourceView(std::move(original), bytes, name, nullptr, nullptr,
                          nullptr, profile);
  }
  AsmParserState parser;
  Block parsed;
  if (failed(parseAsmSourceFile(manager, &parsed, ParserConfig(&context, false),
                                &parser)))
    return error("structured-source-original");
  auto original =
      mlir::detail::constructContainerOpForParserIfNecessary<ModuleOp>(
          &parsed, &context, FileLineColLoc::get(&context, "original", 1, 1));
  return readSourceView(std::move(original), bytes, name, &parser, &manager,
                        nullptr, profile);
}
Expected<SourceView> readSourceView(
    OwningOpRef<ModuleOp> original, StringRef bytes, StringRef name,
    const AsmParserState *parser, const SourceMgr *manager,
    const llvm::DenseMap<Operation *, Operation *> *writtenOperations,
    StructuredSourceProfile profile) {
  if (!original || failed(zkc::admitStage(*original)))
    return error("structured-source-original");
  // The original is one unadorned module.
  if (!(*original)->getAttrs().empty())
    return error("structured-source-attribute",
                 (*original)->getAttrs().front().getName().getValue());
  if (!llvm::hasSingleElement(original->getBody()->getOperations()))
    return error("structured-source-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("structured-source-profile");
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(name);
  if (!selected)
    return error("structured-source-symbol");
  SourceView result;
  result.entry = name.str();
  result.identity =
      "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  result.profile = profile;
  result.native = std::move(original);
  SourceAllowance allowance;
  if (auto e = indexSource(result, allowance))
    return std::move(e);
  if (parser && manager) {
    auto buffer = manager->getMemoryBuffer(manager->getMainFileID());
    const char *begin = buffer->getBufferStart();
    bool bounded = true;
    result.native->walk([&](Operation *op) {
      if (!bounded || !(bounded = allowance.charge()))
        return;
      auto *source = writtenOperations ? writtenOperations->lookup(op) : op;
      if (const auto *written = source ? parser->getOpDef(source) : nullptr) {
        auto [line, column] = manager->getLineAndColumn(written->loc.Start);
        result.written.try_emplace(
            op,
            StructuredSourceTextRange{
                unsigned(written->loc.Start.getPointer() - begin),
                unsigned(written->loc.End.getPointer() - begin), line, column});
      }
    });
    if (!bounded)
      return error("source-view-limit");
  }
  return result;
}
} // namespace zkc::protocol
