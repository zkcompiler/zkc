#include "zkc/Dialect/Table/IR/Program.h"
#include "../../Verification.h"
#include "PhysicalEncoding.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Table/IR/Physical.h"
#include "llvm/ADT/StringSet.h"
#include <optional>
using namespace mlir;
using namespace llvm;
namespace zkc {
namespace table {
Expected<ProgramContext> readProgramContext(const json::Value &json,
                                            Builder &b) {
  auto *a = json.getAsArray();
  if (!a || a->size() != 4)
    return error("invalid-context");
  auto role = (*a)[0].getAsString();
  auto *inputs = (*a)[1].getAsArray();
  if (!role || role->empty() || !inputs)
    return error("invalid-context");
  auto library = resolveLibrary((*a)[3], *b.getContext());
  if (!library)
    return library.takeError();
  auto result = (*library)->decodeType((*a)[2], b);
  if (!result)
    return result.takeError();
  ProgramContext context{{}, *result, *library};
  llvm::StringSet<> names;
  for (auto &input : *inputs) {
    auto *i = input.getAsArray();
    if (!i || i->size() != 4)
      return error("invalid-input-declaration");
    auto name = (*i)[0].getAsString(), kind = (*i)[3].getAsString();
    if (!name || name->empty() || !names.insert(*name).second || !kind ||
        (*kind != "argument" && *kind != "capture"))
      return error("invalid-input-declaration");
    auto *access = (*i)[2].getAsArray();
    if (!access ||
        !(printJson((*i)[2]) == "[\"shared\"]" ||
          (access->size() == 2 && (*access)[0].getAsString() == "private" &&
           (*access)[1].getAsString() == role)))
      return error("wrong-input-role");
    auto type = (*library)->decodeType((*i)[1], b);
    if (!type)
      return type.takeError();
    context.inputs.push_back(*type);
  }
  return context;
}
static Expected<ProgramContext> decodeProgramContext(Operation *program) {
  auto context = program->getAttrOfType<StringAttr>("context");
  if (!context)
    return error("invalid-context");
  auto json = parseJson(context.getValue());
  if (!json)
    return json.takeError();
  Builder builder(program->getContext());
  return readProgramContext(*json, builder);
}
namespace {
// Export uses semantic binding positions, not a snapshot of the original SSA
// environment. CSE may give several region arguments the same outer value;
// unused captures may be removed or reordered without changing their meaning.
struct ExportEnvironment {
  SmallVector<SmallVector<Value>> slots;

  explicit ExportEnvironment(ValueRange values) {
    for (Value value : values)
      slots.push_back({value});
  }
  explicit ExportEnvironment(size_t size) : slots(size) {}
  void push(Value value) {
    slots.insert(slots.begin(), SmallVector<Value>{value});
  }
  std::optional<unsigned> find(Value value) const {
    for (unsigned i = 0; i < slots.size(); ++i)
      if (llvm::is_contained(slots[i], value))
        return i;
    return std::nullopt;
  }
};
Expected<json::Value> index(Value value, const ExportEnvironment &env) {
  auto found = env.find(value);
  if (!found)
    return error("implicit-capture");
  return naturalValue(std::to_string(*found));
}
// All regions are checked, including dormant branches and zero-count bodies.
Expected<json::Value> exportBody(Block &body, ExportEnvironment env, Value flow,
                                 Type result, StringRef control,
                                 bool allowBinding, bool physical,
                                 const SourceLibraryInterface &library,
                                 unsigned depth, Block::iterator cursor) {
  if (!depth)
    return error("depth-limit");
  if (cursor == body.end())
    return error("missing-terminator");
  Operation &op = *cursor++;
  auto name = op.getName().getStringRef();
  auto source = dyn_cast<SourceOpInterface>(&op);
  if (source || isa<zkc::table::PrepareOp, zkc::table::InvokeOp>(op)) {
    json::Value desc(nullptr);
    unsigned offset = 0;
    if (physical) {
      if (source)
        return error("logical-operation-in-physical-plan");
      auto checked = physicalDescriptor(&op, library);
      if (!checked)
        return checked.takeError();
      desc = std::move(*checked);
      offset = op.getNumOperands() &&
               isa<zkc::table::FlowType>(op.getOperand(0).getType());
    } else {
      if (!source || op.getNumRegions())
        return error("invalid-operation");
      desc = source.getSourceDescriptor();
      Builder b(op.getContext());
      auto resolved = library.resolveOperation(desc, b);
      if (!resolved)
        return resolved.takeError();
      if (failed(verifySourceOperation(&op, *resolved)))
        return error("invalid-operation");
      offset = resolved->ordered ? 1 : 0;
    }
    json::Array args;
    if (offset && op.getOperand(0) != flow)
      return error("invalid-flow");
    for (Value value : op.getOperands().drop_front(offset)) {
      auto i = index(value, env);
      if (!i)
        return i.takeError();
      args.push_back(std::move(*i));
    }
    if (offset)
      flow = op.getResult(0);
    env.push(op.getResults().back());
    auto next = exportBody(body, env, flow, result, control, allowBinding,
                           physical, library, depth - 1, cursor);
    if (!next)
      return next.takeError();
    return json::Value(json::Array{"apply", std::move(desc), std::move(args),
                                   std::move(*next)});
  }
  if (name == (control + ".return").str()) {
    if (!op.getAttrDictionary().empty())
      return error("unsupported-attribute");
    if (cursor != body.end() || op.getNumOperands() != 2 ||
        op.getOperand(0) != flow || op.getOperand(1).getType() != result)
      return error("invalid-return");
    auto i = index(op.getOperand(1), env);
    if (!i)
      return i.takeError();
    return json::Value(json::Array{"return", std::move(*i)});
  }
  if (name == (control + ".stop").str()) {
    if (op.getAttrDictionary().size() != 1)
      return error("unsupported-attribute");
    if (cursor != body.end() || op.getOperand(0) != flow)
      return error("invalid-flow");
    return json::Value(
        json::Array{"stop", op.getAttrOfType<StringAttr>("reason").getValue()});
  }
  bool repeat = name == (control + ".repeat").str(),
       choose = name == (control + ".choose").str(),
       binding = name == (control + ".bind").str();
  if (binding && !allowBinding)
    return error("unsupported-source-format");
  if (!repeat && !choose && !binding)
    return error("unsupported-operation");
  if (op.getAttrDictionary().size() != (repeat ? 1 : 0))
    return error("unsupported-attribute");
  unsigned captureOffset = binding ? 1 : 2;
  if (op.getNumOperands() < captureOffset || op.getOperand(0) != flow ||
      op.getNumRegions() != (choose ? 2 : 1))
    return error("invalid-control-operands");
  Builder b(op.getContext());
  SmallVector<unsigned> captureIndices;
  for (Value capture : op.getOperands().drop_front(captureOffset)) {
    auto position = env.find(capture);
    if (!position)
      return error("implicit-capture");
    captureIndices.push_back(*position);
  }
  std::optional<json::Value> initial;
  if (!binding) {
    auto position = index(op.getOperand(1), env);
    if (!position)
      return position.takeError();
    initial = std::move(*position);
  }
  if (binding && op.getNumResults() != 2)
    return error("invalid-binding-result");
  Type regionResult = binding  ? op.getResult(1).getType()
                      : repeat ? op.getOperand(1).getType()
                               : result;
  if (choose && (op.getOperand(1).getType() != library.conditionType(b) ||
                 cursor != body.end()))
    return error("invalid-branch");
  if (!choose &&
      (op.getNumResults() != 2 || op.getResult(0).getType() != flow.getType() ||
       op.getResult(1).getType() != regionResult))
    return error(binding ? "invalid-binding-result" : "invalid-loop-result");
  json::Array regions;
  for (Region &region : op.getRegions()) {
    if (!llvm::hasSingleElement(region))
      return error("expected-single-block");
    Block &child = region.front();
    SmallVector<Type> types{flow.getType()};
    if (repeat)
      types.push_back(regionResult);
    for (Value capture : op.getOperands().drop_front(captureOffset))
      types.push_back(capture.getType());
    if (child.getArgumentTypes() != TypeRange(types))
      return error("region-capture-types");
    ExportEnvironment captures(env.slots.size() + (repeat ? 1 : 0));
    if (repeat)
      captures.slots[0].push_back(child.getArgument(1));
    for (unsigned i = 0; i < captureIndices.size(); ++i)
      captures.slots[captureIndices[i] + (repeat ? 1 : 0)].push_back(
          child.getArgument(i + (repeat ? 2 : 1)));
    auto content =
        exportBody(child, captures, child.getArgument(0), regionResult, control,
                   allowBinding, physical, library, depth - 1, child.begin());
    if (!content)
      return content.takeError();
    regions.push_back(std::move(*content));
  }
  if (choose)
    return json::Value(json::Array{"if", std::move(*initial),
                                   std::move(regions[0]),
                                   std::move(regions[1])});
  if (binding) {
    auto bound =
        library.encodeType(physical ? logicalType(regionResult) : regionResult);
    if (!bound)
      return bound.takeError();
    env.push(op.getResult(1));
    auto next = exportBody(body, env, op.getResult(0), result, control,
                           allowBinding, physical, library, depth - 1, cursor);
    if (!next)
      return next.takeError();
    return json::Value(json::Array{"bind", std::move(*bound),
                                   std::move(regions[0]), std::move(*next)});
  }
  auto attr = op.getAttrOfType<StringAttr>("count");
  if (!attr)
    return error("invalid-loop-count");
  auto count = parseJson(attr.getValue());
  if (!count)
    return count.takeError();
  auto n = natural(*count);
  if (!n || *n != attr.getValue()) {
    if (!n)
      consumeError(n.takeError());
    return error("invalid-loop-count");
  }
  auto acc =
      library.encodeType(physical ? logicalType(regionResult) : regionResult);
  if (!acc)
    return acc.takeError();
  env.push(op.getResult(1));
  auto next = exportBody(body, env, op.getResult(0), result, control,
                         allowBinding, physical, library, depth - 1, cursor);
  if (!next)
    return next.takeError();
  return json::Value(json::Array{"repeat", std::move(*count), std::move(*acc),
                                 std::move(*initial), std::move(regions[0]),
                                 std::move(*next)});
}
} // namespace
Expected<json::Value> readProgramBody(Operation *op) {
  auto context = op->getAttrOfType<StringAttr>("context");
  auto result = op->getAttrOfType<TypeAttr>("resultType");
  auto format = op->getAttrOfType<StringAttr>("sourceFormat");
  bool physical = isPhysicalProgram(op);
  if (op->hasAttr("realization") && !physical)
    return error("unsupported-realization");
  if (format && format.getValue() != "region-source-1")
    return error("unsupported-source-format");
  if (!context || !result ||
      op->getAttrDictionary().size() !=
          (format ? 3u : 2u) + (physical ? 1u : 0u))
    return error("invalid-context");
  auto decoded = decodeProgramContext(op);
  if (!decoded)
    return decoded.takeError();
  if (physical) {
    if (printJson(decoded->library->dependencies()) !=
        "[[\"table-protocol\",\"1\"]]")
      return error("unsupported-physical-library");
    decoded->result = physicalType(decoded->result);
    for (Type &type : decoded->inputs)
      type = physicalType(type);
  }
  if (decoded->result != result.getValue() || op->getNumRegions() != 1 ||
      !llvm::hasSingleElement(op->getRegion(0)))
    return error("invalid-program-region");
  Block &body = op->getRegion(0).front();
  SmallVector<Type> types{zkc::table::FlowType::get(op->getContext())};
  llvm::append_range(types, decoded->inputs);
  if (body.getArgumentTypes() != TypeRange(types))
    return error("program-input-types");
  ExportEnvironment env(body.getArguments().drop_front());
  StringRef control =
      isa<zkc::table::PIRProgramOp>(op) ? "table.source" : "table.plan";
  return exportBody(body, env, body.getArgument(0), decoded->result, control,
                    static_cast<bool>(format) || physical, physical,
                    *decoded->library, 256, body.begin());
}
} // namespace table
using table::decodeProgramContext;
using table::readProgramBody;
Expected<const SourceLibraryInterface *> resolveProgramLibrary(Operation *op) {
  auto context = decodeProgramContext(op);
  if (!context)
    return context.takeError();
  return context->library;
}
LogicalResult verifyProgram(Operation *op) {
  auto body = readProgramBody(op);
  if (!body)
    return diagnostics::emit(op->emitOpError(), body.takeError());
  return success();
}
} // namespace zkc
