#include "zkc/Target/Source.h"
#include "../Compiler/PhysicalEncoding.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Library.h"
#include "zkc/Compiler/Physical.h"
#include "llvm/ADT/StringSet.h"
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
struct Context {
  SmallVector<Type> inputs;
  Type result;
  const SourceLibraryInterface *library;
};
Expected<Context> decodeContext(const json::Value &json, Builder &b) {
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
  Context context{{}, *result, *library};
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
Expected<Context> decodeProgramContext(Operation *program) {
  auto context = program->getAttrOfType<StringAttr>("context");
  if (!context)
    return error("invalid-context");
  auto json = parseJson(context.getValue());
  if (!json)
    return json.takeError();
  Builder builder(program->getContext());
  return decodeContext(*json, builder);
}
Expected<Value> operand(const json::Value &json, ArrayRef<Value> env,
                        Type expected) {
  auto n = natural(json);
  if (!n)
    return n.takeError();
  uint64_t index = 0;
  if (StringRef(*n).getAsInteger(10, index) || index >= env.size() ||
      env[index].getType() != expected)
    return error("invalid-operand");
  return env[index];
}
Operation *create(OpBuilder &b, StringRef name, ValueRange operands = {},
                  TypeRange results = {},
                  ArrayRef<NamedAttribute> attributes = {},
                  unsigned regions = 0) {
  OperationState s(b.getUnknownLoc(), name);
  s.addOperands(operands);
  s.addTypes(results);
  s.addAttributes(attributes);
  for (unsigned i = 0; i < regions; ++i)
    s.addRegion();
  return b.create(s);
}
Block *block(Region &region, TypeRange types, OpBuilder &b) {
  auto *result = new Block();
  region.push_back(result);
  result->addArguments(types,
                       SmallVector<Location>(types.size(), b.getUnknownLoc()));
  return result;
}
Error importBody(const json::Value &json, OpBuilder &b, SmallVector<Value> env,
                 Value flow, Type result, const SourceLibraryInterface &library,
                 unsigned depth) {
  if (!depth)
    return error("depth-limit");
  auto *a = json.getAsArray();
  if (!a || a->empty() || !(*a)[0].getAsString())
    return error("invalid-shape");
  auto tag = *(*a)[0].getAsString();
  if (tag == "return" && a->size() == 2) {
    auto value = operand((*a)[1], env, result);
    if (!value)
      return value.takeError();
    create(b, "pir.return", {flow, *value});
    return Error::success();
  }
  if (tag == "stop" && a->size() == 2 && (*a)[1].getAsString()) {
    create(b, "pir.stop", flow, {},
           {b.getNamedAttr("reason", b.getStringAttr(*(*a)[1].getAsString()))});
    return Error::success();
  }
  if (tag == "apply" && a->size() == 4) {
    auto operation = library.resolveOperation((*a)[1], b);
    if (!operation)
      return operation.takeError();
    auto *indices = (*a)[2].getAsArray();
    if (!indices || indices->size() != operation->inputs.size())
      return error("operand-count");
    SmallVector<Value> operands;
    SmallVector<Type> results;
    if (operation->ordered) {
      operands.push_back(flow);
      results.push_back(flow.getType());
    }
    for (size_t i = 0; i < indices->size(); ++i) {
      auto value = operand((*indices)[i], env, operation->inputs[i]);
      if (!value)
        return value.takeError();
      operands.push_back(*value);
    }
    results.push_back(operation->output);
    auto *op =
        create(b, operation->name, operands, results, operation->attributes);
    if (operation->ordered)
      flow = op->getResult(0);
    env.insert(env.begin(), op->getResults().back());
    return importBody((*a)[3], b, env, flow, result, library, depth - 1);
  }
  if (tag == "if" && a->size() == 4) {
    auto condition = operand((*a)[1], env, library.conditionType(b));
    if (!condition)
      return condition.takeError();
    SmallVector<Value> operands{flow, *condition};
    llvm::append_range(operands, env);
    auto *op = create(b, "pir.choose", operands, {}, {}, 2);
    SmallVector<Type> types{flow.getType()};
    for (auto v : env)
      types.push_back(v.getType());
    for (unsigned i = 0; i < 2; ++i) {
      auto *body = block(op->getRegion(i), types, b);
      b.setInsertionPointToEnd(body);
      SmallVector<Value> captures(body->getArguments().drop_front());
      if (auto e = importBody((*a)[i + 2], b, captures, body->getArgument(0),
                              result, library, depth - 1))
        return e;
    }
    return Error::success();
  }
  if (tag == "bind" && a->size() == 4) {
    auto bound = library.decodeType((*a)[1], b);
    if (!bound)
      return bound.takeError();
    SmallVector<Value> operands{flow};
    llvm::append_range(operands, env);
    auto *op = create(b, "pir.bind", operands, {flow.getType(), *bound}, {}, 1);
    SmallVector<Type> types{flow.getType()};
    for (Value capture : env)
      types.push_back(capture.getType());
    auto *body = block(op->getRegion(0), types, b);
    b.setInsertionPointToEnd(body);
    SmallVector<Value> captures(body->getArguments().drop_front());
    if (auto e = importBody((*a)[2], b, captures, body->getArgument(0), *bound,
                            library, depth - 1))
      return e;
    b.setInsertionPointAfter(op);
    env.insert(env.begin(), op->getResult(1));
    return importBody((*a)[3], b, env, op->getResult(0), result, library,
                      depth - 1);
  }
  if (tag == "repeat" && a->size() == 6) {
    auto count = natural((*a)[1]);
    if (!count)
      return count.takeError();
    auto acc = library.decodeType((*a)[2], b);
    if (!acc)
      return acc.takeError();
    auto initial = operand((*a)[3], env, *acc);
    if (!initial)
      return initial.takeError();
    SmallVector<Value> operands{flow, *initial};
    llvm::append_range(operands, env);
    auto *op = create(b, "pir.repeat", operands, {flow.getType(), *acc},
                      {b.getNamedAttr("count", b.getStringAttr(*count))}, 1);
    SmallVector<Type> types{flow.getType(), *acc};
    for (auto v : env)
      types.push_back(v.getType());
    auto *body = block(op->getRegion(0), types, b);
    b.setInsertionPointToEnd(body);
    SmallVector<Value> captures(body->getArguments().drop_front());
    if (auto e = importBody((*a)[4], b, captures, body->getArgument(0), *acc,
                            library, depth - 1))
      return e;
    b.setInsertionPointAfter(op);
    env.insert(env.begin(), op->getResult(1));
    return importBody((*a)[5], b, env, op->getResult(0), result, library,
                      depth - 1);
  }
  return error("invalid-shape");
}
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
  if (source || isa<PrepareOp, InvokeOp>(op)) {
    json::Value desc(nullptr);
    unsigned offset = 0;
    if (physical) {
      if (source)
        return error("logical-operation-in-physical-plan");
      auto checked = physicalDescriptor(&op, library);
      if (!checked)
        return checked.takeError();
      desc = std::move(*checked);
      offset = op.getNumOperands() && isa<FlowType>(op.getOperand(0).getType());
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
Expected<json::Value> exportProgram(Operation *op) {
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
  SmallVector<Type> types{FlowType::get(op->getContext())};
  llvm::append_range(types, decoded->inputs);
  if (body.getArgumentTypes() != TypeRange(types))
    return error("program-input-types");
  ExportEnvironment env(body.getArguments().drop_front());
  StringRef control = isa<PIRProgramOp>(op) ? "pir" : "plan";
  return exportBody(body, env, body.getArgument(0), decoded->result, control,
                    static_cast<bool>(format) || physical, physical,
                    *decoded->library, 256, body.begin());
}
} // namespace
Expected<const SourceLibraryInterface *> resolveProgramLibrary(Operation *op) {
  auto context = decodeProgramContext(op);
  if (!context)
    return context.takeError();
  return context->library;
}
LogicalResult verifyProgram(Operation *op) {
  auto body = exportProgram(op);
  if (!body)
    return op->emitOpError(toString(body.takeError()));
  return success();
}
Expected<OwningOpRef<ModuleOp>> importSource(const json::Value &request,
                                             MLIRContext &context) {
  auto *a = request.getAsArray();
  if (!a || a->size() != 6 || (*a)[0].getAsString() != "zkc-request" ||
      printJson((*a)[1]) != "1" ||
      ((*a)[2].getAsString() != "finite-source-1" &&
       (*a)[2].getAsString() != "region-source-1") ||
      !(*a)[4].getAsArray())
    return error("invalid-request");
  OpBuilder b(&context);
  auto ctx = decodeContext((*a)[3], b);
  if (!ctx)
    return ctx.takeError();
  // Permitted requirements are decoded even though the direct rule adds none.
  for (const auto &ref : *(*a)[4].getAsArray()) {
    auto *r = ref.getAsArray();
    if (!r || r->size() != 2 || !(*r)[0].getAsString() ||
        !(*r)[1].getAsString())
      return error("invalid-reference");
  }
  OwningOpRef<ModuleOp> module = ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToEnd(module->getBody());
  auto *program =
      create(b, "pir.program", {}, {},
             {b.getNamedAttr("context", b.getStringAttr(printJson((*a)[3]))),
              b.getNamedAttr("resultType", TypeAttr::get(ctx->result))},
             1);
  if ((*a)[2].getAsString() == "region-source-1")
    program->setAttr("sourceFormat", b.getStringAttr("region-source-1"));
  SmallVector<Type> types{FlowType::get(&context)};
  llvm::append_range(types, ctx->inputs);
  auto *body = block(program->getRegion(0), types, b);
  b.setInsertionPointToEnd(body);
  SmallVector<Value> env(body->getArguments().drop_front());
  if (auto e = importBody((*a)[5], b, env, body->getArgument(0), ctx->result,
                          *ctx->library, 256))
    return e;
  if (failed(verify(*module)))
    return error("invalid-source");
  return module;
}
Expected<json::Value> exportPlan(ModuleOp module) {
  if (!llvm::hasSingleElement(*module.getBody()) ||
      !isa<PlanProgramOp>(module.getBody()->front()))
    return error("expected-plan-program");
  auto *program = &module.getBody()->front();
  if (failed(verify(module)))
    return error("invalid-plan");
  auto body = exportProgram(program);
  if (!body)
    return body.takeError();
  auto ctx =
      parseJson(program->getAttrOfType<StringAttr>("context").getValue());
  if (!ctx)
    return ctx.takeError();
  if (isPhysicalProgram(program))
    return json::Value(json::Array{"zkc-table-physical-plan", naturalValue("1"),
                                   std::move(*ctx), std::move(*body)});
  auto format = program->getAttrOfType<StringAttr>("sourceFormat");
  return json::Value(
      json::Array{"zkc-plan", naturalValue("1"),
                  format ? format.getValue() : StringRef("finite-source-1"),
                  json::Array{}, "direct-logical-plan", "direct-lowering",
                  json::Array{"equality", "logical-outcome-state-events",
                              "all-inputs-and-handlers"},
                  std::move(*ctx), json::Array{}, std::move(*body)});
}
} // namespace zkc
