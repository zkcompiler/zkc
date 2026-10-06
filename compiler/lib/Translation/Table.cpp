#include "zkc/Translation/Table.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Table/IR/Physical.h"
#include "zkc/Dialect/Table/IR/Program.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
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
    create(b, "table.source.return", {flow, *value});
    return Error::success();
  }
  if (tag == "stop" && a->size() == 2 && (*a)[1].getAsString()) {
    create(b, "table.source.stop", flow, {},
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
    auto *op = create(b, "table.source.choose", operands, {}, {}, 2);
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
    auto *op = create(b, "table.source.bind", operands,
                      {flow.getType(), *bound}, {}, 1);
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
    auto *op =
        create(b, "table.source.repeat", operands, {flow.getType(), *acc},
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
} // namespace
Expected<OwningOpRef<ModuleOp>> importSource(const json::Value &request,
                                             MLIRContext &context) {
  auto *a = request.getAsArray();
  if (!a || a->size() != 6 || (*a)[0].getAsString() != "zkc-request" ||
      printJson((*a)[1]) != "1" ||
      ((*a)[2].getAsString() != "finite-source-1" &&
       (*a)[2].getAsString() != "region-source-1") ||
      !(*a)[4].getAsArray())
    return error("invalid-request");
  if (!context.getLoadedDialect<zkc::table::TableDialect>())
    return make_error<DialectRegistrationError>(
        InvocationPrecondition::LoadedTableDialect,
        "table import requires the loaded table dialect");
  OpBuilder b(&context);
  auto ctx = table::readProgramContext((*a)[3], b);
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
      create(b, "table.source.program", {}, {},
             {b.getNamedAttr("context", b.getStringAttr(printJson((*a)[3]))),
              b.getNamedAttr("resultType", TypeAttr::get(ctx->result))},
             1);
  if ((*a)[2].getAsString() == "region-source-1")
    program->setAttr("sourceFormat", b.getStringAttr("region-source-1"));
  SmallVector<Type> types{zkc::table::FlowType::get(&context)};
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
      !isa<zkc::table::PlanProgramOp>(module.getBody()->front()))
    return error("expected-plan-program");
  auto *program = &module.getBody()->front();
  if (failed(verify(module)))
    return error("invalid-plan");
  auto body = table::readProgramBody(program);
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
