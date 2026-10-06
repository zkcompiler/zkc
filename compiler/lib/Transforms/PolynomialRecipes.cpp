#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringSet.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// A recipe is evaluated in F[X] by coefficient convolution. This is the same
// finite ring expression used at the terminal in F. Runtime arity never enters
// the static expansion size; only one cube-sum loop is emitted.
class Realizer {
  protocol_ir::ProtocolModuleOp unit;
  OpBuilder builder;
  llvm::StringSet<> names;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
  unsigned nextName = 0, nextSite = 0;
  Location loc;
  algebra::FieldType field;
  Type index, boolean, vector, table, point;
  std::string site() { return "residual_" + std::to_string(nextSite++); }
  FlatSymbolRefAttr binding(StringRef contract,
                            ArrayRef<std::string> arguments) {
    auto key = std::make_pair(
        contract.str(),
        std::vector<std::string>(arguments.begin(), arguments.end()));
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      std::string name;
      do {
        name = "_poly_binding_" + std::to_string(nextName++);
      } while (!names.insert(name).second);
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Attribute> args;
      for (const auto &arg : arguments)
        args.push_back(builder.getStringAttr(arg));
      local::OperationBindingOp::create(builder, loc, name, contract,
                                        builder.getArrayAttr(args), "");
      found = bindings.emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
  SmallVector<Value> emit(StringRef contract, ValueRange inputs,
                          TypeRange outputs,
                          ArrayRef<std::string> parameters = {},
                          std::optional<unsigned> length = {}) {
    SmallVector<std::string> arguments;
    if (!contract.starts_with("index.") && contract != "control.require")
      arguments.push_back(field.getDomain().str());
    if (length)
      arguments.push_back(std::to_string(*length));
    auto reference = binding(contract, arguments);
    OperationState state(loc, protocol::boundOperationName(contract));
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttribute("binding", reference);
    state.addAttribute("site", builder.getStringAttr(site()));
    SmallVector<Attribute> attrs;
    for (const auto &param : parameters)
      attrs.push_back(builder.getStringAttr(param));
    state.addAttribute("parameters", builder.getArrayAttr(attrs));
    auto *op = builder.create(state);
    return SmallVector<Value>(op->result_begin(), op->result_end());
  }
  Value one(StringRef contract, ValueRange inputs, Type output,
            ArrayRef<std::string> params = {}) {
    return emit(contract, inputs, TypeRange{output}, params).front();
  }
  Value natural(unsigned n) {
    return one("index.constant", {}, index, {std::to_string(n)});
  }
  Value scalar(StringRef n) {
    return one("field.constant", {}, field, {n.str()});
  }
  void require(Value value) { (void)emit("control.require", value, {}); }
  Value arity(Value value) { return one("poly.table_arity", value, index); }
  Value shapes(ValueRange tables, std::optional<Value> expected = {}) {
    Value n = arity(tables.front());
    if (expected)
      require(one("index.equal", {n, *expected}, boolean));
    for (auto value : tables.drop_front())
      require(one("index.equal", {n, arity(value)}, boolean));
    return n;
  }
  Value pack(poly::RecipeOp recipe, Value pointValue, ValueRange factors) {
    SmallVector<Value> values{pointValue};
    llvm::append_range(values, factors);
    OperationState state(loc, local::VariantInjectOp::getOperationName());
    state.addOperands(values);
    state.addTypes(poly::residualStateType(recipe));
    state.addAttribute("site", builder.getStringAttr(site()));
    state.addAttribute("alternative", builder.getStringAttr("state"));
    return builder.create(state)->getResult(0);
  }
  using Coefficients = SmallVector<Value>;
  Coefficients expression(poly::RecipeOp recipe, ArrayRef<Coefficients> slots,
                          Value zero) {
    llvm::DenseMap<Value, Coefficients> env;
    for (auto [arg, coefficients] :
         zip(recipe.getBody().front().getArguments(), slots))
      env[arg] = coefficients;
    for (auto &op : recipe.getBody().front().without_terminator()) {
      Coefficients result;
      if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
        result = {scalar(constant.getValue())};
      else {
        const auto &a = env[op.getOperand(0)], &b = env[op.getOperand(1)];
        if (isa<algebra::FieldMultiplyOp>(op)) {
          result.assign(a.size() + b.size() - 1, zero);
          for (unsigned i = 0; i < a.size(); ++i)
            for (unsigned j = 0; j < b.size(); ++j) {
              auto product = one("field.mul", {a[i], b[j]}, field);
              result[i + j] = one("field.add", {result[i + j], product}, field);
            }
        } else {
          result.resize(std::max(a.size(), b.size()));
          for (unsigned i = 0; i < result.size(); ++i)
            result[i] =
                one(isa<algebra::FieldAddOp>(op) ? "field.add" : "field.sub",
                    {i < a.size() ? a[i] : zero, i < b.size() ? b[i] : zero},
                    field);
        }
      }
      env[op.getResult(0)] = std::move(result);
    }
    return env[cast<poly::RecipeYieldOp>(recipe.getBody().front().back())
                   .getValue()];
  }
  Value coefficientArray(ValueRange coefficients) {
    Value values = one("vector.empty", {}, vector);
    for (Value value : coefficients)
      values = one("vector.append", {values, value}, vector);
    Type result = RankedTensorType::get({int64_t(coefficients.size())}, field);
    return emit("field_array.from_vector", values, result, {},
                coefficients.size())
        .front();
  }
  Value round(poly::RecipeOp recipe, ValueRange factors, Value n) {
    auto zeroIndex = natural(0);
    require(one("index.less", {zeroIndex, n}, boolean));
    SmallVector<Value> vectors;
    for (auto factor : factors)
      vectors.push_back(one("vector.from_table", factor, vector));
    auto length = one("vector.length", vectors.front(), index);
    auto half = one("index.div", {length, natural(2)}, index);
    auto zero = scalar("0");
    unsigned width = *poly::recipeDegree(recipe) + 1;
    SmallVector<Value> inputs{zeroIndex, half};
    inputs.append(width, zero);
    // Captures are unique immutable values. half and zero are also explicit
    // because isolated regions cannot refer to the enclosing SSA environment.
    llvm::append_range(inputs, vectors);
    inputs.push_back(half);
    inputs.push_back(zero);
    SmallVector<Type> outputs(width, field);
    OperationState state(loc, local::LocalForOp::getOperationName());
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttribute("site", builder.getStringAttr(site()));
    state.addRegion();
    auto *loop = builder.create(state);
    auto *body = new Block();
    loop->getRegion(0).push_back(body);
    body->addArgument(index, loc);
    for (auto type : outputs)
      body->addArgument(type, loc);
    for (unsigned i = 0; i < vectors.size(); ++i)
      body->addArgument(vector, loc);
    body->addArgument(index, loc);
    body->addArgument(field, loc);
    {
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToEnd(body);
      unsigned start = 1 + width;
      Value i = body->getArgument(0),
            h = body->getArgument(start + vectors.size());
      Value z = body->getArguments().back();
      Value high = one("index.add", {i, h}, index);
      SmallVector<Coefficients> slots;
      for (unsigned j = 0; j < vectors.size(); ++j) {
        Value data = body->getArgument(start + j);
        Value a = one("vector.get", {data, i}, field),
              b = one("vector.get", {data, high}, field);
        slots.push_back({a, one("field.sub", {b, a}, field)});
      }
      auto coefficients = expression(recipe, slots, z);
      SmallVector<Value> yielded;
      for (unsigned j = 0; j < width; ++j)
        yielded.push_back(one("field.add",
                              {body->getArgument(1 + j),
                               j < coefficients.size() ? coefficients[j] : z},
                              field));
      llvm::append_range(yielded, body->getArguments().drop_front(start));
      local::LocalYieldOp::create(builder, loc, yielded);
    }
    return coefficientArray(loop->getResults());
  }
  SmallVector<Value> stateBody(poly::RealizeOp realization,
                               poly::RecipeOp recipe, Block &body) {
    Value p = body.getArgument(0);
    unsigned slots = recipe.getBody().front().getNumArguments();
    auto tables = body.getArguments().slice(1, slots);
    Value n = shapes(tables);
    auto kind = realization.getKind();
    if (kind == "arity")
      return {n};
    if (kind == "round")
      return {round(recipe, tables, n)};
    if (kind == "bind") {
      require(one("index.less", {natural(0), n}, boolean));
      Value challenge = body.getArguments().back();
      SmallVector<Value> fixed;
      for (auto factor : tables)
        fixed.push_back(one("poly.fold", {factor, challenge}, table));
      auto nextPoint = one("poly.append_point", {p, challenge}, point);
      return {pack(recipe, nextPoint, fixed)};
    }
    require(one("index.equal", {n, natural(0)}, boolean));
    Value empty = one("poly.empty_point", {}, point);
    SmallVector<Coefficients> values;
    for (auto factor : tables)
      values.push_back({one("poly.evaluate", {factor, empty}, field)});
    return {p, expression(recipe, values, scalar("0")).front()};
  }

public:
  explicit Realizer(protocol_ir::ProtocolModuleOp unit)
      : unit(unit), builder(unit.getContext()), loc(unit.getLoc()) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  void run(poly::RealizeOp realization) {
    auto recipe = SymbolTable::lookupNearestSymbolFrom<poly::RecipeOp>(
        realization, realization.getRecipeAttr());
    loc = realization.getLoc();
    nextSite = 0;
    field = cast<algebra::FieldType>(
        recipe.getBody().front().getArgument(0).getType());
    auto *context = builder.getContext();
    index = IntegerType::get(context, 64, IntegerType::Unsigned);
    boolean = builder.getI1Type();
    vector = RankedTensorType::get({ShapedType::kDynamic}, field);
    table = poly::MultilinearType::get(context, field.getDomain());
    point = poly::PointType::get(context, field.getDomain());
    auto name = realization.getSymName().str();
    builder.setInsertionPoint(realization);
    auto fn = local::FuncOp::create(builder, loc, name,
                                    realization.getFunctionType());
    fn->setAttr("logical_origin",
                builder.getArrayAttr(
                    {builder.getStringAttr(name), builder.getArrayAttr({})}));
    auto *entry = fn.addEntryBlock();
    builder.setInsertionPointToEnd(entry);
    auto kind = realization.getKind();
    SmallVector<Value> returned;
    if (kind == "init") {
      shapes(entry->getArguments().drop_front(), entry->getArgument(0));
      auto empty = one("poly.empty_point", {}, point);
      returned = {pack(recipe, empty, entry->getArguments().drop_front())};
    } else if (kind == "evaluate") {
      auto coordinates =
          one("vector.from_point", entry->getArgument(0), vector);
      auto length = one("vector.length", coordinates, index);
      shapes(entry->getArguments().drop_front(), length);
      SmallVector<Coefficients> values;
      for (auto factor : entry->getArguments().drop_front())
        values.push_back(
            {one("poly.evaluate", {factor, entry->getArgument(0)}, field)});
      returned = {expression(recipe, values, scalar("0")).front()};
    } else {
      OperationState state(loc, local::LocalMatchOp::getOperationName());
      state.addOperands(entry->getArguments());
      state.addTypes(fn.getResultTypes());
      state.addAttribute("site", builder.getStringAttr(site()));
      state.addAttribute("alternatives", builder.getArrayAttr(
                                             {builder.getStringAttr("state")}));
      state.addRegion();
      auto *match = builder.create(state);
      auto *body = new Block();
      match->getRegion(0).push_back(body);
      body->addArgument(point, loc);
      for (unsigned i = 0; i < recipe.getBody().front().getNumArguments(); ++i)
        body->addArgument(table, loc);
      if (kind == "bind")
        body->addArgument(field, loc);
      {
        OpBuilder::InsertionGuard guard(builder);
        builder.setInsertionPointToEnd(body);
        auto values = stateBody(realization, recipe, *body);
        local::LocalYieldOp::create(builder, loc, values);
      }
      llvm::append_range(returned, match->getResults());
    }
    local::ReturnOp::create(builder, loc, returned);
    realization.erase();
  }
};
} // namespace
static LogicalResult realizeRecipes(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return failure();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return failure();
  SmallVector<poly::RealizeOp> routines;
  uint64_t work = 0;
  for (auto op : unit.getBody().front().getOps<poly::RealizeOp>()) {
    auto recipe = SymbolTable::lookupNearestSymbolFrom<poly::RecipeOp>(
        op, op.getRecipeAttr());
    if (!recipe || failed(poly::realizationType(op)))
      return failure();
    // Upper bound before construction. Count each expression's intermediate
    // width, not just its result, and include slot-dependent shape checks.
    uint64_t cost = 256 + 64 * recipe.getBody().front().getNumArguments();
    llvm::DenseMap<Value, uint64_t> widths;
    bool round = op.getKind() == "round";
    for (auto arg : recipe.getBody().front().getArguments())
      widths[arg] = round ? 2 : 1;
    if (round || op.getKind() == "finish" || op.getKind() == "evaluate") {
      for (auto &expression : recipe.getBody().front().without_terminator()) {
        uint64_t width = 1;
        if (isa<algebra::ConstantFieldOp>(expression))
          ++cost;
        else {
          auto a = widths.lookup(expression.getOperand(0));
          auto b = widths.lookup(expression.getOperand(1));
          if (isa<algebra::FieldMultiplyOp>(expression)) {
            cost += 2 * a * b;
            width = a + b - 1;
          } else {
            width = std::max(a, b);
            cost += width;
          }
        }
        widths[expression.getResult(0)] = width;
      }
    }
    work += cost;
    if (work > 100000)
      return diagnostics::emit(
          op.emitOpError(), "mathematical-expansion-limit",
          "polynomial realization expansion exceeds its static work bound");
    routines.push_back(op);
  }
  Realizer realizer(unit);
  for (auto op : routines)
    realizer.run(op);
  // Declarations have no runtime representation. Their exact expansion remains
  // in local definitions and the compiler invocation retains the source bytes.
  for (auto recipe :
       make_early_inc_range(unit.getBody().front().getOps<poly::RecipeOp>()))
    recipe.erase();
  return verify(module);
}
LogicalResult expandPolynomialRecipes(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  if (failed(realizeRecipes(*candidate)) ||
      failed(verifyPolynomialRecipesPreserved(module, *candidate)))
    return failure();
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::mathematical
