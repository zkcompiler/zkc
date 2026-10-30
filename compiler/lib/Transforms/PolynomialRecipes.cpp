#include "CheckedCandidate.h"
#include "PreparationDialects.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SaveAndRestore.h"
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
  llvm::DenseMap<std::pair<StringAttr, ArrayAttr>, std::string> bindings;
  unsigned nextName = 0, nextSite = 0;
  exec::ScopedExecutionBuilder *scope = nullptr;
  Location loc;
  algebra::FieldType field;
  Type index, boolean, vector, table, point;
  std::string site() { return "residual_" + std::to_string(nextSite++); }
  FlatSymbolRefAttr binding(StringRef contract, ArrayAttr arguments) {
    auto key = std::make_pair(builder.getStringAttr(contract), arguments);
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      std::string name;
      do {
        name = "_poly_binding_" + std::to_string(nextName++);
      } while (!names.insert(name).second);
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      runtime::BindingOp::create(builder, loc, name, contract, arguments, "");
      found = bindings.try_emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
  SmallVector<Value> emit(StringRef contract, ValueRange inputs,
                          TypeRange outputs,
                          ArrayRef<Attribute> parameters = {},
                          std::optional<unsigned> length = {}) {
    SmallVector<Attribute> arguments;
    if (!contract.starts_with("index.") && contract != "control.require")
      arguments.push_back(builder.getStringAttr(field.getDomain()));
    if (length)
      arguments.push_back(
          builder.getIntegerAttr(builder.getIntegerType(64, false), *length));
    auto reference = binding(contract, builder.getArrayAttr(arguments));
    return scope->invoke(
        exec::ApplyOp::getOperationName(), outputs, scope->scoped(inputs),
        {builder.getNamedAttr("binding", reference),
         builder.getNamedAttr("site", builder.getStringAttr(site())),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters))});
  }
  Value one(StringRef contract, ValueRange inputs, Type output,
            ArrayRef<Attribute> params = {}) {
    return emit(contract, inputs, TypeRange{output}, params).front();
  }
  Value natural(unsigned n) {
    return one("index.constant", {}, index, {builder.getIntegerAttr(index, n)});
  }
  Value scalar(algebra::FieldLiteralAttr value) {
    return one("field.constant", {}, field, {value});
  }
  Value scalar(uint64_t value) {
    return scalar(cantFail(algebra::makeFieldLiteral(field, APInt(64, value))));
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
    return scope
        ->invoke(exec::VariantOp::getOperationName(),
                 {poly::residualStateType(recipe)}, scope->scoped(values),
                 {builder.getNamedAttr("site", builder.getStringAttr(site())),
                  builder.getNamedAttr("alternative",
                                       builder.getStringAttr("state"))})
        .front();
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
    Type result = algebra::FieldArrayType::get(
        field.getContext(), field.getDomain(), coefficients.size());
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
    auto zero = scalar(0);
    unsigned width = *poly::recipeDegree(recipe) + 1;
    SmallVector<Value> seeds(width, zero), captures(vectors);
    captures.push_back(half);
    captures.push_back(zero);
    SmallVector<Type> outputs(width, field);
    SmallVector<Type> inputs{index};
    llvm::append_range(inputs, outputs);
    llvm::append_range(inputs, ValueRange(captures).getTypes());
    auto results =
        scope->loop(zeroIndex, half, seeds, captures, outputs, false, site(),
                    [&](unsigned) {
                      auto function = outlined(inputs, outputs);
                      builder.setInsertionPointToStart(&function.front());
                      exec::ScopedExecutionBuilder control(builder, function);
                      SaveAndRestore saved(scope, &control);
                      auto arguments = function.getArguments().drop_front();
                      unsigned start = 1 + width;
                      Value i = arguments[0],
                            h = arguments[start + vectors.size()];
                      Value z = arguments.back();
                      Value high = one("index.add", {i, h}, index);
                      SmallVector<Coefficients> slots;
                      for (unsigned j = 0; j < vectors.size(); ++j) {
                        Value data = arguments[start + j];
                        Value a = one("vector.get", {data, i}, field),
                              b = one("vector.get", {data, high}, field);
                        slots.push_back({a, one("field.sub", {b, a}, field)});
                      }
                      auto coefficients = expression(recipe, slots, z);
                      SmallVector<Value> yielded;
                      for (unsigned j = 0; j < width; ++j)
                        yielded.push_back(
                            one("field.add",
                                {arguments[1 + j],
                                 j < coefficients.size() ? coefficients[j] : z},
                                field));
                      control.complete(yielded);
                      return function;
                    });
    return coefficientArray(results);
  }
  func::FuncOp function(StringRef name, TypeRange inputs, TypeRange outputs) {
    SmallVector<Type> arguments{runtime::ScopeType::get(builder.getContext())};
    llvm::append_range(arguments, inputs);
    auto result = exec::OutcomeType::get(builder.getContext(),
                                         SmallVector<Type>(outputs));
    auto fn = func::FuncOp::create(
        builder, loc, name, builder.getFunctionType(arguments, {result}));
    fn.setNoInline(true);
    fn.addEntryBlock();
    return fn;
  }
  func::FuncOp outlined(TypeRange inputs, TypeRange outputs) {
    std::string name;
    do {
      name = "_poly_body_" + std::to_string(nextName++);
    } while (!names.insert(name).second);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto fn = function(name, inputs, outputs);
    fn.setPrivate();
    fn->setAttr("runtime.region", builder.getUnitAttr());
    return fn;
  }

  SmallVector<Value> stateBody(poly::RealizeOp realization,
                               poly::RecipeOp recipe, ValueRange arguments) {
    Value p = arguments[0];
    unsigned slots = recipe.getBody().front().getNumArguments();
    auto tables = arguments.slice(1, slots);
    Value n = shapes(tables);
    auto kind = realization.getKind();
    if (kind == "arity")
      return {n};
    if (kind == "round")
      return {round(recipe, tables, n)};
    if (kind == "bind") {
      require(one("index.less", {natural(0), n}, boolean));
      Value challenge = arguments.back();
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
    return {p, expression(recipe, values, scalar(0)).front()};
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
    vector = algebra::FieldVectorType::get(context, field.getDomain());
    table = poly::MultilinearType::get(context, field.getDomain());
    point = poly::PointType::get(context, field.getDomain());
    auto name = realization.getSymName().str();
    builder.setInsertionPoint(realization);
    auto type = realization.getFunctionType();
    auto fn = function(name, type.getInputs(), type.getResults());
    fn->setAttr("runtime.origin",
                builder.getArrayAttr(
                    {builder.getStringAttr(name), builder.getArrayAttr({})}));
    builder.setInsertionPointToStart(&fn.front());
    exec::ScopedExecutionBuilder control(builder, fn);
    SaveAndRestore saved(scope, &control);
    auto arguments = fn.getArguments().drop_front();
    auto kind = realization.getKind();
    SmallVector<Value> returned;
    if (kind == "init") {
      shapes(arguments.drop_front(), arguments[0]);
      auto empty = one("poly.empty_point", {}, point);
      returned = {pack(recipe, empty, arguments.drop_front())};
    } else if (kind == "evaluate") {
      auto coordinates = one("vector.from_point", arguments[0], vector);
      auto length = one("vector.length", coordinates, index);
      shapes(arguments.drop_front(), length);
      SmallVector<Coefficients> values;
      for (auto factor : arguments.drop_front())
        values.push_back({one("poly.evaluate", {factor, arguments[0]}, field)});
      returned = {expression(recipe, values, scalar(0)).front()};
    } else {
      SmallVector<Type> inputs{point};
      inputs.append(recipe.getBody().front().getNumArguments(), table);
      if (kind == "bind")
        inputs.push_back(field);
      returned =
          control.match(arguments[0], arguments.drop_front(), type.getResults(),
                        {"state"}, site(), [&](unsigned) {
                          auto body = outlined(inputs, type.getResults());
                          builder.setInsertionPointToStart(&body.front());
                          exec::ScopedExecutionBuilder nested(builder, body);
                          SaveAndRestore saved(scope, &nested);
                          auto values =
                              stateBody(realization, recipe,
                                        body.getArguments().drop_front());
                          nested.complete(values);
                          return body;
                        });
    }
    control.returned(returned);
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
    // Each primitive expands to bounded outcome/dispatch administration;
    // outlined control adds a bounded CFG per loop or match. Reserve that
    // construction before allocating it, independently of runtime arity.
    work += 16 * cost;
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
  // in scoped definitions and the compiler invocation retains the source bytes.
  for (auto recipe :
       make_early_inc_range(unit.getBody().front().getOps<poly::RecipeOp>()))
    recipe.erase();
  return zkc::admitStage(module);
}
LogicalResult expandPolynomialRecipes(ModuleOp module) {
  loadPreparationDialects(*module.getContext());
  if (failed(zkc::admitStage(module)))
    return failure();
  mathematical::CheckedCandidate candidate(module);
  if (failed(realizeRecipes(*candidate)))
    return failure();
  return candidate.publish(verifyPolynomialRecipesPreserved);
}
} // namespace zkc::mathematical
