#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// Read the selected executable recipe against the finite ring expression.
// Values below are actual candidate SSA values. This checker never constructs
// a replacement function or calls the realization producer.
class RecipeCorrespondence {
  SymbolTable &symbols;
  llvm::DenseSet<Operation *> &bindings;
  uint64_t &remaining;
  poly::RecipeOp recipe;
  StringRef domain;
  Operation *cursor = nullptr;
  bool valid = true;
  unsigned nextSite = 0;
  using Coefficients = SmallVector<Value>;

  Operation *take(StringRef name) {
    if (!valid || !remaining || !cursor) {
      valid = false;
      return nullptr;
    }
    --remaining;
    Operation *op = cursor;
    cursor = cursor->getNextNode();
    auto site = op->getAttrOfType<StringAttr>("site");
    if (op->getName().getStringRef() != name || !site ||
        site.getValue() != "residual_" + std::to_string(nextSite++)) {
      valid = false;
      return nullptr;
    }
    return op;
  }
  Value primitive(StringRef contract, ValueRange operands = {},
                  ArrayRef<std::string> parameters = {},
                  std::optional<unsigned> length = {}, bool output = true) {
    Operation *op = take(protocol::boundOperationName(contract));
    if (!op)
      return {};
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto declaration =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    SmallVector<std::string> arguments;
    if (!contract.starts_with("index.") && contract != "control.require")
      arguments.push_back(domain.str());
    if (length)
      arguments.push_back(std::to_string(*length));
    auto strings = [](ArrayAttr attrs, ArrayRef<std::string> expected) {
      return attrs && attrs.size() == expected.size() &&
             all_of(zip(attrs, expected), [](auto pair) {
               auto text = dyn_cast<StringAttr>(std::get<0>(pair));
               return text && text.getValue() == std::get<1>(pair);
             });
    };
    if (!declaration || declaration.getContract() != contract ||
        !declaration.getImplementation().empty() ||
        !strings(declaration.getArguments(), arguments) ||
        !strings(op->getAttrOfType<ArrayAttr>("parameters"), parameters) ||
        op->getAttrs().size() != 3 || op->getNumRegions() ||
        op->getNumResults() != unsigned(output) ||
        !llvm::equal(op->getOperands(), operands)) {
      valid = false;
      return {};
    }
    bindings.insert(declaration);
    return output ? op->getResult(0) : Value();
  }
  Value natural(unsigned value) {
    return primitive("index.constant", {}, {std::to_string(value)});
  }
  Value scalar(StringRef value) {
    return primitive("field.constant", {}, {value.str()});
  }
  void require(Value predicate) {
    primitive("control.require", {predicate}, {}, {}, false);
  }
  void terminal(StringRef name, ValueRange values) {
    if (!valid || !cursor || cursor->getName().getStringRef() != name ||
        !cursor->getAttrs().empty() || cursor->getNumResults() ||
        cursor->getNumRegions() || cursor->getNextNode() ||
        !llvm::equal(cursor->getOperands(), values))
      valid = false;
    cursor = nullptr;
  }
  Value shapes(ValueRange factors, std::optional<Value> expected = {}) {
    Value n = primitive("poly.table_arity", factors.front());
    if (expected)
      require(primitive("index.equal", {n, *expected}));
    for (Value factor : factors.drop_front()) {
      Value arity = primitive("poly.table_arity", factor);
      require(primitive("index.equal", {n, arity}));
    }
    return n;
  }
  Value pack(Value point, ValueRange tables) {
    auto *op = take(local::VariantInjectOp::getOperationName());
    if (!op)
      return {};
    SmallVector<Value> values{point};
    append_range(values, tables);
    auto alternative = op->getAttrOfType<StringAttr>("alternative");
    if (!alternative || alternative.getValue() != "state" ||
        op->getAttrs().size() != 2 || op->getNumRegions() ||
        op->getNumResults() != 1 ||
        op->getResult(0).getType() != poly::residualStateType(recipe) ||
        !llvm::equal(op->getOperands(), values)) {
      valid = false;
      return {};
    }
    return op->getResult(0);
  }
  Coefficients expression(ArrayRef<Coefficients> substitutions, Value zero) {
    llvm::DenseMap<Value, Coefficients> values;
    for (auto [slot, terms] :
         zip(recipe.getBody().front().getArguments(), substitutions))
      values[slot] = terms;
    for (auto &op : recipe.getBody().front().without_terminator()) {
      if (!valid || !remaining) {
        valid = false;
        return {};
      }
      --remaining;
      Coefficients result;
      if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
        result.push_back(scalar(constant.getValue()));
      else {
        const auto &a = values.at(op.getOperand(0));
        const auto &b = values.at(op.getOperand(1));
        if (isa<algebra::FieldMultiplyOp>(op)) {
          result.assign(a.size() + b.size() - 1, zero);
          // Each pair contributes to the coefficient at its exponent sum.
          // Keeping every update checks actual accumulator and operand wiring.
          for (unsigned i = 0; i < a.size(); ++i)
            for (unsigned j = 0; j < b.size(); ++j) {
              Value product = primitive("field.mul", {a[i], b[j]});
              result[i + j] = primitive("field.add", {result[i + j], product});
            }
        } else {
          unsigned width = std::max(a.size(), b.size());
          for (unsigned i = 0; i < width; ++i)
            result.push_back(primitive(
                isa<algebra::FieldAddOp>(op) ? "field.add" : "field.sub",
                {i < a.size() ? a[i] : zero, i < b.size() ? b[i] : zero}));
        }
      }
      values[op.getResult(0)] = std::move(result);
    }
    return values.lookup(
        cast<poly::RecipeYieldOp>(recipe.getBody().front().back()).getValue());
  }
  Value round(ValueRange factors, Value arity) {
    Value start = natural(0);
    require(primitive("index.less", {start, arity}));
    SmallVector<Value> tables;
    for (Value factor : factors)
      tables.push_back(primitive("vector.from_table", factor));
    Value length = primitive("vector.length", tables.front());
    Value two = natural(2);
    Value half = primitive("index.div", {length, two});
    Value zero = scalar("0");
    // Declared degree is the fixed message ABI, including zero padding.
    unsigned width = recipe->getAttrOfType<IntegerAttr>("degree").getInt() + 1;
    auto *loop = take(local::LocalForOp::getOperationName());
    if (!loop)
      return {};
    SmallVector<Value> operands{start, half};
    operands.append(width, zero);
    append_range(operands, tables);
    operands.push_back(half);
    operands.push_back(zero);
    if (loop->getAttrs().size() != 1 || loop->getNumResults() != width ||
        loop->getNumRegions() != 1 || !loop->getRegion(0).hasOneBlock() ||
        !llvm::equal(loop->getOperands(), operands)) {
      valid = false;
      return {};
    }
    auto &body = loop->getRegion(0).front();
    if (body.getNumArguments() != 1 + width + factors.size() + 2) {
      valid = false;
      return {};
    }
    Operation *continuation = cursor;
    cursor = &body.front();
    unsigned capture = 1 + width;
    Value row = body.getArgument(0);
    Value high = primitive("index.add",
                           {row, body.getArgument(capture + factors.size())});
    SmallVector<Coefficients> slots;
    for (unsigned j = 0; j < factors.size(); ++j) {
      Value data = body.getArgument(capture + j);
      Value lowValue = primitive("vector.get", {data, row});
      Value highValue = primitive("vector.get", {data, high});
      slots.push_back(
          {lowValue, primitive("field.sub", {highValue, lowValue})});
    }
    Value padding = body.getArguments().back();
    auto coefficients = expression(slots, padding);
    SmallVector<Value> yielded;
    for (unsigned j = 0; j < width; ++j)
      yielded.push_back(primitive(
          "field.add", {body.getArgument(1 + j),
                        j < coefficients.size() ? coefficients[j] : padding}));
    append_range(yielded, body.getArguments().drop_front(capture));
    terminal(local::LocalYieldOp::getOperationName(), yielded);
    cursor = continuation;
    Value vector = primitive("vector.empty");
    for (Value coefficient : loop->getResults())
      vector = primitive("vector.append", {vector, coefficient});
    return primitive("field_array.from_vector", vector, {}, width);
  }
  SmallVector<Value> evaluate(Value point, ValueRange factors) {
    SmallVector<Coefficients> scalars;
    for (Value factor : factors)
      scalars.push_back({primitive("poly.evaluate", {factor, point})});
    auto terms = expression(scalars, scalar("0"));
    if (terms.size() != 1) {
      valid = false;
      return {};
    }
    return {terms.front()};
  }

public:
  RecipeCorrespondence(SymbolTable &symbols,
                       llvm::DenseSet<Operation *> &bindings,
                       uint64_t &remaining, poly::RecipeOp recipe)
      : symbols(symbols), bindings(bindings), remaining(remaining),
        recipe(recipe),
        domain(cast<algebra::FieldType>(
                   recipe.getBody().front().getArgument(0).getType())
                   .getDomain()) {}
  LogicalResult check(poly::RealizeOp source, local::FuncOp function) {
    auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
    auto name = StringAttr::get(source.getContext(), source.getSymName());
    if (function.getSymName() != source.getSymName() ||
        function.getFunctionType() != source.getFunctionType() ||
        function->getAttrs().size() != 3 || !origin || origin.size() != 2 ||
        origin[0] != name ||
        origin[1] != ArrayAttr::get(source.getContext(), {}) ||
        !function.getBody().hasOneBlock())
      return failure();
    auto &entry = function.getBody().front();
    cursor = &entry.front();
    SmallVector<Value> outputs;
    StringRef kind = source.getKind();
    if (kind == "init") {
      shapes(entry.getArguments().drop_front(), entry.getArgument(0));
      outputs.push_back(pack(primitive("poly.empty_point"),
                             entry.getArguments().drop_front()));
    } else if (kind == "evaluate") {
      Value vector = primitive("vector.from_point", entry.getArgument(0));
      Value length = primitive("vector.length", vector);
      shapes(entry.getArguments().drop_front(), length);
      outputs =
          evaluate(entry.getArgument(0), entry.getArguments().drop_front());
    } else {
      auto *match = take(local::LocalMatchOp::getOperationName());
      if (!match)
        return failure();
      auto alternatives = match->getAttrOfType<ArrayAttr>("alternatives");
      auto state = StringAttr::get(source.getContext(), "state");
      if (match->getAttrs().size() != 2 || !alternatives ||
          alternatives != ArrayAttr::get(source.getContext(), {state}) ||
          !llvm::equal(match->getOperands(), entry.getArguments()) ||
          match->getNumRegions() != 1 || !match->getRegion(0).hasOneBlock())
        return failure();
      Operation *continuation = cursor;
      auto &body = match->getRegion(0).front();
      unsigned count = recipe.getBody().front().getNumArguments();
      if (body.getNumArguments() != count + 1 + unsigned(kind == "bind"))
        return failure();
      cursor = &body.front();
      auto factors = body.getArguments().slice(1, count);
      Value n = shapes(factors);
      SmallVector<Value> result;
      if (kind == "arity")
        result.push_back(n);
      else if (kind == "round")
        result.push_back(round(factors, n));
      else if (kind == "bind") {
        Value zero = natural(0);
        require(primitive("index.less", {zero, n}));
        Value challenge = body.getArguments().back();
        SmallVector<Value> fixed;
        for (Value factor : factors)
          fixed.push_back(primitive("poly.fold", {factor, challenge}));
        Value point =
            primitive("poly.append_point", {body.getArgument(0), challenge});
        result.push_back(pack(point, fixed));
      } else if (kind == "finish") {
        Value zero = natural(0);
        require(primitive("index.equal", {n, zero}));
        Value empty = primitive("poly.empty_point");
        result.push_back(body.getArgument(0));
        append_range(result, evaluate(empty, factors));
      } else
        return failure();
      terminal(local::LocalYieldOp::getOperationName(), result);
      cursor = continuation;
      append_range(outputs, match->getResults());
    }
    terminal(local::ReturnOp::getOperationName(), outputs);
    return success(valid);
  }
};
} // namespace
LogicalResult verifyPolynomialRecipesPreserved(ModuleOp original,
                                               ModuleOp candidate) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto refuse = [&](StringRef reason) {
    return diagnostics::emit(candidate.emitError(),
                             "polynomial-recipe-correspondence", reason);
  };
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return refuse("module shape");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after ||
      before.getProfile() != protocol_ir::Profile::Protocol ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse("profile");
  SymbolTable oldSymbols(before), symbols(after);
  llvm::DenseSet<Operation *> retained, bindings;
  uint64_t remaining = 1000000;
  for (Operation &op : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    if (!name)
      return refuse("unnamed declaration");
    Operation *replacement = symbols.lookup(name.getValue());
    if (isa<poly::RecipeOp>(op)) {
      if (replacement)
        return refuse("recipe declaration retained");
      continue;
    }
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    if (auto realization = dyn_cast<poly::RealizeOp>(op)) {
      auto recipe = oldSymbols.lookup<poly::RecipeOp>(realization.getRecipe());
      auto function = dyn_cast<local::FuncOp>(replacement);
      if (!recipe || !function ||
          failed(RecipeCorrespondence(symbols, bindings, remaining, recipe)
                     .check(realization, function)))
        return refuse(remaining ? "realization body" : "work limit");
    } else if (!OperationEquivalence::isEquivalentTo(
                   &op, replacement, OperationEquivalence::IgnoreLocations))
      return refuse("changed retained declaration");
  }
  for (auto &op : after.getBody().front())
    if (!retained.contains(&op) && !bindings.contains(&op))
      return refuse("unexpected declaration");
  return success();
}
} // namespace zkc::mathematical
