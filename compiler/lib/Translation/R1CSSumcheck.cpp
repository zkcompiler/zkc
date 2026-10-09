#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Relations.h"
#include "llvm/Support/MathExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::relation {
namespace {
namespace pir = protocol_ir;
class R1CSSumcheckBuilder {
  OpBuilder b;
  Location loc;
  Type field;
  unsigned arity, rows;
  const R1CS &relation;
  pir::ProtocolModuleOp unit;
  ArrayAttr strings(ArrayRef<StringRef> values) {
    return b.getStrArrayAttr(values);
  }
  ArrayAttr sets(ArrayRef<ArrayAttr> values) {
    SmallVector<Attribute> attrs(values.begin(), values.end());
    return b.getArrayAttr(attrs);
  }
  Operation *op(StringRef name, TypeRange results, ValueRange operands,
                ArrayRef<NamedAttribute> attrs = {}) {
    OperationState state(loc, name);
    state.addTypes(results);
    state.addOperands(operands);
    state.addAttributes(attrs);
    return b.create(state);
  }
  template <class Op>
  Value value(Type type, ValueRange inputs,
              ArrayRef<NamedAttribute> attrs = {}) {
    return op(Op::getOperationName(), type, inputs, attrs)->getResult(0);
  }
  NamedAttribute text(StringRef key, StringRef val) {
    return b.getNamedAttr(key, b.getStringAttr(val));
  }
  Value constant(StringRef literal) {
    return value<algebra::ConstantFieldOp>(field, {}, {text("value", literal)});
  }
  Value at(Value array, unsigned index) {
    return value<algebra::ArrayAtOp>(
        field, array, {b.getNamedAttr("index", b.getI64IntegerAttr(index))});
  }
  Value array(ValueRange values) {
    return value<tensor::FromElementsOp>(
        RankedTensorType::get({int64_t(values.size())}, field), values);
  }
  Value equal(Value a, Value c) {
    return value<algebra::FieldEqualOp>(b.getI1Type(), {a, c});
  }
  Value conjunction(Value a, Value c) {
    return value<arith::AndIOp>(b.getI1Type(), {a, c});
  }
  Value mul(Value a, Value c) {
    return value<algebra::FieldMultiplyOp>(field, {a, c});
  }
  Value add(Value a, Value c) {
    return value<algebra::FieldAddOp>(field, {a, c});
  }
  Value sub(Value a, Value c) {
    return value<algebra::SubtractFieldOp>(field, {a, c});
  }
  Type polynomial(unsigned variables) {
    return poly::PolynomialType::get(b.getContext(), relation.field(),
                                     variables);
  }
  std::array<SmallVector<Value>, 3> products(Value assignment, Value zero) {
    std::array<SmallVector<Value>, 3> result;
    for (unsigned matrix = 0; matrix < 3; ++matrix) {
      for (const auto &row : relation.constraints()) {
        Value sum = zero;
        for (const auto &term : row[matrix])
          sum = add(sum, mul(constant(term.coefficient),
                             at(assignment, term.column)));
        result[matrix].push_back(sum);
      }
      result[matrix].resize(rows, zero);
    }
    return result;
  }
  pir::MathematicalOp function(StringRef name, TypeRange inputs,
                               TypeRange outputs, ArrayAttr roles,
                               ArrayRef<ArrayAttr> inRoles,
                               ArrayRef<ArrayAttr> outRoles) {
    b.setInsertionPointToEnd(&unit.getBody().front());
    auto f = pir::MathematicalOp::create(b, loc, name,
                                         b.getFunctionType(inputs, outputs),
                                         roles, sets(inRoles), sets(outRoles));
    auto *block = new Block();
    f.getBody().push_back(block);
    for (auto type : inputs)
      block->addArgument(type, loc);
    b.setInsertionPointToEnd(block);
    return f;
  }
  Value recipe(Value z, Value tau) {
    return func::CallOp::create(b, loc, "recipe", TypeRange{polynomial(arity)},
                                ValueRange{z, tau})
        .getResult(0);
  }
  Value evaluate(Value p, ValueRange point) {
    SmallVector<Value> inputs{p};
    append_range(inputs, point);
    return value<poly::EvaluatePolynomialOp>(field, inputs);
  }
  Value exchange(Value input, StringRef sender, StringRef receiver,
                 StringRef site) {
    return value<pir::ExchangeOp>(input.getType(), input,
                                  {text("sender", sender),
                                   text("receiver", receiver),
                                   text("site", site)});
  }
  Value draw(Value service, StringRef owner, StringRef site) {
    return value<pir::QueryOp>(
        field, service,
        {text("method", "draw"), text("owner", owner), text("site", site)});
  }
  void returned(ValueRange values) {
    op(pir::MathematicalReturnOp::getOperationName(), {}, values);
  }

public:
  R1CSSumcheckBuilder(const R1CS &r, MLIRContext &context)
      : b(&context), loc(b.getUnknownLoc()),
        field(algebra::FieldType::get(&context, r.field())),
        arity(std::max(1u, unsigned(Log2_64_Ceil(
                               std::max(size_t(1), r.constraints().size()))))),
        rows(1u << arity), relation(r) {}
  OwningOpRef<ModuleOp> run() {
    OwningOpRef<ModuleOp> module = ModuleOp::create(loc);
    b.setInsertionPointToStart(module->getBody());
    unit = pir::ProtocolModuleOp::create(b, loc, pir::Profile::Protocol);
    unit.getBody().push_back(new Block());
    b.setInsertionPointToEnd(&unit.getBody().front());
    Type assignment = RankedTensorType::get({relation.columns()}, field);
    Type point = RankedTensorType::get({arity}, field);
    Type table = RankedTensorType::get({rows}, field);
    Type service =
        pir::ServiceReferenceType::get(b.getContext(), "random.bls12-381.fr/1");
    auto helper = func::FuncOp::create(
        b, loc, "recipe",
        b.getFunctionType({assignment, point}, {polynomial(arity)}));
    helper.setPrivate();
    auto *body = helper.addEntryBlock();
    b.setInsertionPointToStart(body);
    auto zero = constant("0"), one = constant("1");
    auto matrices = products(body->getArgument(0), zero);
    for (auto &item : matrices[2])
      item = sub(zero, item);
    SmallVector<Value> weights;
    for (unsigned row = 0; row < rows; ++row) {
      Value weight = one;
      for (unsigned axis = 0; axis < arity; ++axis) {
        Value t = at(body->getArgument(1), axis);
        weight =
            mul(weight, row & (1u << (arity - axis - 1)) ? t : sub(one, t));
      }
      weights.push_back(weight);
    }
    auto mle = [&](ValueRange values) {
      return value<poly::MultilinearPolynomialOp>(polynomial(arity),
                                                  array(values));
    };
    Value a = mle(matrices[0]), c = mle(matrices[1]),
          negativeC = mle(matrices[2]), eq = mle(weights);
    auto product = value<poly::MultiplyPolynomialOp>(polynomial(arity), {a, c});
    auto residual =
        value<poly::AddPolynomialOp>(polynomial(arity), {product, negativeC});
    auto weighted =
        value<poly::MultiplyPolynomialOp>(polynomial(arity), {eq, residual});
    func::ReturnOp::create(b, loc, weighted);

    auto pv = strings({"P", "V"}), v = strings({"V"});
    SmallVector<Type> residualTypes{assignment, point};
    residualTypes.append(arity + 1, field);
    SmallVector<ArrayAttr> residualRoles(residualTypes.size(), v);
    auto reduction =
        function("reduction", {assignment, point, field, service},
                 residualTypes, pv, {pv, pv, pv, v}, residualRoles);
    auto args = reduction.getBody().front().getArguments();
    Value f = recipe(args[0], args[1]), current = f, previous = args[2];
    zero = constant("0");
    one = constant("1");
    SmallVector<Value> challenges;
    for (unsigned i = 0; i < arity; ++i) {
      auto round = value<poly::SumPolynomialOp>(
          polynomial(1), current,
          {b.getNamedAttr("count", b.getI64IntegerAttr(arity - i - 1))});
      auto coefficients = value<poly::PolynomialCoefficientsOp>(
          RankedTensorType::get({4}, field), round);
      auto received =
          exchange(coefficients, "P", "V", "round" + std::to_string(i));
      auto q = value<poly::CoefficientPolynomialOp>(polynomial(1), received);
      auto accepted = equal(add(evaluate(q, zero), evaluate(q, one)), previous);
      op(pir::GuardOp::getOperationName(), {}, accepted,
         {text("owner", "V"), text("site", "guard" + std::to_string(i))});
      auto challenge = draw(args[3], "V", "query" + std::to_string(i));
      auto delivered =
          exchange(challenge, "V", "P", "challenge" + std::to_string(i));
      challenges.push_back(challenge);
      previous = evaluate(q, challenge);
      if (i + 1 < arity)
        current = value<poly::FixPolynomialOp>(polynomial(arity - i - 1),
                                               {current, delivered});
    }
    SmallVector<Value> residualValues{args[0], args[1]};
    append_range(residualValues, challenges);
    residualValues.push_back(previous);
    returned(residualValues);
    auto terminal = function("terminal", residualTypes, {b.getI1Type()}, v,
                             residualRoles, {v});
    auto terminalArgs = terminal.getBody().front().getArguments();
    auto actual = evaluate(recipe(terminalArgs[0], terminalArgs[1]),
                           terminalArgs.slice(2, arity));
    returned(equal(actual, terminalArgs.back()));

    // Independent evaluator client exposes the imported matrix products and
    // both exact predicates; it does not reuse the polynomial recipe.
    SmallVector<Type> evaluationInputs{assignment};
    evaluationInputs.append(relation.publicCount(), field);
    SmallVector<ArrayAttr> evaluationRoles(evaluationInputs.size(),
                                           strings({"Checker"}));
    auto check = function("evaluate", evaluationInputs,
                          {table, table, table, b.getI1Type(), b.getI1Type()},
                          strings({"Checker"}), evaluationRoles,
                          SmallVector<ArrayAttr>(5, strings({"Checker"})));
    auto ea = check.getBody().front().getArguments();
    zero = constant("0");
    one = constant("1");
    auto rowsValues = products(ea[0], zero);
    Value bound = equal(at(ea[0], 0), one);
    for (unsigned i = 0; i < relation.publicCount(); ++i)
      bound = conjunction(bound, equal(at(ea[0], i + 1), ea[i + 1]));
    Value satisfied = bound;
    for (unsigned row = 0; row < relation.constraints().size(); ++row)
      satisfied = conjunction(satisfied,
                              equal(mul(rowsValues[0][row], rowsValues[1][row]),
                                    rowsValues[2][row]));
    returned({array(rowsValues[0]), array(rowsValues[1]), array(rowsValues[2]),
              bound, satisfied});

    // Fix ONE and the public layout by construction. Witness scalars are
    // available to both roles in this explicitly non-hiding client.
    auto both = strings({"Prover", "Checker"}), verifier = strings({"Checker"});
    SmallVector<Type> inputs(relation.columns() - 1, field);
    inputs.push_back(service);
    SmallVector<ArrayAttr> inRoles(relation.columns() - 1, both);
    inRoles.push_back(verifier);
    auto main =
        function("main", inputs, {b.getI1Type()}, both, inRoles, {verifier});
    auto ma = main.getBody().front().getArguments();
    {
      OpBuilder::InsertionGuard insertion(b);
      b.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Type> publicTypes(relation.publicCount(), field);
      SmallVector<Attribute> purposes;
      purposes.assign(relation.publicCount(), b.getStringAttr("statement"));
      op(DeclareOp::getOperationName(), {}, {},
         {text("sym_name", "subject"), text("kind", "r1cs"),
          text("key", relation.identity()), text("revision", "1"),
          b.getNamedAttr("signature", TypeAttr::get(b.getFunctionType(
                                          publicTypes, b.getI1Type()))),
          b.getNamedAttr("purposes", b.getArrayAttr(purposes))});
    }
    SmallVector<Attribute> selectors(relation.publicCount(),
                                     b.getStringAttr("Checker"));
    op(pir::StatementOp::getOperationName(), {},
       ma.take_front(relation.publicCount()),
       {b.getNamedAttr("relation",
                       FlatSymbolRefAttr::get(b.getContext(), "subject")),
        b.getNamedAttr("selectors", b.getArrayAttr(selectors)),
        b.getNamedAttr("acceptance", b.getI64IntegerAttr(0))});
    SmallVector<Value> z{constant("1")};
    append_range(z, ma.drop_back());
    auto assignmentValue = array(z);
    SmallVector<Value> draws;
    for (unsigned i = 0; i < arity; ++i)
      draws.push_back(exchange(
          draw(ma.back(), "Checker", "weight_draw" + std::to_string(i)),
          "Checker", "Prover", "weight" + std::to_string(i)));
    auto tau = array(draws);
    zero = constant("0");
    auto reduce =
        pir::ApplyOp::create(b, loc, residualTypes,
                             ValueRange{assignmentValue, tau, zero, ma.back()},
                             "reduction", both, "reduce");
    auto end = pir::ApplyOp::create(b, loc, TypeRange{b.getI1Type()},
                                    reduce.getOutputs(), "terminal", verifier,
                                    "decide");
    returned(end.getOutputs());
    return module;
  }
};
} // namespace
Expected<OwningOpRef<ModuleOp>> authorR1CSSumcheck(const R1CS &relation,
                                                   MLIRContext &context) {
  if (relation.field() != "bls12-381.fr")
    return error("native-r1cs-field");
  // A scalar reference adapter, not a scalable sparse prover. Bound before
  // constructing SSA; ordinary compiler work limits still apply afterwards.
  if (relation.constraints().size() > 8 || relation.columns() > 128 ||
      relation.nonzeros() > 1024)
    return error("native-r1cs-limit");
  context.getOrLoadDialect<RelationDialect>();
  context.getOrLoadDialect<pir::ProtocolDialect>();
  context.getOrLoadDialect<algebra::AlgebraDialect>();
  context.getOrLoadDialect<poly::PolynomialDialect>();
  context.getOrLoadDialect<func::FuncDialect>();
  context.getOrLoadDialect<tensor::TensorDialect>();
  context.getOrLoadDialect<arith::ArithDialect>();
  auto module = R1CSSumcheckBuilder(relation, context).run();
  if (failed(verify(*module)))
    return error("native-r1cs-ir");
  return module;
}
json::Value r1csSumcheckRequirements(const R1CS &relation) {
  unsigned arity =
      std::max(1u, unsigned(Log2_64_Ceil(
                       std::max(size_t(1), relation.constraints().size()))));
  json::Array points;
  for (unsigned i = 0; i < arity; ++i)
    points.push_back(i + 2);
  json::Object requirement{
      {"id", "r1cs"},
      {"family", "r1cs-sum-to-point/1"},
      {"reduction", "reduction"},
      {"terminal", "terminal"},
      {"recipe", "recipe"},
      {"verifier", "V"},
      {"terminal_role", "V"},
      {"subjects", json::Array{0, 1}},
      {"claim", 2},
      {"service", 3},
      {"residual_subjects", json::Array{0, 1}},
      {"residual_point", json::Array(points)},
      {"residual_scalar", arity + 2},
      {"terminal_subjects", json::Array{0, 1}},
      {"terminal_point", std::move(points)},
      {"terminal_scalar", arity + 2},
      {"decision", 0},
      {"composition", json::Object{{"entry", "main"},
                                   {"reduction_site", "reduce"},
                                   {"terminal_site", "decide"}}},
      {"relation", relation.encode()}};
  return json::Object{{"format", "zkc.polynomial-requirements"},
                      {"requirements", json::Array{std::move(requirement)}}};
}
} // namespace zkc::relation
