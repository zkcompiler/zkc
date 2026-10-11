#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
finite::Computation computation(ModuleOp module) {
  Operation *found = nullptr;
  module.walk([&](Operation *op) {
    if (finite::isComputation(op))
      found = op;
  });
  require(found, "missing computation");
  finite::Computation result;
  require(succeeded(finite::describe(found, result)), "invalid computation");
  return result;
}
const char *indexed = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V,%ys:!V):
   %x = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   %y = "data.domain_indices"(%ys) {axis=0:i64} : (!V)->!data.domain<ui64>
   %d = "data.domain_zip"(%x,%y) : (!data.domain<ui64>,!data.domain<ui64>)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V)->!data.domain<ui64,ui64>} : ()->()
 local.func private @step(%s:!F,%i:ui64,%j:ui64,%xs:!V,%ys:!V)->!F attributes {logical_origin=["step",[]]} {
   %x = "algebra.exec.vector_get"(%xs,%i) {binding=@get,parameters=[],site="x"} : (!V,ui64)->!F
   %y = "algebra.exec.vector_get"(%ys,%i) {binding=@get,parameters=[],site="y"} : (!V,ui64)->!F
   %p = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,parameters=[],site="p"} : (!F,!F)->!F
   %r = "algebra.exec.field_add"(%p,%s) {binding=@add,parameters=[],site="r"} : (!F,!F)->!F
   local.return %r : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%ys:!V,%seed:!F)->!F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%seed) {site="fold"} : (!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%ys:!V,%seed:!F):
   %r = "protocol.local_call"(%xs,%ys,%seed) {callee=@work,role="P",site="work"} : (!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("exact nominal facets", [&] {
    auto field = take(protocol::parseBoundType("field:bls12-381.fr", false));
    auto other = take(protocol::parseBoundType("field:bn254.fr", false));
    auto group = take(protocol::parseBoundType("group:bls12-381.g1", false));
    protocol::BindingApplication app{"field.add", {"bls12-381.fr"}, ""};
    auto *facet =
        protocol::admitComputationContract(app, {field, field}, {field});
    require(facet && facet->law.commutative && facet->reduction && facet->lanes,
            "field sum/lifting facets missing");
    require(!protocol::admitComputationContract(app, {field, other}, {field}),
            "different nominal field acquired a law");
    app.implementation = "arkworks/field.add";
    require(!protocol::admitComputationContract(app, {field, field}, {field}),
            "explicit implementation was replaced");
    app = {"curve.scale", {"bls12-381.g1"}, ""};
    require(protocol::admitComputationContract(app, {group, field}, {group}),
            "associated scalar field rejected");
    require(!protocol::admitComputationContract(app, {group, other}, {group}),
            "wrong associated scalar field acquired a law");
    auto *subtract = protocol::computationContract("field.sub");
    require(subtract && !subtract->law.commutative && !subtract->reduction,
            "subtraction acquired commutative reduction laws");
    auto *scale = protocol::computationContract("curve.scale");
    require(scale && !scale->law.commutative && scale->lanes &&
                scale->lanes->first == 1 && scale->lanes->second == 0 &&
                scale->law.algebra == protocol::ComputationAlgebra::GroupModule,
            "group scalar action lost its ordered module operands");
    require(!protocol::computationContract("user.field.add"),
            "unknown contract acquired installed authority");
  });
  for (auto [name, kernel] : {std::pair{"sum", "vector.sum"},
                              {"product", "vector.product"},
                              {"dot", "vector.dot"},
                              {"msm-direct", "curve.msm"},
                              {"matrix-row", "matrix.row_dot"},
                              {"matrix-column", "matrix.column_dot"}})
    cases.run(name, [&, name = name, kernel = kernel] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "fixture refused");
      auto c = computation(*module);
      auto plan = finite::recognizeReduction(c);
      require(plan && plan->kernel == kernel, "kernel not recognized");
      auto originalInputs = plan->inputs;
      auto *combine = plan->combiner;
      Value left = combine->getOperand(0), right = combine->getOperand(1);
      combine->setOperands({right, left});
      plan = finite::recognizeReduction(c);
      require(plan && plan->kernel == kernel && plan->inputs == originalInputs,
              "symmetric accumulator changed the contraction");
      if (StringRef(name).starts_with("matrix-")) {
        require(plan->selectedIndex == 3 &&
                    plan->inputs == SmallVector<unsigned>({0, 1}),
                "selected matrix demand/input positions lost");
        require(plan->demand == (StringRef(name) == "matrix-row"
                                     ? finite::DemandKind::MatrixRow
                                     : finite::DemandKind::MatrixColumn),
                "matrix orientation lost");
      }
      auto view = finite::analyzeComputation(c);
      require(view && view->seeds.size() == 1 &&
                  view->captures.size() == c.arguments + c.captures &&
                  view->reduction && !view->admission.empty(),
              "seed/capture/admission structure missing");
      require(!finite::analyzeComputation(c, 0), "analysis ignored budget");
      // A recognized ordered helper cannot lose even unused successful work.
      OpBuilder builder(combine);
      builder.clone(*combine);
      require(!finite::recognizeReduction(c),
              "unused ordered operation erased");
    });
  cases.run("bilinear multiplication order and symmetric combine", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("bilinear"), &context);
    require(bool(module), "bilinear fixture refused");
    auto c = computation(*module);
    require(bool(finite::recognizeBilinear(c)), "bilinear contraction missing");
    auto &body = c.helper->getRegion(0).front();
    for (auto &op : body.without_terminator()) {
      auto *facet = finite::semantics(&op);
      if (!facet || !facet->law.commutative)
        continue;
      Value left = op.getOperand(0), right = op.getOperand(1);
      op.setOperands({right, left});
    }
    require(bool(finite::recognizeBilinear(c)),
            "bilinear operand variation refused");
    // Matrix coordinates are ordered even though scalar products commute.
    auto &lookup = body.front();
    Value row = lookup.getOperand(1), column = lookup.getOperand(2);
    lookup.setOperands({lookup.getOperand(0), column, row});
    require(!finite::recognizeBilinear(c),
            "transposed access acquired the same contraction");
  });
  cases.run("ordered collect keeps unused instructions", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(module), "collect fixture refused");
    auto c = computation(*module);
    require(bool(finite::recognizeElementwise(c)), "collect formula missing");
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    builder.clone(body.front());
    require(!finite::recognizeElementwise(c),
            "unused ordered lane operation erased");
  });
  cases.run("indexed dot and indexed unary reductions", [&] {
    auto module = parseSourceString<ModuleOp>(indexed, &context);
    require(bool(module), "indexed fixture refused");
    auto c = computation(*module);
    auto plan = finite::recognizeReduction(c);
    require(plan && plan->kernel == "vector.dot" &&
                plan->inputs == SmallVector<unsigned>({0, 1}) &&
                plan->accesses.size() == 2 && plan->accesses[0].item == 0 &&
                plan->accesses[1].item == 0,
            "indexed dot lost captured container identity");
    auto &body = c.helper->getRegion(0).front();
    auto *combine = plan->combiner;
    auto *product = plan->term.getDefiningOp();
    auto *second = product->getOperand(1).getDefiningOp();
    combine->setOperand(0, product->getOperand(0));
    product->erase();
    second->erase();
    plan = finite::recognizeReduction(c);
    require(plan && plan->kernel == "vector.sum", "indexed sum missing");
    OpBuilder builder(combine);
    OperationState state(combine->getLoc(), "algebra.exec.field_multiply");
    state.addOperands(combine->getOperands());
    state.addTypes(combine->getResultTypes());
    state.addAttributes(combine->getAttrs());
    state.attributes.set("binding", FlatSymbolRefAttr::get(&context, "mul"));
    auto *multiply = builder.create(state);
    body.back().setOperand(0, multiply->getResult(0));
    combine->erase();
    plan = finite::recognizeReduction(c);
    require(plan && plan->kernel == "vector.product",
            "indexed product missing");
    auto *lookup = body.front().getResult(0).getDefiningOp();
    lookup->setAttr("algebra.commutative", builder.getUnitAttr());
    require(!finite::recognizeReduction(c), "user metadata acquired authority");
  });
  cases.run("indexed access must traverse the complete container", [&] {
    auto module = parseSourceString<ModuleOp>(indexed, &context);
    require(bool(module), "indexed fixture refused");
    auto c = computation(*module);
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.front());
    auto index = data::IndexOp::create(
        builder, body.front().getLoc(),
        IntegerType::get(&context, 64, IntegerType::Unsigned), "0");
    auto &lookup = *std::next(body.begin());
    lookup.setOperand(1, index);
    require(finite::semantics(&lookup),
            "fixed-index control has invalid ports");
    require(!finite::recognizeReduction(c),
            "fixed access became a complete-vector reduction");
  });
  cases.run("pure neutral and unused expressions", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    require(bool(module), "nested fixture refused");
    auto c = computation(*module);
    auto nested = finite::analyzeComputation(c);
    require(nested && nested->nested.size() == 1 &&
                nested->nested[0].seeds[0].actual &&
                nested->nested[0].admission.size() == 1,
            "nested admission or seed occurrence lost");
    auto inner = nested->nested[0].computation;
    auto &body = inner.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    auto field = body.back().getOperand(0).getType();
    auto zero = algebra::ConstantFieldOp::create(builder, body.back().getLoc(),
                                                 field, "0");
    auto neutral = algebra::FieldAddOp::create(
        builder, body.back().getLoc(), field, body.back().getOperand(0), zero);
    body.back().setOperand(0, neutral);
    algebra::FieldMultiplyOp::create(builder, body.back().getLoc(), field,
                                     body.getArgument(0), body.getArgument(1));
    require(bool(finite::recognizeReduction(inner)),
            "pure neutral/unused form refused");
  });
  cases.run("common lane formula and noncommutative subtraction", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-collect"), &context);
    require(bool(module), "collect fixture refused");
    auto c = computation(*module);
    auto plan = finite::recognizeElementwise(c);
    require(bool(plan), "elementwise formula not recognized");
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    auto value = body.back().getOperand(0);
    auto difference = algebra::SubtractFieldOp::create(
        builder, body.back().getLoc(), value.getType(), body.getArgument(2),
        value);
    body.back().setOperand(0, difference);
    plan = finite::recognizeElementwise(c);
    require(plan && plan->modes.lookup(difference) == finite::FormulaMode::Rows,
            "ordered subtraction lane mode lost");
  });
  return cases.result();
}
