#include "../lib/Transforms/ComputationEquations.h"
#include "../lib/Transforms/ComputationSelection.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/NestedContractions.h"
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
OwningOpRef<ModuleOp> clone(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
bool hasKernel(ModuleOp module, StringRef contract) {
  bool found = false;
  module.walk([&](Operation *op) {
    found |=
        op->getName().getStringRef() == protocol::boundOperationName(contract);
  });
  return found;
}
bool hasOrderedLoop(ModuleOp module) {
  bool found = false;
  module.walk([&](local::LocalForOp) { found = true; });
  return found;
}
Operation *neutralResult(Block &body, bool multiply, bool left = false) {
  OpBuilder builder(&body.back());
  auto location = body.back().getLoc();
  Value result = body.back().getOperand(0);
  OperationState constant(location, "algebra.exec.field_constant");
  constant.addTypes(result.getType());
  constant.addAttribute(
      "binding", FlatSymbolRefAttr::get(builder.getContext(), "constant"));
  constant.addAttribute("parameters",
                        builder.getStrArrayAttr({multiply ? "1" : "0"}));
  constant.addAttribute("site", builder.getStringAttr("neutral_constant"));
  Value identity = builder.create(constant)->getResult(0);
  OperationState operation(location, multiply ? "algebra.exec.field_multiply"
                                              : "algebra.exec.field_add");
  operation.addOperands(left ? ValueRange{identity, result}
                             : ValueRange{result, identity});
  operation.addTypes(result.getType());
  operation.addAttribute(
      "binding",
      FlatSymbolRefAttr::get(builder.getContext(), multiply ? "mul" : "add"));
  operation.addAttribute("parameters", builder.getArrayAttr({}));
  operation.addAttribute("site", builder.getStringAttr("neutral_result"));
  auto *wrapped = builder.create(operation);
  body.back().setOperand(0, wrapped->getResult(0));
  return wrapped;
}
const char *indexed = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
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
const char *capturedReduction = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @step(%s:!F,%i:ui64,%xs:!V,%ys:!V)->!F attributes {data.preconditions=[#data.index_bound<1,3,0>]} {
   %x = "data.bounded_at"(%ys,%i) : (!V,ui64)->!F
   %r = algebra.field_add %s,%x : (!F,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = "algebra.finite_fold"(%xs,%seed,%xs) {domain=@items,step=@step} : (!V,!F,!V)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
const char *indexedCollect = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @body(%i:ui64,%xs:!V,%factor:!F)->!F attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %x = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   %r = algebra.field_subtract %factor,%x : (!F,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%factor:!F):
   %r = "algebra.finite_collect"(%xs,%factor) {domain=@items,body=@body} : (!V,!F)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V,!F)->!V,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
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
    require(facet && facet->law.commutative && facet->law.associative,
            "field ring laws missing");
    require(!protocol::admitComputationContract(app, {field, other}, {field}),
            "different nominal field acquired a law");
    app.implementation = "arkworks/field.add";
    require(protocol::admitMathematicalMeaning(app, {field, field}, {field}) ==
                facet,
            "explicit implementation erased logical meaning");
    require(!protocol::admitComputationContract(app, {field, field}, {field}),
            "explicit implementation was replaced");
    app = {"curve.scale", {"bls12-381.g1"}, ""};
    require(protocol::admitComputationContract(app, {group, field}, {group}),
            "associated scalar field rejected");
    require(!protocol::admitComputationContract(app, {group, other}, {group}),
            "wrong associated scalar field acquired a law");
    auto *subtract = protocol::computationContract("field.sub");
    require(subtract && !subtract->law.commutative &&
                !subtract->law.associative,
            "subtraction acquired commutative reduction laws");
    auto *scale = protocol::computationContract("curve.scale");
    require(scale && !scale->law.commutative && scale->law.scalarAction &&
                scale->law.groupOperand == 0 && scale->law.scalarOperand == 1 &&
                scale->law.algebra == protocol::ComputationAlgebra::GroupModule,
            "group scalar action lost its ordered module operands");
    require(!protocol::computationContract("user.field.add"),
            "unknown contract acquired installed authority");
  });
  for (auto name :
       {"sum", "product", "dot", "msm-direct", "matrix-row", "matrix-column"})
    cases.run(name, [&, name = name] {
      auto identity =
          StringRef(name) == "product" ? MathematicalIdentity::FieldMultiply
          : StringRef(name) == "msm-direct" ? MathematicalIdentity::GroupAdd
                                            : MathematicalIdentity::FieldAdd;
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "fixture refused");
      auto c = computation(*module);
      auto view = finite::analyzeComputation(c);
      require(bool(view), "computation view missing");
      auto plan = mathematical::matchComputation(*view).reduction;
      require(plan && plan->combine == identity,
              "combiner meaning not recognized");
      auto originalInputs = plan->inputs;
      auto *combine = plan->combiner;
      Value left = combine->getOperand(0), right = combine->getOperand(1);
      combine->setOperands({right, left});
      view = finite::analyzeComputation(c);
      require(bool(view), "changed computation view missing");
      plan = mathematical::matchComputation(*view).reduction;
      require(plan && plan->combine == identity &&
                  plan->inputs == originalInputs,
              "symmetric accumulator changed the contraction");
      if (StringRef(name).starts_with("matrix-")) {
        require(plan->selectedIndex == 3 &&
                    plan->inputs == SmallVector<unsigned>({0, 1}),
                "selected matrix demand/input positions lost");
        require(plan->matrixAccess == (StringRef(name) == "matrix-row"
                                           ? finite::AccessKind::MatrixRow
                                           : finite::AccessKind::MatrixColumn),
                "matrix orientation lost");
      }
      require(view && view->seeds.size() == 1 &&
                  view->captures.size() == c.arguments + c.captures &&
                  mathematical::matchComputation(*view).reduction &&
                  !view->admission.empty(),
              "seed/capture/admission structure missing");
      require(!finite::analyzeComputation(c, 0), "analysis ignored budget");
      // A recognized ordered helper cannot lose even unused successful work.
      OpBuilder builder(combine);
      builder.clone(*combine);
      view = finite::analyzeComputation(c);
      require(view && !mathematical::matchComputation(*view).reduction &&
                  view->payload.back() == combine && view->payload.size() >= 2,
              "unused ordered operation erased");
    });
  cases.run("bilinear multiplication order and symmetric combine", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("bilinear"), &context);
    require(bool(module), "bilinear fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).bilinear &&
                view->items.size() == 4 && view->accesses.size() == 3 &&
                view->accesses.back().kind == finite::AccessKind::MatrixCell &&
                view->accesses.back().item == 0 &&
                view->accesses.back().columnItem == 2,
            "bilinear contraction or coordinate facts missing");
    auto &body = c.helper->getRegion(0).front();
    for (auto &op : body.without_terminator()) {
      auto *facet = finite::semantics(&op);
      if (!facet || !facet->law.commutative)
        continue;
      Value left = op.getOperand(0), right = op.getOperand(1);
      op.setOperands({right, left});
    }
    view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).bilinear,
            "bilinear operand variation refused");
    // Matrix coordinates are ordered even though scalar products commute.
    auto &lookup = body.front();
    Value row = lookup.getOperand(1), column = lookup.getOperand(2);
    lookup.setOperands({lookup.getOperand(0), column, row});
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).bilinear &&
                view->accesses.size() == 2,
            "transposed access acquired the same contraction");
  });
  cases.run("ordered collect keeps unused instructions", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(module), "collect fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).elementwise,
            "collect formula missing");
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    builder.clone(body.front());
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).elementwise &&
                view->payload.size() == 2,
            "unused ordered lane operation erased");
  });
  cases.run("indexed dot and indexed unary reductions", [&] {
    auto module = parseSourceString<ModuleOp>(indexed, &context);
    require(bool(module), "indexed fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(bool(view), "indexed computation view missing");
    auto plan = mathematical::matchComputation(*view).reduction;
    require(plan && plan->combine == MathematicalIdentity::FieldAdd &&
                plan->termIdentity == MathematicalIdentity::FieldMultiply &&
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
    view = finite::analyzeComputation(c);
    require(bool(view), "changed indexed computation view missing");
    plan = mathematical::matchComputation(*view).reduction;
    require(plan && plan->combine == MathematicalIdentity::FieldAdd &&
                !plan->termIdentity,
            "indexed sum missing");
    OpBuilder builder(combine);
    OperationState state(combine->getLoc(), "algebra.exec.field_multiply");
    state.addOperands(combine->getOperands());
    state.addTypes(combine->getResultTypes());
    state.addAttributes(combine->getAttrs());
    state.attributes.set("binding", FlatSymbolRefAttr::get(&context, "mul"));
    auto *multiply = builder.create(state);
    body.back().setOperand(0, multiply->getResult(0));
    combine->erase();
    view = finite::analyzeComputation(c);
    require(bool(view), "changed indexed computation view missing");
    plan = mathematical::matchComputation(*view).reduction;
    require(plan && plan->combine == MathematicalIdentity::FieldMultiply &&
                !plan->termIdentity,
            "indexed product missing");
    auto *lookup = body.front().getResult(0).getDefiningOp();
    lookup->setAttr("algebra.commutative", builder.getUnitAttr());
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).reduction &&
                view->accesses.empty(),
            "user metadata acquired authority");
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
    auto view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).reduction &&
                view->accesses.size() == 1,
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
    auto view = finite::analyzeComputation(inner);
    require(view && mathematical::matchComputation(*view).reduction,
            "pure neutral/unused form refused");
  });
  cases.run("common lane formula and noncommutative subtraction", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-collect"), &context);
    require(bool(module), "collect fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).elementwise &&
                view->accesses.size() == 1 && view->captures.size() == 2,
            "elementwise inputs or formula not recognized");
    auto &body = c.helper->getRegion(0).front();
    OpBuilder builder(&body.back());
    auto value = body.back().getOperand(0);
    auto difference = algebra::SubtractFieldOp::create(
        builder, body.back().getLoc(), value.getType(), body.getArgument(2),
        value);
    body.back().setOperand(0, difference);
    view = finite::analyzeComputation(c);
    require(
        view && mathematical::matchComputation(*view).elementwise &&
            view->result == difference &&
            mathematical::matchComputation(*view).elementwise->lookups.empty(),
        "ordered subtraction lane formula lost");
  });
  cases.run("dead domain admission is independent of accessed items", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("dead-domain"), &context);
    require(bool(module), "dead-domain fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(
        view && view->root == 0 && view->items.size() == 1 &&
            view->admission.size() == 4 && view->accesses.size() == 1 &&
            view->captures.size() == 3 &&
            mathematical::matchComputation(*view).reduction &&
            mathematical::matchComputation(*view).reduction->inputs ==
                SmallVector<unsigned>({0}),
        "unused constructors changed traversal or disappeared from admission");
    for (auto [operation, recorded] : llvm::zip(
             c.domain.getBody().front().without_terminator(), view->admission))
      require(&operation == recorded, "constructor admission order changed");
    require(view->seeds[0].input == 3 && !view->seeds[0].actual &&
                view->seeds[0].formal ==
                    c.helper->getRegion(0).front().getArgument(0),
            "declaration seed acquired a fabricated call occurrence");
  });
  cases.run("multiple states retain exact seed and result mappings", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("total-state"), &context);
    require(bool(module), "multiple-state fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && view->seeds.size() == 2 && view->captures.size() == 1 &&
                view->results.size() == 2 && !view->result &&
                !mathematical::matchComputation(*view).reduction &&
                view->accesses.size() == 1 && view->accesses[0].input == 0,
            "ordered multi-state facts lost");
    for (unsigned i = 0; i < 2; ++i)
      require(view->seeds[i].input == i + 1 &&
                  view->seeds[i].formal ==
                      c.helper->getRegion(0).front().getArgument(i) &&
                  view->seeds[i].actual == c.operation->getOperand(i + 1),
              "state input/formal/actual partition changed");
    require(view->results[0] == view->seeds[1].formal &&
                view->results[1] == view->accesses[0].value,
            "state transition result identity changed");
  });
  cases.run("shared indexed lane facts and exact lookup identity", [&] {
    auto module = parseSourceString<ModuleOp>(indexedCollect, &context);
    require(bool(module), "indexed collect refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    auto &body = c.helper->getRegion(0).front();
    Value lookup = body.front().getResult(0);
    require(
        view && mathematical::matchComputation(*view).elementwise &&
            view->accesses.size() == 1 &&
            view->accesses[0].kind == finite::AccessKind::Indexed &&
            view->accesses[0].value == lookup &&
            mathematical::matchComputation(*view).elementwise->lookups.lookup(
                lookup) == view->captures[0].formal &&
            view->captures[1].actual == c.operation->getOperand(1),
        "lane selection lost analyzed access or uniform capture");
    llvm::DenseMap<Value, Value> indices{
        {body.getArgument(0), body.getArgument(1)}};
    auto lanes = mathematical::matchLaneFormula(body, view->result.getType(),
                                                {}, indices);
    require(lanes && lanes->lookups.lookup(lookup) == body.getArgument(1),
            "shared formula API disagrees with computation access");
    indices[body.getArgument(0)] = body.getArgument(2);
    require(!mathematical::matchLaneFormula(body, view->result.getType(), {},
                                            indices),
            "unrelated index/container mapping granted a lane lookup");
    body.front().setAttr("data.in_bounds", UnitAttr::get(&context));
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).elementwise &&
                view->accesses.empty(),
            "forged lookup metadata acquired a lane realization");
  });
  cases.run("reduction extent premises must be shared with the reader", [&] {
    auto module = parseSourceString<ModuleOp>(capturedReduction, &context);
    require(bool(module), "captured reduction refused");
    auto c = computation(*module);
    require(finite::provesEqualExtent(c.operation->getOperand(0), 0,
                                      c.operation->getOperand(2), 0),
            "control lacks occurrence-only extent evidence");
    auto view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).reduction &&
                view->accesses.empty(),
            "occurrence-only extent fact escaped into reduction selection");
    auto premises = c.helper->getAttrOfType<ArrayAttr>("data.preconditions");
    SmallVector<Attribute> shared(premises.begin(), premises.end());
    shared.push_back(data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
    c.helper->setAttr("data.preconditions", ArrayAttr::get(&context, shared));
    require(succeeded(mlir::verify(*module)),
            "shared helper premise is not admitted");
    view = finite::analyzeComputation(c);
    require(
        view && mathematical::matchComputation(*view).reduction &&
            mathematical::matchComputation(*view).reduction->combine ==
                MathematicalIdentity::FieldAdd &&
            !mathematical::matchComputation(*view).reduction->termIdentity &&
            mathematical::matchComputation(*view).reduction->inputs ==
                SmallVector<unsigned>({2}) &&
            view->accesses.size() == 1 && view->accesses[0].input == 2,
        "shared helper premise did not restore captured-container reduction");
  });
  cases.run(
      "nested contraction composes exact free and reduced environments", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
        require(bool(module) && succeeded(verify(*module)),
                "nested fixture refused");
        auto c = computation(*module);
        auto view = finite::analyzeComputation(c);
        require(bool(view), "nested structure missing");
        auto equation = mathematical::matchNestedContraction(*view);
        require(
            equation && equation->matrix == 0 && equation->vector == 1 &&
                equation->seed.input == 5 &&
                equation->witness.freeAxes.size() == 1 &&
                equation->witness.reducedAxes.size() == 3 &&
                equation->witness.accesses.size() == 2 &&
                equation->witness.admission.size() == 4 &&
                equation->witness.seed.actual == view->captures[5].formal &&
                equation->witness.yielded == view->nested[0].result &&
                equation->witness.freeAxes[0] == view->axes[0].identity &&
                equation->witness.reducedAxes[0] ==
                    view->nested[0].axes[0].identity,
            "nested match lost seed, ignored admission, or occurrence axes");
        auto &child = view->nested.front();
        for (const auto &mapping : equation->witness.environment)
          require(child.environment.inputPosition(mapping.formal) &&
                      mapping.source ==
                          child.environment.actualInput(
                              *child.environment.inputPosition(mapping.formal)),
                  "nested witness substituted a different capture");
        // Both scalar operations may commute without changing the composed
        // access environment, seed, or conditional admission.
        for (Operation *op : child.payload) {
          Value left = op->getOperand(0), right = op->getOperand(1);
          op->setOperands({right, left});
        }
        view = finite::analyzeComputation(c);
        auto equivalent = mathematical::matchNestedContraction(*view);
        require(equivalent && equivalent->matrix == equation->matrix &&
                    equivalent->vector == equation->vector &&
                    equivalent->seed.input == equation->seed.input,
                "equivalent nested equation changed environment roles");
        // An unrelated, same-typed matrix capture does not inherit outer axis
        // identity merely because both matrices have the same nominal type.
        view->nested[0].occurrence->setOperand(0, view->captures[3].formal);
        view = finite::analyzeComputation(c);
        require(view && !mathematical::matchNestedContraction(*view),
                "unrelated matrix capture acquired the outer free axis");
      });
  for (bool columns : {false, true})
    for (unsigned form = 0; form < 5; ++form)
      cases.run(
          std::string(columns ? "column" : "row") + " nested neutral form " +
              std::to_string(form),
          [&] {
            auto text = fixture("nested-matrix");
            if (columns) {
              auto at = text.find("domain_matrix_row");
              text.replace(at, StringRef("domain_matrix_row").size(),
                           "domain_matrix_column");
              at = text.find("axis=0:i64");
              text.replace(at, StringRef("axis=0:i64").size(), "axis=1:i64");
            }
            auto source = parseSourceString<ModuleOp>(text, &context);
            auto c = computation(*source);
            auto view = finite::analyzeComputation(c);
            require(view && view->nested.size() == 1,
                    "nested control unavailable");
            if (form) {
              auto *helper =
                  form < 3 ? view->nested[0].computation.helper : c.helper;
              neutralResult(helper->getRegion(0).front(), form % 2 == 0,
                            form >= 3);
            }
            require(succeeded(verify(*source)), "neutral source not admitted");
            view = finite::analyzeComputation(c);
            auto match = mathematical::matchNestedContraction(*view);
            require(match && match->matrix == 0 && match->vector == 1 &&
                        match->seed.input == 5 &&
                        match->axis == unsigned(columns) &&
                        match->witness.admission.size() == 4,
                    "neutral spelling lost composed equation or admission");
            auto candidate = clone(*source);
            StringRef target =
                columns ? "matrix.transpose_mul_vector" : "matrix.mul_vector";
            require(succeeded(nested::rewriteFiniteCollections(*candidate)) &&
                        hasKernel(*candidate, target) &&
                        succeeded(nested::verifyFiniteCollections(*source,
                                                                  *candidate)),
                    "neutral equation did not produce independently checked "
                    "matvec");
            for (unsigned change = 0; change < 3; ++change) {
              auto drift = clone(*candidate);
              Operation *changed = nullptr;
              StringRef contract = change == 0   ? "vector.fill"
                                   : change == 1 ? target
                                                 : "control.require";
              drift->walk([&](Operation *op) {
                if (op->getName().getStringRef() ==
                    protocol::boundOperationName(contract))
                  changed = op;
              });
              require(changed, "candidate drift target missing");
              if (change < 2)
                changed->setOperand(
                    change == 0 ? 0 : 1,
                    changed->getBlock()->getArgument(change == 0 ? 6 : 4));
              else
                changed->erase();
              require(succeeded(verify(*drift)),
                      "drift control is not admitted");
              ScopedDiagnosticHandler quiet(
                  &context, [](Diagnostic &) { return success(); });
              require(failed(nested::verifyFiniteCollections(*source, *drift)),
                      "independent reader accepted changed seed, capture, or "
                      "admission");
            }
          });
  for (bool pinned : {false, true})
    cases.run(
        pinned ? "neutral nested pin retains ordered fallback"
               : "neutral nested dead work retains ordered fallback",
        [&] {
          auto source =
              parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
          auto view = finite::analyzeComputation(computation(*source));
          auto &step = view->nested[0].computation.helper->getRegion(0).front();
          auto *neutral = neutralResult(step, false);
          if (pinned) {
            auto binding = SymbolTable::lookupNearestSymbolFrom(
                neutral, neutral->getAttrOfType<FlatSymbolRefAttr>("binding"));
            binding->setAttr("implementation",
                             StringAttr::get(&context, "arkworks/field.add"));
          } else {
            OpBuilder builder(&step.back());
            auto *dead = builder.clone(*neutral);
            dead->setAttr("site", builder.getStringAttr("dead_neutral"));
          }
          require(succeeded(verify(*source)), "fallback control not admitted");
          view = finite::analyzeComputation(computation(*source));
          auto selection = mathematical::selectNestedContraction(*view);
          require(!selection.recipe && bool(selection.equation) == pinned,
                  "dead body or pin permitted nested replacement");
          auto candidate = clone(*source);
          require(
              succeeded(nested::rewriteFiniteCollections(*candidate)) &&
                  !hasKernel(*candidate, "matrix.mul_vector") &&
                  succeeded(
                      nested::verifyFiniteCollections(*source, *candidate)) &&
                  succeeded(finite::realizeLocals(*candidate)) &&
                  succeeded(finite::verifyRealizations(*source, *candidate)) &&
                  hasOrderedLoop(*candidate),
              "neutral unsupported payload lost checked ordered fallback");
        });
  for (auto name : {"sum", "bilinear", "nested-matrix"})
    cases.run(std::string(name) + " cumulative optional selection work", [&] {
      auto source = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(source) && succeeded(verify(*source)),
              "budget source not admitted");
      auto c = computation(*source);
      bool nested = StringRef(name) == "nested-matrix";
      auto select = [&](finite::Computation subject,
                        finite::ComputationWork &work) {
        if (!nested)
          return mathematical::selectComputation(subject, {}, work).kind !=
                 mathematical::RealizationKind::Ordered;
        auto view = finite::analyzeComputation(subject, work);
        return view &&
               mathematical::selectNestedContraction(*view, work).recipe;
      };
      finite::ComputationWork measured;
      measured.equations = 1000;
      require(select(c, measured), "small control budget did not select");
      uint64_t cost = 1000 - measured.equations;
      require(cost > 1 && cost < 1000, "equation matching was not charged");
      mathematical::RealizationWork shared;
      shared.matching.equations = cost;
      require(select(c, shared.matching) && !shared.matching.equations,
              "exact first-subject allowance was not consumed");
      auto second = clone(*source);
      require(!select(computation(*second), shared.matching) &&
                  !shared.matching.equations,
              "second subject replenished optional selection allowance");
      // Exercise stage orchestration with the same exhausted context. Neither
      // nested selection nor ordinary realization may reset optional work.
      auto candidate = clone(*source);
      if (nested)
        require(
            succeeded(
                nested::rewriteFiniteCollections(*candidate, {}, &shared)) &&
                succeeded(nested::verifyFiniteCollections(*source, *candidate)),
            "exhausted nested selection failed identity checking");
      require(succeeded(finite::realizeLocals(*candidate, {}, &shared)) &&
                  succeeded(finite::verifyRealizations(*source, *candidate)) &&
                  hasOrderedLoop(*candidate) && shared.helperOperations &&
                  shared.helperSlots && !shared.matching.equations &&
                  !hasKernel(*candidate, "matrix.mul_vector") &&
                  !hasKernel(*candidate, "matrix.bilinear"),
              "optional exhaustion consumed ordered reserve or prevented "
              "checked fallback");
      finite::ComputationWork shortWork;
      shortWork.equations = cost - 1;
      require(!select(c, shortWork),
              "partial optional selection escaped exhaustion");
    });
  cases.run("extent queries share remaining evidence across subjects", [&] {
    auto source = parseSourceString<ModuleOp>(capturedReduction, &context);
    auto c = computation(*source);
    auto premises = c.helper->getAttrOfType<ArrayAttr>("data.preconditions");
    SmallVector<Attribute> shared(premises.begin(), premises.end());
    shared.push_back(data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
    c.helper->setAttr("data.preconditions", ArrayAttr::get(&context, shared));
    require(succeeded(verify(*source)), "extent control not admitted");
    finite::ComputationWork measured;
    measured.evidence = 1000;
    auto view = finite::analyzeComputation(c, measured);
    require(view && view->accesses.size() == 1,
            "shared extent fact unavailable");
    uint64_t cost = 1000 - measured.evidence;
    require(cost && cost < 1000, "extent queries bypassed shared allowance");
    finite::ComputationWork work;
    work.evidence = cost;
    view = finite::analyzeComputation(c, work);
    require(view && view->accesses.size() == 1 && !work.evidence,
            "first extent query did not consume exact allowance");
    auto second = clone(*source);
    view = finite::analyzeComputation(computation(*second), work);
    require(view && view->accesses.empty() &&
                !mathematical::matchComputation(*view, work).reduction &&
                !work.evidence,
            "later extent query replenished optional evidence");
  });
  cases.run(
      "nested pointwise extension retains independently checked fallback", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
        auto c = computation(*module);
        auto &body = c.helper->getRegion(0).front();
        OpBuilder builder(&body.back());
        OperationState state(body.back().getLoc(), "algebra.exec.field_add");
        state.addOperands({body.back().getOperand(0), body.getArgument(6)});
        state.addTypes(body.back().getOperand(0).getType());
        state.addAttribute("binding", FlatSymbolRefAttr::get(&context, "add"));
        state.addAttribute("parameters", builder.getArrayAttr({}));
        state.addAttribute("site", builder.getStringAttr("bias"));
        auto *bias = builder.create(state);
        body.back().setOperand(0, bias->getResult(0));
        require(succeeded(verify(*module)),
                "pointwise composition not admitted");
        auto view = finite::analyzeComputation(c);
        require(
            view && view->nested.size() == 1 && view->payload.size() == 2 &&
                !mathematical::matchNestedContraction(*view),
            "unsupported outer equation erased payload or invented a match");
        OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
        require(succeeded(finite::realizeLocals(*candidate)) &&
                    succeeded(finite::verifyRealizations(*module, *candidate)),
                "composed outer payload lost independently checked fallback");
      });
  cases.run("seeded contraction witness retains exact selected axes", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("matrix-row"), &context);
    auto view = finite::analyzeComputation(computation(*module));
    auto equation = mathematical::matchComputation(*view).reduction;
    require(equation && equation->witness.seed.input == view->seeds[0].input &&
                equation->witness.seed.formal == equation->accumulator &&
                equation->witness.yielded == view->result &&
                equation->witness.reducedAxes.size() == view->axes.size() &&
                equation->accesses[0].container == view->captures[0].formal &&
                equation->accesses[0].axes.size() == 1 &&
                view->axes[equation->accesses[0].axes[0]].containerAxis == 1 &&
                equation->accesses[0].indices.size() == 1,
            "row contraction witness invented axes, access, or seed identity");
  });
  return cases.result();
}
