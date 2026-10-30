#include "../lib/Transforms/ComputationEquations.h"
#include "../lib/Transforms/ComputationSelection.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/IR.h"

#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Finite.h"

#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::scopedComputation;
namespace sf = zkc::test::scopedFinite;
namespace {
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
std::string printed(Operation *operation) {
  std::string text;
  llvm::raw_string_ostream stream(text);
  operation->print(stream);
  return text;
}
OwningOpRef<ModuleOp> numericalAdditionFixture(MLIRContext &context,
                                               StringRef name) {
  auto module = parseSourceString<ModuleOp>(fixture(name), &context);
  require(bool(module), "missing numerical source");
  numericalAddition(*module);
  return module;
}
OwnedComputation computation(ModuleOp module) {
  return readComputation(module);
}
OwningOpRef<ModuleOp> clone(ModuleOp module) { return sf::clone(module); }
bool hasKernel(ModuleOp module, StringRef contract) {
  return !sf::applications(module, contract).empty();
}
bool hasOrderedLoop(ModuleOp module) { return sf::hasLoop(module); }
Operation *neutralResult(func::FuncOp helper, bool multiply,
                         bool left = false) {
  auto end = returned(helper);
  Value result = end.getValues().front();
  auto *constant = appendApply(helper, "constant", {}, result.getType(),
                               "neutral_constant", {multiply ? "1" : "0"});
  Value identity = payload(constant).front();
  auto *wrapped = appendApply(helper, multiply ? "mul" : "add",
                              left ? ValueRange{identity, result}
                                   : ValueRange{result, identity},
                              result.getType(), "neutral_result");
  end->setOperand(0, payload(wrapped).front());
  return wrapped;
}
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
  // Include omitted defaults and every combination of the three policy bits.
  for (unsigned callPolicy = 0; callPolicy < 9; ++callPolicy)
    cases.run(
        "reused scalar view and policy " + std::to_string(callPolicy),
        [&, callPolicy] {
          auto module = numericalAdditionFixture(context, "sum");
          require(bool(module), "numerical callback did not parse");
          auto c = computation(*module);
          auto *call = &c.helper->getRegion(0).front().front();
          OpBuilder builder(&context);
          if (!callPolicy)
            call->removeAttr("policy");
          else
            call->setAttr("policy", builder.getBoolArrayAttr(
                                        {((callPolicy - 1) & 2) != 0,
                                         ((callPolicy - 1) & 1) != 0,
                                         ((callPolicy - 1) & 4) != 0}));
          require(succeeded(verify(*module)), "numerical policy not admitted");
          auto before = printed(*module);
          auto view = finite::analyzeComputation(c);
          require(view && view->numericalBody &&
                      isa<func::FuncOp>(view->callbackBody->getParentOp()),
                  "standard structural view missing");
          finite::ComputationWork work;
          work.structural = work.evidence = 0;
          auto enabled = mathematical::selectComputation(*view, {}, work);
          auto disabled =
              mathematical::selectComputation(*view, {false, true}, work);
          bool allowed = !callPolicy || ((callPolicy - 1) & 2) != 0;
          require(
              enabled.equations.reduction && disabled.equations.reduction &&
                  enabled.kind ==
                      (allowed ? mathematical::RealizationKind::Reduction
                               : mathematical::RealizationKind::Ordered) &&
                  enabled.outcome() ==
                      (allowed ? OptimizationStatus::Succeeded
                               : OptimizationStatus::ReplacementRestricted) &&
                  disabled.kind == mathematical::RealizationKind::Ordered &&
                  disabled.outcome() == OptimizationStatus::PolicyDisabled &&
                  enabled.view->numericalBody == view->numericalBody &&
                  disabled.view->callbackBody == view->callbackBody &&
                  enabled.view->numericalCalls().front() == call &&
                  !work.structural && !work.evidence,
              "reuse lost equations, policy separation, or shared SSA "
              "ownership");
          auto body = view->callbackBody;
          view.reset();
          require(enabled.view->payload.front()->getBlock() == body &&
                      disabled.view->result == enabled.view->result &&
                      printed(*module) == before,
                  "selection lost owned storage or mutated source IR");
        });
  cases.run("reused selection charges each recognition without a cache", [&] {
    auto module = numericalAdditionFixture(context, "sum");
    require(bool(module), "numerical callback did not parse");
    auto c = computation(*module);
    c.helper->getRegion(0).front().front().removeAttr("policy");
    require(succeeded(verify(*module)), "selection control not admitted");
    auto before = printed(*module);
    auto view = finite::analyzeComputation(c);
    require(bool(view), "structural view missing");
    finite::ComputationWork measured;
    measured.structural = measured.evidence = 0;
    measured.equations = 1000;
    auto selected = mathematical::selectComputation(*view, {}, measured);
    uint64_t cost = 1000 - measured.equations;
    require(selected.kind == mathematical::RealizationKind::Reduction &&
                cost > 1 && cost < 1000,
            "reused recognition/selection was not charged");
    finite::ComputationWork fresh;
    fresh.equations = 1000;
    auto convenience = mathematical::selectComputation(c, {}, fresh);
    require(
        convenience.kind == selected.kind && convenience.equations.reduction &&
            fresh.equations == measured.equations &&
            fresh.structural < finite::ComputationWork{}.structural,
        "convenience selection did not delegate with the same equation work");
    finite::ComputationWork exact;
    exact.structural = exact.evidence = 0;
    exact.equations = cost;
    require(mathematical::selectComputation(*view, {}, exact).kind ==
                    mathematical::RealizationKind::Reduction &&
                !exact.equations,
            "reused view did not consume its exact selection allowance");
    auto exhausted = mathematical::selectComputation(*view, {}, exact);
    require(exhausted.kind == mathematical::RealizationKind::Ordered &&
                exhausted.outcome() == OptimizationStatus::Capacity &&
                exhausted.diagnostic.outcome.capacity &&
                exhausted.diagnostic.outcome.capacity->owner ==
                    WorkOwner::Equations &&
                !exact.structural && !exact.evidence,
            "second reuse replenished work or cached a successful selection");
    exact.equations = cost;
    auto moved = mathematical::selectComputation(std::move(*view), {}, exact);
    view.reset();
    require(moved.kind == mathematical::RealizationKind::Reduction &&
                moved.view->payload.front()->getBlock() ==
                    moved.view->callbackBody &&
                !exact.equations && printed(*module) == before,
            "moving a view lost storage, changed work, or mutated the source");
  });
  cases.run(
      "shared numerical unit retains distinct call policies and axes", [&] {
        auto module = numericalAdditionFixture(context, "sum");
        require(bool(module), "numerical callback did not parse");
        auto first = computation(*module);
        OpBuilder builder(first.helper);
        auto otherHelper = cast<func::FuncOp>(builder.clone(*first.helper));
        otherHelper.setSymName("other_step");
        otherHelper->setAttr(
            "runtime.origin",
            builder.getArrayAttr({builder.getStringAttr("other_step"),
                                  builder.getArrayAttr({})}));
        auto &otherBody = otherHelper.getBody().front();
        auto *otherCall = &otherBody.front();
        otherCall->setAttr("policy",
                           builder.getBoolArrayAttr({true, false, false}));
        otherCall->setOperands({otherBody.getArgument(0),
                                otherBody.getArgument(2),
                                otherBody.getArgument(1)});
        auto firstWork = first.operation->getParentOfType<func::FuncOp>();
        auto otherWork = cast<func::FuncOp>(builder.clone(*firstWork));
        otherWork.setSymName("other_work");
        otherWork->setAttr(
            "runtime.origin",
            builder.getArrayAttr({builder.getStringAttr("other_work"),
                                  builder.getArrayAttr({})}));
        auto *other = &otherWork.front().front();
        other->setAttr("step",
                       FlatSymbolRefAttr::get(otherHelper.getSymNameAttr()));
        require(succeeded(verify(*module)), "second callback not admitted");
        first = readComputation(*module, first.operation);
        auto second = readComputation(*module, other);
        auto before = printed(*module);
        auto a = finite::analyzeComputation(first);
        auto b = finite::analyzeComputation(second);
        require(a && b &&
                    a->numericalCalls().front() !=
                        b->numericalCalls().front() &&
                    b->numericalCalls().front() == otherCall &&
                    a->sourceOperation(a->payload.front()) ==
                        b->sourceOperation(b->payload.front()) &&
                    a->axes[0].identity != b->axes[0].identity &&
                    b->payload.front()->getOperand(0) == b->items[0].formal &&
                    b->payload.front()->getOperand(1) == b->seeds[0].formal,
                "shared source merged call occurrences or permuted same-type "
                "arguments");
        finite::ComputationWork work;
        auto disabled = mathematical::selectComputation(*a, {}, work);
        auto enabled = mathematical::selectComputation(*b, {}, work);
        require(disabled.equations.reduction && enabled.equations.reduction &&
                    disabled.outcome() ==
                        OptimizationStatus::ReplacementRestricted &&
                    enabled.kind == mathematical::RealizationKind::Reduction &&
                    printed(*module) == before,
                "one call policy escaped into another occurrence or changed "
                "its source");
      });
  cases.run("reused view retains malformed call policy restrictions", [&] {
    auto module = numericalAdditionFixture(context, "sum");
    require(bool(module) && succeeded(verify(*module)),
            "numerical callback not admitted");
    auto c = computation(*module);
    auto *call = &c.helper->getRegion(0).front().front();
    OpBuilder builder(&context);
    SmallVector<Attribute> policies{
        builder.getArrayAttr({}),
        builder.getArrayAttr({builder.getBoolAttr(true)}),
        builder.getBoolArrayAttr({true, false}),
        builder.getBoolArrayAttr({true, false, false, false}),
        builder.getArrayAttr({builder.getBoolAttr(true),
                              builder.getStringAttr("invalid"),
                              builder.getBoolAttr(false)}),
        builder.getArrayAttr({builder.getBoolAttr(true),
                              builder.getBoolAttr(false),
                              builder.getStringAttr("invalid")}),
        builder.getArrayAttr({builder.getStringAttr("invalid"),
                              builder.getBoolAttr(false),
                              builder.getBoolAttr(false)})};
    // Deliberate post-admission mutations probe conservative selection only.
    // Each mutation invalidates the previous borrowed structural view.
    for (Attribute policy : policies) {
      call->setAttr("policy", policy);
      require(call->getAttr("policy") == policy,
              "malformed policy mutation did not reach the source");
      auto before = printed(*module);
      auto view = finite::analyzeComputation(c);
      require(bool(view), "malformed policy erased structural facts");
      finite::ComputationWork work;
      auto selection = mathematical::selectComputation(*view, {}, work);
      require(selection.equations.reduction &&
                  selection.kind == mathematical::RealizationKind::Ordered &&
                  selection.outcome() ==
                      OptimizationStatus::ReplacementRestricted &&
                  selection.view->numericalCalls().front() == call &&
                  printed(*module) == before,
              "malformed policy gained replacement permission through reuse");
    }
  });
  for (bool pinned : {false, true})
    cases.run(
        pinned ? "reused nested numerical view preserves pins"
               : "disabled inner call restricts enabled nested selection",
        [&, pinned] {
          auto module = numericalAdditionFixture(context, "nested-matrix");
          require(bool(module), "nested numerical callback did not parse");
          if (pinned) {
            module->walk(
                [&](exec::ComputeOp call) { call->removeAttr("policy"); });
            module->walk([&](runtime::BindingOp binding) {
              if (binding.getSymName() == "mul")
                binding->setAttr(
                    "implementation",
                    StringAttr::get(&context, "arkworks/field.mul"));
            });
          }
          require(succeeded(verify(*module)),
                  "nested policy/pin control not admitted");
          auto before = printed(*module);
          auto owner = computation(*module);
          auto view = finite::analyzeComputation(owner);
          require(view && view->nested.size() == 1 &&
                      view->nested.front().numericalBody &&
                      view->nested.front().numericalCalls().size() == 1,
                  "nested owned view or original numerical occurrence missing");
          finite::ComputationWork work;
          auto inner =
              mathematical::selectComputation(view->nested.front(), {}, work);
          auto outer = mathematical::selectNestedContraction(*view, work);
          require(
              inner.equations.reduction && outer.equation && !outer.recipe &&
                  inner.outcome() ==
                      OptimizationStatus::ReplacementRestricted &&
                  outer.outcome() ==
                      OptimizationStatus::ReplacementRestricted &&
                  (!pinned ||
                   !finite::replaceable(view->nested.front().sourceOperation(
                       view->nested.front().payload.front()))) &&
                  printed(*module) == before,
              "enabled outer strategy bypassed an inner call policy or pin");
          if (!pinned) {
            auto fallback = sf::prepare(*module);
            require(!hasKernel(*fallback, "matrix.mul_vector") &&
                        succeeded(sf::compare(*module, *fallback)),
                    "disabled inner call lost independently checked fallback");
            auto permissive = clone(*module);
            permissive->walk(
                [&](exec::ComputeOp call) { call->removeAttr("policy"); });
            auto forbidden = sf::prepare(*permissive);
            require(hasKernel(*forbidden, "matrix.mul_vector"),
                    "permissive nested control did not optimize");
            // The candidate contains the selected algorithm and independently
            // transformed helper definitions. The reader must use the original
            // source policy when checking the actual root invocation.
            require(failed(sf::compare(*module, *forbidden)) &&
                        printed(*module) == before,
                    "independent reader accepted disabled inner replacement");
          }
        });
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
      auto *combine = view->sourceOperation(plan->combiner);
      Value left = combine->getOperand(1), right = combine->getOperand(2);
      combine->setOperand(1, right);
      combine->setOperand(2, left);
      require(succeeded(verify(*module)), "commuted source refused");
      c = computation(*module);
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
      // Unused total arithmetic remains visible in the observation. The
      // scalar comparison may justify its removal under sufficient capacity.
      duplicateInvocation(combine, cast<func::FuncOp>(c.helper),
                          "unused_combine");
      require(succeeded(verify(*module)), "unused source operation refused");
      c = computation(*module);
      view = finite::analyzeComputation(c);
      require(view && mathematical::matchComputation(*view).reduction &&
                  view->payload.size() >= 2 &&
                  view->sourceOperation(view->payload.front()) !=
                      view->sourceOperation(view->payload.back()),
              "unused scalar work disappeared from the structural view");
      auto candidate = sf::prepare(*module);
      require(succeeded(sf::compare(*module, *candidate)),
              "unused scalar arithmetic lost independently checked execution");
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
    c.helper->walk([&](exec::ApplyOp op) {
      auto *facet = finite::semantics(op);
      if (!facet || !facet->law.commutative)
        return;
      Value left = op.getInputs()[0], right = op.getInputs()[1];
      op->setOperand(1, right);
      op->setOperand(2, left);
    });
    c = computation(*module);
    view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).bilinear,
            "bilinear operand variation refused");
    auto lookup = sf::application(c.helper, "matrix.get");
    Value row = lookup.getInputs()[1], column = lookup.getInputs()[2];
    lookup->setOperand(2, column);
    lookup->setOperand(3, row);
    c = computation(*module);
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).bilinear &&
                view->accesses.size() == 2,
            "transposed access acquired the same contraction");
  });
  cases.run("scoped collect observes unused scalar instructions", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(module), "collect fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).elementwise,
            "collect formula missing");
    auto helper = cast<func::FuncOp>(c.helper);
    duplicateInvocation(&helper.front().front(), helper, "unused_lane");
    require(succeeded(verify(*module)), "unused lane source refused");
    c = computation(*module);
    view = finite::analyzeComputation(c);
    require(view && mathematical::matchComputation(*view).elementwise &&
                view->payload.size() == 2,
            "unused scalar lane observation disappeared");
    auto candidate = sf::prepare(*module);
    require(succeeded(sf::compare(*module, *candidate)),
            "unused scalar lane work lost checked execution");
  });
  for (auto name : {"coordinates-row", "coordinates-column"})
    cases.run(std::string(name) + " retains checked opaque arithmetic", [&] {
      auto source = parseSourceString<ModuleOp>(fixture(name), &context);
      auto owner = computation(*source);
      auto view = finite::analyzeComputation(owner);
      require(view && view->axes.size() == 2 && view->payload.size() == 2,
              "opaque coordinate view unavailable");
      finite::ComputationWork work;
      auto selected = mathematical::selectComputation(*view, {}, work);
      require(selected.kind == mathematical::RealizationKind::Ordered &&
                  !selected.equations.elementwise,
              "checked index arithmetic acquired a total lane equation");
      auto candidate = sf::prepare(*source);
      require(succeeded(sf::compare(*source, *candidate)),
              "opaque arithmetic lost independently checked execution");
      for (StringRef contract : {"index.mul", "index.add"}) {
        auto original =
            sf::application(cast<func::FuncOp>(owner.helper), contract);
        auto operations =
            sf::executionApplications(*candidate, "work", contract);
        require(llvm::count_if(operations,
                               [&](exec::ApplyOp op) {
                                 return op.getLoc() == original.getLoc();
                               }) == 1,
                "opaque callback arithmetic lost its source occurrence");
      }
    });
  cases.run(
      "unused checked arithmetic cannot disappear through a scalar view", [&] {
        auto source = parseSourceString<ModuleOp>(fixture("sum"), &context);
        auto c = computation(*source);
        auto helper = cast<func::FuncOp>(c.helper);
        OpBuilder builder(helper);
        runtime::BindingOp::create(builder, helper.getLoc(), "index_constant",
                                   "index.constant", builder.getArrayAttr({}),
                                   "");
        runtime::BindingOp::create(builder, helper.getLoc(), "index_add",
                                   "index.add", builder.getArrayAttr({}), "");
        Type index = IntegerType::get(&context, 64, IntegerType::Unsigned);
        auto *maximum = appendApply(helper, "index_constant", {}, index,
                                    "maximum", {"18446744073709551615"});
        auto *one =
            appendApply(helper, "index_constant", {}, index, "one", {"1"});
        appendApply(helper, "index_add",
                    {payload(maximum).front(), payload(one).front()}, index,
                    "unused_overflow");
        require(succeeded(verify(*source)), "unused checked source refused");
        c = computation(*source);
        auto view = finite::analyzeComputation(c);
        require(view && view->payload.size() == 4 &&
                    !mathematical::matchComputation(*view).reduction,
                "unused overflow acquired permission for a bulk reduction");
        auto candidate = sf::prepare(*source);
        require(succeeded(sf::compare(*source, *candidate)) &&
                    hasOrderedLoop(*candidate),
                "unused checked arithmetic lost fallback");
        auto changed = sf::application(*candidate, "index.add");
        omit(changed, changed.getInputs().front());
        require(succeeded(verify(*candidate)),
                "omitted checked candidate malformed");
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(failed(sf::compare(*source, *candidate)),
                "independent comparison erased an unused checked failure");
      });
  cases.run("indexed dot and indexed unary reductions", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("indexed-zip-dot"), &context);
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
    auto add = sf::application(c.helper, "field.add");
    auto multiply = sf::application(c.helper, "field.mul");
    auto reads = sf::applications(c.helper, "vector.get");
    Value first = payload(reads[0]).front();
    add->setOperand(1, first);
    omit(multiply, first);
    omit(reads[1], first);
    require(succeeded(verify(*module)), "indexed unary source refused");
    c = computation(*module);
    view = finite::analyzeComputation(c);
    require(bool(view), "changed indexed computation view missing");
    plan = mathematical::matchComputation(*view).reduction;
    require(plan && plan->combine == MathematicalIdentity::FieldAdd &&
                !plan->termIdentity,
            "indexed sum missing");
    add.setBindingAttr(FlatSymbolRefAttr::get(&context, "mul"));
    require(succeeded(verify(*module)), "indexed product source refused");
    c = computation(*module);
    view = finite::analyzeComputation(c);
    require(bool(view), "changed indexed computation view missing");
    plan = mathematical::matchComputation(*view).reduction;
    require(plan && plan->combine == MathematicalIdentity::FieldMultiply &&
                !plan->termIdentity,
            "indexed product missing");
    // Deliberate post-admission metadata is not permission for a law.
    reads[0]->setAttr("algebra.commutative", UnitAttr::get(&context));
    view = finite::analyzeComputation(c);
    require(view && !mathematical::matchComputation(*view).reduction &&
                view->accesses.empty(),
            "user metadata acquired authority");
  });
  cases.run("indexed access must traverse the complete container", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("indexed-zip-dot"), &context);
    auto c = computation(*module);
    auto helper = cast<func::FuncOp>(c.helper);
    auto lookup = sf::application(helper, "vector.get");
    auto failed = cast<exec::DispatchOp>(lookup->getNextNode()).getStopped();
    IRRewriter rewriter(&context);
    auto *before = lookup->getBlock();
    auto *tail = rewriter.splitBlock(before, lookup->getIterator());
    OpBuilder builder(helper);
    runtime::BindingOp::create(builder, helper.getLoc(), "fixed_index",
                               "index.constant", builder.getArrayAttr({}), "");
    builder.setInsertionPointToEnd(before);
    exec::ScopedExecutionBuilder control(builder, helper);
    auto index = control.invoke(
        "exec.apply", IntegerType::get(&context, 64, IntegerType::Unsigned),
        control.getScope(),
        {builder.getNamedAttr("binding",
                              FlatSymbolRefAttr::get(&context, "fixed_index")),
         builder.getNamedAttr("parameters",
                              builder.getArrayAttr({builder.getIntegerAttr(
                                  builder.getIntegerType(64, false), 0)})),
         builder.getNamedAttr("site", builder.getStringAttr("fixed"))},
        failed);
    rewriter.mergeBlocks(tail, builder.getInsertionBlock());
    lookup->setOperand(2, index.front());
    require(succeeded(verify(*module)) && finite::semantics(lookup),
            "fixed-index control has invalid ports");
    c = computation(*module);
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
    auto zero = algebra::ConstantFieldOp::create(
        builder, body.back().getLoc(), field,
        cantFail(algebra::makeFieldLiteral(cast<algebra::FieldType>(field),
                                           llvm::APInt(1, 0))));
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
    require(view->seeds[0].input == 3 &&
                view->seeds[0].actual == c.operation->getOperand(4) &&
                view->seeds[0].formal ==
                    view->callbackValue(
                        c.helper->getRegion(0).front().getArgument(1)),
            "scoped seed lost its actual invocation or callback coordinate");
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
        for (Operation *projected : child.payload) {
          auto *op = child.sourceOperation(projected);
          Value left = op->getOperand(1), right = op->getOperand(2);
          op->setOperand(1, right);
          op->setOperand(2, left);
        }
        c = computation(*module);
        view = finite::analyzeComputation(c);
        auto equivalent = mathematical::matchNestedContraction(*view);
        require(equivalent && equivalent->matrix == equation->matrix &&
                    equivalent->vector == equation->vector &&
                    equivalent->seed.input == equation->seed.input,
                "equivalent nested equation changed environment roles");
        // An unrelated, same-typed matrix capture does not inherit outer axis
        // identity merely because both matrices have the same nominal type.
        auto *nested = view->sourceOperation(view->nested[0].occurrence);
        nested->setOperand(1, cast<func::FuncOp>(c.helper).getArgument(5));
        require(succeeded(verify(*module)), "unrelated matrix source refused");
        c = computation(*module);
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
              at = text.find("axis = 0 : i64");
              text.replace(at, StringRef("axis = 0 : i64").size(),
                           "axis = 1 : i64");
            }
            auto source = parseSourceString<ModuleOp>(text, &context);
            auto c = computation(*source);
            auto view = finite::analyzeComputation(c);
            require(view && view->nested.size() == 1,
                    "nested control unavailable");
            if (form) {
              auto *helper =
                  form < 3 ? view->nested[0].computation.helper : c.helper;
              neutralResult(cast<func::FuncOp>(helper), form % 2 == 0,
                            form >= 3);
            }
            require(succeeded(verify(*source)), "neutral source not admitted");
            c = computation(*source);
            view = finite::analyzeComputation(c);
            auto match = mathematical::matchNestedContraction(*view);
            require(match && match->matrix == 0 && match->vector == 1 &&
                        match->seed.input == 5 &&
                        match->axis == unsigned(columns) &&
                        match->witness.admission.size() == 4,
                    "neutral spelling lost composed equation or admission");
            auto candidate = sf::prepare(*source);
            StringRef target =
                columns ? "matrix.transpose_mul_vector" : "matrix.mul_vector";
            require(hasKernel(*candidate, target) &&
                        succeeded(sf::compare(*source, *candidate)),
                    "neutral equation did not produce independently checked "
                    "matvec");
            for (unsigned change = 0; change < 3; ++change) {
              auto drift = clone(*candidate);
              StringRef contract = change == 0   ? "vector.fill"
                                   : change == 1 ? target
                                                 : "control.require";
              auto operations =
                  sf::executionApplications(*drift, "work", contract);
              require(!operations.empty(), "missing executed mutation target");
              auto changed = operations.front();
              if (change < 2) {
                auto helper = changed->getParentOfType<func::FuncOp>();
                auto index = change == 0 ? 1u : 2u;
                Value original = changed->getOperand(index), alternate;
                for (Value value : helper.getArguments())
                  if (value.getType() == original.getType() &&
                      value != original)
                    alternate = value;
                require(bool(alternate),
                        "missing same-type candidate mutation");
                changed->setOperand(index, alternate);
              } else
                omit(changed);
              require(succeeded(verify(*drift)),
                      "drift control is not admitted");
              ScopedDiagnosticHandler quiet(
                  &context, [](Diagnostic &) { return success(); });
              require(failed(sf::compare(*source, *drift)),
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
          auto owner = computation(*source);
          auto view = finite::analyzeComputation(owner);
          auto step = cast<func::FuncOp>(view->nested[0].computation.helper);
          auto *neutral = neutralResult(step, false);
          if (pinned) {
            auto binding = SymbolTable::lookupNearestSymbolFrom(
                neutral, neutral->getAttrOfType<FlatSymbolRefAttr>("binding"));
            binding->setAttr("implementation",
                             StringAttr::get(&context, "arkworks/field.add"));
          } else {
            duplicateInvocation(neutral, step, "dead_neutral");
          }
          require(succeeded(verify(*source)), "fallback control not admitted");
          owner = computation(*source);
          view = finite::analyzeComputation(owner);
          auto selection = mathematical::selectNestedContraction(*view);
          require(!selection.recipe && bool(selection.equation) == pinned,
                  "dead body or pin permitted nested replacement");
          auto candidate = sf::prepare(*source);
          require(!hasKernel(*candidate, "matrix.mul_vector") &&
                      succeeded(sf::compare(*source, *candidate)) &&
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
      uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
      std::optional<CapacityCause> capacity;
      auto candidate = protocol::prepareScopedFinite(*source, shared, copies,
                                                     bytes, capacity);
      require(candidate && succeeded(sf::compare(*source, *candidate)) &&
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
    auto before = printed(*source);
    finite::ComputationWork reuse;
    reuse.structural = reuse.evidence = 0;
    auto selected = mathematical::selectComputation(*view, {}, reuse);
    require(
        selected.kind == mathematical::RealizationKind::Reduction &&
            selected.equations.reduction && !reuse.structural &&
            !reuse.evidence && printed(*source) == before,
        "selection reread evidence instead of reusing immutable access facts");
    auto second = clone(*source);
    auto secondOwner = computation(*second);
    view = finite::analyzeComputation(secondOwner, work);
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
        auto helper = cast<func::FuncOp>(c.helper);
        auto end = returned(helper);
        Value result = end.getValues().front();
        auto *bias = appendApply(helper, "add", {result, helper.getArgument(7)},
                                 result.getType(), "bias");
        end->setOperand(0, payload(bias).front());
        c = computation(*module);
        require(succeeded(verify(*module)),
                "pointwise composition not admitted");
        auto view = finite::analyzeComputation(c);
        require(
            view && view->nested.size() == 1 && view->payload.size() == 2 &&
                !mathematical::matchNestedContraction(*view),
            "unsupported outer equation erased payload or invented a match");
        auto candidate = sf::prepare(*module);
        require(succeeded(sf::compare(*module, *candidate)),
                "composed outer payload lost independently checked fallback");
      });
  cases.run("seeded contraction witness retains exact selected axes", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("matrix-row"), &context);
    auto owner = computation(*module);
    auto view = finite::analyzeComputation(owner);
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
