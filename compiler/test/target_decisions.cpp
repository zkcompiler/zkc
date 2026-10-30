#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeBindings.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Transforms/Protocol.h"
#include <tuple>
#include <type_traits>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;

static_assert(!std::is_default_constructible_v<CheckedPhysicalPlan>);
static_assert(
    !std::is_constructible_v<CheckedPhysicalPlan, const PhysicalPlan &,
                             LinearContractionStats>);
namespace {
std::string printed(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return text;
}
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void reject(Error error, StringRef code) {
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
std::string layouts(bool fixed = true) {
  auto text = scopedFixture(R"(
"runtime.binding"() {sym_name="msb",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
"runtime.binding"() {sym_name="dense",contract="poly.fold",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
)",
                            "%a:!T,%r:!F", "%a,%r", "!T,!F", "!T", R"(
%first_attempt = "exec.apply"(%scope,%a,%r) {binding=@msb,site="first",parameters=[]} : (!runtime.scope,!T,!F)->!exec.outcome<(!T)>
"exec.dispatch"(%first_attempt)[^first,^failed] : (!exec.outcome<(!T)>)->()
^first(%x:!T):
%same_attempt = "exec.apply"(%scope,%x,%r) {binding=@msb,site="same",parameters=[]} : (!runtime.scope,!T,!F)->!exec.outcome<(!T)>
"exec.dispatch"(%same_attempt)[^same,^failed] : (!exec.outcome<(!T)>)->()
^same(%q:!T):
%left_attempt = "exec.apply"(%scope,%x,%r) {binding=@dense,site="left",parameters=[]} : (!runtime.scope,!T,!F)->!exec.outcome<(!T)>
"exec.dispatch"(%left_attempt)[^left,^failed] : (!exec.outcome<(!T)>)->()
^left(%y:!T):
%right_attempt = "exec.apply"(%scope,%x,%r) {binding=@dense,site="right",parameters=[]} : (!runtime.scope,!T,!F)->!exec.outcome<(!T)>
"exec.dispatch"(%right_attempt)[^right,^failed] : (!exec.outcome<(!T)>)->()
^right(%z:!T):
%done = "exec.returned"(%q) : (!T)->!exec.outcome<(!T)>
func.return %done : !exec.outcome<(!T)>
)",
                            2);
  if (!fixed)
    text = replaceText(text, "arkworks-msb/poly.fold", "");
  return "!F = !algebra.field<\"bls12-381.fr\">\n!T = "
         "!poly.multilinear<\"bls12-381.fr\">\n" +
         text;
}
std::string contractions(bool group = false, bool escape = false) {
  auto text = scopedFixture(R"(
"runtime.binding"() {sym_name="map",contract="vector.mul",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope,!V,!A) -> !exec.outcome<(!A)>} : ()->()
"runtime.binding"() {sym_name="reduce",contract="vector.dot",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope,!V,!A) -> !exec.outcome<(!R)>} : ()->()
)",
                            "%w:!V,%f:!V,%v:!A", "%w,%f,%v", "!V,!V,!A",
                            escape ? "!A" : "!R",
                            std::string(R"(
%map_attempt = "exec.apply"(%scope,%f,%v) {binding=@map,site="map",parameters=[]} : (!runtime.scope,!V,!A)->!exec.outcome<(!A)>
"exec.dispatch"(%map_attempt)[^map,^failed] : (!exec.outcome<(!A)>)->()
^map(%mapped:!A):
%first_attempt = "exec.apply"(%scope,%w,%mapped) {binding=@reduce,site="first",parameters=[]} : (!runtime.scope,!V,!A)->!exec.outcome<(!R)>
"exec.dispatch"(%first_attempt)[^first,^failed] : (!exec.outcome<(!R)>)->()
^first(%a:!R):
%second_attempt = "exec.apply"(%scope,%w,%mapped) {binding=@reduce,site="second",parameters=[]} : (!runtime.scope,!V,!A)->!exec.outcome<(!R)>
"exec.dispatch"(%second_attempt)[^second,^failed] : (!exec.outcome<(!R)>)->()
^second(%b:!R):
)") + (escape ? R"(%done = "exec.returned"(%mapped) : (!A)->!exec.outcome<(!A)>
func.return %done : !exec.outcome<(!A)>)"
              : R"(%done = "exec.returned"(%b) : (!R)->!exec.outcome<(!R)>
func.return %done : !exec.outcome<(!R)>)"),
                            3);
  if (group) {
    text = replaceText(text, "bls12-381.fr", "ristretto255.group");
    text = replaceText(text, "vector.mul", "curve.scale_each");
    text = replaceText(text, "vector.dot", "curve.msm");
  }
  std::string scalar = group ? "ristretto255.scalar" : "bls12-381.fr";
  return "!V = !algebra.field_vector<\"" + scalar + "\">\n!A = " +
         (group ? "!algebra.group_vector<\"ristretto255.group\">"
                : "!algebra.field_vector<\"bls12-381.fr\">") +
         "\n!R = " +
         (group ? "!algebra.group<\"ristretto255.group\">"
                : "!algebra.field<\"bls12-381.fr\">") +
         "\n" + text;
}
std::string arithmetic(std::string identity = "bls12-381.fr") {
  return "!F = !algebra.field<\"" + identity + "\">\n" +
         scopedFixture(
             "\"runtime.binding\"() "
             "{sym_name=\"add\",contract=\"field.add\",arguments=[\"" +
                 identity +
                 "\"],implementation=\"\",function_type=(!runtime.scope,!F,!F)-"
                 ">!exec.outcome<(!F)>} : ()->()",
             "%a:!F,%b:!F", "%a,%b", "!F,!F", "!F", R"(
%add_attempt = "exec.apply"(%scope,%a,%b) {binding=@add,site="add",parameters=[]} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%add_attempt)[^add,^failed] : (!exec.outcome<(!F)>)->()
^add(%c:!F):
%done = "exec.returned"(%c) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
)",
             2);
}
std::string orderedCrossings() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)" + scopedFixture(R"(
"runtime.binding"() {sym_name="product",contract="poly.product_sum",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.product_sum",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !poly.multilinear<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
"runtime.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation="",function_type=(!runtime.scope, i1) -> !exec.outcome<>} : ()->()
)",
                   "%a:!T,%b:!T,%allowed:i1", "%a,%b,%allowed", "!T,!T,i1",
                   "!F", R"(
%before_attempt = "exec.apply"(%scope,%allowed) {binding=@guard,site="before",parameters=[]} : (!runtime.scope,i1)->!exec.outcome<>
"exec.dispatch"(%before_attempt)[^before,^failed] : (!exec.outcome<>)->()
^before():
%product_attempt = "exec.apply"(%scope,%a,%b) {binding=@product,site="product",parameters=[]} : (!runtime.scope,!T,!T)->!exec.outcome<(!F)>
"exec.dispatch"(%product_attempt)[^product,^failed] : (!exec.outcome<(!F)>)->()
^product(%value:!F):
%after_attempt = "exec.apply"(%scope,%allowed) {binding=@guard,site="after",parameters=[]} : (!runtime.scope,i1)->!exec.outcome<>
"exec.dispatch"(%after_attempt)[^after,^failed] : (!exec.outcome<>)->()
^after():
%done = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
)",
                   3);
}
std::string nestedLayouts(MLIRContext &context) {
  auto text = R"(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)" + scopedFixture(R"(
"runtime.binding"() {sym_name="fold",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
)",
                   "%a:!T,%r:!F,%condition:i1", "%a,%r,%condition", "!T,!F,i1",
                   "!T", R"(
%done = "exec.returned"(%a) : (!T)->!exec.outcome<(!T)>
func.return %done : !exec.outcome<(!T)>
)",
                   3);
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "nested layout source parse");
  auto work = scopedFinite::function(*module, "Work");
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, work);
  auto table = work.getArgument(1), scalar = work.getArgument(2);
  auto outer = scopedComputation::apply(control, builder, "fold", "outer",
                                        {table, scalar}, {table.getType()});
  auto selected = control.conditional(
      work.getArgument(3), {outer.front(), scalar}, {table.getType()}, "choose",
      [&](unsigned index) {
        auto region = scopedComputation::region(
            builder, work, index ? "right" : "left",
            {table.getType(), scalar.getType()}, {table.getType()});
        exec::ScopedExecutionBuilder nested(builder, region);
        auto inner = scopedComputation::apply(
            nested, builder, "fold", index ? "other" : "inner",
            region.getArguments().drop_front(), {table.getType()});
        nested.complete(inner);
        return region;
      });
  control.returned(selected);
  require(succeeded(verify(*module)), "nested layout source formation");
  return printed(*module);
}
std::string nestedContractions(MLIRContext &context, bool group) {
  auto module = parseSourceString<ModuleOp>(contractions(group), &context);
  require(bool(module), "nested contraction source parse");
  auto work = scopedFinite::function(*module, "Work");
  auto output =
      cast<exec::OutcomeType>(work.getResultTypes().front()).getPayload();
  work.getBody().dropAllReferences();
  work.getBody().getBlocks().clear();
  OpBuilder builder(&context);
  builder.setInsertionPointToEnd(work.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, work);
  auto condition = control.invoke(
      "exec.boolean", {builder.getI1Type()}, {work.getArgument(0)},
      {builder.getNamedAttr("value", builder.getBoolAttr(true)),
       builder.getNamedAttr("site", builder.getStringAttr("yes"))});
  auto values = control.conditional(
      condition.front(), work.getArguments().drop_front(), output, "branch",
      [&](unsigned index) {
        auto region = scopedComputation::region(
            builder, work, index ? "unchosen" : "chosen",
            work.getArgumentTypes().drop_front(), output);
        exec::ScopedExecutionBuilder nested(builder, region);
        if (index) {
          nested.reject("abort", "unused");
        } else {
          auto mapped = scopedComputation::apply(
              nested, builder, "map", "map",
              {region.getArgument(2), region.getArgument(3)},
              {region.getArgument(3).getType()});
          scopedComputation::apply(nested, builder, "reduce", "first",
                                   {region.getArgument(1), mapped.front()},
                                   output);
          auto second = scopedComputation::apply(
              nested, builder, "reduce", "second",
              {region.getArgument(1), mapped.front()}, output);
          nested.complete(second);
        }
        return region;
      });
  control.returned(values);
  require(succeeded(verify(*module)), "nested contraction source formation");
  return printed(*module);
}
std::string encodedSite(StringRef name) {
  return "lc_" + std::to_string(name.size()) + "_" + name.str();
}
OperationDecision &site(PhysicalPlan &plan, ModuleOp module, StringRef name) {
  auto ops = physicalPlanOperations(module);
  for (auto &decision : plan.operations)
    if (auto attr = ops[decision.operation]->getAttrOfType<StringAttr>("site"))
      if (attr.getValue() == encodedSite(name))
        return decision;
  throw std::runtime_error("missing site " + name.str());
}
func::FuncOp function(ModuleOp module) {
  return scopedFinite::function(module, "Work");
}
std::string implementation(exec::ApplyOp op) {
  return SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
             op, op.getBindingAttr())
      .getImplementation()
      .str();
}
void refusedMutation(ModuleOp module, PhysicalPlan &plan, StringRef code) {
  auto before = printed(module);
  refuses(validatePhysical(module, plan), code);
  require(before == printed(module), "validation mutated logical input");
}
class TestCandidates final : public CandidateCatalog {
public:
  bool reverseOrder = false, available = true, invalidFirst = true;
  bool withholdOrdinary = false;
  bool diagonalAvailable = true, invalidDiagonalFirst = false;
  std::string withheldDiagonalContract;
  std::vector<std::string> diagonalImplementations(
      const zkc::NativeBindingApplication &application) const override {
    if (!diagonalAvailable || application.contract == withheldDiagonalContract)
      return {};
    auto result = installedCandidates().diagonalImplementations(application);
    if (invalidDiagonalFirst) {
      auto ordinary = take(defaultNativeImplementation(application));
      result.insert(result.begin(), {"test/" + application.contract, ordinary});
    }
    return result;
  }
  Expected<std::vector<std::string>> implementations(
      const zkc::NativeBindingApplication &application) const override {
    if (withholdOrdinary)
      return std::vector<std::string>{};
    if (application.contract == "poly.fold" &&
        hasNativeArguments(application, {"bls12-381.fr"})) {
      std::vector<std::string> result{"arkworks-msb/poly.fold",
                                      "arkworks/poly.fold"};
      if (reverseOrder)
        std::reverse(result.begin(), result.end());
      return result;
    }
    return installedCandidates().implementations(application);
  }
  std::vector<zkc::NativeBindingApplication>
  conversions(mlir::Type from, mlir::Type to) const override {
    if (!available)
      return {};
    auto result = installedCandidates().conversions(from, to);
    // Synthetic rule order; it cannot install a backend or a semantic law.
    if (invalidFirst)
      result.insert(result.begin(),
                    {"table.relayout",
                     {mlir::StringAttr::get(from.getContext(), "bls12-381.fr")},
                     "test/table.relayout",
                     mlir::FunctionType::get(from.getContext(), {from}, {to})});
    return result;
  }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto refusedSelection = [&](ModuleOp module, StringRef code) {
    auto before = printed(module);
    std::vector<std::string> codes;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      for (const auto &refusal : diagnostics::refusals(diagnostic))
        codes.push_back(refusal.code);
      return success();
    });
    LinearContractionStats stats;
    stats.selectedPairs = 123;
    require(failed(lowerPhysical(module, {}, false, &stats)),
            "invalid selection input accepted");
    require(codes == std::vector<std::string>{code.str()},
            "selection refusal changed");
    require(printed(module) == before && stats.selectedPairs == 0,
            "failed public selection changed input or retained statistics");
  };
  for (StringRef source : {"module {}", "module { module {} module {} }"})
    cases.run("physical selection requires one root: " + source, [&] {
      auto module = parseSourceString<ModuleOp>(source, &context);
      require(bool(module), "wrapper fixture parse");
      refusedSelection(*module, "interactive-module-count");
    });
  cases.run("physical selection rejects a non-protocol root", [&] {
    auto module = parseSourceString<ModuleOp>("module { module {} }", &context);
    require(bool(module), "wrapper fixture parse");
    refusedSelection(*module, "interactive-module");
  });
  for (bool project : {false, true})
    cases.run(project ? "physical selection rejects participant mathematics"
                      : "physical selection rejects common mathematics",
              [&] {
                auto module = parseSourceString<ModuleOp>(layouts(), &context);
                require(bool(module), "mathematical fixture parse");
                if (project) {
                  PassManager pipeline(&context);
                  pipeline.addPass(createProjectProtocolPass(false));
                  require(succeeded(pipeline.run(*module)), "projection");
                }
                refusedSelection(*module, "interactive-module");
              });
  cases.run("physical selection admits exec and refuses reselection", [&] {
    auto module = take(executableFixture(layouts(), context));
    require(succeeded(lowerPhysical(*module)), "physical selection");
    require(succeeded(verify(*module)), "selected candidate admission");
    refusedSelection(*module, "interactive-physical-stage");
  });
  for (bool extraRoot : {false, true})
    cases.run(extraRoot ? "execution admission precedes wrapper refusal"
                        : "physical selection still admits local definitions",
              [&] {
                auto module = take(executableFixture(layouts(), context));
                function(*module)->removeAttr("runtime.origin");
                if (extraRoot)
                  module->getBody()->push_back(
                      ModuleOp::create(module->getLoc()).getOperation());
                refusedSelection(*module, "execution-source-closure");
              });
  cases.run(
      "mixed layouts, per-use crossing order and immutable checked copy", [&] {
        auto module = take(executableFixture(layouts(), context));
        auto original = printed(*module);
        auto plan = take(proposePhysical(*module));
        require(printed(*module) == original, "proposal mutated input");
        require(site(plan, *module, "first").conversions.size() == 1 &&
                    site(plan, *module, "same").conversions.empty() &&
                    site(plan, *module, "left").conversions.size() == 1 &&
                    site(plan, *module, "right").conversions.size() == 1,
                "per-use layout decisions");
        auto checked = take(validatePhysical(*module, plan));
        require(printed(*module) == original, "validator mutated input");
        plan.bindings.clear(); // Must not change the checked owned copy.
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)), "physical verification");
        std::vector<std::string> implementations;
        unsigned conversions = 0;
        for (auto op : scopedFinite::applications(function(*module))) {
          implementations.push_back(implementation(op));
          if (implementation(op) == "arkworks/table.relayout") {
            ++conversions;
            require(scopedComputation::payload(op).front().hasOneUse(),
                    "conversion result is per-use");
          }
        }
        require(implementations ==
                    std::vector<std::string>{
                        "arkworks/table.relayout", "arkworks-msb/poly.fold",
                        "arkworks-msb/poly.fold", "arkworks/table.relayout",
                        "arkworks/poly.fold", "arkworks/table.relayout",
                        "arkworks/poly.fold", "arkworks/table.relayout"},
                "independent ordered expected kernels");
        require(conversions == 4, "all four crossings execute independently");
        unsigned declarations = 0;
        for (auto op : cast<zkc::protocol_ir::ProtocolModuleOp>(
                           &module->getBody()->front())
                           .getBody()
                           .front()
                           .getOps<zkc::runtime::BindingOp>())
          declarations += op.getContract() == "table.relayout";
        require(declarations == 2,
                "two direct declarations shared by four uses");
      });
  cases.run("missing operation", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    plan.operations.pop_back();
    refusedMutation(*module, plan, "binding-plan-coverage");
  });
  cases.run("duplicate or reordered operation", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    plan.operations[1] = plan.operations[0];
    refusedMutation(*module, plan, "binding-plan-coverage");
  });
  cases.run("missing conversion", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "left").conversions.clear();
    refusedMutation(*module, plan, "binding-no-conversion");
  });
  cases.run("wrong conversion endpoint", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    auto &conversion = site(plan, *module, "left").conversions.front();
    conversion.to = conversion.from;
    refusedMutation(*module, plan, "binding-no-conversion");
  });
  cases.run("wrong conversion operand", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "left").conversions.front().operand = 1;
    refusedMutation(*module, plan, "binding-no-conversion");
  });
  cases.run(
      "forged binding with another operation and identical physical ports",
      [&] {
        auto module = take(executableFixture(arithmetic(), context));
        auto plan = take(proposePhysical(*module));
        auto forged = plan.bindings.front();
        forged.binding.name = "forged";
        forged.binding.application.contract = "field.mul";
        forged.binding.application.implementation = "arkworks/field.mul";
        forged.purpose = BindingPurpose::Contraction;
        forged.declaration.reset();
        auto add = take(resolveNativeApplication(
            plan.bindings.front().binding.application));
        auto mul = take(resolveNativeApplication(forged.binding.application));
        require(add == mul,
                "mutation must preserve the complete physical signature");
        site(plan, *module, "add").binding = plan.bindings.size();
        plan.bindings.push_back(forged);
        refusedMutation(*module, plan, "binding-operation");
      });
  cases.run("source contract mutation cannot hide behind unchanged ports", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto plan = take(proposePhysical(*module));
    plan.bindings.front().binding.application.contract = "field.mul";
    plan.bindings.front().binding.application.implementation =
        "arkworks/field.mul";
    refusedMutation(*module, plan, "binding-operation");
  });
  cases.run("nominal arguments cannot be substituted", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto plan = take(proposePhysical(*module));
    plan.bindings.front().binding.application.arguments = {
        StringAttr::get(&context, "bn254.fr")};
    refusedMutation(*module, plan, "binding-operation");
  });
  cases.run("source fixedness is recomputed", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    plan.bindings.front().fixed = false;
    refusedMutation(*module, plan, "binding-selection-conflict");
  });
  cases.run("request fixedness is recomputed", [&] {
    auto module = take(executableFixture(layouts(false), context));
    auto plan = take(proposePhysical(*module, installedCandidates(),
                                     {{"msb", "arkworks-msb/poly.fold"}}));
    plan.bindings.front().binding.application.implementation =
        "arkworks/poly.fold";
    refusedMutation(*module, plan, "binding-selection-conflict");
  });
  cases.run("stale attribute and materialization rejection", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    auto checked = take(validatePhysical(*module, plan));
    function(*module)->setAttr("changed", UnitAttr::get(&context));
    refusedMutation(*module, plan, "binding-stale-selection");
    auto before = printed(*module);
    reject(materializePhysical(*module, checked), "binding-stale-selection");
    require(printed(*module) == before, "stale application mutated input");
  });
  cases.run("erased operation and values never dereferenced", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    function(*module)->erase();
    refusedMutation(*module, plan, "binding-stale-selection");
  });
  cases.run("structurally identical replacement is stale", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    auto old = function(*module);
    auto *copy = old->clone();
    old->getBlock()->getOperations().insert(Block::iterator(old), copy);
    old->erase();
    refusedMutation(*module, plan, "binding-stale-selection");
  });
  cases.run("separate equal module is stale", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto other = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    refusedMutation(*other, plan, "binding-stale-selection");
  });
  cases.run(
      "test provider candidate order, valid installed conversion only", [&] {
        TestCandidates catalog;
        auto module = take(executableFixture(layouts(false), context));
        auto plan = take(proposePhysical(*module, catalog));
        require(plan.bindings.front().binding.application.implementation ==
                    "arkworks-msb/poly.fold",
                "alternate first candidate selected");
        for (const auto &binding : plan.bindings)
          if (binding.purpose == BindingPurpose::Conversion)
            require(binding.binding.application.implementation ==
                        "arkworks/table.relayout",
                    "synthetic rule must resolve an installed adapter");
        take(validatePhysical(*module, plan, catalog));
        catalog.reverseOrder = true;
        auto dense = take(proposePhysical(*module, catalog));
        require(dense.bindings.front().binding.application.implementation ==
                    "arkworks/poly.fold",
                "alternate ordering affects preference");
        require(dense.bindings.size() == 2,
                "dense choice needs no conversions");
        take(validatePhysical(*module, dense, catalog));
      });
  cases.run(
      "explicit pins bypass withheld automatic implementation preferences",
      [&] {
        TestCandidates catalog;
        catalog.withholdOrdinary = true;
        auto module = take(executableFixture(layouts(false), context));
        auto plan = take(proposePhysical(*module, catalog,
                                         {{"msb", "arkworks-msb/poly.fold"},
                                          {"dense", "arkworks/poly.fold"}}));
        require(plan.bindings[0].fixed && plan.bindings[1].fixed,
                "explicit selections were recorded as automatic preferences");
        take(validatePhysical(*module, plan, catalog));
        auto pinned = take(executableFixture(layouts(), context));
        refuses(
            proposePhysical(*pinned, catalog, {{"msb", "arkworks/poly.fold"}}),
            "binding-selection-conflict");
      });
  cases.run(
      "automatic implementation advances after real conversion refusal", [&] {
        TestCandidates catalog;
        catalog.available = false;
        auto module = take(executableFixture(layouts(false), context));
        auto before = printed(*module);
        auto plan = take(proposePhysical(*module, catalog));
        require(plan.bindings.front().binding.application.implementation ==
                    "arkworks/poly.fold",
                "conversion refusal discarded a later feasible implementation");
        for (const auto &decision : plan.operations)
          require(decision.conversions.empty(),
                  "dense implementation retained stale conversion decisions");
        take(validatePhysical(*module, plan, catalog));
        require(printed(*module) == before,
                "implementation retry changed the original SSA subject");
      });
  cases.run(
      "unavailable conversion fails read-only proposal and validation", [&] {
        TestCandidates catalog;
        auto module = take(executableFixture(layouts(), context));
        auto before = printed(*module);
        auto plan = take(proposePhysical(*module, catalog));
        catalog.available = false;
        refuses(proposePhysical(*module, catalog), "binding-no-conversion");
        refuses(validatePhysical(*module, plan, catalog),
                "binding-no-conversion");
        require(printed(*module) == before,
                "unavailable conversion changed input");
      });
  cases.run("unary signatures and cross-field ports grant no law", [&] {
    auto from = nativeType(
        context,
        take(parseBoundType("field:bls12-381.fr@arkworks.fr/0", true)));
    auto resident = nativeType(
        context, take(parseBoundType("field:bls12-381.fr@blst/fr", true)));
    auto negation = nativeRequest(
        context, {"field.neg", {"bls12-381.fr"}, "arkworks/field.neg"});
    negation.valueType = FunctionType::get(&context, {from}, {from});
    require(take(resolveNativeApplication(negation)) == negation.valueType,
            "unary contract signature must be independently installed");
    reject(checkDirectConversion(negation, from, from),
           "binding-no-conversion");
    negation.valueType = FunctionType::get(&context, {from}, {resident});
    reject(checkDirectConversion(negation, from, resident),
           "binding-no-conversion");
    auto to = nativeType(context,
                         take(defaultRepresentation(
                             take(parseBoundType("field:bn254.fr", false)))));
    NativeBindingApplication crossField{
        "table.relayout",
        {StringAttr::get(&context, "bls12-381.fr")},
        "arkworks/table.relayout",
        FunctionType::get(&context, {from}, {to})};
    reject(checkDirectConversion(crossField, from, to),
           "binding-no-conversion");
  });
  cases.run("Plonky3 compatible nominal operation retains default", [&] {
    auto module = take(executableFixture(arithmetic("koala-bear"), context));
    auto plan = take(proposePhysical(*module));
    require(plan.bindings.front().binding.application.implementation ==
                "plonky3/field.add",
            "independent Plonky3 expectation");
    auto checked = take(validatePhysical(*module, plan));
    accept(materializePhysical(*module, checked));
    require(succeeded(verify(*module)), "Plonky3 physical verification");
  });
  for (bool group : {false, true}) {
    cases.run(
        group ? "group contraction complete producer and consumers"
              : "field contraction complete producer and consumers",
        [&] {
          auto module = take(executableFixture(contractions(group), context));
          auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                           PhysicalPlanOptions{true}));
          require(plan.contractions.size() == 1 &&
                      plan.contractions.front().consumers.size() == 2 &&
                      plan.bindings.size() == 5,
                  "atomic shared-producer choice");
          auto checked = take(validatePhysical(*module, plan));
          require(checked.stats().selectedProducers == 1 &&
                      checked.stats().selectedPairs == 2,
                  "checked statistics");
          accept(materializePhysical(*module, checked));
          require(succeeded(verify(*module)), "diagonal physical verification");
          std::vector<std::string> expected =
              group
                  ? std::vector<std::string>{"dalek-diagonal/curve.scale_each",
                                             "dalek-diagonal/curve.msm",
                                             "dalek-diagonal/curve.msm"}
                  : std::vector<std::string>{"arkworks-diagonal/vector.mul",
                                             "arkworks-diagonal/vector.dot",
                                             "arkworks-diagonal/vector.dot"};
          std::vector<std::string> actual;
          for (auto op : scopedFinite::applications(function(*module)))
            actual.push_back(implementation(op));
          require(actual == expected,
                  "independent contraction implementation expectations");
        });
  }
  cases.run("diagonal preferences leave ordinary default order unchanged", [&] {
    for (const auto &[contract, identity, backend] :
         {std::tuple{"vector.mul", "bls12-381.fr", "arkworks"},
          std::tuple{"vector.dot", "bls12-381.fr", "arkworks"},
          std::tuple{"curve.scale_each", "ristretto255.group", "dalek"},
          std::tuple{"curve.msm", "ristretto255.group", "dalek"}}) {
      BindingApplication application{contract, {identity}, ""};
      require(
          take(installedCandidates().implementations(
              nativeRequest(context, application))) ==
              std::vector<std::string>{std::string(backend) + "/" + contract},
          "ordinary default remains dense");
      require(installedCandidates().diagonalImplementations(
                  nativeRequest(context, application)) ==
                  std::vector<std::string>{std::string(backend) + "-diagonal/" +
                                           contract},
              "separate diagonal preference resolves through Contracts");
    }
  });
  cases.run("multiple diagonal candidates have deterministic discovery", [&] {
    auto a = *installedImplementations().find("vector.mul",
                                              "arkworks-diagonal/vector.mul");
    auto b = a;
    a.identity = "test.a/0";
    b.identity = "test.b/0";
    for (bool reverse : {false, true}) {
      auto catalog = take(ImplementationCatalog::create(
          reverse ? std::vector<ImplementationDescriptor>{b, a}
                  : std::vector<ImplementationDescriptor>{a, b},
          {}));
      require(diagonalCandidates(
                  nativeRequest(context, {"vector.mul", {"bls12-381.fr"}, ""}),
                  catalog) == std::vector<std::string>{a.identity, b.identity},
              "stable candidate identities");
      require(
          diagonalCandidates(
              nativeRequest(context, {"vector.mul", {"bn254.fr"}, ""}), catalog)
              .empty(),
          "discovery preserves exact domain applicability");
    }
    // Discovery in an independent catalog cannot install code into this build.
    auto module = take(executableFixture(contractions(), context));
    refuses(proposePhysical(*module, installedCandidates(),
                            {{"map", a.identity}}, PhysicalPlanOptions{true}),
            "binding-implementation");
  });
  cases.run("nested block contractions are checked before publication", [&] {
    for (bool group : {false, true}) {
      auto module =
          take(executableFixture(nestedContractions(context, group), context));
      auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                       PhysicalPlanOptions{true}));
      require(plan.contractions.size() == 1, "nested opportunity is selected");
      auto corrupted = plan;
      corrupted.contractions.front().consumers.pop_back();
      refusedMutation(*module, corrupted, "binding-contraction");
      auto checked = take(validatePhysical(*module, plan));
      accept(materializePhysical(*module, checked));
      require(succeeded(verify(*module)), "nested plan materializes");
    }
  });
  cases.run(
      "logical roles survive absence of an installed diagonal layout", [&] {
        auto source = replaceText(contractions(), "bls12-381.fr", "koala-bear");
        auto module = take(executableFixture(source, context));
        auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                         PhysicalPlanOptions{true}));
        require(plan.contractions.empty() && plan.bindings.size() == 2,
                "unavailable target keeps ordinary installed choices");
        auto checked = take(validatePhysical(*module, plan));
        require(checked.stats().eligibleProducers == 1 &&
                    checked.stats().selectedProducers == 0,
                "semantic eligibility and target availability are distinct");
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)), "dense fallback verifies");
      });
  for (bool group : {false, true}) {
    cases.run(
        group ? "group policy skips uninstalled and dense preferences"
              : "field policy skips uninstalled and dense preferences",
        [&] {
          auto module = take(executableFixture(contractions(group), context));
          TestCandidates policy;
          policy.invalidDiagonalFirst = true;
          auto plan = take(
              proposePhysical(*module, policy, {}, PhysicalPlanOptions{true}));
          require(plan.contractions.size() == 1,
                  "installed diagonal candidate chosen");
          auto checked = take(validatePhysical(*module, plan, policy));
          accept(materializePhysical(*module, checked));
          require(succeeded(verify(*module)), "installed choice materializes");
        });
  }
  for (const auto &contract : {"vector.mul", "vector.dot"}) {
    cases.run(std::string("withheld diagonal alternative: ") + contract, [&] {
      auto module = take(executableFixture(contractions(), context));
      TestCandidates policy;
      policy.withheldDiagonalContract = contract;
      auto plan =
          take(proposePhysical(*module, policy, {}, PhysicalPlanOptions{true}));
      require(plan.contractions.empty() && plan.bindings.size() == 2,
              "withheld member prevents the whole group");
      take(validatePhysical(*module, plan, policy));
      auto selected = take(proposePhysical(*module, installedCandidates(), {},
                                           PhysicalPlanOptions{true}));
      refuses(validatePhysical(*module, selected, policy),
              "binding-implementation");
    });
  }
  cases.run(
      "dense contracts and complete ports cannot forge a diagonal group", [&] {
        auto module = take(executableFixture(contractions(), context));
        TestCandidates policy;
        policy.invalidDiagonalFirst =
            true; // Dense candidates are available but illegal here.
        auto plan = take(
            proposePhysical(*module, policy, {}, PhysicalPlanOptions{true}));
        for (auto &decision : plan.operations) {
          if (!decision.binding)
            continue;
          auto &binding = plan.bindings[*decision.binding];
          if (binding.purpose != BindingPurpose::Contraction)
            continue;
          binding.binding.application.implementation =
              "arkworks/" + binding.binding.application.contract;
          binding.binding.application.valueType = {};
          auto installed =
              take(resolveNativeApplication(binding.binding.application));
          binding.binding.application.valueType = installed;
          decision.inputs.clear();
          decision.outputs.clear();
          for (const auto &port : installed.getInputs())
            decision.inputs.push_back(port);
          for (const auto &port : installed.getResults())
            decision.outputs.push_back(port);
        }
        // All producer/consumer edges and full signatures still agree. Only
        // exact diagonal semantic admission should refuse this proposal.
        refuses(validatePhysical(*module, plan, policy), "binding-contraction");
      });
  cases.run("diagonal output does not waive complete factor port checks", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    auto &producer = site(plan, *module, "map");
    producer.inputs[0] = producer.outputs[0];
    refusedMutation(*module, plan, "binding-operation-signature");
  });
  cases.run(
      "uninstalled diagonal mutation cannot be authorized by policy", [&] {
        auto module = take(executableFixture(contractions(), context));
        TestCandidates policy;
        policy.invalidDiagonalFirst = true;
        auto plan = take(
            proposePhysical(*module, policy, {}, PhysicalPlanOptions{true}));
        auto &producer = site(plan, *module, "map");
        plan.bindings[*producer.binding].binding.application.implementation =
            "test/vector.mul";
        refuses(validatePhysical(*module, plan, policy),
                "binding-implementation");
      });
  cases.run(
      "explicit diagonals ignore optional preferences and automatic flag", [&] {
        auto module = take(executableFixture(contractions(), context));
        TestCandidates policy;
        policy.diagonalAvailable = false;
        auto plan =
            take(proposePhysical(*module, policy,
                                 {{"map", "arkworks-diagonal/vector.mul"},
                                  {"reduce", "arkworks-diagonal/vector.dot"}},
                                 PhysicalPlanOptions{false}));
        require(plan.contractions.empty(),
                "no automatic group for explicit choices");
        auto checked = take(validatePhysical(*module, plan, policy));
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)),
                "explicit installed diagonals verify");
      });
  cases.run("contraction missing use", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    plan.contractions.front().consumers.pop_back();
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction missing producer group", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    plan.contractions.clear();
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction duplicate consumer", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    plan.contractions.front().consumers[1] =
        plan.contractions.front().consumers[0];
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction mismatched producer", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    plan.contractions.front().producer = plan.contractions.front().consumers[0];
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("fixed consumer preflights the entire group", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(),
                                     {{"reduce", "arkworks/vector.dot"}},
                                     PhysicalPlanOptions{true}));
    require(plan.contractions.empty() && plan.bindings.size() == 2,
            "fixed consumer keeps producer and all uses dense");
    take(validatePhysical(*module, plan));
    auto forged = plan.bindings.front();
    forged.binding.name = "forged";
    forged.purpose = BindingPurpose::Contraction;
    forged.declaration.reset();
    // Fixedness must come from the consumer's original declaration, even if
    // a same-signature generated binding claims it is unfixed.
    forged.binding.application = plan.bindings[1].binding.application;
    site(plan, *module, "first").binding = plan.bindings.size();
    plan.bindings.push_back(forged);
    refusedMutation(*module, plan, "binding-selection-conflict");
  });
  cases.run("fixed producer preflights the entire group", [&] {
    auto source = contractions();
    source = replaceText(source, "implementation=\"\"",
                         "implementation=\"arkworks/vector.mul\"");
    source =
        replaceText(source,
                    "sym_name=\"reduce\",contract=\"vector.dot\",arguments=["
                    "\"bls12-381.fr\"],implementation=\"arkworks/vector.mul\"",
                    "sym_name=\"reduce\",contract=\"vector.dot\",arguments=["
                    "\"bls12-381.fr\"],implementation=\"\"");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    require(plan.contractions.empty() && plan.bindings.size() == 2,
            "source-fixed producer keeps all uses dense");
    take(validatePhysical(*module, plan));
  });
  cases.run("all-uses escape keeps group dense", [&] {
    auto source = contractions(false, true);
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    require(plan.contractions.empty(), "escaping producer is dense");
    take(validatePhysical(*module, plan));
  });
  cases.run("explicit diagonal escape rejected before materialization", [&] {
    auto source = contractions(false, true);
    auto module = take(executableFixture(source, context));
    auto before = printed(*module);
    // Dense return has no installed representation conversion for a view.
    refuses(proposePhysical(*module, installedCandidates(),
                            {{"map", "arkworks-diagonal/vector.mul"},
                             {"reduce", "arkworks-diagonal/vector.dot"}}),
            "binding-no-conversion");
    require(printed(*module) == before,
            "explicit invalid choice mutated input");
  });
  cases.run("two slots using a producer keep group dense", [&] {
    auto source = contractions();
    source =
        replaceText(source, "(%scope,%w,%mapped)", "(%scope,%mapped,%mapped)");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    require(plan.contractions.empty(),
            "values cannot occupy coefficients slot");
    take(validatePhysical(*module, plan));
  });
  cases.run("declaration budget reserves conversions before contractions", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto folds = take(executableFixture(layouts(), context));
    auto root =
        cast<protocol_ir::ProtocolModuleOp>(&module->getBody()->front());
    auto foldRoot =
        cast<protocol_ir::ProtocolModuleOp>(&folds->getBody()->front());
    for (auto &operation : foldRoot.getBody().front()) {
      if (auto local = dyn_cast<func::FuncOp>(operation)) {
        auto *clone = local->clone();
        clone->setAttr("sym_name", StringAttr::get(&context, "Fold"));
        OpBuilder builder(&context);
        clone->setAttr("runtime.origin",
                       builder.getArrayAttr({builder.getStringAttr("Fold"),
                                             builder.getArrayAttr({})}));
        root.getBody().front().push_back(clone);
      } else if (isa<zkc::runtime::BindingOp>(operation)) {
        root.getBody().front().push_back(operation.clone());
      }
    }
    auto binding =
        *root.getBody().front().getOps<zkc::runtime::BindingOp>().begin();
    for (unsigned i = 4; i < 4092; ++i) {
      auto *clone = binding->clone();
      clone->setAttr("sym_name",
                     StringAttr::get(&context, "unused" + std::to_string(i)));
      root.getBody().front().push_back(clone);
    }
    require(succeeded(verify(*module)), "native budget fixture formation");
    auto plan = take(proposePhysical(*module, installedCandidates(), {},
                                     PhysicalPlanOptions{true}));
    require(plan.contractions.empty() && plan.bindings.size() == 4094,
            "conversion-aware atomic dense fallback");
    auto checked = take(validatePhysical(*module, plan));
    accept(materializePhysical(*module, checked));
    require(succeeded(verify(*module)), "budget-aware result is admitted");
  });
  cases.run("identical input and choices produce identical output", [&] {
    auto first = take(executableFixture(layouts(), context));
    auto second = take(executableFixture(layouts(), context));
    require(succeeded(lowerBoundPhysical(*first, {}, false, nullptr)) &&
                succeeded(lowerBoundPhysical(*second, {}, false, nullptr)),
            "transactional planning");
    require(printed(*first) == printed(*second), "deterministic output");
  });
  cases.run("failed transaction preserves exact input and statistics", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto before = printed(*module);
    LinearContractionStats stats;
    stats.selectedPairs = 123;
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(lowerBoundPhysical(*module, {{"msb", "arkworks/poly.fold"}},
                                      true, &stats)),
            "fixed conflict refuses");
    require(printed(*module) == before && stats.selectedPairs == 123,
            "failed transaction never publishes a partial candidate");
  });
  cases.run(
      "two operands convert in operand order before a stopping guard", [&] {
        auto module = take(executableFixture(orderedCrossings(), context));
        auto plan = take(proposePhysical(*module));
        auto &product = site(plan, *module, "product");
        require(product.conversions.size() == 2 &&
                    product.conversions[0].operand == 0 &&
                    product.conversions[1].operand == 1,
                "explicit operand order");
        auto changed = plan;
        std::reverse(site(changed, *module, "product").conversions.begin(),
                     site(changed, *module, "product").conversions.end());
        refusedMutation(*module, changed, "binding-no-conversion");
        auto checked = take(validatePhysical(*module, plan));
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)), "ordered crossing verification");
        std::vector<std::string> actual;
        for (auto op : scopedFinite::applications(function(*module)))
          actual.push_back(implementation(op));
        require(actual ==
                    std::vector<std::string>{"arkworks/control.require",
                                             "arkworks/table.relayout",
                                             "arkworks/table.relayout",
                                             "arkworks-msb/poly.product_sum",
                                             "arkworks/control.require"},
                "stopping source instructions retain their original positions");
      });
  cases.run("nested control captures preserve actual interface layouts", [&] {
    auto module = take(executableFixture(nestedLayouts(context), context));
    auto plan = take(proposePhysical(*module));
    auto &control = site(plan, *module, "choose");
    require(control.conversions.empty(),
            "an exact capture was converted before control");
    auto physical = decodeBoundType(
        &context,
        take(parseBoundType("table:bls12-381.fr@arkworks.mle-msb/0", true)));
    require(control.inputs.size() == 3 && control.outputs.size() == 1 &&
                control.inputs[1] == physical &&
                control.outputs[0] == physical &&
                control.blockArguments.empty(),
            "control ports preserve the actual complete layout");
    auto ports = take(ExecutionPorts::read(*module));
    auto operations = physicalPlanOperations(*module);
    const auto &regions = ports.get(operations[control.operation]).bodies;
    require(regions.size() == 2, "conditional lost its outlined branches");
    for (auto *entry : regions) {
      auto *owner = ports.body(entry).owner;
      auto found = llvm::find_if(plan.operations, [&](const auto &decision) {
        return operations[decision.operation] == owner;
      });
      require(found != plan.operations.end() && found->functionType &&
                  found->functionType.getNumInputs() == 2 &&
                  found->functionType.getInput(0) == physical &&
                  found->functionType.getResult(0) == physical &&
                  found->blockArguments.size() == 1 &&
                  found->blockArguments[0].size() == 2 &&
                  found->blockArguments[0][0] == physical,
              "outlined branch ABI changed the captured table layout");
    }
    auto checked = take(validatePhysical(*module, plan));
    accept(materializePhysical(*module, checked));
    require(succeeded(verify(*module)),
            "nested physical interface verification");
  });
  cases.run("unexpected conversion on equal types is not a cast", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "same").conversions =
        site(plan, *module, "first").conversions;
    refusedMutation(*module, plan, "binding-no-conversion");
  });
  cases.run(
      "explicit full diagonal selection independently checks all uses", [&] {
        auto module = take(executableFixture(contractions(), context));
        auto plan =
            take(proposePhysical(*module, installedCandidates(),
                                 {{"map", "arkworks-diagonal/vector.mul"},
                                  {"reduce", "arkworks-diagonal/vector.dot"}},
                                 PhysicalPlanOptions{true}));
        require(plan.contractions.empty(),
                "fixed choices do not receive automatic clones");
        auto checked = take(validatePhysical(*module, plan));
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)),
                "explicit diagonal implementations valid");
      });
  cases.run("physical output port cannot acquire another nominal identity",
            [&] {
              auto module = take(executableFixture(arithmetic(), context));
              auto plan = take(proposePhysical(*module));
              auto wrong = take(defaultRepresentation(
                  take(parseBoundType("field:bn254.fr", false))));
              site(plan, *module, "add").outputs[0] =
                  decodeBoundType(&context, wrong);
              refusedMutation(*module, plan, "binding-operation-signature");
            });
  cases.run("unknown and duplicate selection requests preserve input", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto before = printed(*module);
    refuses(proposePhysical(*module, installedCandidates(),
                            {{"unknown", "arkworks/field.add"}}),
            "binding-unknown-selection");
    refuses(proposePhysical(
                *module, installedCandidates(),
                {{"add", "arkworks/field.add"}, {"add", "arkworks/field.add"}}),
            "binding-duplicate-selection");
    require(printed(*module) == before, "request refusal changed input");
  });
  cases.run("missing selected binding coverage", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "add").binding.reset();
    refusedMutation(*module, plan, "binding-plan-coverage");
  });
  cases.run("physical materialization preserves empty ABI dictionaries", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    runtime::BindingOp binding;
    module->walk([&](runtime::BindingOp value) {
      if (value.getContract() == "field.add")
        binding = value;
    });
    require(binding, "missing addition declaration");
    auto empty = DictionaryAttr::get(&context);
    binding->setAttr("arg_attrs",
                     ArrayAttr::get(&context, {empty, empty, empty}));
    binding->setAttr("res_attrs", ArrayAttr::get(&context, {empty}));
    require(succeeded(admitStage(*module)), "inert call dictionaries refused");
    auto plan = take(proposePhysical(*module));
    auto checked = take(validatePhysical(*module, plan));
    accept(materializePhysical(*module, checked));
    // Publication replaces the complete module body; reacquire actual owners.
    binding = {};
    module->walk([&](runtime::BindingOp value) {
      if (value.getContract() == "field.add")
        binding = value;
    });
    require(binding && succeeded(admitStage(*module)) &&
                binding->getAttrOfType<ArrayAttr>("arg_attrs").size() == 3 &&
                binding->getAttrOfType<ArrayAttr>("res_attrs").size() == 1,
            "materialization dropped or invalidated inert ABI dictionaries");
    binding->setAttr("arg_attrs", ArrayAttr::get(&context, {empty, empty}));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(admitStage(*module)), "wrong ABI dictionary arity admitted");
  });
  cases.run("null proposed port refuses before type dereference", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "add").outputs[0] = Type{};
    refusedMutation(*module, plan, "binding-operation-signature");
  });
  cases.run(
      "unavailable physical implementation is not installed by proposal", [&] {
        auto module = take(executableFixture(layouts(), context));
        auto plan = take(proposePhysical(*module));
        for (auto &binding : plan.bindings)
          if (binding.purpose == BindingPurpose::Conversion)
            binding.binding.application.implementation = "test/table.relayout";
        refusedMutation(*module, plan, "binding-conversion");
      });
  cases.run("invalid conversion site refuses before rewriting", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "left").conversions.front().site = "not/a/site";
    refusedMutation(*module, plan, "binding-plan-coverage");
  });
  cases.run("stale operand graph refuses despite matching types", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto plan = take(proposePhysical(*module));
    auto operations = physicalPlanOperations(*module);
    auto index = site(plan, *module, "left").operation;
    operations[index]->setOperand(1, function(*module).getArgument(1));
    refusedMutation(*module, plan, "binding-stale-selection");
  });
  cases.run("unused generated declaration refuses", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto plan = take(proposePhysical(*module));
    auto unused = plan.bindings.front();
    unused.purpose = BindingPurpose::Contraction;
    unused.declaration.reset();
    unused.binding.name = "unused";
    plan.bindings.push_back(unused);
    refusedMutation(*module, plan, "binding-plan-coverage");
  });
  cases.run(
      "selection refusal preserves declaration location and metadata", [&] {
        auto module = take(executableFixture(arithmetic(), context));
        auto location = FileLineColLoc::get(&context, "selection.mlir", 2, 3);
        module->walk([&](zkc::runtime::BindingOp op) { op->setLoc(location); });
        auto before = printed(*module);
        bool located = false, identified = false;
        ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
          located |= diagnostic.getLocation() == location;
          for (const auto &refusal : diagnostics::refusals(diagnostic))
            identified |= refusal.code == "binding-implementation";
          return success();
        });
        require(failed(lowerBoundPhysical(
                    *module, {{"add", "arkworks/vector.dot"}}, false, nullptr)),
                "wrong-contract selection refuses");
        require(located && identified,
                "structured refusal retains declaration location");
        require(printed(*module) == before, "failed lowering preserves input");
      });
  cases.run("conversion refusal identifies its actual consumer", [&] {
    auto module = take(executableFixture(layouts(), context));
    auto location = FileLineColLoc::get(&context, "conversion.mlir", 7, 5);
    module->walk([&](Operation *op) {
      if (auto name = op->getAttrOfType<StringAttr>("site"))
        if (name.getValue() == encodedSite("first"))
          op->setLoc(location);
    });
    TestCandidates policy;
    policy.available = false;
    Location failureLocation = module->getLoc();
    refuses(proposePhysical(*module, policy, {}, {}, &failureLocation),
            "binding-no-conversion");
    require(failureLocation == location,
            "conversion refusal retains consumer location");
  });
  cases.run("validation refusal identifies its actual operation", [&] {
    auto module = take(executableFixture(arithmetic(), context));
    auto location = FileLineColLoc::get(&context, "validation.mlir", 9, 7);
    module->walk([&](Operation *op) {
      if (op->hasAttr("site"))
        op->setLoc(location);
    });
    auto plan = take(proposePhysical(*module));
    site(plan, *module, "add").outputs.clear();
    Location failureLocation = module->getLoc();
    refuses(validatePhysical(*module, plan, installedCandidates(),
                             &failureLocation),
            "binding-operation-signature");
    require(failureLocation == location,
            "validation refusal retains operation location");
  });
  cases.run(
      "unused native binding outside byte depth reaches physical "
      "materialization",
      [&] {
        auto module = take(executableFixture(arithmetic(), context));
        auto root =
            cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
        auto emit = [&] { return module->emitError(); };
        Type element = constructLogicalType(
            emit, &context,
            {"field", {StringAttr::get(&context, "bls12-381.fr")}});
        require(bool(element), "missing native scalar");
        for (unsigned depth = 0; depth != 12; ++depth) {
          element = constructLogicalType(
              emit, &context, {"sequence", {TypeAttr::get(element)}});
          require(bool(element), "native nested sequence formation failed");
        }
        NativeBindingApplication request{
            "sequence.empty", {TypeAttr::get(element)}, "", {}, &context};
        auto logical = resolveLogicalSignature(emit, &context, request.contract,
                                               request.arguments);
        require(bool(logical), "native logical signature failed");
        OpBuilder builder(&root.getBody().front(),
                          root.getBody().front().begin());
        auto unused = runtime::BindingOp::create(
            builder, module->getLoc(), "unused_deep", request.contract,
            builder.getArrayAttr(request.arguments), "",
            executableBindingSignature(logical), ArrayAttr{}, ArrayAttr{});
        require(succeeded(readNativeBinding(emit, unused, false)),
                "native declaration inherited byte limits");
        refuses(readBinding(unused), "binding-type-limit");
        auto plan = take(proposePhysical(*module));
        auto selected =
            llvm::find_if(plan.bindings, [](const BindingDecision &choice) {
              return choice.binding.name == "unused_deep";
            });
        require(selected != plan.bindings.end() &&
                    selected->binding.application.arguments.front() ==
                        TypeAttr::get(element) &&
                    bool(selected->binding.application.valueType),
                "unused selection lost complete native arguments or ports");
        auto altered = plan;
        auto index = std::distance(plan.bindings.begin(), selected);
        altered.bindings[index].binding.application.arguments[0] =
            TypeAttr::get(logical.getResult(0));
        refuses(validatePhysical(*module, altered), "binding-operation");
        auto checked = take(validatePhysical(*module, plan));
        accept(materializePhysical(*module, checked));
        // Materialization replaced the root; resolve against the actual body.
        root = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
        auto actual = dyn_cast_or_null<runtime::BindingOp>(
            SymbolTable::lookupSymbolIn(root, "unused_deep"));
        require(actual && succeeded(readNativeBinding(emit, actual, true)),
                "complete native declaration was lost at materialization");
        refuses(readBinding(actual), "binding-type-limit");
        auto arguments =
            SmallVector<Attribute>(actual.getArguments().getValue());
        arguments[0] = TypeAttr::get(logical.getResult(0));
        actual.setArgumentsAttr(builder.getArrayAttr(arguments));
        require(failed(readNativeBinding([&] { return actual.emitOpError(); },
                                         actual, true)),
                "actual reader admitted an altered complete Type argument");
        arguments[0] =
            StringAttr::get(&context, "sequence<field:bls12-381.fr>");
        actual.setArgumentsAttr(builder.getArrayAttr(arguments));
        require(failed(readNativeBinding([&] { return actual.emitOpError(); },
                                         actual, true)),
                "actual reader admitted an altered static argument kind");
      });
  for (bool changeReturn : {false, true}) {
    cases.run(changeReturn ? "materialized scoped return changed"
                           : "materialized invocation operand changed",
              [&] {
                auto before = take(executableFixture(arithmetic(), context));
                auto checked = take(
                    validatePhysical(*before, take(proposePhysical(*before))));
                OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
                auto own = take(
                    validatePhysical(*after, take(proposePhysical(*after))));
                accept(materializePhysical(*after, own));
                accept(verifyPhysicalMaterialization(*before, *after, checked));
                auto fn = function(*after);
                if (changeReturn)
                  [&] {
                    exec::CompleteOp returned;
                    fn.walk([&](exec::CompleteOp op) { returned = op; });
                    require(bool(returned), "missing native completion");
                    returned->setOperand(1, fn.getArgument(1));
                  }();
                else {
                  auto kernel = scopedFinite::application(fn, "field.add");
                  kernel->setOperand(2, kernel->getOperand(1));
                }
                require(succeeded(verify(*after)),
                        "physical mutation must remain formed");
                reject(verifyPhysicalMaterialization(*before, *after, checked),
                       "binding-materialization-correspondence");
              });
  }
  cases.run("conversion feeds the wrong same-typed table", [&] {
    auto before = take(executableFixture(layouts(), context));
    auto checked =
        take(validatePhysical(*before, take(proposePhysical(*before))));
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    auto own = take(validatePhysical(*after, take(proposePhysical(*after))));
    accept(materializePhysical(*after, own));
    auto fn = function(*after);
    Value other;
    exec::ApplyOp crossing;
    fn.walk([&](exec::ApplyOp op) {
      if (op.getSite() == encodedSite("same"))
        other = scopedComputation::payload(op).front();
      if (other && implementation(op) == "arkworks/table.relayout" && !crossing)
        crossing = op;
    });
    require(other && crossing, "missing per-use conversion");
    crossing->setOperand(1, other);
    require(succeeded(verify(*after)),
            "conversion mutation must remain formed");
    reject(verifyPhysicalMaterialization(*before, *after, checked),
           "binding-materialization-correspondence");
  });
  return cases.result();
}
