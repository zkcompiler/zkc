#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/MathematicalFixture.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
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
  auto text = mathematicalFixture(R"(
"local.binding"() {sym_name="msb",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
"local.binding"() {sym_name="dense",contract="poly.fold",arguments=["bls12-381.fr"],implementation=""} : ()->()
)",
                                  "%a:!T,%r:!F", "%a,%r", "!T,!F", "!T", R"(
%x = "poly.exec.fold"(%a,%r) {binding=@msb,site="first",parameters=[]} : (!T,!F)->!T
%q = "poly.exec.fold"(%x,%r) {binding=@msb,site="same",parameters=[]} : (!T,!F)->!T
%y = "poly.exec.fold"(%x,%r) {binding=@dense,site="left",parameters=[]} : (!T,!F)->!T
%z = "poly.exec.fold"(%x,%r) {binding=@dense,site="right",parameters=[]} : (!T,!F)->!T
local.return %q : !T
)",
                                  2);
  if (!fixed)
    text = replaceText(text, "arkworks-msb/poly.fold", "");
  return "!F = !algebra.field<\"bls12-381.fr\">\n!T = "
         "!poly.multilinear<\"bls12-381.fr\">\n" +
         text;
}
std::string contractions(bool group = false) {
  auto text =
      mathematicalFixture(R"(
"local.binding"() {sym_name="map",contract="vector.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
"local.binding"() {sym_name="reduce",contract="vector.dot",arguments=["bls12-381.fr"],implementation=""} : ()->()
)",
                          "%w:!V,%f:!V,%v:!A", "%w,%f,%v", "!V,!V,!A", "!R", R"(
%mapped = "algebra.exec.vector_mul"(%f,%v) {binding=@map,site="map",parameters=[]} : (!V,!A)->!A
%a = "algebra.exec.vector_dot"(%w,%mapped) {binding=@reduce,site="first",parameters=[]} : (!V,!A)->!R
%b = "algebra.exec.vector_dot"(%w,%mapped) {binding=@reduce,site="second",parameters=[]} : (!V,!A)->!R
local.return %b : !R
)",
                          3);
  if (group) {
    text = replaceText(text, "bls12-381.fr", "ristretto255.group");
    text = replaceText(text, "vector.mul", "curve.scale_each");
    text = replaceText(text, "vector.dot", "curve.msm");
    text = replaceText(text, "algebra.exec.vector_mul",
                       "algebra.exec.group_scale_each");
    text =
        replaceText(text, "algebra.exec.vector_dot", "algebra.exec.group_msm");
  }
  std::string scalar = group ? "ristretto255.scalar" : "bls12-381.fr";
  return "!V = tensor<?x!algebra.field<\"" + scalar + "\">>\n!A = " +
         (group ? "tensor<?x!algebra.group<\"ristretto255.group\">>"
                : "tensor<?x!algebra.field<\"bls12-381.fr\">>") +
         "\n!R = " +
         (group ? "!algebra.group<\"ristretto255.group\">"
                : "!algebra.field<\"bls12-381.fr\">") +
         "\n" + text;
}
std::string arithmetic(std::string identity = "bls12-381.fr") {
  return "!F = !algebra.field<\"" + identity + "\">\n" +
         mathematicalFixture(
             "\"local.binding\"() "
             "{sym_name=\"add\",contract=\"field.add\",arguments=[\"" +
                 identity + "\"],implementation=\"\"} : ()->()",
             "%a:!F,%b:!F", "%a,%b", "!F,!F", "!F", R"(
%c = "algebra.exec.field_add"(%a,%b) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
local.return %c : !F
)",
             2);
}
std::string orderedCrossings() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="product",contract="poly.product_sum",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.product_sum"} : ()->()
"local.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation=""} : ()->()
)",
                         "%a:!T,%b:!T,%allowed:i1", "%a,%b,%allowed",
                         "!T,!T,i1", "!F", R"(
"local.exec.require"(%allowed) {binding=@guard,site="before",parameters=[]} : (i1)->()
%value = "poly.exec.product_sum"(%a,%b) {binding=@product,site="product",parameters=[]} : (!T,!T)->!F
"local.exec.require"(%allowed) {binding=@guard,site="after",parameters=[]} : (i1)->()
local.return %value : !F
)",
                         3);
}
std::string nestedLayouts() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="fold",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
)",
                         "%a:!T,%r:!F,%condition:i1", "%a,%r,%condition",
                         "!T,!F,i1", "!T", R"(
%x = "poly.exec.fold"(%a,%r) {binding=@fold,site="outer",parameters=[]} : (!T,!F)->!T
%z = "local.if"(%condition,%x,%r) ({^left(%leftTable:!T,%leftScalar:!F):
  %y = "poly.exec.fold"(%leftTable,%leftScalar) {binding=@fold,site="inner",parameters=[]} : (!T,!F)->!T
  "local.yield"(%y) : (!T)->()
}, {^right(%rightTable:!T,%rightScalar:!F):
  %y = "poly.exec.fold"(%rightTable,%rightScalar) {binding=@fold,site="other",parameters=[]} : (!T,!F)->!T
  "local.yield"(%y) : (!T)->()
}) {site="choose"} : (i1,!T,!F)->!T
local.return %z : !T
)",
                         3);
}
OperationDecision &site(PhysicalPlan &plan, ModuleOp module, StringRef name) {
  auto ops = physicalPlanOperations(module);
  for (auto &decision : plan.operations)
    if (auto attr = ops[decision.operation]->getAttrOfType<StringAttr>("site"))
      if (attr.getValue() == name)
        return decision;
  throw std::runtime_error("missing site " + name.str());
}
zkc::local::FuncOp function(ModuleOp module) {
  return *cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front())
              .getBody()
              .front()
              .getOps<zkc::local::FuncOp>()
              .begin();
}
void refusedMutation(ModuleOp module, PhysicalPlan &plan, StringRef code) {
  auto before = printed(module);
  refuses(validatePhysical(module, plan), code);
  require(before == printed(module), "validation mutated logical input");
}
class TestCandidates final : public CandidateCatalog {
public:
  bool reverseOrder = false, available = true, invalidFirst = true;
  bool diagonalAvailable = true, invalidDiagonalFirst = false;
  std::string withheldDiagonalContract;
  std::vector<std::string> diagonalImplementations(
      const BindingApplication &application) const override {
    if (!diagonalAvailable || application.contract == withheldDiagonalContract)
      return {};
    auto result = installedCandidates().diagonalImplementations(application);
    if (invalidDiagonalFirst) {
      auto ordinary = take(defaultImplementation(application));
      result.insert(result.begin(), {"test/" + application.contract, ordinary});
    }
    return result;
  }
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    if (application.contract == "poly.fold" &&
        application.arguments == std::vector<std::string>{"bls12-381.fr"}) {
      std::vector<std::string> result{"arkworks-msb/poly.fold",
                                      "arkworks/poly.fold"};
      if (reverseOrder)
        std::reverse(result.begin(), result.end());
      return result;
    }
    return installedCandidates().implementations(application);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    if (!available)
      return {};
    auto result = installedCandidates().conversions(from, to);
    // Synthetic rule order; it cannot install a backend or a semantic law.
    if (invalidFirst)
      result.insert(result.begin(),
                    {"table.relayout",
                     {from.identity, from.representation, to.representation},
                     "test/table.relayout"});
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
        for (auto op : function(*module)
                           .getBody()
                           .front()
                           .getOps<zkc::plan::ExecuteKernelOp>()) {
          implementations.push_back(op.getKernel().str());
          if (op.getKernel() == "arkworks/table.relayout") {
            ++conversions;
            require(op.getResult(0).hasOneUse(),
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
                           .getOps<zkc::local::OperationBindingOp>())
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
        auto add = take(
            resolveBinding(plan.bindings.front().binding.application, true));
        auto mul = take(resolveBinding(forged.binding.application, true));
        require(add.inputs == mul.inputs && add.outputs == mul.outputs,
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
    plan.bindings.front().binding.application.arguments = {"bn254.fr"};
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
  cases.run("unary signatures and cross-field layouts grant no law", [&] {
    auto logical = take(parseBoundType("field:bls12-381.fr", false));
    auto field = take(defaultRepresentation(logical));
    reject(checkDirectConversion(
               {"field.neg", {"bls12-381.fr"}, "arkworks/field.neg"}, field,
               field),
           "binding-no-conversion");
    auto from =
        take(parseBoundType("table:bls12-381.fr@arkworks.mle-lsb/1", true));
    auto to = from;
    to.identity = "bn254.fr";
    reject(checkDirectConversion(
               {"table.relayout",
                {"bls12-381.fr", from.representation, to.representation},
                "arkworks/table.relayout"},
               from, to),
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
          auto plan =
              take(proposePhysical(*module, installedCandidates(), {}, true));
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
          for (auto op : function(*module)
                             .getBody()
                             .front()
                             .getOps<zkc::plan::ExecuteKernelOp>())
            actual.push_back(op.getKernel().str());
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
          take(installedCandidates().implementations(application)) ==
              std::vector<std::string>{std::string(backend) + "/" + contract},
          "ordinary default remains dense");
      require(installedCandidates().diagonalImplementations(application) ==
                  std::vector<std::string>{std::string(backend) + "-diagonal/" +
                                           contract},
              "separate diagonal preference resolves through Contracts");
    }
  });
  cases.run(
      "logical roles survive absence of an installed diagonal layout", [&] {
        auto source = replaceText(contractions(), "bls12-381.fr", "koala-bear");
        auto module = take(executableFixture(source, context));
        LinearContractionStats opportunities;
        require(
            findLinearContractions(function(*module), opportunities).size() ==
                1,
            "logical scalar action remains eligible without a diagonal "
            "backend");
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, true));
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
          auto plan = take(proposePhysical(*module, policy, {}, true));
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
      auto plan = take(proposePhysical(*module, policy, {}, true));
      require(plan.contractions.empty() && plan.bindings.size() == 2,
              "withheld member prevents the whole group");
      take(validatePhysical(*module, plan, policy));
      auto selected =
          take(proposePhysical(*module, installedCandidates(), {}, true));
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
        auto plan = take(proposePhysical(*module, policy, {}, true));
        for (auto &decision : plan.operations) {
          if (!decision.binding)
            continue;
          auto &binding = plan.bindings[*decision.binding];
          if (binding.purpose != BindingPurpose::Contraction)
            continue;
          binding.binding.application.implementation =
              "arkworks/" + binding.binding.application.contract;
          auto installed =
              take(resolveBinding(binding.binding.application, true));
          decision.inputs.clear();
          decision.outputs.clear();
          for (const auto &port : installed.inputs)
            decision.inputs.push_back(decodeBoundType(&context, port));
          for (const auto &port : installed.outputs)
            decision.outputs.push_back(decodeBoundType(&context, port));
        }
        // All producer/consumer edges and full signatures still agree. Only
        // exact diagonal semantic admission should refuse this proposal.
        refuses(validatePhysical(*module, plan, policy), "binding-contraction");
      });
  cases.run("diagonal output does not waive complete factor port checks", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    auto &producer = site(plan, *module, "map");
    producer.inputs[0] = producer.outputs[0];
    refusedMutation(*module, plan, "binding-operation-signature");
  });
  cases.run(
      "uninstalled diagonal mutation cannot be authorized by policy", [&] {
        auto module = take(executableFixture(contractions(), context));
        TestCandidates policy;
        policy.invalidDiagonalFirst = true;
        auto plan = take(proposePhysical(*module, policy, {}, true));
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
                                 false));
        require(plan.contractions.empty(),
                "no automatic group for explicit choices");
        auto checked = take(validatePhysical(*module, plan, policy));
        accept(materializePhysical(*module, checked));
        require(succeeded(verify(*module)),
                "explicit installed diagonals verify");
      });
  cases.run("contraction missing use", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    plan.contractions.front().consumers.pop_back();
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction missing producer group", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    plan.contractions.clear();
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction duplicate consumer", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    plan.contractions.front().consumers[1] =
        plan.contractions.front().consumers[0];
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("contraction mismatched producer", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    plan.contractions.front().producer = plan.contractions.front().consumers[0];
    refusedMutation(*module, plan, "binding-contraction");
  });
  cases.run("fixed consumer preflights the entire group", [&] {
    auto module = take(executableFixture(contractions(), context));
    auto plan =
        take(proposePhysical(*module, installedCandidates(),
                             {{"reduce", "arkworks/vector.dot"}}, true));
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
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    require(plan.contractions.empty() && plan.bindings.size() == 2,
            "source-fixed producer keeps all uses dense");
    take(validatePhysical(*module, plan));
  });
  cases.run("all-uses escape keeps group dense", [&] {
    auto source = contractions();
    source = replaceText(source, "local.return %b : !R",
                         "local.return %mapped : !A");
    source = replaceText(source, ")->!R attributes", ")->!A attributes");
    source = replaceText(source, "(!V,!V,!A)->!R", "(!V,!V,!A)->!A");
    source = replaceText(source, "(%out) : (!R)", "(%out) : (!A)");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
    require(plan.contractions.empty(), "escaping producer is dense");
    take(validatePhysical(*module, plan));
  });
  cases.run("explicit diagonal escape rejected before materialization", [&] {
    auto source = contractions();
    source = replaceText(source, "local.return %b : !R",
                         "local.return %mapped : !A");
    source = replaceText(source, ")->!R attributes", ")->!A attributes");
    source = replaceText(source, "(!V,!V,!A)->!R", "(!V,!V,!A)->!A");
    source = replaceText(source, "(%out) : (!R)", "(%out) : (!A)");
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
    source = replaceText(source, "(%w,%mapped)", "(%mapped,%mapped)");
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
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
      if (auto local = dyn_cast<zkc::local::FuncOp>(operation)) {
        auto *clone = local->clone();
        clone->setAttr("sym_name", StringAttr::get(&context, "Fold"));
        OpBuilder builder(&context);
        clone->setAttr("logical_origin",
                       builder.getArrayAttr({builder.getStringAttr("Fold"),
                                             builder.getArrayAttr({})}));
        root.getBody().front().push_back(clone);
      } else if (isa<zkc::local::OperationBindingOp>(operation)) {
        root.getBody().front().push_back(operation.clone());
      }
    }
    auto binding = *root.getBody()
                        .front()
                        .getOps<zkc::local::OperationBindingOp>()
                        .begin();
    for (unsigned i = 4; i < 4092; ++i) {
      auto *clone = binding->clone();
      clone->setAttr("sym_name",
                     StringAttr::get(&context, "unused" + std::to_string(i)));
      root.getBody().front().push_back(clone);
    }
    require(succeeded(verify(*module)), "native budget fixture formation");
    auto plan = take(proposePhysical(*module, installedCandidates(), {}, true));
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
        for (auto op : function(*module)
                           .getBody()
                           .front()
                           .getOps<zkc::plan::ExecuteKernelOp>())
          actual.push_back(op.getKernel().str());
        require(actual ==
                    std::vector<std::string>{"arkworks/control.require",
                                             "arkworks/table.relayout",
                                             "arkworks/table.relayout",
                                             "arkworks-msb/poly.product_sum",
                                             "arkworks/control.require"},
                "stopping source instructions retain their original positions");
      });
  cases.run("nested control captures retain default interface layouts", [&] {
    auto module = take(executableFixture(nestedLayouts(), context));
    auto plan = take(proposePhysical(*module));
    auto &control = site(plan, *module, "choose");
    require(control.conversions.size() == 1 &&
                control.conversions.front().operand == 1,
            "capture converted immediately before control");
    auto logical = take(parseBoundType("table:bls12-381.fr", false));
    auto physical =
        decodeBoundType(&context, take(defaultRepresentation(logical)));
    require(control.inputs[1] == physical &&
                control.blockArguments[0][0] == physical &&
                control.blockArguments[1][0] == physical &&
                control.outputs[0] == physical,
            "all control boundaries retain installed default layout");
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
                                 true));
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
    operations[index]->setOperand(0, function(*module).getArgument(0));
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
        module->walk(
            [&](zkc::local::OperationBindingOp op) { op->setLoc(location); });
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
        if (name.getValue() == "first")
          op->setLoc(location);
    });
    TestCandidates policy;
    policy.available = false;
    Location failureLocation = module->getLoc();
    refuses(proposePhysical(*module, policy, {}, false, &failureLocation),
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
  for (bool changeReturn : {false, true}) {
    cases.run(changeReturn ? "materialized local return changed"
                           : "materialized kernel operand changed",
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
                  fn.getBody().front().back().setOperand(0, fn.getArgument(0));
                else {
                  auto kernel = *fn.getBody()
                                     .front()
                                     .getOps<zkc::plan::ExecuteKernelOp>()
                                     .begin();
                  kernel->setOperand(1, kernel->getOperand(0));
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
    zkc::plan::ExecuteKernelOp crossing;
    fn.walk([&](zkc::plan::ExecuteKernelOp op) {
      if (op.getSite() == "same")
        other = op.getResult(0);
      if (other && op.getKernel() == "arkworks/table.relayout" && !crossing)
        crossing = op;
    });
    require(other && crossing, "missing per-use conversion");
    crossing->setOperand(0, other);
    require(succeeded(verify(*after)),
            "conversion mutation must remain formed");
    reject(verifyPhysicalMaterialization(*before, *after, checked),
           "binding-materialization-correspondence");
  });
  return cases.result();
}
