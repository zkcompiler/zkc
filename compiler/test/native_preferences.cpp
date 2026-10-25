#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/MathematicalFixture.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Protocol.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;

namespace {
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
std::string source(StringRef contract, StringRef domain,
                   StringRef implementation = {}, unsigned count = 1) {
  require(count && count <= 18000, "fixture repetition bound");
  const bool pairing = contract == "pairing.check";
  const bool each = contract == "curve.scale_each";
  const bool scalar = contract == "curve.scale";
  const std::string arguments = each ? "%s:!V,%p:!G" : "%p:!G,%s:!F";
  const std::string inputs = each ? "%s,%p" : "%p,%s";
  const std::string types = each ? "!V,!G" : "!G,!F";
  const std::string output = pairing ? "i1" : "!G";
  std::string group = pairing ? "bls12-381.g1" : domain.str();
  const std::string aliases =
      "!F = " +
      std::string(pairing ? "!algebra.group_vector<\"bls12-381.g2\">"
                          : "!algebra.field<\"bls12-381.fr\">") +
      "\n!V = !algebra.field_vector<\"bls12-381.fr\">\n!G = " +
      (scalar ? "!algebra.group<\"" : "!algebra.group_vector<\"") + group +
      "\">\n";
  StringRef operation = pairing  ? "pairing_check"
                        : each   ? "group_scale_each"
                        : scalar ? "group_scale"
                                 : "group_vector_scale";
  std::string body;
  std::string point = "%p", result;
  for (unsigned i = 0; i < count; ++i) {
    result = "%result" + std::to_string(i);
    body += result + " = \"algebra.exec." + operation.str() + "\"(" +
            (each ? "%s," + point : point + ",%s") +
            ") {binding=@work,site=\"step" + std::to_string(i) +
            "\",parameters=[]} : (" + types + ")->" + output + "\n";
    if (!pairing)
      point = result;
  }
  body += "local.return " + result + " : " + output + "\n";
  return aliases + mathematicalFixture(
                       "\"local.binding\"() {sym_name=\"work\",contract=\"" +
                           contract.str() + "\",arguments=[\"" + domain.str() +
                           "\"],implementation=\"" + implementation.str() +
                           "\"} : ()->()",
                       arguments, inputs, types, output, body, 2);
}
program::Participants publish(ModuleOp module, const PhysicalPlan &plan) {
  auto checked = take(validatePhysical(module, plan));
  accept(materializePhysical(module, checked));
  require(succeeded(verify(module)), "physical module admission");
  auto model = take(readExecutionModel(module));
  accept(program::checkStructure(model));
  return model;
}
class NoConversions final : public CandidateCatalog {
public:
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    return installedCandidates().implementations(application);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &, const BoundType &) const override {
    return {};
  }
};
void fillDeclarations(ModuleOp module) {
  auto root = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  auto bindings = root.getBody().front().getOps<local::OperationBindingOp>();
  auto original = *bindings.begin();
  for (unsigned i = llvm::range_size(bindings); i < 4096; ++i) {
    auto *binding = original->clone();
    binding->setAttr(
        "sym_name",
        StringAttr::get(module.getContext(), "unused_" + std::to_string(i)));
    binding->setAttr("contract",
                     StringAttr::get(module.getContext(), "field.add"));
    binding->setAttr("implementation",
                     StringAttr::get(module.getContext(), ""));
    binding->setAttr(
        "arguments",
        ArrayAttr::get(module.getContext(),
                       {StringAttr::get(module.getContext(), "bls12-381.fr")}));
    root.getBody().front().push_back(binding);
  }
}
} // namespace

int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (argc != 1) {
    if (argc != 6 || StringRef(argv[1]) != "--emit")
      return 2;
    try {
      unsigned count;
      require(!StringRef(argv[5]).getAsInteger(10, count), "repetition count");
      StringRef implementation = argv[4];
      auto module = take(executableFixture(
          source(argv[2], argv[3],
                 implementation == "auto" ? "" : implementation, count),
          context));
      auto plan = take(proposePhysical(*module));
      outs() << printJson(program::encode(publish(*module, plan))) << '\n';
      return 0;
    } catch (const std::exception &error) {
      errs() << error.what() << '\n';
      return 1;
    }
  }
  Cases cases;
  for (StringRef contract : {"curve.scale", "curve.scale_each",
                             "curve.vector_scale", "pairing.check"}) {
    for (StringRef domain : {"bls12-381.g1", "bls12-381.g2"}) {
      if ((contract == "pairing.check" && domain != "bls12-381.g1") ||
          (contract != "pairing.check" && domain != "bls12-381.g2"))
        continue;
      const std::string argument =
          contract == "pairing.check" ? "bls12-381.fr" : domain.str();
      const std::string preferred = "blst/resident/" + contract.str();
      const std::string fallback = "arkworks/" + contract.str();
      BindingApplication application{contract.str(), {argument}, ""};
      cases.run(contract + " " + argument + " preferred and checked", [&] {
        require(take(defaultImplementation(application)) == fallback,
                "Contracts canonical default changed");
        require(take(installedCandidates().implementations(application)) ==
                    std::vector<std::string>{preferred, fallback},
                "target preference or fallback missing");
        auto module =
            take(executableFixture(source(contract, argument, {}, 3), context));
        auto plan = take(proposePhysical(*module));
        require(plan.bindings.front().binding.application.implementation ==
                        preferred &&
                    !plan.bindings.front().fixed,
                "automatic choice is not an installed preference");
        unsigned imports = 0, exports = 0;
        for (const auto &op : plan.operations)
          for (const auto &conversion : op.conversions) {
            auto from = take(encodeBoundType(conversion.from, true));
            auto to = take(encodeBoundType(conversion.to, true));
            imports += StringRef(to.representation).starts_with("blst/");
            exports += StringRef(from.representation).starts_with("blst/");
          }
        require(exports == unsigned(contract != "pairing.check") &&
                    imports == (contract == "pairing.check" ? 6 : 4),
                "unexpected conversion boundary or adjacent result round trip");
        publish(*module, plan);
      });
      cases.run(contract + " " + argument + " explicit Arkworks retained", [&] {
        for (bool authored : {false, true}) {
          auto module = take(executableFixture(
              source(contract, argument, authored ? fallback : ""), context));
          Assignments requests;
          if (!authored)
            requests.push_back({"work", fallback});
          auto plan =
              take(proposePhysical(*module, installedCandidates(), requests));
          require(plan.bindings.front().binding.application.implementation ==
                          fallback &&
                      plan.bindings.front().fixed,
                  "explicit implementation replaced");
          for (const auto &op : plan.operations)
            require(op.conversions.empty(),
                    "explicit Arkworks acquired conversions");
          publish(*module, plan);
        }
      });
      cases.run(
          contract + " " + argument + " unavailable conversion falls back",
          [&] {
            auto module =
                take(executableFixture(source(contract, argument), context));
            NoConversions catalog;
            auto plan = take(proposePhysical(*module, catalog));
            require(plan.bindings.front().binding.application.implementation ==
                        fallback,
                    "unavailable adapter did not advance existing fallback");
            take(validatePhysical(*module, plan, catalog));
          });
      cases.run(
          contract + " " + argument + " exact requests are not retried", [&] {
            auto module = take(executableFixture(
                source(contract, argument, preferred), context));
            NoConversions catalog;
            refuses(proposePhysical(*module, catalog), "binding-no-conversion");
            refuses(proposePhysical(*module, installedCandidates(),
                                    {{"work", fallback}}),
                    "binding-selection-conflict");
          });
    }
  }
  cases.run("field and permission-sensitive MSM defaults retained", [&] {
    for (StringRef contract : {"field.mul", "vector.mul", "curve.msm"}) {
      BindingApplication app{
          contract.str(),
          {contract == "curve.msm" ? "bls12-381.g1" : "bls12-381.fr"},
          ""};
      require(take(installedCandidates().implementations(app)) ==
                  std::vector<std::string>{"arkworks/" + contract.str()},
              "unmeasured or permission-sensitive automatic choice");
    }
  });
  cases.run("other domains retain their provider", [&] {
    for (auto [domain, provider] :
         {std::pair{"bls12-381.g1", "arkworks"},
          std::pair{"bn254.g1", "arkworks"}, std::pair{"bn254.g2", "arkworks"},
          std::pair{"ristretto255.group", "dalek"}}) {
      BindingApplication app{"curve.scale", {domain}, ""};
      require(
          take(installedCandidates().implementations(app)) ==
              std::vector<std::string>{std::string(provider) + "/curve.scale"},
          "BLS preference leaked into other domain");
    }
    refuses(
        installedCandidates().implementations({"curve.scale", {"missing"}, ""}),
        "binding-static-identity");
  });
  cases.run("optional conversions fall back at the declaration limit", [&] {
    auto module =
        take(executableFixture(source("curve.scale", "bls12-381.g2"), context));
    fillDeclarations(*module);
    auto plan = take(proposePhysical(*module));
    require(plan.bindings.size() == 4096 &&
                plan.bindings.front().binding.application.implementation ==
                    "arkworks/curve.scale",
            "optional conversions made a canonical program inadmissible");
    take(validatePhysical(*module, plan));
  });
  cases.run(
      "optional observation specialization falls back at declaration capacity",
      [&] {
        for (auto [fixed, joined] :
             {std::pair{false, false}, std::pair{true, false},
              std::pair{false, true}, std::pair{true, true}}) {
          auto origin = take(encodeNativeOriginTemplate(
              "main", {}, {"message", "Round", "point", "point", "P", "V"}));
          std::string scale =
              joined
                  ? R"(%p = "local.if"(%c,%g,%s) ({
^left(%point:!G,%scalar:!F):
 %left = "algebra.exec.group_scale"(%point,%scalar) {binding=@work,site="left",parameters=[]} : (!G,!F)->!G
 "local.yield"(%left) : (!G)->()
}, {
^right(%point:!G,%scalar:!F):
 %right = "algebra.exec.group_scale"(%point,%scalar) {binding=@work,site="right",parameters=[]} : (!G,!F)->!G
 "local.yield"(%right) : (!G)->()
}) {site="join"} : (i1,!G,!F)->!G
)"
                  : R"(%p = "algebra.exec.group_scale"(%g,%s) {binding=@work,site="scale",parameters=[]} : (!G,!F)->!G
)";
          auto text =
              R"(!T = !runtime.capability<"transcript:merlin3.bls12-381.fr64be/0">
!G = !algebra.group<"bls12-381.g2">
!F = !algebra.field<"bls12-381.fr">
!I = !algebra.indices
)" + mathematicalFixture(
                  R"("local.binding"() {sym_name="work",contract="curve.scale",arguments=["bls12-381.g2"],implementation=")" +
                      std::string(fixed ? "blst/resident/curve.scale" : "") +
                      R"("} : ()->()
"local.binding"() {sym_name="observe",contract="transcript.native.indexed.observe.data",arguments=["merlin3.bls12-381.fr64be/0","group:bls12-381.g2"],implementation=""} : ()->())",
                  joined ? "%c:i1,%g:!G,%s:!F,%t:!T,%i:!I"
                         : "%g:!G,%s:!F,%t:!T,%i:!I",
                  joined ? "%c,%g,%s,%t,%i" : "%g,%s,%t,%i",
                  joined ? "i1,!G,!F,!T,!I" : "!G,!F,!T,!I", "!T",
                  scale +
                      R"(%out = "crypto.exec.indexed_transcript_observe_data"(%t,%p,%i) {binding=@observe,site="observe",parameters=[")" +
                      origin + R"("]} : (!T,!G,!I)->!T
local.return %out : !T)",
                  joined ? 5 : 4);
          auto module = take(executableFixture(text, context));
          fillDeclarations(*module);
          auto proposal = proposePhysical(*module);
          if (fixed)
            refuses(std::move(proposal), "binding-declaration-limit");
          else {
            auto plan = take(std::move(proposal));
            require(
                plan.bindings.size() == 4096 &&
                    plan.bindings.front().binding.application.implementation ==
                        "arkworks/curve.scale",
                "observation specialization did not advance its producer");
            take(validatePhysical(*module, plan));
          }
        }
      });
  cases.run("inferred aggregate specialization declines at capacity", [&] {
    for (bool fixed : {false, true}) {
      auto text =
          R"(!G = !algebra.group<"bls12-381.g2">
!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.group<"bls12-381.g2">>
)" + mathematicalFixture(
              R"("local.binding"() {sym_name="work",contract="curve.scale",arguments=["bls12-381.g2"],implementation=")" +
                  std::string(fixed ? "blst/resident/curve.scale" : "") +
                  R"("} : ()->()
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["group:bls12-381.g2"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["group:bls12-381.g2"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["group:bls12-381.g2"],implementation="native/sequence.length"} : ()->())",
              "%g:!G,%s:!F", "%g,%s", "!G,!F", "ui64", R"(
%p = "algebra.exec.group_scale"(%g,%s) {binding=@work,site="scale",parameters=[]} : (!G,!F)->!G
%empty = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%values = "data.exec.sequence_append"(%empty,%p) {binding=@append,site="append",parameters=[]} : (!S,!G)->!S
%n = "data.exec.sequence_length"(%values) {binding=@length,site="length",parameters=[]} : (!S)->ui64
local.return %n : ui64)",
              2);
      auto module = take(executableFixture(text, context));
      fillDeclarations(*module);
      auto proposal = proposePhysical(*module);
      if (fixed)
        refuses(std::move(proposal), "binding-declaration-limit");
      else {
        auto plan = take(std::move(proposal));
        require(plan.bindings.size() == 4096 &&
                    plan.bindings.front().binding.application.implementation ==
                        "arkworks/curve.scale",
                "inferred aggregate layout hid the automatic choice");
        take(validatePhysical(*module, plan));
      }
    }
  });
  cases.run("real escaped carrier capacity declines optional conversions", [&] {
    // Canonical calls fit the 32,768-element body bound; one reached scalar
    // conversion per call makes the resident candidate exceed it.
    constexpr unsigned count = 16500;
    for (StringRef implementation :
         {"arkworks/curve.scale", "", "blst/resident/curve.scale"}) {
      auto module = take(executableFixture(
          source("curve.scale", "bls12-381.g2", implementation, count),
          context));
      std::vector<std::string> codes;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &value) {
        for (const auto &refusal : diagnostics::refusals(value))
          codes.push_back(refusal.code);
        return success();
      });
      auto lowered = lowerPhysical(*module);
      if (implementation == "blst/resident/curve.scale") {
        require(failed(lowered) &&
                    codes == std::vector<std::string>{"source-limit"},
                "fixed conversion expansion did not refuse carrier capacity");
      } else {
        require(succeeded(lowered),
                "canonical carrier stopped fitting after preference");
        auto model = take(readExecutionModel(*module));
        accept(program::checkStructure(model));
        require(model.bindings.front().application.implementation ==
                    "arkworks/curve.scale",
                "escaped carrier capacity did not select canonical fallback");
      }
    }
  });
  cases.run(
      "escaped capacity advances the producer of a return conversion", [&] {
        for (bool fixed : {false, true}) {
          auto module = take(executableFixture(
              source("curve.scale", "bls12-381.g2",
                     fixed ? "blst/resident/curve.scale" : ""),
              context));
          unsigned attempts = 0;
          PhysicalPlanOptions options;
          options.programCapacity = [&](ModuleOp, const PhysicalPlan &plan)
              -> Expected<SmallVector<OperationIndex>> {
            ++attempts;
            for (const auto &operation : plan.operations)
              if (!operation.binding && !operation.conversions.empty())
                return SmallVector<OperationIndex>{operation.operation};
            return SmallVector<OperationIndex>{};
          };
          auto proposed =
              proposePhysical(*module, installedCandidates(), {}, options);
          if (fixed) {
            refuses(std::move(proposed), "source-limit");
            require(attempts == 1, "fixed implementation retried on capacity");
          } else {
            auto plan = take(std::move(proposed));
            require(
                attempts == 2 && plan.bindings.size() == 1 &&
                    plan.bindings.front().binding.application.implementation ==
                        "arkworks/curve.scale",
                "return conversion did not attribute its automatic producer");
            take(validatePhysical(*module, plan));
          }
        }
      });
  cases.run("capacity advances independent automatic choices together", [&] {
    auto module = take(executableFixture(
        source("curve.scale", "bls12-381.g2", {}, 2), context));
    auto root = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    auto original =
        *root.getBody().front().getOps<local::OperationBindingOp>().begin();
    auto *alias = original->clone();
    alias->setAttr("sym_name", StringAttr::get(&context, "alias"));
    root.getBody().front().push_back(alias);
    module->walk([&](Operation *op) {
      auto site = op->getAttrOfType<StringAttr>("site");
      if (site && site.getValue() == "step1")
        op->setAttr("binding", FlatSymbolRefAttr::get(&context, "alias"));
    });
    unsigned attempts = 0;
    PhysicalPlanOptions options;
    options.programCapacity =
        [&](ModuleOp,
            const PhysicalPlan &plan) -> Expected<SmallVector<OperationIndex>> {
      ++attempts;
      SmallVector<OperationIndex> affected;
      for (const auto &operation : plan.operations)
        if (!operation.conversions.empty())
          affected.push_back(operation.operation);
      return affected;
    };
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(attempts == 2 && plan.bindings.size() == 2,
            "independent choices did not advance together");
    for (const auto &binding : plan.bindings)
      require(binding.binding.application.implementation ==
                  "arkworks/curve.scale",
              "alias retained optional expansion");
    take(validatePhysical(*module, plan));
  });
  cases.run("invalid capacity attribution remains terminal", [&] {
    auto module =
        take(executableFixture(source("curve.scale", "bls12-381.g2"), context));
    unsigned attempts = 0;
    PhysicalPlanOptions options;
    options.programCapacity =
        [&](ModuleOp,
            const PhysicalPlan &plan) -> Expected<SmallVector<OperationIndex>> {
      ++attempts;
      return SmallVector<OperationIndex>{plan.operations.size()};
    };
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "source-limit");
    require(attempts == 1, "invalid capacity attribution triggered retry");
  });
  cases.run("automatic policy cannot replenish exhausted selection work", [&] {
    auto module =
        take(executableFixture(source("curve.scale", "bls12-381.g2"), context));
    mathematical::RealizationWork work;
    work.selectionBookkeeping = 0;
    PhysicalPlanOptions options;
    options.numericalWork = &work;
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "finite-analysis-limit");
    require(work.selectionBookkeeping == 0, "selection work was replenished");
  });
  cases.run("capacity retry preserves cumulative nonzero selection work", [&] {
    auto module =
        take(executableFixture(source("curve.scale", "bls12-381.g2"), context));
    mathematical::RealizationWork work;
    constexpr uint64_t initial = 1000000;
    uint64_t firstDebit = 0;
    unsigned attempts = 0;
    PhysicalPlanOptions options;
    options.numericalWork = &work;
    options.programCapacity =
        [](ModuleOp,
           const PhysicalPlan &) -> Expected<SmallVector<OperationIndex>> {
      return error("source-limit");
    };
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "source-limit");
    firstDebit = initial - work.selectionBookkeeping;
    work = {};
    options.programCapacity =
        [&](ModuleOp,
            const PhysicalPlan &plan) -> Expected<SmallVector<OperationIndex>> {
      ++attempts;
      for (const auto &operation : plan.operations)
        if (!operation.conversions.empty())
          return SmallVector<OperationIndex>{operation.operation};
      return SmallVector<OperationIndex>{};
    };
    take(proposePhysical(*module, installedCandidates(), {}, options));
    require(attempts == 2 && firstDebit > 0, "missing initial retry debit");
    work = {};
    work.selectionBookkeeping = firstDebit + 1;
    attempts = 0;
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "finite-analysis-limit");
    require(attempts == 1 && !work.selectionBookkeeping,
            "retry skipped initial preflight or refunded catalog work");
  });
  return cases.result();
}
