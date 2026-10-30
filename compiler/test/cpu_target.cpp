#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ScopedFixture.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/CpuTarget.h"
#include "zkc/Target/Selection.h"
#include <set>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;
namespace {
CpuTarget installation(StringRef providers) {
  return take(
      CpuTarget::parse("{\"format\":\"zkc.cpu-target/0\",\"providers\":[" +
                       providers.str() + "]}"));
}
void accept(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
void reject(Error e, StringRef code = "cpu-target-unavailable") {
  require(bool(e), "expected refusal");
  require(namesIdentifier(toString(std::move(e)), code), "unexpected refusal");
}
BoundType ordinary(StringRef text) {
  return take(defaultRepresentation(take(parseBoundType(text, false))));
}
std::string moduleToString(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out);
  return text;
}
language::CheckedOriginal original(StringRef source,
                                   StringRef entry = "sample::Demo") {
  auto captured =
      take(language::capture({{"sample", source.str(), "sample.zkc"}}));
  auto checked = take(language::analyze(captured).checkedProject());
  return take(
      language::prepareOriginal(take(language::closeEntry(checked, entry))));
}
std::string arithmetic(StringRef field) {
  return "!F = !algebra.field<\"" + field.str() + R"mlir(">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %sum = algebra.field_add %a,%b : (!F,!F)->!F
   "protocol.return"(%sum) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string scale() {
  return R"mlir(
!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g2">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%g:!G,%x:!F):
   %scaled = algebra.group_scale %g,%x : (!G,!F)->!G
   "protocol.return"(%scaled) : (!G)->()
 }) {sym_name="main",function_type=(!G,!F)->!G,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string boundScale() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!G = !algebra.group<"bls12-381.g2">
)" + scopedFixture(
             R"(
"runtime.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g2"],implementation="",function_type=(!runtime.scope, !algebra.group<"bls12-381.g2">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.group<"bls12-381.g2">)>} : ()->()
)",
             "%g:!G,%x:!F", "%g,%x", "!G,!F", "!G",
             scopedApply("scale", "scale", "%g,%x", "!G,!F", "%scaled", "!G") +
                 scopedReturn("%scaled", "!G"),
             2);
}
std::string tableLayouts() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)" + scopedFixture(
             R"(
"runtime.binding"() {sym_name="msb",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
"runtime.binding"() {sym_name="dense",contract="poly.fold",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !poly.multilinear<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!poly.multilinear<"bls12-381.fr">)>} : ()->()
)",
             "%a:!T,%r:!F", "%a,%r", "!T,!F", "!T",
             scopedApply("msb", "first", "%a,%r", "!T,!F", "%x", "!T") +
                 scopedApply("msb", "same", "%x,%r", "!T,!F", "%q", "!T") +
                 scopedApply("dense", "left", "%x,%r", "!T,!F", "%y", "!T") +
                 scopedApply("dense", "right", "%x,%r", "!T,!F", "%z", "!T") +
                 scopedReturn("%q", "!T"),
             2);
}
unsigned conversionUses(const PhysicalPlan &plan, StringRef contract) {
  unsigned count = 0;
  for (const auto &operation : plan.operations)
    for (const auto &conversion : operation.conversions) {
      require(conversion.binding < plan.bindings.size(),
              "missing adapter binding");
      const auto &binding = plan.bindings[conversion.binding];
      require(binding.purpose == BindingPurpose::Conversion &&
                  binding.binding.application.contract == contract,
              "unexpected generated adapter");
      ++count;
    }
  return count;
}
unsigned adapterDeclarations(const PhysicalPlan &plan, StringRef contract,
                             StringRef implementation) {
  unsigned count = 0;
  for (const auto &binding : plan.bindings)
    if (binding.purpose == BindingPurpose::Conversion) {
      require(binding.binding.application.contract == contract &&
                  binding.binding.application.implementation ==
                      implementation &&
                  !binding.declaration,
              "adapter was not synthesized with the expected implementation");
      take(resolveBinding(binding.binding.application, true));
      ++count;
    }
  return count;
}
void publishAdapters(ModuleOp module, const PhysicalPlan &plan,
                     StringRef contract, unsigned declarations, unsigned uses) {
  auto checked = take(validatePhysical(module, plan));
  accept(materializePhysical(module, checked));
  require(succeeded(verify(module)), "materialized physical module refused");
  unsigned actualDeclarations = 0, actualUses = 0;
  module.walk([&](runtime::BindingOp binding) {
    actualDeclarations += binding.getContract() == contract;
  });
  module.walk([&](exec::ApplyOp operation) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        operation, operation.getBindingAttr());
    require(bool(binding), "materialized invocation has no declaration");
    actualUses += binding.getContract() == contract;
  });
  require(
      actualDeclarations == declarations && actualUses == uses,
      "materialization changed generated adapter declarations or crossings");
}
class WithoutConversions final : public CandidateCatalog {
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
std::string internalFieldDeployment(StringRef field) {
  return "module sample; domain Fr=field(\"" + field.str() + R"(");
fn from_index<F:Field>(value:index)->F=primitive("field.from_index");
protocol Child<F:Field> roles(P)(x:index@P)->(value:bool@P){
  let a=from_index<F>(x);return(value=a==0);
}
protocol Work<F:Field> roles(P)(x:index@P)->(value:bool@P){
  let value=Child<F>(x);return(value=value);
}
entry fn Relay(inputs:Work<Fr>::Inputs){return Work<Fr>::run(inputs);}
entry fn Demo(inputs:Work<Fr>::Inputs){return Relay(inputs);})";
}
void reachedDeployment(const CompilationObservation &observations,
                       StringRef id) {
  auto journal = observations.json();
  bool reachedProtocol = false, reachedExecution = false;
  for (const auto &phase : *journal.getAsObject()->getArray("phases")) {
    auto &record = *phase.getAsObject();
    auto &unit = *record.getArray("unit");
    if (unit.size() != 3 || unit[0].getAsString() != "sample::Demo" ||
        unit[1].getAsString() != id || unit[2].getAsString() != "sample::Work")
      continue;
    reachedProtocol |= record.getString("phase") == "protocol" &&
                       record.getObject("histogram")
                               ->getInteger("algebra.field_equal")
                               .value_or(0) > 0;
    reachedExecution |= record.getString("phase") == "exec";
  }
  require(reachedProtocol && reachedExecution,
          "target refusal occurred before recursive deployment lowering");
}
} // namespace
int main() {
  Cases cases;
  const auto small = installation("\"plonky3\"");
  const auto empty = installation("");
  cases.run("bounded exact descriptor and unordered input subset", [&] {
    auto both = installation("\"plonky3\",\"arkworks\"");
    require(both.includes("arkworks") && both.includes("plonky3") &&
                !both.includes("blst") && !both.includes("native"),
            "provider subset differs");
    require(!small.includes("arkworks") && !empty.includes("plonky3"),
            "reduced target restored a provider");
  });
  for (
      StringRef malformed :
      {"{}", "[]", "null", R"({"format":"zkc.cpu-target/1","providers":[]})",
       R"({"format":"zkc.cpu-target/0","providers":[],"extra":0})",
       R"({"format":"zkc.cpu-target/0","format":"zkc.cpu-target/0","providers":[]})",
       R"({"format":"zkc.cpu-target/0","providers":[],"pro\u0076iders":[]})",
       R"({"format":"zkc.cpu-target/0","providers":["plonky3","plonky3"]})",
       R"({"format":"zkc.cpu-target/0","providers":["arkworks","blst","dalek","halo2curves","plonky3","native"]})",
       R"({"format":"zkc.cpu-target/0","providers":["halo2curves-axiom"]})",
       R"({"format":"zkc.cpu-target/0","providers":["native"]})",
       R"({"format":"zkc.cpu-target/0","providers":[true]})",
       R"({"format":"zkc.cpu-target/0","providers":{}})",
       R"({"format":"zkc.cpu-target/0","providers":["\ud800"]})"})
    cases.run("descriptor refusal: " + malformed, [&] {
      refuses(CpuTarget::parse(malformed), "cpu-target-invalid");
    });
  cases.run("descriptor byte and nesting ceilings", [] {
    refuses(CpuTarget::parse(std::string(4097, ' ')), "cpu-target-limit");
    refuses(CpuTarget::parse("[[[[[[]]]]]]"), "cpu-target-limit");
  });
  cases.run("default target covers every compiled atomic representation", [] {
    for (const auto &rep : installedDomains().allRepresentations()) {
      auto logical = take(applyBoundType(
          rep.kind, rep.domain.empty() ? std::vector<std::string>{}
                                       : std::vector{rep.domain}));
      auto physical = take(physicalType(logical, rep.identity, {}));
      accept(CpuTarget().checkType(physical));
    }
    for (const auto &rep : appliedTypeRepresentations()) {
      std::vector<std::string> args;
      for (const auto &arg : rep.arguments)
        args.push_back(arg.argument.kind == TypeArgument::Kind::Nat
                           ? std::to_string(arg.minimum)
                           : arg.argument.spelling());
      auto logical = take(applyBoundType(rep.constructor, args));
      auto physical =
          take(physicalType(logical, rep.representation, {rep.childType}));
      accept(CpuTarget().checkType(physical));
    }
    for (const auto &impl : installedImplementations().all())
      accept(
          CpuTarget().checkImplementation({impl.contract, {}, impl.identity}));
  });
  cases.run(
      "empty target retains generic controls and byte/index storage", [&] {
        for (StringRef type :
             {"bool", "index", "indices", "bytes", "sequence<bool>"})
          accept(empty.checkType(ordinary(type)));
        for (StringRef contract :
             {"control.require", "bool.and", "bool.or", "bool.not",
              "hash.keccak256", "hash.sha256", "bytes.empty", "index.constant"})
          take(selectImplementation({contract.str(), {}, ""}, {}, empty));
        reject(empty.checkType(ordinary("field:koala-bear")));
      });
  cases.run("native external adapters retain their numerical owners", [&] {
    take(selectImplementation({"external.openvm.init", {}, ""}, {}, small));
    refuses(selectImplementation({"external.openvm.init", {}, ""}, {}, empty),
            "cpu-target-unavailable");
    take(selectImplementation({"external.monero.init", {}, ""}, {},
                              installation("\"dalek\"")));
    refuses(selectImplementation({"external.monero.init", {}, ""}, {}, small),
            "cpu-target-unavailable");
  });
  cases.run("small and binary fields require plonky3", [&] {
    for (StringRef field :
         {"koala-bear", "koala-bear.ext8-binomial3",
          "baby-bear.ext4-binomial11", "goldilocks.ext2-binomial7",
          "gf2-64.pentanomial-4-3-1.ext3-trinomial1"}) {
      auto type = ordinary(("field:" + field).str());
      accept(small.checkType(type));
      reject(empty.checkType(type));
    }
    reject(small.checkType(ordinary("field:bls12-381.fr")));
    reject(small.checkType(ordinary("group:edwards25519.prime")));
  });
  cases.run("resident layouts require their actual owner", [&] {
    auto resident = take(parseBoundType("field:bls12-381.fr@blst/fr", true));
    accept(installation("\"blst\"").checkType(resident));
    reject(installation("\"arkworks\"").checkType(resident));
    reject(installation("\"blst\"").checkType(ordinary("field:bls12-381.fr")));
    auto halo =
        take(parseBoundType("field:bn254.fr@halo2curves-axiom/bn254.fr", true));
    accept(installation("\"halo2curves\"").checkType(halo));
    reject(small.checkType(halo));
  });
  cases.run("inactive nested variant payloads require their provider", [&] {
    auto spelling = encodeVariant(
        {"TargetChoice",
         {{"empty", {}}, {"hidden", {"sequence<field:bls12-381.fr>"}}}});
    require(bool(spelling), "variant formation");
    reject(small.checkType(ordinary(*spelling)));
    auto supported = encodeVariant(
        {"TargetChoice",
         {{"empty", {}}, {"hidden", {"sequence<field:koala-bear>"}}}});
    require(bool(supported), "variant formation");
    accept(small.checkType(ordinary(*supported)));
  });
  cases.run("default, explicit and special resolver choices obey target", [&] {
    take(selectImplementation({"field.add", {"koala-bear"}, ""}, {}, small));
    refuses(
        selectImplementation({"field.add", {"bls12-381.fr"}, ""}, {}, small),
        "cpu-target-unavailable");
    refuses(selectImplementation(
                {"field.add", {"bls12-381.fr"}, "blst/resident/field.add"}, {},
                small),
            "cpu-target-unavailable");
    BindingApplication conversion{
        "representation.convert",
        {"field:bls12-381.fr"},
        "native/representation.convert",
        {"field:bls12-381.fr@arkworks.fr/0", "field:bls12-381.fr@blst/fr"}};
    take(resolveBinding(conversion, true));
    take(selectImplementation(conversion, {},
                              installation("\"arkworks\",\"blst\"")));
    for (const auto &subset :
         {small, installation("\"arkworks\""), installation("\"blst\"")})
      refuses(selectImplementation(conversion, {}, subset),
              "cpu-target-unavailable");
    BindingApplication relayout{
        "table.relayout",
        {"bls12-381.fr", "arkworks.mle-lsb/0", "arkworks.mle-msb/0"},
        "arkworks/table.relayout"};
    take(resolveBinding(relayout, true));
    take(selectImplementation(relayout, {}, installation("\"arkworks\"")));
    refuses(selectImplementation(relayout, {}, small),
            "cpu-target-unavailable");
  });
  cases.run("field service draw layout is mandatory", [&] {
    accept(small.checkService("random.goldilocks.ext2-binomial7/0"));
    reject(empty.checkService("random.goldilocks.ext2-binomial7/0"));
    reject(small.checkService("random.bn254.fr/0"));
    reject(installation("\"blst\"").checkService("random.bls12-381.fr/0"));
  });
  cases.run("codec payload owner is independent of transcript challenge owner",
            [&] {
              BindingApplication observation{
                  "transcript.native.indexed.observe.data",
                  {"merlin3.koala-bear.ext8-binomial3.rejection31le/0",
                   "field:koala-bear"},
                  "plonky3/transcript.native.indexed.observe.data"};
              observation.physicalArguments =
                  take(defaultPhysicalArguments(observation));
              take(selectImplementation(observation, {}, small));
              observation.arguments[1] = "sequence<field:bls12-381.fr>";
              observation.physicalArguments =
                  take(defaultPhysicalArguments(observation));
              take(resolveBinding(observation, true));
              take(selectImplementation(
                  observation, {}, installation("\"plonky3\",\"arkworks\"")));
              refuses(selectImplementation(observation, {}, small),
                      "cpu-target-unavailable");
            });
  DialectRegistry registry;
  registerDialects(registry);
  cases.run("owned numerical compilation uses the genuine reduced target", [&] {
    RunOptions options;
    options.cpuTarget = small;
    auto compiled = take(
        compileRun(arithmetic("koala-bear"), "small.mlir", options, registry));
    require(compiled.bundle.find("plonky3/field.add") != std::string::npos,
            "small-field arithmetic not realized");
    refuses(compileRun(arithmetic("bls12-381.fr"), "omitted.mlir", options,
                       registry),
            "cpu-target-unavailable");
  });
  cases.run(
      "withholding preferred resident implementation uses canonical fallback",
      [&] {
        RunOptions options;
        options.cpuTarget = installation("\"arkworks\"");
        auto compiled =
            take(compileRun(scale(), "scale.mlir", options, registry));
        require(compiled.bundle.find("arkworks/curve.scale") !=
                        std::string::npos &&
                    compiled.bundle.find("blst/resident/") == std::string::npos,
                "omitted preferred provider survived fallback");
      });
  cases.run("reduced target synthesizes resident scale adapters", [&] {
    MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module = take(executableFixture(boundScale(), context));
    PhysicalPlanOptions options;
    options.cpuTarget = installation("\"arkworks\",\"blst\"");
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(plan.bindings.front().binding.application.implementation ==
                "blst/resident/curve.scale",
            "preferred resident scale was not selected");
    require(adapterDeclarations(plan, "representation.convert",
                                "native/representation.convert") == 3 &&
                conversionUses(plan, "representation.convert") == 3,
            "expected two resident imports and one canonical result export");
    unsigned imports = 0, exports = 0;
    for (const auto &operation : plan.operations)
      for (const auto &conversion : operation.conversions) {
        auto from = take(encodeBoundType(conversion.from, true));
        auto to = take(encodeBoundType(conversion.to, true));
        imports += StringRef(from.representation).starts_with("arkworks.") &&
                   StringRef(to.representation).starts_with("blst/");
        exports += StringRef(from.representation).starts_with("blst/") &&
                   StringRef(to.representation).starts_with("arkworks.");
      }
    require(imports == 2 && exports == 1, "canonical ABI crossings changed");
    publishAdapters(*module, plan, "representation.convert", 3, 3);
  });
  cases.run("Arkworks-only planner fallback has no resident crossings", [&] {
    MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module = take(executableFixture(boundScale(), context));
    PhysicalPlanOptions options;
    options.cpuTarget = installation("\"arkworks\"");
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(plan.bindings.front().binding.application.implementation ==
                    "arkworks/curve.scale" &&
                adapterDeclarations(plan, "representation.convert",
                                    "native/representation.convert") == 0 &&
                conversionUses(plan, "representation.convert") == 0,
            "canonical fallback acquired resident crossings");
    refuses(proposePhysical(*module, installedCandidates(),
                            {{"scale", "blst/resident/curve.scale"}}, options),
            "cpu-target-unavailable");
    publishAdapters(*module, plan, "representation.convert", 0, 0);
  });
  cases.run("Blst-only target cannot publish scale with canonical ABI", [&] {
    MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module = take(executableFixture(boundScale(), context));
    auto before = moduleToString(*module);
    PhysicalPlanOptions options;
    options.cpuTarget = installation("\"blst\"");
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "cpu-target-unavailable");
    require(moduleToString(*module) == before,
            "refusal published a physical plan");
  });
  cases.run(
      "missing scale adapters fall back but exact resident pins refuse", [&] {
        MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module = take(executableFixture(boundScale(), context));
        PhysicalPlanOptions options;
        options.cpuTarget = installation("\"arkworks\",\"blst\"");
        WithoutConversions catalog;
        auto plan = take(proposePhysical(*module, catalog, {}, options));
        require(
            plan.bindings.front().binding.application.implementation ==
                    "arkworks/curve.scale" &&
                conversionUses(plan, "representation.convert") == 0,
            "missing adapters did not advance the existing canonical fallback");
        take(validatePhysical(*module, plan, catalog));
        auto before = moduleToString(*module);
        refuses(proposePhysical(*module, catalog,
                                {{"scale", "blst/resident/curve.scale"}},
                                options),
                "binding-no-conversion");
        require(moduleToString(*module) == before,
                "refused pin changed logical input");
        publishAdapters(*module, plan, "representation.convert", 0, 0);
      });
  cases.run(
      "Arkworks-only target synthesizes both table relayout directions", [&] {
        MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module = take(executableFixture(tableLayouts(), context));
        PhysicalPlanOptions options;
        options.cpuTarget = installation("\"arkworks\"");
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(adapterDeclarations(plan, "table.relayout",
                                    "arkworks/table.relayout") == 2 &&
                    conversionUses(plan, "table.relayout") == 4,
                "table relayout declarations or per-use crossings changed");
        std::set<std::pair<std::string, std::string>> directions;
        for (const auto &binding : plan.bindings)
          if (binding.purpose == BindingPurpose::Conversion) {
            auto &application = binding.binding.application;
            require(application.arguments.size() == 3 &&
                        application.arguments[0] == "bls12-381.fr",
                    "generated relayout has wrong field or endpoints");
            directions.emplace(application.arguments[1],
                               application.arguments[2]);
          }
        require(directions ==
                    std::set<std::pair<std::string, std::string>>{
                        {"arkworks.mle-lsb/0", "arkworks.mle-msb/0"},
                        {"arkworks.mle-msb/0", "arkworks.mle-lsb/0"}},
                "generated table relayout is not bidirectional");
        auto invalid = plan;
        for (auto &binding : invalid.bindings)
          if (binding.purpose == BindingPurpose::Conversion)
            binding.binding.application.implementation = "test/table.relayout";
        refuses(validatePhysical(*module, invalid), "binding-conversion");
        publishAdapters(*module, plan, "table.relayout", 2, 4);
      });
  cases.run(
      "omitting Arkworks refuses table relayout without publication", [&] {
        MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module = take(executableFixture(tableLayouts(), context));
        auto before = moduleToString(*module);
        PhysicalPlanOptions options;
        options.cpuTarget = small;
        refuses(proposePhysical(*module, installedCandidates(), {}, options),
                "cpu-target-unavailable");
        require(moduleToString(*module) == before,
                "refusal published table relayout");
      });
  cases.run(
      "final validation rejects a withheld unused binding independently", [&] {
        MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto text = scopedFixture(R"(
"runtime.binding"() {sym_name="scale",contract="curve.scale",arguments=["bls12-381.g2"],implementation="",function_type=(!runtime.scope, !algebra.group<"bls12-381.g2">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.group<"bls12-381.g2">)>} : ()->()
)",
                                  "%x:i1", "%x", "i1", "i1",
                                  scopedReturn("%x", "i1"), 1);
        auto module = take(executableFixture(text, context));
        PhysicalPlanOptions options;
        options.cpuTarget = installation("\"arkworks\"");
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        take(validatePhysical(*module, plan));
        bool changed = false;
        for (auto &binding : plan.bindings)
          if (binding.binding.application.contract == "curve.scale") {
            binding.binding.application.implementation =
                "blst/resident/curve.scale";
            changed = true;
          }
        require(changed, "unused source binding disappeared");
        refuses(validatePhysical(*module, plan), "cpu-target-unavailable");
      });
  cases.run(
      "explicit ABI layouts require their selected owner without rewriting",
      [&] {
        MLIRContext context(registry);
        context.loadAllAvailableDialects();
        const std::string field = "!algebra.field<\"bls12-381.fr\">";
        auto text = scopedFixture("", "%x:" + field, "%x", field, field,
                                  scopedReturn("%x", field), 1);
        auto module = take(executableFixture(text, context));
        auto flow = take(ExecutionPorts::read(*module));
        PhysicalPlanOptions options;
        options.cpuTarget = installation("\"blst\"");
        for (auto *operation : flow.operations())
          if (flow.get(operation).callable &&
              !operation->hasAttr("runtime.region"))
            for (bool output : {false, true})
              options.functionPorts.push_back(
                  {operation->getAttrOfType<StringAttr>("sym_name")
                       .getValue()
                       .str(),
                   output, 0, "field:bls12-381.fr@blst/fr"});
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        take(validatePhysical(*module, plan));
        options.cpuTarget = installation("\"arkworks\"");
        refuses(proposePhysical(*module, installedCandidates(), {}, options),
                "cpu-target-unavailable");
        options.functionPorts.clear();
        options.cpuTarget = installation("\"blst\"");
        refuses(proposePhysical(*module, installedCandidates(), {}, options),
                "cpu-target-unavailable");
      });
  cases.run(
      "Host values and generic nested deployments receive the same target",
      [&] {
        language::EntryOptions options;
        options.cpuTarget = small;
        for (StringRef field : {"koala-bear", "bls12-381.fr"}) {
          std::string source =
              "module sample; domain Fr=field(\"" + field.str() + R"(");
        protocol Work<F:Field> roles(P)(x:F@P)->(value:F@P){return(value=x);}
        entry fn Demo(inputs:Work<Fr>::Inputs){return Work<Fr>::run(inputs);})";
          auto checked = original(source);
          if (field == "koala-bear")
            take(language::compileEntry(checked, options));
          else
            refuses(language::compileEntry(checked, options),
                    "cpu-target-unavailable");
        }
        auto passthrough =
            original(R"(module sample; domain Fr=field("bls12-381.fr");
      entry fn Demo(x:Fr)->Fr{return x;})");
        refuses(language::compileEntry(passthrough, options),
                "cpu-target-unavailable");
      });
  cases.run(
      "Host numerical refusal retains structured target diagnostics", [&] {
        auto checked = original(R"(module sample;
domain Fr=field("bls12-381.fr");
fn from_index<F:Field>(value:index)->F=primitive("field.from_index");
fn hidden(x:index)->bool { let a=from_index<Fr>(x); return a==0; }
entry fn Demo(x:index)->bool { return hidden(x); })");
        take(language::compileEntry(checked));
        language::EntryOptions options;
        options.cpuTarget = small;
        auto compiled = language::compileEntry(checked, options);
        require(!compiled, "excluded numerical provider compiled");
        bool preserved = false;
        auto remaining = handleErrors(
            compiled.takeError(), [&](const CompilationError &error) {
              preserved =
                  any_of(error.refusals,
                         [](const auto &refusal) {
                           return refusal.code == "cpu-target-unavailable";
                         }) &&
                  any_of(error.locations, [](const auto &location) {
                    return location.filename == "sample.zkc" &&
                           location.line == 5;
                  });
            });
        if (remaining)
          throw std::runtime_error(toString(std::move(remaining)));
        require(preserved,
                "numerical lowering lost refusal metadata or source");
      });
  for (StringRef field : {"koala-bear", "bls12-381.fr"})
    cases.run("generic Host call reaches internal-field child: " + field, [&] {
      auto checked = original(internalFieldDeployment(field));
      auto baseline = take(language::compileEntry(checked));
      auto artifact = take(json::parse(baseline.bytes()));
      auto &host = *artifact.getAsObject();
      require(host.getString("format") == "zkc.host/0" &&
                  host.getArray("functions")->size() == 2 &&
                  host.getArray("deployments")->size() == 1,
              "fixture lost the Host-to-Host call or protocol deployment");
      auto deployment =
          *host.getArray("deployments")->front().getAsObject()->getString("id");
      StringRef relay;
      for (const auto &function : *host.getArray("functions")) {
        auto &signature = *function.getAsObject()->getObject("signature");
        std::set<std::string> leaves;
        auto checkSchema = [&](const json::Value &schema) {
          for (const auto &leaf : *schema.getAsObject()->getArray("leaves")) {
            auto type = leaf.getAsString();
            require(type == "index" || type == "bool",
                    "outer Host ports expose nongeneric data");
            leaves.insert(type->str());
          }
        };
        for (const auto &parameter : *signature.getArray("parameters"))
          checkSchema(*parameter.getAsObject()->get("schema"));
        checkSchema(*signature.get("result"));
        require(leaves == std::set<std::string>{"index", "bool"},
                "outer Host ports lost their generic index/bool layouts");
        auto symbol = *signature.getString("symbol");
        if (symbol != host.getString("entry"))
          relay = symbol;
      }
      bool callsRelay = false, invokesChild = false;
      for (const auto &function : *host.getArray("functions")) {
        auto &f = *function.getAsObject();
        bool root = f.getObject("signature")->getString("symbol") ==
                    host.getString("entry");
        for (const auto &operation :
             *f.getObject("body")->getArray("operations")) {
          auto &op = *operation.getAsObject();
          callsRelay |= root && op.getString("op") == "call" &&
                        op.getString("callee") == relay;
          invokesChild |= !root && op.getString("op") == "invoke" &&
                          op.getString("deployment") == deployment;
        }
      }
      require(!relay.empty() && callsRelay && invokesChild,
              "fixture lost the Host call before protocol deployment");
      CompilationObservation observations;
      language::EntryOptions options;
      options.cpuTarget = small;
      options.observations = &observations;
      if (field == "koala-bear") {
        auto compiled = take(language::compileEntry(checked, options));
        require(compiled.bytes().contains("plonky3/field.from_index"),
                "internal supported field was not lowered in the child");
      } else
        refuses(language::compileEntry(checked, options),
                "cpu-target-unavailable");
      reachedDeployment(observations, deployment);
    });
  return cases.result();
}
