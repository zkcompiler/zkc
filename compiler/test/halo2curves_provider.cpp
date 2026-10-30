#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeBindings.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/ScopedFixture.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"

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
void flatLayouts(MLIRContext &context) {
  for (StringRef spelling : {"field:bn254.fr@halo2curves-axiom/bn254.fr",
                             "vector:bn254.fr@halo2curves-axiom/bn254.fr",
                             "group:bn254.g1@halo2curves-axiom/bn254.g1",
                             "groups:bn254.g1@halo2curves-axiom/bn254.g1",
                             "group:bn254.g2@halo2curves-axiom/bn254.g2",
                             "groups:bn254.g2@halo2curves-axiom/bn254.g2"}) {
    auto resident = take(parseBoundType(spelling, true));
    auto logical = erasePhysicalType(resident);
    auto canonical = take(defaultRepresentation(logical));
    require(nativeMessageData(resident), "resident canonical codec permission");
    for (bool reverse : {false, true}) {
      auto from = reverse ? resident : canonical;
      auto to = reverse ? canonical : resident;
      auto source = nativeType(context, from), target = nativeType(context, to);
      auto candidates = installedCandidates().conversions(source, target);
      require(candidates.size() == 1, "exact direct conversion candidate");
      accept(checkDirectConversion(candidates.front(), source, target));
      auto signature = take(resolveNativeApplication(candidates.front()));
      require(signature == FunctionType::get(&context, {source}, {target}),
              "exact conversion signature");
      candidates.front().valueType =
          FunctionType::get(&context, {source}, {source});
      refuses(resolveNativeApplication(candidates.front()),
              "binding-conversion");
    }
  }
  for (StringRef spelling :
       {"field:bls12-381.fr@halo2curves-axiom/bn254.fr",
        "field:bn254.fr@blst/fr", "group:bn254.gt@halo2curves-axiom/bn254.g1",
        "matrix:bn254.fr@halo2curves-axiom/bn254.fr"}) {
    auto parsed = parseBoundType(spelling, true);
    require(!parsed, "unsupported physical leaf admitted");
    consumeError(parsed.takeError());
  }
}
void inventory(MLIRContext &context) {
  const auto &catalog = installedImplementations();
  // Independently enumerated expected operations and domains.
  for (StringRef contract : {"field.constant",    "field.from_index",
                             "field.add",         "field.sub",
                             "field.neg",         "field.mul",
                             "field.inverse",     "field.equal",
                             "vector.empty",      "vector.constant",
                             "vector.splat",      "vector.append",
                             "vector.at",         "vector.get",
                             "vector.length",     "vector.length_check",
                             "vector.add",        "vector.sub",
                             "vector.mul",        "vector.dot",
                             "vector.scale",      "vector.sum",
                             "vector.product",    "vector.split",
                             "vector.concat",     "vector.slice",
                             "vector.equal",      "curve.generator",
                             "curve.identity",    "curve.add",
                             "curve.neg",         "curve.equal",
                             "curve.nonidentity", "curve.scale",
                             "curve.empty",       "curve.append",
                             "curve.at",          "curve.get",
                             "curve.length",      "curve.vector_add",
                             "curve.scale_each",  "curve.vector_scale",
                             "curve.split",       "curve.concat",
                             "curve.msm",         "pairing.check"}) {
    std::vector<std::string> domains =
        contract.starts_with("curve.")
            ? std::vector<std::string>{"bn254.g1", "bn254.g2"}
            : std::vector<std::string>{"bn254.fr"};
    auto name = ("halo2curves-axiom/resident/" + contract).str();
    auto *entry = catalog.find(contract, name);
    require(entry && entry->requiresExplicitSelection &&
                catalog.preferred(contract, "halo2curves-axiom") == entry,
            "explicit provider operation inventory");
    for (auto &domain : domains) {
      BindingApplication application{contract.str(), {domain}, name};
      auto signature = take(resolveBinding(application, true));
      for (const auto *ports : {&signature.inputs, &signature.outputs})
        for (const auto &port : *ports) {
          if (port.kind == "bool" || port.kind == "index" ||
              port.kind == "indices")
            continue;
          require(port.representation == "halo2curves-axiom/" + port.identity,
                  "positive exact physical ports");
        }
      application.implementation.clear();
      require(take(defaultImplementation(application)) ==
                  ("arkworks/" + contract).str(),
              "canonical default changed");
      require(take(installedCandidates().implementations(
                  nativeRequest(context, application))) ==
                  std::vector<std::string>{("arkworks/" + contract).str()},
              "alternative became automatic");
      application.implementation = name;
      application.arguments = {domain == "bn254.g1"   ? "bls12-381.g1"
                               : domain == "bn254.g2" ? "bls12-381.g2"
                                                      : "bls12-381.fr"};
      refuses(resolveBinding(application, true), "binding-implementation");
    }
  }
  for (StringRef contract :
       {"pairing.apply", "poly.fft", "matrix.mul_vector", "vector.powers"})
    require(!catalog.find(contract,
                          ("halo2curves-axiom/resident/" + contract).str()),
            "unsupported operation installed from a field match");
  refuses(resolveBinding({"curve.scale",
                          {"bn254.gt"},
                          "halo2curves-axiom/resident/curve.scale"},
                         true),
          "binding-implementation");
}

// Ordinary .zkc source enters the existing checked original pipeline. Exact
// implementation requests exercise provider selection without changing its ABI.
const char *scalarSource = R"(module m;
domain Fr=field("bn254.fr");domain G=group("bn254.g1");
fn work(g:G,s:Fr)->G {
  let t=kernel<Fr>("field.add",s,s);
  let a=kernel<G>("curve.scale",g,t);
  let b=kernel<G>("curve.scale",a,t);
  return kernel<G>("curve.neg",b);
}
protocol Demo roles(P)(g:G@P,s:Fr@P)->(r:G@P){return work(g,s);}
)";
const char *bulkSource = R"(module m;
domain Fr=field("bn254.fr");
domain G1=group("bn254.g1");domain G2=group("bn254.g2");
type Vector<F:Field>=builtin("vector",F);
type Groups<G:Group>=builtin("groups",G);
fn work(s:Vector<Fr>,a:Groups<G1>,b:Groups<G2>)->bool {
  let t=kernel<Fr>("vector.add",s,s);
  let x=kernel<G1>("curve.msm",t,a);
  let y=kernel<G2>("curve.msm",t,b);
  let left=kernel<G1>("curve.append",kernel<G1>("curve.empty"),x);
  let right=kernel<G2>("curve.append",kernel<G2>("curve.empty"),y);
  return kernel<Fr>("pairing.check",left,right);
}
protocol Demo roles(P)(s:Vector<Fr>@P,a:Groups<G1>@P,b:Groups<G2>@P)->(r:bool@P){
  return work(s,a,b);
}
)";
program::Participants sourceProgram(MLIRContext &context, StringRef source,
                                    bool residentPorts, bool mixedProvider) {
  auto captured =
      take(language::capture({{"m", source.str(), "bn254-provider.zkc"}}));
  auto project = take(language::analyze(captured).checkedProject());
  auto closed = take(closeNativeRun(project, "m::Demo"));
  auto original = take(language::emitOriginal(closed, context));
  auto module = take(executableFixture(original, context));
  SmallVector<std::pair<std::string, std::string>> selections;
  module->walk([&](runtime::BindingOp binding) {
    auto contract = binding->getAttrOfType<StringAttr>("contract").getValue();
    auto *entry =
        installedImplementations().preferred(contract, "halo2curves-axiom");
    if (entry && (!mixedProvider || contract != "curve.neg"))
      selections.emplace_back(
          binding->getAttrOfType<StringAttr>("sym_name").getValue().str(),
          entry->identity);
  });
  require(!selections.empty(), "source operation bindings missing");
  PhysicalPlanOptions options;
  if (residentPorts) {
    auto ports = take(ExecutionPorts::read(*module));
    for (auto *operation : ports.operations()) {
      auto type = ports.get(operation).callable;
      if (!type)
        continue;
      auto name = SymbolTable::getSymbolName(operation);
      require(bool(name), "callable physical ports require a named owner");
      for (bool output : {false, true})
        for (auto [index, port] :
             enumerate(output ? type.getResults() : type.getInputs())) {
          auto logical = take(encodeBoundType(port, false));
          if (logical.kind == "field" || logical.kind == "vector" ||
              logical.kind == "group" || logical.kind == "groups")
            options.functionPorts.push_back(
                {name.getValue().str(), output, unsigned(index),
                 logical.spelling() + "@halo2curves-axiom/" +
                     logical.identity});
        }
    }
  }
  auto plan = take(
      proposePhysical(*module, installedCandidates(), selections, options));
  size_t conversions = 0;
  for (const auto &operation : plan.operations)
    conversions += operation.conversions.size();
  require((residentPorts && !mixedProvider) ? conversions == 0
                                            : conversions > 0,
          "source conversion retention");
  auto checked = take(validatePhysical(*module, plan));
  accept(materializePhysical(*module, checked));
  require(succeeded(verify(*module)), "source physical program rejected");
  return take(readExecutionModel(*module));
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  if (argc == 3 && StringRef(argv[1]) == "--emit") {
    StringRef mode(argv[2]);
    if (mode != "canonical" && mode != "resident" && mode != "mixed" &&
        mode != "g2-canonical" && mode != "g2-resident" &&
        mode != "bulk-canonical" && mode != "bulk-resident")
      return 2;
    try {
      auto source =
          StringRef(mode.starts_with("bulk-") ? bulkSource : scalarSource)
              .str();
      if (mode.starts_with("g2-"))
        source = replaceText(source, "bn254.g1", "bn254.g2");
      outs() << printJson(program::encode(
                    sourceProgram(context, source, mode.ends_with("resident"),
                                  mode == "mixed")))
             << '\n';
      return 0;
    } catch (const std::exception &failure) {
      errs() << failure.what() << '\n';
      return 1;
    }
  }
  if (argc != 1)
    return 2;
  Cases cases;
  cases.run("flat layout and codec ownership", [&] { flatLayouts(context); });
  cases.run("finite exact operation inventory", [&] { inventory(context); });
  for (auto domain : {"bn254.g1", "bn254.g2"})
    for (bool resident : {false, true})
      cases.run(Twine(resident ? "retained source ports: "
                               : "canonical source ports: ") +
                    domain,
                [&] {
                  (void)sourceProgram(
                      context, replaceText(scalarSource, "bn254.g1", domain),
                      resident, false);
                });
  for (bool resident : {false, true})
    cases.run(
        resident ? "retained source bulk and pairing"
                 : "canonical source bulk and pairing",
        [&] { (void)sourceProgram(context, bulkSource, resident, false); });
  cases.run("mixed source providers",
            [&] { (void)sourceProgram(context, scalarSource, false, true); });
  return cases.result();
}
