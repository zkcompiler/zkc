#include "Names.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Execution.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
namespace {
unsigned checks = 0;
void check(bool condition, StringRef message) {
  ++checks;
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
void accept(Error error) {
  if (error) {
    errs() << toString(std::move(error)) << '\n';
    std::exit(1);
  }
  ++checks;
}
// The identifier leads the message; compare it whole, so a longer identifier
// that merely contains the expected one is a failure.
void reject(Error error, StringRef code) {
  std::string message = toString(std::move(error));
  if (StringRef(message).split(':').first.trim() != code)
    errs() << "expected " << code << ", got " << message << '\n';
  check(StringRef(message).split(':').first.trim() == code,
        "expected refusal identifier");
}
std::string variant(protocol::VariantDescriptor descriptor) {
  auto value = protocol::encodeVariant(descriptor);
  check(bool(value), "valid descriptor rejected");
  return *value;
}
template <typename T> source::Instruction ins(std::string site, T value) {
  return {{}, std::move(site), std::move(value)};
}
source::Module sample(const std::string &type) {
  source::Function f;
  f.name = "Choose";
  f.origin = source::LogicalOrigin{"Choose", {}};
  f.arguments = {{"x", "bool"}};
  f.results = {"bool"};
  f.body = source::Body{
      ins("pack", source::VariantConstruct{type, "Ok", {"x"}, "sum"}),
      ins("match",
          source::Match{
              "sum",
              {"x"},
              {{"Ok", {"payload"}, {ins("", source::Yield{{"payload"}})}},
               {"Err", {}, {ins("terminal", source::Stop{"", "exhausted"})}}},
              {"result"}}),
      ins("", source::Return{{"result"}})};
  source::Protocol p;
  p.name = "Demo";
  p.roles = {"Alice"};
  p.arguments = {{"x", "Alice", "bool"}};
  p.results = {{"Alice", "bool"}};
  p.body = source::Body{
      ins("choose", source::LocalCall{"Alice", "Choose", {"x"}, {"r"}}),
      ins("", source::Return{{"r"}})};
  source::Module m;
  m.functions = {f};
  m.protocols = {p};
  m.instances = {{{}, "demo", "Demo", {}, {}, {{"Alice", "Alice"}}}};
  m.entries = {{{}, "main", "demo"}};
  return m;
}
} // namespace
int main() {
  std::string type =
      variant({"lib.Result<T=bool>", {{"Ok", {"bool"}}, {"Err", {}}}});
  auto descriptor = protocol::decodeVariant(type);
  check(descriptor && descriptor->nominal == "lib.Result<T=bool>",
        "nominal roundtrip");
  check(protocol::duplicable(type) && protocol::discardable(type) &&
            !protocol::serializable(type),
        "local copy/drop properties");
  std::string affine = variant(
      {"GuardResult", {{"Guard", {"resource_unit:Guard"}}, {"Empty", {}}}});
  check(!protocol::duplicable(affine) && protocol::discardable(affine) &&
            protocol::affine(affine),
        "all-arm permission conjunction");
  auto nested = variant({"Nested", {{"Some", {affine}}, {"None", {}}}});
  check(!protocol::duplicable(nested) && !protocol::serializable(nested),
        "nested permissions");
  auto privateType = variant(
      {"Private",
       {{"Key", {"prover_key:multilinear.kzg.bls12-381/1"}}, {"Empty", {}}}});
  check(protocol::duplicable(privateType) &&
            !protocol::serializable(privateType),
        "private immutable custody");
  auto spelling = [](StringRef json) { return "variant:" + toHex(json, true); };
  auto padded = fromHex(StringRef(type).drop_front(8));
  padded.insert(1, " ");
  // The accepted descriptor under a raised version name, and nothing else
  // changed, so only the version check can refuse it.
  auto raised = fromHex(StringRef(type).drop_front(8));
  raised.replace(raised.find("zkc.variant/1"), 13, "zkc.variant/2");
  for (
      const auto &bad : std::vector<std::string>{
          "variant:", type + "00", spelling(padded), spelling(raised),
          // Canonical graphs with invalid semantic roots: no arms, duplicate
          // alternatives, an unknown logical leaf and a physical payload.
          spelling(R"(["zkc.variant/1",["X",[],["0","1"]]])"),
          spelling(
              R"(["zkc.variant/1",["X","A",[],["1","2"],["3","3"],["0","4"]]])"),
          spelling(
              R"(["zkc.variant/1",["X","A","no_type",["2"],["1","3"],["4"],["0","5"]]])"),
          spelling(
              R"(["zkc.variant/1",["X","A","bool@native.bool/1",["2"],["1","3"],["4"],["0","5"]]])")}) {
    check(!protocol::decodeVariant(bad), "malformed descriptor accepted");
    check(!protocol::duplicable(bad) && !protocol::discardable(bad),
          "malformed permissions admitted");
  }
  check(!protocol::decodeVariant(type + "@logical.variant/1"),
        "logical parser accepts physical variant");
  auto upper = type;
  for (size_t i = 8; i < upper.size(); ++i)
    upper[i] = llvm::toUpper(upper[i]);
  check(!protocol::decodeVariant(upper), "uppercase hex accepted");
  check(
      !protocol::encodeVariant(
          {std::string(protocol::VariantSpellingBytes + 1, 'x'), {{"A", {}}}}),
      "nominal limit");
  std::vector<protocol::VariantAlternative> manyArms;
  for (unsigned i = 0; i < 32; ++i)
    manyArms.push_back({"A" + std::to_string(i), {}});
  check(bool(protocol::encodeVariant({"X", manyArms})), "arm limit control");
  manyArms.push_back({"A32", {}});
  check(!protocol::encodeVariant({"X", manyArms}), "arm limit");
  auto bound = take(protocol::parseBoundType(type, false));
  auto physical = take(protocol::defaultRepresentation(bound));
  check(physical.spelling() == type + "@logical.variant/1",
        "fixed representation");
  auto longType = variant({std::string(16384, 'x'), {{"Some", {"bool"}}}});
  check(longType.size() > 4096, "large exact nominal fixture");
  auto largePhysical = take(protocol::defaultRepresentation(
      take(protocol::parseBoundType(longType, false))));
  check(largePhysical.spelling() == longType + "@logical.variant/1",
        "physical suffix has a separate bound");
  auto wrongRep = protocol::parseBoundType(type + "@native.bool/1", true);
  check(!wrongRep, "variant arbitrary representation accepted");
  reject(wrongRep.takeError(), "binding-representation");

  auto module = sample(type);
  accept(protocol::admit(module, true));
  auto encoded = source::encode(module);
  auto decoded = take(source::decode(take(parseJson(printJson(encoded)))));
  check(printJson(source::encode(decoded)) == printJson(encoded),
        "serialized source roundtrip");
  accept(protocol::admit(decoded, true));
  unsigned walked = 0;
  source::walk(*module.functions[0].body, [&](const auto &) { ++walked; });
  check(walked == 5, "match traversal excludes arm bodies");
  auto bad = module;
  (*bad.functions[0].body)[0].get<source::VariantConstruct>()->alternative =
      "Missing";
  reject(protocol::admit(bad, true), "variant-alternative");
  bad = module;
  (*bad.functions[0].body)[0].get<source::VariantConstruct>()->payload.clear();
  reject(protocol::admit(bad, true), "variant-payload");
  bad = module;
  (*bad.functions[0].body)[1].get<source::Match>()->arms.pop_back();
  reject(protocol::admit(bad, true), "local-match-arms");
  bad = module;
  (*bad.functions[0].body)[1].get<source::Match>()->arms[1].alternative = "Ok";
  reject(protocol::admit(bad, true), "local-match-arm");
  bad = module;
  (*bad.functions[0].body)[1].get<source::Match>()->captures.clear();
  (*bad.functions[0].body)[1].get<source::Match>()->arms[0].body = {
      ins("", source::Yield{{"x"}})};
  reject(protocol::admit(bad, true), "interactive-unavailable");
  bad = module;
  bad.protocols[0].arguments[0].type = type;
  reject(protocol::admit(bad, true), "variant-boundary");
  bad = module;
  (*bad.functions[0].body)[1].get<source::Match>()->arms[1].body = {
      ins("forbidden", source::Message{"tag", "Alice", "Bob", "x", "leak"}),
      ins("", source::Yield{{"x"}})};
  reject(protocol::admit(bad, true), "interactive-instruction");

  bad = module;
  bad.bindings.push_back({{}, "both", {"bool.and", {}, ""}});
  bad.functions[0].body->insert(
      bad.functions[0].body->begin() + 1,
      ins("raw",
          source::Operation{"both", {}, {}, {"sum", "sum"}, {"raw_result"}}));
  reject(protocol::admit(bad, true), "binding-operation-signature");
  auto trace = source::inspectExecution(module, "main");
  check(!trace, "static execution silently admitted local variant control");
  reject(trace.takeError(), "execution-local-control-static-trace");
  auto affineModule = sample(affine);
  affineModule.functions[0].arguments[0].type = "resource_unit:Guard";
  affineModule.functions[0].results = {"resource_unit:Guard"};
  affineModule.protocols[0].arguments[0].type = "resource_unit:Guard";
  affineModule.protocols[0].results[0].type = "resource_unit:Guard";
  auto &affineBody = *affineModule.functions[0].body;
  affineBody[0].get<source::VariantConstruct>()->alternative = "Guard";
  auto *affineMatch = affineBody[1].get<source::Match>();
  affineMatch->captures.clear();
  affineMatch->arms[0].alternative = "Guard";
  affineMatch->arms[1].alternative = "Empty";
  accept(protocol::admit(affineModule, true));
  bad = affineModule;
  bad.functions[0].body->insert(
      bad.functions[0].body->begin() + 1,
      ins("reuse",
          source::VariantConstruct{affine, "Guard", {"x"}, "duplicate"}));
  reject(protocol::admit(bad, true), "interactive-resource-reuse");
  bad = affineModule;
  (*bad.functions[0].body)[1].get<source::Match>()->captures = {"sum"};
  reject(protocol::admit(bad, true), "interactive-resource-reuse");
  auto rngType =
      variant({"RngResult", {{"Some", {"rng:bls12-381.fr"}}, {"None", {}}}});
  check(!protocol::discardable(rngType),
        "inactive rng permits dropping variant");
  bad = module;
  bad.functions[0].body = source::Body{
      ins("empty", source::VariantConstruct{rngType, "None", {}, "resource"}),
      ins("", source::Return{{"x"}})};
  accept(protocol::admit(bad, true));
  // Distinct nominal identities remain unequal even with identical layouts.
  auto other = variant({"Other", {{"Ok", {"bool"}}, {"Err", {}}}});
  bad = module;
  bad.functions[0].results = {other};
  bad.functions[0].body = source::Body{
      ins("make", source::VariantConstruct{type, "Ok", {"x"}, "sum"}),
      ins("", source::Return{{"sum"}})};
  reject(protocol::admit(bad, true), "function-return-types");

  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto native = take(protocol::importModule(module, context));
  check(succeeded(mlir::verify(*native)), "native MLIR verify");
  native->walk([&](LocalMatchOp match) {
    auto edge = mlir::RegionSuccessor(&match.getRegion(0));
    check(match.getEntrySuccessorOperands(edge).size() == 1 &&
              match.getSuccessorInputs(edge).size() == 1 &&
              match.getSuccessorInputs(edge)[0] ==
                  match.getRegion(0).front().getArgument(1),
          "RegionBranch must forward captures only");
  });
  std::string mlirText;
  raw_string_ostream stream(mlirText);
  native->print(stream);
  auto parsed = mlir::parseSourceString<mlir::ModuleOp>(mlirText, &context);
  check(bool(parsed), "serialized MLIR roundtrip");
  accept(protocol::admit(take(protocol::exportSource(*parsed)), true));
  {
    // The verifier's refusal is read back, so the check names the rule it
    // meant rather than accepting any failure.
    std::string said;
    mlir::ScopedDiagnosticHandler capture(&context,
                                          [&](mlir::Diagnostic &diagnostic) {
                                            said += diagnostic.str() + "\n";
                                            return mlir::success();
                                          });
    mlir::OwningOpRef<mlir::ModuleOp> malformed(
        mlir::cast<mlir::ModuleOp>(native->clone()));
    malformed->walk(
        [&](VariantInjectOp pack) { pack.setAlternative("Unknown"); });
    check(failed(mlir::verify(*malformed)) &&
              namesIdentifier(said, "variant-alternative"),
          "native unknown alternative admitted");
    auto exported = protocol::exportSource(*malformed);
    check(!exported, "native malformed export admitted");
    reject(exported.takeError(), "interactive-malformed-ir");
    // The payload-free arm given a payload its alternative does not carry.
    // Its yield still forwards the capture, so only the arm's payload rule
    // can refuse it.
    malformed = mlir::cast<mlir::ModuleOp>(native->clone());
    malformed->walk([&](LocalMatchOp match) {
      match.getRegion(1).front().insertArgument(
          0u, mlir::IntegerType::get(&context, 64, mlir::IntegerType::Unsigned),
          match.getLoc());
    });
    said.clear();
    check(failed(mlir::verify(*malformed)) &&
              namesIdentifier(said, "local-control-arguments"),
          ("native arm payload admitted: " + said).c_str());
  }
  auto expanded = take(protocol::expandAlgorithms(module, context));
  accept(protocol::admit(expanded.source, true));
  auto projected = take(protocol::project(*native));
  check(
      succeeded(protocol::lowerPhysical(*projected, {}, false, nullptr, true)),
      "physical variant and last-use storage");
  auto final = take(protocol::exportSource(*projected));
  accept(protocol::admit(final, true));
  auto reimported = take(protocol::importModule(
      take(source::decode(take(parseJson(printJson(source::encode(final)))))),
      context));
  check(succeeded(mlir::verify(*reimported)), "physical source reimport");
  auto affineNative = take(protocol::importModule(affineModule, context));
  auto affineProjected = take(protocol::project(*affineNative));
  check(succeeded(protocol::lowerPhysical(*affineProjected, {}, false, nullptr,
                                          true)),
        "affine active payload physical lowering");
  accept(protocol::admit(take(protocol::exportSource(*affineProjected)), true));
  // A callee stop terminates the caller arm; no yield/result is manufactured.
  auto stopModule = module;
  source::Function stopFunction;
  stopFunction.name = "Stop";
  stopFunction.origin = source::LogicalOrigin{"Stop", {}};
  stopFunction.results = {"bool"};
  stopFunction.body = source::Body{ins("stop", source::Stop{"", "refused"})};
  stopModule.functions.push_back(stopFunction);
  auto &stoppedArm =
      (*stopModule.functions[0].body)[1].get<source::Match>()->arms[1];
  stoppedArm.body = {
      ins("callstop", source::AlgorithmCall{"Stop", {}, {"never"}}),
      ins("", source::Yield{{"never"}})};
  auto stopped = take(protocol::expandAlgorithms(stopModule, context));
  auto *expandedMatch =
      (*stopped.source.functions[0].body)[1].get<source::Match>();
  check(expandedMatch && expandedMatch->arms[1].body.size() == 1 &&
            expandedMatch->arms[1].body[0].get<source::Stop>(),
        "inlined stop continued to yield");
  auto allStop = stopModule;
  (*allStop.functions[0].body)[1].get<source::Match>()->arms[0].body =
      stoppedArm.body;
  (*allStop.functions[0].body)[1].get<source::Match>()->arms[0].body[0].site =
      "other_stop";
  accept(protocol::admit(allStop, true));
  std::string stopDiagnostic;
  {
    mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
      raw_string_ostream out(stopDiagnostic);
      d.print(out);
      return mlir::success();
    });
    auto refused = protocol::expandAlgorithms(allStop, context);
    check(!refused, "all-stopping specialization retained undefined results");
    consumeError(refused.takeError());
  }
  check(StringRef(stopDiagnostic).contains("algorithm-terminal-results"),
        "all-stopping expansion must diagnose the control operation");
  auto nestedModule = sample(type);
  auto wrapper = variant({"Wrapper", {{"Wrapped", {type}}}});
  source::Match innerMatch{
      "inner",
      {},
      {{"Ok", {"payload"}, {ins("", source::Yield{{"payload"}})}},
       {"Err", {}, {ins("nested_stop", source::Stop{"", "abort"})}}},
      {"inner_result"}};
  nestedModule.functions[0].body = source::Body{
      ins("inner_pack", source::VariantConstruct{type, "Ok", {"x"}, "value"}),
      ins("outer_pack",
          source::VariantConstruct{wrapper, "Wrapped", {"value"}, "wrapped"}),
      ins("outer_match",
          source::Match{"wrapped",
                        {},
                        {{"Wrapped",
                          {"inner"},
                          {ins("inner_match", innerMatch),
                           ins("", source::Yield{{"inner_result"}})}}},
                        {"result"}}),
      ins("", source::Return{{"result"}})};
  auto nestedNative = take(protocol::importModule(nestedModule, context));
  auto nestedProjected = take(protocol::project(*nestedNative));
  check(succeeded(protocol::lowerPhysical(*nestedProjected, {}, false, nullptr,
                                          true)),
        "nested active variant physical lowering");
  accept(protocol::admit(take(protocol::exportSource(*nestedProjected)), true));
  auto emptyModule = module;
  auto &emptyBody = *emptyModule.functions[0].body;
  *emptyBody[0].get<source::VariantConstruct>() = {type, "Err", {}, "sum"};
  emptyBody[1].get<source::Match>()->arms[1].body = {
      ins("", source::Yield{{"x"}})};
  auto emptyNative = take(protocol::importModule(emptyModule, context));
  auto emptyProjected = take(protocol::project(*emptyNative));
  check(succeeded(
            protocol::lowerPhysical(*emptyProjected, {}, false, nullptr, true)),
        "zero active payload physical lowering");
  accept(protocol::admit(take(protocol::exportSource(*emptyProjected)), true));
  bad = module;
  bad.functions[0].arguments[0].type = "rng:bls12-381.fr";
  bad.functions[0].results.clear();
  bad.functions[0].body = source::Body{
      ins("rng_pack",
          source::VariantConstruct{rngType, "Some", {"x"}, "resource"}),
      ins("rng_match",
          source::Match{"resource",
                        {},
                        {{"Some", {"payload"}, {ins("", source::Yield{})}},
                         {"None", {}, {ins("", source::Yield{})}}},
                        {}}),
      ins("", source::Return{})};
  // Portable control is affine, as it was before variants. The stronger
  // checked-library drop permission is established by source checking, not
  // inferred from whether a portable body happens to contain a sum.
  bad.protocols.clear();
  bad.instances.clear();
  bad.entries.clear();
  accept(protocol::admit(bad, false));
  bad.functions[0].body = source::Body{ins("", source::Return{})};
  accept(protocol::admit(bad, false));
  auto challenged = module;
  challenged.protocols.clear();
  challenged.instances.clear();
  challenged.entries.clear();
  challenged.bindings.push_back(
      {{},
       "draw",
       {"transcript.challenge", {"merlin3.bls12-381.fr64be/1"}, ""}});
  const std::string transcript = "transcript:merlin3.bls12-381.fr64be/1";
  auto &challengeFunction = challenged.functions[0];
  challengeFunction.arguments.push_back({"t", transcript});
  challengeFunction.results = {"field:bls12-381.fr", transcript};
  auto &challengeBody = *challengeFunction.body;
  auto *challengeMatch = challengeBody[1].get<source::Match>();
  challengeMatch->captures = {"t"};
  challengeMatch->outputs = {"result", "next"};
  challengeMatch->arms[0].body = {
      ins("draw", source::Operation{"draw", {}, {}, {"t"}, {"f", "nt"}}),
      ins("", source::Yield{{"f", "nt"}})};
  challengeBody[2] = ins("", source::Return{{"result", "next"}});
  reject(protocol::admit(challenged, false), "local-match-challenge");
  source::Function drawHelper;
  drawHelper.name = "Draw";
  drawHelper.origin = source::LogicalOrigin{"Draw", {}};
  drawHelper.arguments = {{"t", transcript}};
  drawHelper.results = {"field:bls12-381.fr", transcript};
  drawHelper.body = source::Body{
      ins("draw", source::Operation{"draw", {}, {}, {"t"}, {"f", "nt"}}),
      ins("", source::Return{{"f", "nt"}})};
  challengeMatch->arms[0].body[0] =
      ins("draw_helper", source::AlgorithmCall{"Draw", {"t"}, {"f", "nt"}});
  challenged.functions.push_back(drawHelper);
  reject(protocol::admit(challenged, false), "local-match-challenge");
  for (bool helper : {false, true}) {
    auto observed = challenged;
    observed.bindings[0].application.contract = "transcript.observe.bool";
    observed.bindings[0].application.arguments.push_back("zkcv.bool/1");
    auto &fn = observed.functions[0];
    fn.results = {transcript};
    auto *match = (*fn.body)[1].get<source::Match>();
    match->captures = {"t", "x"};
    match->outputs = {"next"};
    source::Operation observe{
        "draw", {}, {"a", "b", "c", "d", "e"}, {"t", "x"}, {"nt"}};
    match->arms[0].body = {ins("observe", observe),
                           ins("", source::Yield{{"nt"}})};
    (*fn.body)[2] = ins("", source::Return{{"next"}});
    if (helper) {
      auto &helperFn = observed.functions[1];
      helperFn.arguments.push_back({"x", "bool"});
      helperFn.results = {transcript};
      helperFn.body = source::Body{ins("observe", observe),
                                   ins("", source::Return{{"nt"}})};
      match->arms[0].body[0] = ins(
          "observe_helper", source::AlgorithmCall{"Draw", {"t", "x"}, {"nt"}});
    }
    reject(protocol::admit(observed, false), "local-match-challenge");
  }
  for (const char *contract :
       {"external.openvm.observe", "external.openvm.sample",
        "external.openvm.sample_ext", "external.openvm.sample_bits",
        "external.openvm.check_witness", "external.monero.update"}) {
    auto external = module;
    external.protocols.clear();
    external.instances.clear();
    external.entries.clear();
    external.bindings = {{{}, "effect", {contract, {}, ""}}};
    const auto signature =
        take(protocol::resolveBinding(external.bindings[0].application, false));
    auto &fn = external.functions[0];
    source::Names inputs, outputs;
    for (size_t i = 0; i < signature.inputs.size(); ++i) {
      inputs.push_back("arg" + std::to_string(i));
      fn.arguments.push_back({inputs.back(), signature.inputs[i].spelling()});
    }
    fn.results.clear();
    for (size_t i = 0; i < signature.outputs.size(); ++i) {
      outputs.push_back("out" + std::to_string(i));
      fn.results.push_back(signature.outputs[i].spelling());
    }
    auto *match = (*fn.body)[1].get<source::Match>();
    match->captures = inputs;
    match->outputs = outputs;
    match->arms[0].body = {
        ins("effect", source::Operation{"effect", {}, {}, inputs, outputs}),
        ins("", source::Yield{outputs})};
    (*fn.body)[2] = ins("", source::Return{outputs});
    reject(protocol::admit(external, false), "local-match-challenge");
  }
  auto selectorType = variant({"Selector", {{"Count", {"index"}}}});
  auto family = sample(type);
  auto &select = family.functions[0];
  select.arguments = {{"x", "index"}};
  select.results = {"index"};
  select.body = source::Body{
      ins("pack",
          source::VariantConstruct{selectorType, "Count", {"x"}, "sum"}),
      ins("match",
          source::Match{
              "sum",
              {},
              {{"Count", {"payload"}, {ins("", source::Yield{{"payload"}})}}},
              {"result"}}),
      ins("", source::Return{{"result"}})};
  family.protocols[0].parameters = {"count"};
  family.protocols[0].arguments[0].type = "index";
  family.protocols[0].results[0].type = "index";
  family.instances[0].parameters = {
      {"count", source::FamilyIngress{"8", {{"Alice", "Choose", {"x"}}}}}};
  reject(protocol::admit(family, true), "variant-family-selector");
  auto selectorHelper = select;
  selectorHelper.name = "SelectorHelper";
  selectorHelper.origin = source::LogicalOrigin{"SelectorHelper", {}};
  select.body = source::Body{
      ins("select", source::AlgorithmCall{"SelectorHelper", {"x"}, {"r"}}),
      ins("", source::Return{{"r"}})};
  family.functions.push_back(selectorHelper);
  reject(protocol::admit(family, true), "variant-family-selector");
  errs() << checks << " variant checks passed\n";
}
