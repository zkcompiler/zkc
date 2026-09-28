#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Subject.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::mathematical;
namespace r = zkc::mathematical::raw;

namespace {
void check(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}

// A deliberately finite test interpretation, selected explicitly by the
// caller. Each package pins its actual descriptor; zero digests grant nothing.
StringRef descriptor(StringRef name) {
  if (name == "fixture.bls-domain")
    return "domain:v1:installed=bls12-381.fr:nominal=closed-unary-values:"
           "polynomial=field:residual=field";
  if (name == "fixture.boolean-wire")
    return "wire:v1:payload=Fin2";
  if (name == "fixture.counter")
    return "service:v1:state=Nat:args=[]:result=Fin2:reply=state%2:next=state+"
           "1";
  if (name == "fixture.pair-step")
    return "ordered:v1:capabilities=[counter,counter]:distinct=[[0,1]]:args=[]:"
           "result=Fin2";
  if (name == "fixture.identity")
    return "total:v1:capabilities=[]:args=[Fin2]:result=Fin2:identity";
  return {};
}
r::Identity packageIdentity(StringRef name) {
  SHA256 hash;
  hash.update(descriptor(name));
  return {name.str(), "1", toHex(hash.final(), true)};
}
class FixtureRegistry final : public Registry {
public:
  Error identity(Category kind, const r::Identity &id,
                 const r::Manifest &) const override {
    auto expected = packageIdentity(id.name);
    bool category =
        (kind == Category::Domain && id.name == "fixture.bls-domain") ||
        (kind == Category::Wire && id.name == "fixture.boolean-wire") ||
        (kind == Category::Service && id.name == "fixture.counter") ||
        (kind == Category::Operation &&
         (id.name == "fixture.identity" || id.name == "fixture.pair-step"));
    if (!category || descriptor(id.name).empty() ||
        id.version != expected.version || id.digest != expected.digest)
      return zkc::error("fixture-package");
    return Error::success();
  }
  Error domainType(const r::Identity &id,
                   const TypeShape &shape) const override {
    if (id.name == "fixture.bls-domain")
      return checkInstalledDomainType("bls12-381.fr", shape);
    return zkc::error("fixture-domain");
  }
  Expected<OperationFacts> operation(const r::Identity &id,
                                     const OperationSignature &sig,
                                     const TypeTable &types,
                                     const r::Manifest &) const override {
    if (!sig.parameters.empty() || !types.isCondition(sig.result))
      return zkc::error("fixture-signature");
    if (id.name == "fixture.identity" && sig.capabilities.empty() &&
        sig.arguments.size() == 1 && types.isCondition(sig.arguments[0]))
      return OperationFacts{r::Operation::Purity::Total, {}};
    if (id.name == "fixture.pair-step" && sig.arguments.empty() &&
        sig.capabilities.size() == 2) {
      for (const auto &cap : sig.capabilities)
        if (cap.service != 0 || !cap.statics.empty() ||
            !cap.arguments.empty() || !types.isCondition(cap.result))
          return zkc::error("fixture-signature");
      return OperationFacts{r::Operation::Purity::Ordered, {{0, 1}}};
    }
    return zkc::error("fixture-operation");
  }
  Error wire(const r::Identity &id, ArrayRef<NormalStatic> params, TypeId type,
             const TypeTable &types, const r::Manifest &) const override {
    return id.name == "fixture.boolean-wire" && params.empty() &&
                   types.isCondition(type)
               ? Error::success()
               : zkc::error("fixture-wire");
  }
  Error service(const r::Identity &id, const CapabilitySignature &sig,
                const TypeTable &types, const r::Manifest &) const override {
    return id.name == "fixture.counter" && sig.statics.empty() &&
                   sig.arguments.empty() && types.isCondition(sig.result)
               ? Error::success()
               : zkc::error("fixture-service");
  }
  Error attributes(const r::Identity &, ArrayRef<NormalStatic>,
                   const json::Value &value) const override {
    return value.getAsObject() && value.getAsObject()->empty()
               ? Error::success()
               : zkc::error("fixture-attributes");
  }
};
FixtureRegistry registry;
r::TypeUse boolean() { return {{0}, {}}; }
r::Port port(std::initializer_list<uint64_t> owners,
             r::TypeUse type = boolean()) {
  std::vector<r::Role> roles;
  for (auto owner : owners)
    roles.push_back({owner});
  return {std::move(roles), std::move(type)};
}
r::Subject basic() {
  r::Subject source;
  source.module.roles = {"prover", "verifier"};
  source.module.types.push_back({0, r::FinType{Static::literal(2)}});
  source.module.definitions.push_back(
      {0, 2, {}, {port({0})}, {port({0})}, {}, {{}, r::Return{{{0}}}}});
  source.module.entry = {{0}, {}, {{0}, {1}}, {}};
  return source;
}
Subject accepts(const r::Subject &source) {
  auto admitted = admit(source, registry);
  if (!admitted) {
    errs() << "unexpected refusal: " << toString(admitted.takeError()) << '\n';
    std::exit(1);
  }
  auto encoded = r::encode(admitted->source());
  if (!encoded) {
    errs() << toString(encoded.takeError());
    std::exit(1);
  }
  auto digest = subjectDigest(*encoded);
  if (!digest) {
    errs() << toString(digest.takeError());
    std::exit(1);
  }
  check(*digest == admitted->digest(), "admitted custody changed");
  return std::move(*admitted);
}
void refuses(const r::Subject &source, StringRef expected) {
  auto admitted = admit(source, registry);
  check(!admitted, "malformed mathematical subject accepted");
  auto message = toString(admitted.takeError());
  if (message != expected) {
    errs() << "expected " << expected << ", got " << message << '\n';
    std::exit(1);
  }
}
r::Subject serviceCalls() {
  auto source = basic();
  source.module.roles.push_back("observer");
  source.manifest.services.push_back(packageIdentity("fixture.counter"));
  source.manifest.operations.push_back(packageIdentity("fixture.pair-step"));
  source.module.capabilityTypes.push_back({{0}, 0, {}, boolean()});
  r::CapabilityUse counter{{0}, {}};
  source.module.roots = {{counter, {{0}}}, {counter, {{0}}}};
  source.module.operations.push_back({{0},
                                      0,
                                      {counter, counter},
                                      {},
                                      boolean(),
                                      r::Operation::Purity::Ordered,
                                      {{0, 1}}});
  source.module.definitions.clear();
  r::Local local{0, {1}, {0}, {}, json::Object{}, {{0}, {1}}, {}};
  source.module.definitions.push_back({0,
                                       2,
                                       {{counter, {{1}}}, {counter, {{1}}}},
                                       {},
                                       {port({1})},
                                       {},
                                       {{local}, r::Return{{{0}}}}});
  r::Invoke first{0, {0}, {}, {{2}, {0}}, {{0}, {1}}, {}};
  auto second = first;
  second.site = 1;
  source.module.definitions.push_back({0,
                                       3,
                                       {{counter, {{0}}}, {counter, {{0}}}},
                                       {},
                                       {port({0})},
                                       {},
                                       {{first, second}, r::Return{{{0}}}}});
  source.module.entry = {{1}, {}, {{0}, {1}, {2}}, {{0}, {1}}};
  return source;
}

void sourceAndMessages() {
  auto source = basic();
  auto admitted = accepts(source);
  check(admitted.instances().size() == 1, "entry closure");
  auto independent = accepts(source);
  auto localType = admitted.definitions()[0].arguments[0].type;
  auto foreignType = independent.definitions()[0].arguments[0].type;
  check(localType.ordinal() == foreignType.ordinal() &&
            localType != foreignType,
        "type identity must retain table ownership");
  check(admitted.types().get(localType) && !admitted.types().get(foreignType),
        "foreign in-range type ID must refuse");
  source.module.definitions[0].results[0].roles = {{1}};
  refuses(source, "math-availability");
  source = basic();
  source.manifest.wires.push_back(packageIdentity("fixture.boolean-wire"));
  source.module.wires.push_back({{0}, 0, boolean()});
  source.module.definitions[0].body.steps.push_back(
      r::Message{0, {0}, {}, {0}, {1}, {0}});
  source.module.definitions[0].results[0].roles = {{0}, {1}};
  admitted = accepts(source);
  check(admitted.instances()[0].typed.body.steps[0].outputs[0].roles ==
            std::vector<uint32_t>({0, 1}),
        "message availability");
  source.module.definitions[0].body.terminal = r::Return{{{1}}};
  refuses(source, "math-availability"); // The old operand is still sender-only.
  source.module.definitions[0].body.terminal = r::Return{{{0}}};
  source.module.definitions[0].body.steps.push_back(r::Guard{0, {1}, {0}});
  refuses(source, "math-site-order");
  std::get<r::Guard>(source.module.definitions[0].body.steps.back()).site = 1;
  accepts(source);
  source.manifest.wires[0].digest.assign(64, '0');
  refuses(source, "fixture-package");
}
void rootsAndCalls() {
  auto source = serviceCalls();
  auto admitted = accepts(source);
  check(admitted.instances().size() == 2,
        "identical closed callees must share one instance");
  check(admitted.instances()[0].definition == 1 &&
            admitted.instances()[1].definition == 0,
        "DFS instance order");
  check(admitted.instances()[0].callees ==
            std::vector<std::pair<uint64_t, uint32_t>>({{0, 1}, {1, 1}}),
        "call site closure");
  check(admitted.instances()[1].roles == std::vector<uint32_t>({2, 0}),
        "non-monotone role composition");
  source.module.entry.capabilities[1] = {0};
  refuses(source, "math-distinct-roots");
  source = serviceCalls();
  source.module.roots[0].roles = {{1}};
  refuses(source, "math-root-permission");
  source = serviceCalls();
  std::get<r::Invoke>(source.module.definitions[1].body.steps[0]).definition = {
      1};
  refuses(source, "math-earlier-definition");
  source = serviceCalls();
  std::get<r::Invoke>(source.module.definitions[1].body.steps[0]).roles = {{0},
                                                                           {0}};
  refuses(source, "math-role-binding");
  source = serviceCalls();
  source.module.definitions[1].capabilities[0].roles = {{2}};
  refuses(source, "math-capability-permission");
  // Ordinary queries can alias one root: alias rejection belongs only to the
  // registered operation's distinct requirement.
  source = serviceCalls();
  source.module.operations.clear();
  source.manifest.operations.clear();
  source.module.definitions[0].body.steps = {r::Query{0, {1}, {0}, {}},
                                             r::Query{1, {1}, {1}, {}}};
  source.module.entry.capabilities[1] = {0};
  accepts(source);
}
void compactIndexedGraphs() {
  auto source = basic();
  source.module.types.push_back(
      {1, r::VectorType{boolean(), Static::parameter(0)}});
  auto &definition = source.module.definitions[0];
  definition.statics = 1;
  definition.results = {port({0}, {{1}, {Static::parameter(0)}})};
  r::Region inner{{{0}}, {}, {{1}}}; // index, then the private capture
  r::Map map{Static::parameter(0), std::make_shared<const r::Region>(inner)};
  definition.body.steps = {r::Pure{r::Region{{{0}}, {map}, {{0}}}}};
  source.module.entry.statics = {0};
  auto zero = accepts(source);
  source.module.entry.statics = {1000000000};
  auto large = accepts(source);
  const auto &smallRegion = *zero.instances()[0].typed.body.steps[0].region;
  const auto &largeRegion = *large.instances()[0].typed.body.steps[0].region;
  check(smallRegion.nodes.size() == 1 && largeRegion.nodes.size() == 1 &&
            largeRegion.nodes[0].body->nodes.empty(),
        "map must remain compact");
  source.module.entry.statics = {0};
  inner.outputs = {{2}};
  std::get<r::Map>(std::get<r::Pure>(definition.body.steps[0]).region.nodes[0])
      .body = std::make_shared<const r::Region>(inner);
  refuses(source, "math-value-reference"); // Dormant map body still checks.

  source = basic();
  r::Body body{{r::Guard{1, {1}, {1}}}, r::Return{{{1}}}};
  source.module.definitions[0].body.steps = {
      r::Repeat{0,
                Static::literal(0),
                {port({0})},
                {{0}},
                {},
                std::make_shared<const r::Body>(body)}};
  refuses(source, "math-availability");
  body.steps.clear();
  std::get<r::Repeat>(source.module.definitions[0].body.steps[0]).body =
      std::make_shared<const r::Body>(body);
  accepts(source);
  body.terminal = r::Stop{1, {0}, r::StopReason::Abort};
  std::get<r::Repeat>(source.module.definitions[0].body.steps[0]).body =
      std::make_shared<const r::Body>(body);
  accepts(source);
}
void graphBindingIdentity() {
  auto source = basic();
  auto &definition = source.module.definitions[0];
  definition.arguments = {port({0}), port({0})};
  definition.body.steps = {
      r::Pure{r::Region{{{0}, {1}},
                        {r::Tuple{{{0}, {1}}}, r::Project{{0}, 1}},
                        {{0}, {2}, {3}}}},
      r::Pure{r::Region{{{0}, {3}}, {}, {{0}, {1}}}}};
  auto admitted = accepts(source);
  const auto &body = admitted.definitions()[0].body;
  const auto &first = *body.steps[0].region;
  const auto &second = *body.steps[1].region;
  check(body.parameterBindings == std::vector<BindingId>({{0}, {1}}) &&
            body.steps[0].outputBindings ==
                std::vector<BindingId>({{2}, {3}, {4}}) &&
            body.steps[1].outputBindings == std::vector<BindingId>({{5}, {6}}),
        "body bindings follow parameter and result-block order");
  check(first.parameterBindings == std::vector<BindingId>({{0}, {1}}) &&
            first.nodes[0].outputBindings == std::vector<BindingId>({{2}}) &&
            first.nodes[1].outputBindings == std::vector<BindingId>({{3}}) &&
            first.nodes[1].inputs[0].binding == BindingId{2},
        "region nodes select stable graph bindings");
  check(first.outputs[0].binding == BindingId{3} &&
            first.outputs[1].binding == BindingId{0} &&
            first.outputs[2].binding == BindingId{1},
        "old graph values retain identity after new nodes prepend results");
  check(second.captures[0].binding == BindingId{2} &&
            second.captures[1].binding == BindingId{0} &&
            second.captures[1].index == 3 &&
            second.parameterBindings == std::vector<BindingId>({{0}, {1}}),
        "captures connect parent identities to a fresh nested scope");
}
void installedDomains() {
  auto source = basic();
  source.manifest.domains.push_back(packageIdentity("fixture.bls-domain"));
  source.module.types.push_back({0, r::NominalType{{0}, "field", {}}});
  source.module.definitions[0].arguments[0].type = {{1}, {}};
  source.module.definitions[0].results[0].type = {{1}, {}};
  auto admitted = accepts(source);
  const auto *shape =
      admitted.types().get(admitted.definitions()[0].arguments[0].type);
  check(shape && shape->constructor == "field",
        "installed nominal field formation");
  source.module.types[1].body = r::NominalType{{0}, "group", {}};
  refuses(source, "math-installed-nominal-constructor");
  source.module.types[1].body = r::NominalType{{0}, "rng", {}};
  refuses(source, "math-installed-nominal-resource");
  source.module.types[1].body =
      r::NominalType{{0}, "field", {Static::literal(1)}};
  refuses(source, "math-installed-nominal-shape");
  source.module.types[1].body =
      r::PolynomialType{{0},
                        Static::literal(3),
                        Static::literal(2),
                        r::PolynomialType::Degree::Total};
  accepts(source);
  source.module.types[1].body =
      r::ResidualType{{0}, Static::literal(3), Static::literal(2)};
  accepts(source);
  auto refused = checkInstalledDomainType("bls12-381.g1", *shape);
  check(bool(refused), "field constructor must reject a group domain");
  check(toString(std::move(refused)) == "math-installed-nominal-constructor",
        "nominal sort refusal");
  refused = checkInstalledDomainType("not-installed", *shape);
  check(bool(refused), "unknown catalog domain");
  check(toString(std::move(refused)) == "math-installed-domain",
        "unknown catalog refusal");
  TypeShape candidate = *shape;
  candidate.kind = TypeShape::Kind::Polynomial;
  candidate.constructor.clear();
  candidate.statics = {NormalStatic::parameter(0), NormalStatic::literal(2)};
  auto accepted = checkInstalledDomainType("bls12-381.fr", candidate);
  check(!accepted, "open polynomial family over an installed field");
  refused = checkInstalledDomainType("bls12-381.g1", candidate);
  check(bool(refused), "polynomial coefficient domain must be a field");
  check(toString(std::move(refused)) == "math-installed-field-family",
        "polynomial domain refusal");
  candidate.statics.pop_back();
  refused = checkInstalledDomainType("bls12-381.fr", candidate);
  check(bool(refused), "polynomial family exact arity");
  check(toString(std::move(refused)) == "math-installed-field-family",
        "polynomial arity refusal");
  candidate = *shape;
  candidate.constructor = "table";
  refused = checkInstalledDomainType("koala-bear", candidate);
  check(bool(refused), "a matching sort cannot grant a missing type instance");
  check(toString(std::move(refused)) == "math-installed-nominal-instance",
        "nominal instance refusal");
  candidate = *shape;
  candidate.domain.reset();
  refused = checkInstalledDomainType("bls12-381.fr", candidate);
  check(bool(refused), "domain-owned shape requires a manifest slot");
  check(toString(std::move(refused)) == "math-installed-domain",
        "missing domain slot refusal");
  source.module.types[1].body = r::NominalType{{0}, "not-installed", {}};
  refuses(source, "math-installed-nominal-constructor");
}

void flatAndNestedBodies() {
  auto source = basic();
  auto &steps = source.module.definitions[0].body.steps;
  steps.assign(5000, r::Pure{r::Region{}});
  auto flat = accepts(source);
  check(flat.instances()[0].typed.body.steps.size() == 5000,
        "flat siblings must preserve the complete body");

  r::Region nested;
  for (unsigned depth = 0; depth < 12; ++depth)
    nested = {{},
              {r::Map{Static::literal(0),
                      std::make_shared<const r::Region>(std::move(nested))}},
              {}};
  steps = {r::Pure{nested}};
  accepts(source);
  steps.assign(4070, r::Pure{r::Region{}});
  steps.push_back(r::Pure{std::move(nested)});
  auto late = accepts(source);
  check(late.instances()[0].typed.body.steps.size() == 4071,
        "late nested graph must retain the same depth allowance");

  // These widths reach the codec node limit in the larger Lean fixture.
  // This fixture has a smaller header; the counts exercise the same body
  // shapes without claiming identical complete carrier bytes.
  auto guards = basic();
  for (uint64_t site = 0; site < 14236; ++site)
    guards.module.definitions[0].body.steps.push_back(r::Guard{site, {0}, {0}});
  auto wideGuards = accepts(guards);
  check(wideGuards.instances()[0].typed.body.steps.size() == 14236,
        "wide guard sequence must preserve all effect sites");

  auto tuples = basic();
  r::Region wide;
  wide.nodes.assign(28472, r::Tuple{});
  tuples.module.definitions[0].body.steps = {r::Pure{std::move(wide)}};
  auto wideTuples = accepts(tuples);
  check(wideTuples.instances()[0].typed.body.steps[0].region->nodes.size() ==
            28472,
        "wide tuple graph must preserve every produced binding");
}

r::Subject tupleCapacity(unsigned doubling, unsigned unary) {
  auto source = basic();
  r::Region region{{{0}}, {}, {{0}}};
  for (unsigned i = 0; i < doubling; ++i)
    region.nodes.push_back(r::Tuple{{{0}, {0}}});
  for (unsigned i = 0; i < unary; ++i)
    region.nodes.push_back(r::Tuple{{{0}}});
  for (unsigned i = 0; i < doubling + unary; ++i)
    region.nodes.push_back(r::Project{{0}, 0});
  source.module.definitions[0].body.steps = {r::Pure{std::move(region)}};
  return source;
}

r::Subject parametricTypeChain(bool warmCache, unsigned deepest = 64,
                               bool shifted = false) {
  auto source = basic();
  source.module.types.push_back(
      {1, r::VectorType{boolean(), Static::parameter(0)}});
  for (unsigned i = 2; i <= deepest; ++i)
    source.module.types.push_back(
        {1, r::ProductType{{{{i - 1},
                             {shifted ? Static::add(Static::parameter(0),
                                                    Static::literal(1))
                                      : Static::parameter(0)}}}}});
  r::TypeUse final{{deepest}, {Static::literal(5)}};
  auto &definition = source.module.definitions[0];
  definition.arguments = {port({0}, final)};
  definition.results = {port({0}, final)};
  if (warmCache) {
    definition.arguments.insert(definition.arguments.begin(),
                                port({0}, {{32}, {Static::literal(5)}}));
    definition.body.terminal = r::Return{{{1}}};
  }
  return source;
}

void structuralTypeCapacity() {
  auto cold = accepts(parametricTypeChain(false));
  auto warm = accepts(parametricTypeChain(true));
  const auto *coldSize =
      cold.types().size(cold.definitions()[0].results[0].type);
  const auto *warmSize =
      warm.types().size(warm.definitions()[0].results[0].type);
  check(coldSize && warmSize && coldSize->nodes == 65 &&
            warmSize->nodes == 65 && coldSize->height == 65 &&
            warmSize->height == 65,
        "parametric template depth is independent of previous cache entries");
  accepts(parametricTypeChain(false, 64, true));
  // Every template is formed before ports. An excessive port type therefore
  // refuses while forming its declaration, whether the child lookup is cached
  // or its changing static arguments force a complete recursive expansion.
  refuses(parametricTypeChain(false, 65), "math-type-depth");
  refuses(parametricTypeChain(false, 65, true), "math-type-template-depth");
  auto boundary = accepts(tupleCapacity(15, 1));
  const auto &graph = *boundary.instances()[0].typed.body.steps[0].region;
  const auto *size = boundary.types().size(graph.nodes[15].outputs[0].type);
  check(size && size->nodes == typeNodeLimit && size->height == 17,
        "cached size counts both occurrences of shared children");
  refuses(tupleCapacity(16, 0), "math-type-size");
  refuses(tupleCapacity(15, 2), "math-type-size");
  auto depth = accepts(tupleCapacity(0, 64));
  const auto &deepGraph = *depth.instances()[0].typed.body.steps[0].region;
  const auto *deepSize =
      depth.types().size(deepGraph.nodes[63].outputs[0].type);
  check(deepSize && deepSize->nodes == 65 && deepSize->height == 65,
        "structural depth starts at zero for the root");
  refuses(tupleCapacity(0, 65), "math-type-depth");
  check(!depth.types().size(graph.nodes[15].outputs[0].type),
        "measurements reject foreign type IDs");

  // Unused templates must obey the same expanded-size limit.
  auto templates = basic();
  for (unsigned i = 0; i < 15; ++i)
    templates.module.types.push_back(
        {0, r::ProductType{{{{i}, {}}, {{i}, {}}}}});
  auto validTemplates = accepts(templates);
  check(validTemplates.types().all().size() == 16,
        "earlier template children retain shared storage");
  templates.module.types.push_back(
      {0, r::ProductType{{{{15}, {}}, {{15}, {}}}}});
  refuses(templates, "math-type-size");

  templates.module.types.back().body = r::ProductType{{{{15}, {}}}};
  auto exactTemplate = accepts(templates);
  check(exactTemplate.types().all().size() == 17,
        "exact expanded template size is admitted");
  templates.module.types.push_back(
      {0, r::VectorType{{{16}, {}}, Static::literal(0)}});
  refuses(templates, "math-type-size");
  templates.module.types.pop_back();
  templates.module.types.back().body =
      r::VectorType{{{15}, {}}, Static::literal(1000000000)};
  accepts(templates);

  auto vectors = basic();
  for (unsigned i = 0; i < 64; ++i)
    vectors.module.types.push_back(
        {0, r::VectorType{{{i}, {}}, Static::literal(0)}});
  accepts(vectors);
  vectors.module.types.push_back(
      {0, r::VectorType{{{64}, {}}, Static::literal(0)}});
  refuses(vectors, "math-type-depth");
}

void typesAndFormation() {
  auto source = basic();
  auto x = Static::parameter(0), y = Static::parameter(1);
  source.module.types.push_back(
      {2,
       r::VectorType{boolean(),
                     Static::multiply(x, Static::add(y, Static::literal(1)))}});
  source.module.types.push_back(
      {2, r::VectorType{boolean(), Static::add(Static::multiply(y, x), x)}});
  auto &definition = source.module.definitions[0];
  definition.statics = 2;
  definition.arguments = {port({0}, {{1}, {x, y}})};
  definition.results = {port({0}, {{2}, {x, y}})};
  source.module.entry.statics = {3, 4};
  accepts(source);
  source.module.entry.statics = {UINT64_MAX, 4};
  refuses(source, "math-static-overflow");
  source = basic();
  source.module.types[0].body = r::VectorType{boolean(), Static::literal(1)};
  refuses(source, "math-type-reference");
  source = basic();
  source.module.types.push_back(source.module.types[0]);
  refuses(source, "math-duplicate-type");
  source = basic();
  source.module.definitions[0].body.steps = {
      r::Pure{{{}, {r::Tuple{}}, {{0}}}}};
  refuses(source, "math-operand-type");
  source = basic();
  source.module.definitions[0].arguments[0].roles = {{1}, {0}};
  refuses(source, "math-role-binding");
  source = basic();
  auto limited = admit(source, registry, AdmissionBudget{1});
  check(!limited, "work exhaustion must refuse");
  check(toString(limited.takeError()) == "math-admission-limit",
        "resource refusal class");
}
} // namespace

int main() {
  sourceAndMessages();
  rootsAndCalls();
  compactIndexedGraphs();
  graphBindingIdentity();
  typesAndFormation();
  structuralTypeCapacity();
  flatAndNestedBodies();
  installedDomains();
  outs() << "mathematical typed admission: closure, root aliasing, roles, "
            "private values, compact loops and hostile controls passed\n";
}
