#include "../lib/Frontend/Lowering/Library.h"
#include "Names.h"
#include "zkc/Frontend/Library.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Bindings.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <functional>
#include <type_traits>

using zkc::frontend::ValueId;
using namespace zkc::frontend::library;
namespace {
int failures = 0;
void expect(bool ok, llvm::StringRef name) {
  if (!ok) {
    llvm::errs() << "FAIL: " << name << '\n';
    ++failures;
  }
}
template <typename T> T must(llvm::Expected<T> value) {
  if (!value) {
    llvm::errs() << llvm::toString(value.takeError()) << '\n';
    std::abort();
  }
  return std::move(*value);
}
template <typename T>
std::string refusal(llvm::Expected<T> value, llvm::StringRef code) {
  if (value) {
    expect(false, "expected refusal " + code.str());
    return {};
  }
  std::string message = llvm::toString(value.takeError());
  expect(llvm::StringRef(message).split(": ").first == code,
         "wrong refusal: " + message);
  return message;
}
// A refusal names its identifier first: a library diagnostic renders as
// `code: message` and an installed-table one as the bare code. The identifier
// is compared whole, because containment would accept a longer identifier that
// begins with this one, such as library-substitution-cycle for
// library-substitution.
void refusedWith(llvm::Error error, llvm::StringRef code) {
  if (!error) {
    expect(false, "expected refusal " + code.str());
    return;
  }
  std::string message = llvm::toString(std::move(error));
  expect(llvm::StringRef(message).split(": ").first == code,
         "expected " + code.str() + ", refused with: " + message);
}
template <typename T>
void refusedWith(llvm::Expected<T> value, llvm::StringRef code) {
  refusedWith(value.takeError(), code);
}
struct Fixture {
  LibraryId library{"tests", "checked", "1", "capture-A"};
  Environment env;
  QualifiedDecl id(std::string name) const {
    return {library, {"core"}, std::move(name)};
  }
  StaticTerm root(std::string name) const {
    return StaticTerm::root(id(std::move(name)));
  }
  Fixture() {
    CapturedLibrary capture{library, {}};
    for (const auto *name :
         {"Cell",    "self",   "C",    "D",      "scalar", "pair",     "zero",
          "F",       "G",      "T",    "N",      "A",      "seal",     "seal2",
          "functor", "client", "step", "record", "Other",  "otherSelf"})
      capture.declarations.push_back(id(name));
    env.libraries.push_back(capture);
    auto component = [&](std::string name, bool parameter) {
      env.statics.push_back({id(name),
                             Sort::component(),
                             {},
                             {{"Value", Sort::type()}},
                             {},
                             {},
                             parameter});
    };
    component("self", true);
    component("C", true);
    component("D", true);
    component("scalar", false);
    component("pair", false);
    component("zero", false);
    component("otherSelf", true);
    env.statics.push_back(
        {id("F"), Sort::domainOf("Field"), {}, {}, "koala-bear"});
    env.statics.push_back(
        {id("G"), Sort::domainOf("Field"), {}, {}, "bls12-381.fr"});
    env.statics.push_back({id("T"), Sort::type(), {}, {}, {}, {}, true});
    env.statics.push_back({id("N"), Sort::natural(), {}, {}, {}, {}, true});
    env.statics.push_back(
        {id("A"), Sort::association(), {}, {}, "descriptor-exact-bytes"});
    env.statics.push_back({id("seal"),
                           Sort::component(),
                           {Sort::component()},
                           {{"Value", Sort::type()}},
                           {},
                           {},
                           false,
                           true});
    env.statics.push_back({id("seal2"),
                           Sort::component(),
                           {Sort::component()},
                           {{"Value", Sort::type()}},
                           {},
                           {},
                           false,
                           true});
    env.statics.push_back({id("functor"),
                           Sort::component(),
                           {Sort::domainOf("Field")},
                           {{"Value", Sort::type()}},
                           {},
                           {root("A")}});
    for (const auto &t : zkc::protocol::boundTypeConstructors())
      env.logicalTypes.push_back({t, true});
    for (const auto &o : zkc::protocol::boundOperationContracts())
      env.operations.push_back(
          {o, o.name == "control.require"
                  ? std::set<std::string>{"local", "may-stop"}
                  : std::set<std::string>{"local"}});
  }
  Type field() const { return Type::logical("field", {root("F")}); }
  Interface interface(bool copy = false, std::vector<Facet> facets = {}) const {
    InterfaceDecl d;
    d.id = id("Cell");
    d.self = root("self");
    d.types.push_back({"Value", {copy, true}});
    d.facets = std::move(facets);
    Type a = Type::abstract(d.self, "Value");
    d.functions.emplace("step", Signature{{{a, ""}}, {{a, ""}}, {}, {}, {}});
    return must(formInterface(d, env));
  }
  Body clientBody(const Interface &) const {
    Type a = Type::abstract(root("C"), "Value");
    Body b;
    b.id = id("client");
    b.signature = {{{a, ""}}, {{a, ""}}, {}, {}, {}};
    b.inputs = {{{0}, {a, ""}}};
    b.instructions.push_back(Call{
        MemberCall{root("C"), "step"}, "", {{{0}, {}}}, {{{1}, {a, ""}}}, {}});
    b.returns.push_back({{1}, {}});
    return b;
  }
  CheckedBody client(const Interface &i) const {
    return must(checkBody(clientBody(i), env, {{root("C"), i}}));
  }
  CheckedBody privateBody(Type t, bool changed = false) const {
    Body b;
    b.id = id("step");
    b.signature = {{{t, ""}}, {{t, ""}}, {}, {}, {}};
    b.inputs = {{{0}, {t, ""}}};
    b.returns = {{{0}, {}}};
    if (changed) {
      b.instructions.push_back(Project{{{0}, {}}, {{1}, {t, ""}}});
      b.returns = {{{1}, {}}};
    }
    return must(checkBody(b, env));
  }
  std::shared_ptr<Implementation>
  implementation(const Interface &i, Type t, std::string selection = "scalar",
                 bool changed = false) const {
    return std::make_shared<Implementation>(
        Implementation{root(selection),
                       i,
                       {{"Value", t}},
                       {},
                       {{"step", privateBody(t, changed)}},
                       {},
                       {}});
  }
};
void identityAndSorts() {
  Fixture f;
  auto a = StaticTerm::apply(f.id("functor"), {f.root("F")});
  expect(must(selectionIdentity(a, f.env)) == must(selectionIdentity(a, f.env)),
         "applicative selection repeats");
  auto b = StaticTerm::apply(f.id("functor"), {f.root("G")});
  expect(must(selectionIdentity(a, f.env)) != must(selectionIdentity(b, f.env)),
         "actuals distinguish selection");
  auto seal = StaticTerm::seal(f.id("seal"), a);
  expect(must(selectionIdentity(seal, f.env)) ==
             must(selectionIdentity(seal, f.env)),
         "stable seal repeats");
  expect(must(selectionIdentity(seal, f.env)) !=
             must(selectionIdentity(StaticTerm::seal(f.id("seal2"), a), f.env)),
         "different seal declarations differ");
  expect(must(selectionIdentity(seal, f.env)) !=
             must(selectionIdentity(StaticTerm::seal(f.id("seal"), b), f.env)),
         "enclosing actuals distinguish seal");
  auto aliases = f.env;
  for (auto &d : aliases.statics)
    if (d.id.name == "G")
      d.capturedSubject = "koala-bear";
  expect(must(selectionIdentity(a, aliases)) ==
             must(selectionIdentity(b, aliases)),
         "installed domain aliases normalize before applicative selection");
  auto modified = f.env;
  for (auto &d : modified.statics)
    if (d.id.name == "A")
      d.capturedSubject = "another-setup";
  expect(must(selectionIdentity(a, f.env)) !=
             must(selectionIdentity(a, modified)),
         "private descriptor enters identity");
  refusal(sortOf(StaticTerm::apply(f.id("functor"), {StaticTerm::natural(2)}),
                 f.env),
          "library-static-sort");
  auto malicious = a;
  malicious.declaration.library.resolution = "capture-B";
  refusal(sortOf(malicious, f.env), "library-static");
  malicious = a;
  malicious.kind = static_cast<StaticTerm::Kind>(99);
  refusal(sortOf(malicious, f.env), "library-static");
  auto hiddenEffect = f.env;
  hiddenEffect.operations.front().effects.clear();
  refusal(formInterface(f.interface().declaration(), hiddenEffect),
          "library-operation-effect");
  auto badEnv = f.env;
  badEnv.statics[0].result.kind = static_cast<Sort::Kind>(99);
  InterfaceDecl d = f.interface().declaration();
  refusal(formInterface(d, badEnv), "library-sort");
  malicious = f.root("F");
  malicious.member = "inactive";
  refusal(sortOf(malicious, f.env), "library-static");
}
void abstractClientsAndLayouts() {
  Fixture f;
  auto i = f.interface();
  auto client = f.client(i);
  auto snapshot = client.identity();
  auto left = f.implementation(i, f.field());
  auto right =
      f.implementation(i, Type::product({f.field(), f.field()}), "pair");
  auto a = must(link({client, {{f.root("C"), left, "left"}}, {}}));
  auto b = must(link({client, {{f.root("C"), right, "right"}}, {}}));
  expect(a.functions().back().values.at(0).leaves.size() == 1, "scalar layout");
  expect(b.functions().back().values.at(0).leaves.size() == 2,
         "two-leaf layout");
  expect(snapshot == client.identity(), "same immutable client reused");
  expect(a.fingerprint() != b.fingerprint(), "concrete artifacts differ");
  auto z = must(link(
      {client,
       {{f.root("C"), f.implementation(i, Type::product({}), "zero"), "empty"}},
       {}}));
  const auto &leaf = z.functions().back().values.at(0).leaves;
  expect(leaf.size() == 1 && leaf[0].kind == LayoutLeaf::Kind::ResourceUnit,
         "opaque empty affine stays resource");
  expect(z.functions().front().values.at(0).leaves[0].resourceIdentity ==
             leaf[0].resourceIdentity,
         "private empty boundary agrees with client resource slot");
  auto copy = f.interface(true);
  auto copyClient = f.client(copy);
  refusal(link({copyClient,
                {{f.root("C"),
                  f.implementation(copy, Type::logical("rng", {f.root("F")})),
                  "affine"}},
                {}}),
          "library-permission-bound");
  expect(
      bool(
          must(link({client,
                     {{f.root("C"),
                       f.implementation(i, Type::logical("rng", {f.root("F")})),
                       "threaded"}},
                     {}}))
              .functions()
              .size()),
      "state threading does not need copy");
  auto counterfeit = f.implementation(i, f.field());
  refusal(link({copyClient, {{f.root("C"), counterfeit, "stale"}}, {}}),
          "library-interface-drift");
}
void resourcesAndNominality() {
  Fixture f;
  auto affine = f.interface();
  auto copy = f.interface(true);
  Body b = f.clientBody(affine);
  b.instructions.clear();
  b.signature.outputs.push_back(b.signature.outputs[0]);
  b.returns = {{{0}, {}}, {{0}, {}}};
  refusal(checkBody(b, f.env, {{f.root("C"), affine}}), "library-resource-use");
  expect(bool(must(checkBody(b, f.env, {{f.root("C"), copy}}))
                  .body()
                  .returns.size()),
         "copy-bound client checks independently");
  auto x = Type::abstract(f.root("C"), "Value"),
       y = Type::abstract(f.root("D"), "Value");
  b.signature = {{{x, ""}}, {{y, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {x, ""}}};
  b.returns = {{{0}, {}}};
  refusal(checkBody(b, f.env, {{f.root("C"), copy}, {f.root("D"), copy}}),
          "library-type-mismatch");
  b.signature = {{{f.field(), ""}},
                 {{Type::logical("field", {f.root("G")}), ""}},
                 {},
                 {},
                 {}};
  b.inputs = {{{0}, {f.field(), ""}}};
  refusal(checkBody(b, f.env), "library-type-mismatch");
  Type pair = Type::product({x, x});
  b.signature = {
      {{pair, "prover"}}, {{x, "prover"}, {x, "prover"}}, {}, {}, {}};
  b.inputs = {{{0}, {pair, "prover"}}};
  b.returns = {{{0}, {0}}, {{0}, {1}}};
  must(checkBody(b, f.env, {{f.root("C"), affine}}));
  b.returns[1].path = {0};
  refusal(checkBody(b, f.env, {{f.root("C"), affine}}), "library-resource-use");
  b.returns = {{{0}, {0}}, {{0}, {1}}};
  b.signature.outputs[1].role = "verifier";
  refusal(checkBody(b, f.env, {{f.root("C"), affine}}), "library-role");
  Type record = Type::record(f.id("record"), {"x"}, {f.field()});
  b.signature = {
      {{record, ""}}, {{Type::product({f.field()}), ""}}, {}, {}, {}};
  b.inputs = {{{0}, {record, ""}}};
  b.returns = {{{0}, {}}};
  refusal(checkBody(b, f.env), "library-type-mismatch");
  Type malformed = f.field();
  malformed.kind = static_cast<Type::Kind>(99);
  b.signature = {{{malformed, ""}}, {}, {}, {}, {}};
  b.inputs = {{{0}, {malformed, ""}}};
  b.returns.clear();
  refusal(checkBody(b, f.env), "library-type");
}
void diamondsAndInvalidation() {
  Fixture f;
  auto i = f.interface();
  auto client = f.client(i);
  auto original = f.implementation(i, f.field());
  auto changed = f.implementation(i, f.field(), "scalar", true);
  auto conflict = refusal(link({client,
                                {{f.root("C"), original, "left/path"},
                                 {f.root("D"), changed, "right/path"}},
                                {}}),
                          "library-diamond-conflict");
  expect(llvm::StringRef(conflict).contains("left/path") &&
             llvm::StringRef(conflict).contains("right/path"),
         "diamond diagnostic carries both paths");
  auto diamond = must(link({client,
                            {{f.root("C"), original, "left/path"},
                             {f.root("D"), original, "right/path"}},
                            {}}));
  expect(diamond.dependencies().size() == 1 &&
             diamond.dependencies()[0].paths.size() == 2,
         "diamond shares one interpretation");
  auto before = must(link({client, {{f.root("C"), original, "path"}}, {}}));
  auto after = must(link({client, {{f.root("C"), changed, "path"}}, {}}));
  expect(before.dependencies()[0].selection ==
             after.dependencies()[0].selection,
         "body edit preserves nominal key");
  expect(before.dependencies()[0].implementationIdentity !=
             after.dependencies()[0].implementationIdentity,
         "body edit invalidates artifact");
  auto layoutChange =
      f.implementation(i, Type::product({f.field(), f.field()}));
  auto layout = must(link({client, {{f.root("C"), layoutChange, "path"}}, {}}));
  expect(before.dependencies()[0].selection ==
                 layout.dependencies()[0].selection &&
             before.dependencies()[0].implementationIdentity !=
                 layout.dependencies()[0].implementationIdentity,
         "layout edit preserves key but invalidates layout artifact");
  refusal(link({client,
                {{f.root("C"), original, "left"},
                 {f.root("D"), layoutChange, "right"}},
                {}}),
          "library-diamond-conflict");
}
void facetsAndEffects() {
  Fixture f;
  auto i = f.interface(false, {{"unknown.owner", "proof", true}});
  refusal(link({f.client(i),
                {{f.root("C"), f.implementation(i, f.field()), "required"}},
                {}}),
          "library-required-facet");
  i = f.interface(false, {{"unknown.owner", "proof", false},
                          {"zkc.frontend.library", "resources", true}});
  auto linked =
      must(link({f.client(i),
                 {{f.root("C"), f.implementation(i, f.field()), "optional"}},
                 {}}));
  expect(linked.evidence().size() == 2 &&
             linked.evidence()[0].state == Evidence::State::Unavailable &&
             linked.evidence()[1].state == Evidence::State::Established,
         "optional unavailable differs from supported owner evidence");
  Body b;
  b.id = f.id("client");
  b.signature.inputs = {{Type::logical("bool"), "prover"}};
  b.inputs = {{{0}, {Type::logical("bool"), "prover"}}};
  b.signature.effects.insert("may-stop");
  b.signature.effects.insert("local");
  b.instructions.push_back(
      Call{LogicalCall{"control.require", {}}, "prover", {{{0}, {}}}, {}, {}});
  b.instructions.push_back(Call{LogicalCall{"field.constant", {f.root("F")}},
                                "prover",
                                {},
                                {{{1}, {f.field(), "prover"}}},
                                {"7"}});
  auto checked = must(checkBody(b, f.env));
  auto program = must(link({checked, {}, {}}));
  expect(program.functions().back().calls.size() == 2 &&
             std::get<Call>(program.functions().back().body.instructions[0])
                 .outputs.empty() &&
             std::get<Call>(program.functions().back().body.instructions[1])
                     .attributes[0] == "7",
         "effectful zero-output call and attributes survive link");
  b.signature.effects.clear();
  refusal(checkBody(b, f.env), "library-effect");
}
void genericsAndArrays() {
  Fixture f;
  Body b;
  b.id = f.id("client");
  Type t = Type::parameter(f.id("T"));
  b.typeBounds = {{f.id("T"), {true, true}}};
  b.signature = {{{t, ""}}, {{t, ""}, {t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {t, ""}}};
  b.returns = {{{0}, {}}, {{0}, {}}};
  auto checked = must(checkBody(b, f.env));
  must(link({checked, {}, {{}, {{f.id("T"), f.field()}}}}));
  refusal(link({checked,
                {},
                {{}, {{f.id("T"), Type::logical("rng", {f.root("F")})}}}}),
          "library-permission-bound");
  b.typeBounds[0].permissions.copy = false;
  refusal(checkBody(b, f.env), "library-resource-use");
  Type array = Type::array(Type::logical("rng", {f.root("F")}), f.root("N"));
  b.typeBounds.clear();
  b.signature = {{{array, ""}}, {{array, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {array, ""}}};
  b.returns = {{{0}, {}}};
  checked = must(checkBody(b, f.env));
  auto program =
      must(link({checked, {}, {{{f.root("N"), StaticTerm::natural(2)}}, {}}}));
  expect(program.functions().back().values.at(0).leaves.size() == 2,
         "symbolic array checked before selected expansion");
  auto bad = b;
  bad.returns[0].path = {0};
  refusal(checkBody(bad, f.env), "library-array-unresolved");

  // Static projection follows the element type without expanding the array.
  f.env.expansionLimit = 1000000;
  Type large = Type::array(Type::product({f.field(), Type::logical("bool")}),
                           StaticTerm::natural(1000000));
  b.signature = {{{large, ""}}, {{Type::logical("bool"), ""}}, {}, {}, {}};
  b.inputs = {{{0}, {large, ""}}};
  b.returns = {{{0}, {999999, 1}}};
  must(checkBody(b, f.env));
  b.returns[0].path = {1000000, 1};
  refusal(checkBody(b, f.env), "library-projection");
  b.returns[0].path = {999999, 2};
  refusal(checkBody(b, f.env), "library-projection");
}
void requirementApplications() {
  Fixture f;
  auto i = f.interface();
  auto left = StaticTerm::apply(f.id("functor"), {f.root("F")});
  auto right = StaticTerm::apply(f.id("functor"), {f.root("G")});
  Type a = Type::abstract(left, "Value"), b = Type::abstract(right, "Value");
  Body body;
  body.id = f.id("client");
  body.signature = {
      {{a, ""}}, {{b, ""}}, {{"", {f.root("F"), f.root("G")}}}, {}, {}};
  body.inputs = {{{0}, {a, ""}}};
  body.returns = {{{0}, {}}};
  auto checked = must(checkBody(body, f.env, {{left, i}, {right, i}}));
  body.signature.preconditions.clear();
  refusal(checkBody(body, f.env, {{left, i}, {right, i}}),
          "library-type-mismatch");
  auto first = f.implementation(i, f.field());
  first->selection = left;
  auto second = f.implementation(i, f.field());
  second->selection = right;
  refusal(
      link({checked, {{left, first, "left"}, {right, second, "right"}}, {}}),
      "library-bound");
}

void capturedClosureAndResources() {
  Fixture f;
  auto i = f.interface();
  auto client = f.client(i);
  auto changed = f.env;
  for (auto &t : changed.logicalTypes)
    if (t.contract.name == "rng")
      t.contract.affine = false;
  refusal(checkBody(f.clientBody(i), changed, {{f.root("C"), i}}),
          "library-logical-type");
  changed = f.env;
  changed.implications.push_back({"Field", "InventedCryptographicSecurity"});
  refusal(checkBody(f.clientBody(i), changed, {{f.root("C"), i}}),
          "library-implication");
  changed = f.env;
  changed.operations[0].contract.signature.inputs.clear();
  // Some installed first operations have zero inputs: change the result as
  // well.
  changed.operations[0].contract.signature.outputs.push_back({"bool", {}});
  refusal(checkBody(f.clientBody(i), changed, {{f.root("C"), i}}),
          "library-operation");

  auto leaf = f.implementation(i, f.field());
  auto parent = f.implementation(i, f.field(), "pair");
  parent->imports = {{f.root("D"), i}};
  parent->dependencies = {{f.root("D"), leaf, "captured"}};
  auto before = must(link({client, {{f.root("C"), parent, "parent"}}, {}}));
  auto editedLeaf = f.implementation(i, f.field(), "scalar", true);
  auto editedParent = std::make_shared<Implementation>(*parent);
  editedParent->dependencies[0].implementation = editedLeaf;
  auto after =
      must(link({client, {{f.root("C"), editedParent, "parent"}}, {}}));
  expect(before.dependencies().back().selection ==
                 after.dependencies().back().selection &&
             before.dependencies().back().implementationIdentity !=
                 after.dependencies().back().implementationIdentity,
         "captured body change invalidates dependent artifact without nominal "
         "drift");
  auto bad = f.implementation(i, f.field());
  bad->functions.insert_or_assign(
      "step", f.privateBody(Type::logical("field", {f.root("G")})));
  refusal(link({client, {{f.root("C"), bad, "wrong-domain"}}, {}}),
          "library-type-mismatch");

  auto empty = f.implementation(i, Type::product({}), "zero");
  Body chain = empty->functions.at("step").body();
  chain.instructions = {Project{{{0}, {}}, {{1}, {Type::product({}), ""}}},
                        Project{{{1}, {}}, {{2}, {Type::product({}), ""}}}};
  chain.returns = {{{2}, {}}};
  empty->functions.insert_or_assign("step", must(checkBody(chain, f.env)));
  auto linked = must(link({client, {{f.root("C"), empty, "chain"}}, {}}));
  expect(linked.functions().front().values.at(1).leaves.size() == 1 &&
             linked.functions().front().values.at(1).leaves[0].kind ==
                 LayoutLeaf::Kind::ResourceUnit,
         "empty resource survives private identity chain");
  chain.instructions.push_back(
      Project{{{0}, {}}, {{3}, {Type::product({}), ""}}});
  chain.returns = {{{3}, {}}};
  empty->functions.insert_or_assign("step", must(checkBody(chain, f.env)));
  refusal(link({client, {{f.root("C"), empty, "duplicate"}}, {}}),
          "library-resource-use");

  Body malformed;
  malformed.id = f.id("client");
  malformed.instructions.push_back(
      Call{LogicalCall{"field.constant", {f.root("F")}},
           "",
           {},
           {{{0}, {f.field(), ""}}},
           {}});
  refusal(checkBody(malformed, f.env), "library-operation-attributes");
  std::get<Call>(malformed.instructions[0]).attributes = {"01"};
  refusal(checkBody(malformed, f.env), "library-operation-attributes");
  auto unknown = f.env;
  for (auto &d : unknown.statics)
    if (d.id.name == "F")
      d.capturedSubject = "not-installed";
  Body forwarding;
  forwarding.id = f.id("client");
  forwarding.signature = {{{f.field(), ""}}, {{f.field(), ""}}, {}, {}, {}};
  forwarding.inputs = {{{0}, {f.field(), ""}}};
  forwarding.returns = {{{0}, {}}};
  auto nominallyTyped = must(checkBody(forwarding, unknown));
  refusal(link({nominallyTyped, {}, {}}), "library-logical-domain");

  // The checked client does not capture any selected implementation
  // declaration.
  Environment earlier = f.env;
  earlier.statics.erase(
      std::remove_if(earlier.statics.begin(), earlier.statics.end(),
                     [](const auto &d) {
                       return d.id.name == "scalar" || d.id.name == "pair" ||
                              d.id.name == "zero";
                     }),
      earlier.statics.end());
  auto earlierInterface = must(formInterface(i.declaration(), earlier));
  auto earlierClient = must(checkBody(f.clientBody(earlierInterface), earlier,
                                      {{f.root("C"), earlierInterface}}));
  must(link({earlierClient,
             {{f.root("C"), f.implementation(earlierInterface, f.field()),
               "later-selection"}},
             {}}));

  Type emptyArray =
      Type::array(Type::array(Type::product({}), StaticTerm::natural(65)),
                  StaticTerm::natural(65));
  Body expansion;
  expansion.id = f.id("client");
  expansion.signature = {{{emptyArray, ""}}, {{emptyArray, ""}}, {}, {}, {}};
  expansion.inputs = {{{0}, {emptyArray, ""}}};
  expansion.returns = {{{0}, {}}};
  auto arrayBody = must(checkBody(expansion, f.env));
  refusal(link({arrayBody, {}, {}}), "library-limit");

  Body generic;
  generic.id = f.id("client");
  Type parameter = Type::parameter(f.id("T"));
  generic.typeBounds = {{f.id("T"), {true, true}}};
  generic.signature = {{{parameter, ""}}, {{parameter, ""}}, {}, {}, {}};
  generic.inputs = {{{0}, {parameter, ""}}};
  generic.returns = {{{0}, {}}};
  auto genericBody = must(checkBody(generic, f.env));
  auto a = must(link({genericBody, {}, {{}, {{f.id("T"), f.field()}}}}));
  auto b =
      must(link({genericBody,
                 {},
                 {{}, {{f.id("T"), Type::logical("field", {f.root("G")})}}}}));
  expect(a.fingerprint() != b.fingerprint() && a.entry() != b.entry(),
         "type-only specialization changes cache identity");
}

ComponentDecl declaration(const Implementation &i) {
  return {i.interface, i.representations, i.statics,     i.functions,
          i.imports,   i.typeBounds,      i.requirements};
}
void parametricConformance() {
  Fixture f;
  auto affine = f.interface();
  auto copy = f.interface(true);
  auto base = f.implementation(affine, Type::logical("bool"));
  auto wrapper = f.implementation(copy, Type::logical("bool"), "pair");
  Type dep = Type::abstract(f.root("D"), "Value");
  Body forwarding = f.clientBody(affine);
  forwarding.signature = {{{dep, ""}}, {{dep, ""}}, {}, {}, {}};
  forwarding.inputs = {{{0}, {dep, ""}}};
  forwarding.instructions = {Call{MemberCall{f.root("D"), "step"},
                                  "",
                                  {{{0}, {}}},
                                  {{{1}, {dep, ""}}},
                                  {}}};
  wrapper->representations["Value"] = dep;
  wrapper->imports = {{f.root("D"), affine}};
  wrapper->dependencies = {{f.root("D"), base, "dependency"}};
  wrapper->functions.insert_or_assign(
      "step", must(checkBody(forwarding, f.env, wrapper->imports)));
  refusal(checkComponent(declaration(*wrapper), f.env),
          "library-permission-bound");
  refusal(link({f.client(copy), {{f.root("C"), wrapper, "upgrade"}}, {}}),
          "library-permission-bound");
  // A concrete bool dependency cannot repair an invalid template. Forwarding
  // under the affine bound is lawful, and the client judgment is unchanged.
  wrapper->interface = affine;
  auto checked = must(checkComponent(declaration(*wrapper), f.env));
  auto client = f.client(affine);
  const auto clientIdentity = client.identity();
  must(link({client, {{f.root("C"), wrapper, "forward"}}, {}}));
  expect(client.identity() == clientIdentity,
         "template selection leaves client immutable");
  wrapper->interface = copy;
  wrapper->imports = {{f.root("D"), copy}};
  wrapper->functions.insert_or_assign(
      "step", must(checkBody(forwarding, f.env, wrapper->imports)));
  wrapper->dependencies[0].implementation =
      f.implementation(copy, Type::logical("bool"));
  must(checkComponent(declaration(*wrapper), f.env));
  must(link({f.client(copy), {{f.root("C"), wrapper, "copy-bound"}}, {}}));
  // Snapshot owns declaration content; later mutation grants no new authority.
  expect(checked.declaration().interface.identity() == affine.identity(),
         "checked component is an immutable snapshot");
  auto malformed = f.implementation(copy, Type::logical("bool"));
  malformed->functions.insert_or_assign("step",
                                        f.privateBody(Type::logical("index")));
  refusal(checkComponent(declaration(*malformed), f.env),
          "library-type-mismatch");
  // Nominally different imported slots remain different even when selections
  // will both use bool. Concrete layout equality cannot discharge conformance.
  auto nominal = declaration(*base);
  nominal.imports = {{f.root("C"), affine}, {f.root("D"), affine}};
  nominal.representations["Value"] = Type::abstract(f.root("C"), "Value");
  nominal.functions.insert_or_assign(
      "step", must(checkBody(forwarding, f.env, nominal.imports)));
  refusal(checkComponent(nominal, f.env), "library-type-mismatch");
  // Method-local assumptions cannot silently strengthen the template bounds.
  auto unrecorded = declaration(*wrapper);
  unrecorded.imports.clear();
  refusal(checkComponent(unrecorded, f.env), "library-abstract-type");
  auto changed = declaration(*base);
  Body b = base->functions.at("step").body();
  b.signature.effects = {"local"};
  changed.functions.insert_or_assign("step", must(checkBody(b, f.env)));
  refusal(checkComponent(changed, f.env), "library-effect");
  b = base->functions.at("step").body();
  b.signature.inputs[0].role = b.signature.outputs[0].role = "prover";
  b.inputs[0].port.role = "prover";
  changed.functions.insert_or_assign("step", must(checkBody(b, f.env)));
  refusal(checkComponent(changed, f.env), "library-role");
  b = base->functions.at("step").body();
  b.signature.preconditions = {{"", {f.root("F"), f.root("G")}}};
  changed.functions.insert_or_assign("step", must(checkBody(b, f.env)));
  refusal(checkComponent(changed, f.env), "library-precondition");
  auto strong = affine.declaration();
  strong.functions.at("step").postconditions = {
      {"", {f.root("F"), f.root("G")}}};
  changed = declaration(*base);
  changed.interface = must(formInterface(strong, f.env));
  refusal(checkComponent(changed, f.env), "library-postcondition");
}
void persistentUnusedBounds() {
  Fixture f;
  auto needDecl = f.interface(true).declaration();
  needDecl.functions.clear();
  auto need = must(formInterface(needDecl, f.env));
  auto otherDecl = needDecl;
  otherDecl.id = f.id("Other");
  otherDecl.types[0].permissions.copy = false;
  auto other = must(formInterface(otherDecl, f.env));
  auto marker = f.interface(true);
  auto wrong = std::make_shared<Implementation>(
      Implementation{f.root("scalar"),
                     other,
                     {{"Value", Type::logical("bool")}},
                     {},
                     {},
                     {},
                     {}});
  auto wrap = f.implementation(marker, Type::logical("bool"), "pair");
  wrap->imports = {{f.root("D"), need}};
  wrap->dependencies = {{f.root("D"), wrong, "unused"}};
  must(checkComponent(declaration(*wrap), f.env));
  refusal(link({f.client(marker), {{f.root("C"), wrap, "unused-bound"}}, {}}),
          "library-interface-drift");
  // No methods anywhere: persistent obligations still apply.
  wrap->interface = need;
  wrap->functions.clear();
  Body b;
  b.id = f.id("client");
  Type t = Type::abstract(f.root("C"), "Value");
  b.signature = {{{t, ""}}, {{t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {t, ""}}};
  b.returns = {{{0}, {}}};
  auto client = must(checkBody(b, f.env, {{f.root("C"), need}}));
  must(checkComponent(declaration(*wrap), f.env));
  refusal(link({client, {{f.root("C"), wrap, "no-method"}}, {}}),
          "library-interface-drift");
  wrong->interface = need;
  must(link({client, {{f.root("C"), wrap, "lawful"}}, {}}));
  wrap->dependencies.clear();
  refusal(link({client, {{f.root("C"), wrap, "missing"}}, {}}),
          "library-binding");
  // An ordinary concrete actual cannot repair insufficient generic bounds.
  auto generic = declaration(*wrap);
  generic.imports.clear();
  generic.typeBounds = {{f.id("T"), {false, true}}};
  generic.representations["Value"] = Type::parameter(f.id("T"));
  refusal(checkComponent(generic, f.env), "library-permission-bound");
  generic.typeBounds[0].permissions.copy = true;
  must(checkComponent(generic, f.env));
  // Unused ordinary bounds and requirements also survive without bodies.
  wrap->imports.clear();
  wrap->typeBounds = {{f.id("T"), {true, true}}};
  wrap->arguments.types = {{f.id("T"), Type::abstract(f.root("D"), "Value")}};
  wrong->interface = other;
  wrap->imports = {{f.root("D"), other}};
  wrap->dependencies = {{f.root("D"), wrong, "ordinary-bound"}};
  refusal(
      link({client,
            {{f.root("D"), wrong, "affine"}, {f.root("C"), wrap, "ordinary"}},
            {}}),
      "library-permission-bound");
  wrap->arguments.types = {{f.id("T"), Type::logical("bool")}};
  must(link({client, {{f.root("C"), wrap, "copy"}}, {}}));
  wrap->requirements = {{"", {f.root("F"), f.root("G")}}};
  must(checkComponent(declaration(*wrap), f.env));
  refusal(link({client, {{f.root("C"), wrap, "unsatisfied"}}, {}}),
          "library-bound");
}
void abstractActualPermissions() {
  Fixture f;
  auto affine = f.interface();
  auto copy = f.interface(true);
  Body b;
  b.id = f.id("client");
  Type t = Type::parameter(f.id("T"));
  b.typeBounds = {{f.id("T"), {true, true}}};
  b.signature = {{{t, ""}}, {{t, ""}, {t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {t, ""}}};
  b.returns = {{{0}, {}}, {{0}, {}}};
  auto client = must(checkBody(b, f.env));
  auto base = f.implementation(affine, Type::logical("bool"));
  Type actual = Type::abstract(f.root("C"), "Value");
  refusal(link({client,
                {{f.root("C"), base, "affine-bool"}},
                {{}, {{f.id("T"), actual}}}}),
          "library-permission-bound");
  refusal(link({client,
                {{f.root("C"), base, "nested-affine-bool"}},
                {{}, {{f.id("T"), Type::product({actual})}}}}),
          "library-permission-bound");
  base->interface = copy;
  must(link({client,
             {{f.root("C"), base, "copy-bool"}},
             {{}, {{f.id("T"), actual}}}}));
}
void componentSubstitutionAuthority() {
  Fixture f;
  auto iface = f.interface();
  auto x = f.implementation(iface, Type::logical("bool"));
  auto z = f.implementation(iface, Type::logical("bool"), "pair", true);
  auto body = f.clientBody(iface);
  body.signature.preconditions = {{"", {f.root("C"), f.root("D")}}};
  body.signature.inputs[0].type = Type::abstract(f.root("D"), "Value");
  body.inputs[0].port.type = body.signature.inputs[0].type;
  auto client = must(
      checkBody(body, f.env, {{f.root("C"), iface}, {f.root("D"), iface}}));
  // Equality is lawful only when requirement checking and dispatch agree.
  must(link({client, {{f.root("C"), x, "c"}, {f.root("D"), x, "d"}}, {}}));
  refusal(link({client, {{f.root("C"), z, "c"}, {f.root("D"), x, "d"}}, {}}),
          "library-bound");
  refusal(link({client,
                {{f.root("C"), z, "c"}, {f.root("D"), x, "d"}},
                {{{f.root("C"), f.root("scalar")}}, {}}}),
          "library-substitution-component");

  // The same authority boundary applies to Self and persistent dependencies.
  auto wrap = f.implementation(iface, Type::logical("bool"), "zero");
  wrap->arguments.statics = {{f.root("self"), f.root("scalar")}};
  refusal(link({f.client(iface), {{f.root("C"), wrap, "self"}}, {}}),
          "library-substitution-component");
  wrap->imports = {{f.root("D"), iface}};
  wrap->dependencies = {{f.root("D"), x, "dependency"}};
  wrap->arguments.statics = {{f.root("D"), f.root("pair")}};
  refusal(link({f.client(iface), {{f.root("C"), wrap, "dependency"}}, {}}),
          "library-substitution-component");
  wrap->arguments.statics = {{f.root("N"), StaticTerm::natural(2)}};
  must(link({f.client(iface), {{f.root("C"), wrap, "ordinary-static"}}, {}}));
}
void linkedBindingAndCaptureIdentity() {
  Fixture f;
  auto iface = f.interface();
  auto body = f.clientBody(iface);
  auto client = must(
      checkBody(body, f.env, {{f.root("C"), iface}, {f.root("D"), iface}}));
  auto a = f.implementation(iface, Type::logical("bool"));
  auto b = f.implementation(iface, Type::logical("bool"), "pair", true);
  auto x =
      must(link({client, {{f.root("C"), a, "a"}, {f.root("D"), b, "b"}}, {}}));
  auto y =
      must(link({client, {{f.root("D"), a, "a"}, {f.root("C"), b, "b"}}, {}}));
  expect(x.identity() != y.identity() && x.fingerprint() != y.fingerprint() &&
             x.entry() != y.entry(),
         "exact identity includes client parameter binding relation");
  auto reordered =
      must(link({client, {{f.root("D"), b, "b"}, {f.root("C"), a, "a"}}, {}}));
  expect(x.identity() == reordered.identity() && x.entry() == reordered.entry(),
         "binding traversal order does not change exact identity");
  expect(x.functions().back().calls.at({0}).target !=
             y.functions().back().calls.at({0}).target,
         "swapped binding changes call target");
  auto first = f.implementation(iface, Type::logical("bool"));
  auto second = f.implementation(iface, Type::logical("bool"), "scalar", true);
  first->arguments.types = {{f.id("T"), Type::logical("bool")}};
  second->arguments.types = {{f.id("T"), f.field()}};
  auto oneClient = f.client(iface);
  auto p = must(link({oneClient, {{f.root("C"), first, "first"}}, {}}));
  auto q = must(link({oneClient, {{f.root("C"), second, "second"}}, {}}));
  const auto &pd = p.dependencies()[0];
  const auto &qd = q.dependencies()[0];
  expect(pd.normalizedSelection == qd.normalizedSelection &&
             pd.captureIdentity != qd.captureIdentity &&
             pd.captureFingerprint != qd.captureFingerprint,
         "independent worlds retain exact conflicting hidden captures");
  refusal(
      link({client,
            {{f.root("C"), first, "first"}, {f.root("D"), second, "second"}},
            {}}),
      "library-selection-capture");
  // Main's shared lowering owner consumes these exact metadata fields.
  refusal(lower(std::vector<LinkedProgram>{p, q}), "library-selection-capture");
}

void capturedDomainAuthority() {
  Fixture f;
  expect(must(resolvedDomain(f.root("F"), f.env)) == "koala-bear",
         "closed domains resolve from captured owner identity");
  auto client = f.privateBody(f.field());
  auto linked = must(link({client, {}, {}}));
  auto changed = f.env;
  for (auto &d : changed.statics)
    if (d.id.name == "F")
      d.capturedSubject = "bls12-381.fr";
  expect(must(resolvedDomain(f.root("F"), linked.environment())) ==
             "koala-bear",
         "linked domain environment is immutable");
  must(lower(linked));
  for (auto &d : changed.statics)
    if (d.id.name == "F")
      d.capturedDependencies = {f.root("A")};
  refusal(resolvedDomain(f.root("F"), changed), "library-domain-capture");
  refusal(selectionIdentity(f.root("F"), changed), "library-domain-capture");
  refusal(checkBody(client.body(), changed), "library-domain-capture");
  changed = f.env;
  for (auto &d : changed.statics)
    if (d.id.name == "F")
      d.result = Sort::domainOf("Group");
  refusal(resolvedDomain(f.root("F"), changed), "library-domain-sort");
  refusal(checkBody(client.body(), changed), "library-domain-sort");
  // Same physical type is not the same ordinary type actual.
  auto iface = f.interface(true);
  auto base = f.implementation(iface, Type::logical("bool"));
  Body b;
  b.id = f.id("client");
  Type t = Type::parameter(f.id("T"));
  b.typeBounds = {{f.id("T"), {true, true}}};
  b.signature = {{{t, ""}}, {{t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {t, ""}}};
  b.returns = {{{0}, {}}};
  auto checked = must(checkBody(b, f.env));
  auto opaque =
      must(link({checked,
                 {{f.root("C"), base, "base"}},
                 {{}, {{f.id("T"), Type::abstract(f.root("C"), "Value")}}}}));
  auto plain = must(link({checked,
                          {{f.root("C"), base, "base"}},
                          {{}, {{f.id("T"), Type::logical("bool")}}}}));
  expect(opaque.identity() != plain.identity(),
         "ordinary actual identity preserves opaque nominal type");
}

void lexicalSelectionScope() {
  Fixture f;
  for (auto &d : f.env.statics)
    if (d.result.kind == Sort::Kind::Component)
      d.members = {{"N", Sort::natural()}};
  InterfaceDecl declaration;
  declaration.id = f.id("Cell");
  declaration.self = f.root("self");
  declaration.statics = {{"N", Sort::natural(), std::nullopt}};
  auto iface = must(formInterface(declaration, f.env));
  auto leaf = std::make_shared<Implementation>(
      Implementation{f.root("scalar"),
                     iface,
                     {},
                     {{"N", StaticTerm::natural(2)}},
                     {},
                     {},
                     {}});
  auto wrapper = std::make_shared<Implementation>(
      Implementation{f.root("pair"),
                     iface,
                     {},
                     {{"N", StaticTerm::project(f.root("scalar"), "N")}},
                     {},
                     {},
                     {}});
  Body body;
  body.id = f.id("client");
  auto client = must(checkBody(body, f.env, {{f.root("C"), iface}}));
  // Selecting an unrelated sibling first cannot make an undeclared projection
  // visible inside the wrapper. Both traversal orders refuse.
  refusal(
      link({client,
            {{f.root("D"), leaf, "sibling"}, {f.root("C"), wrapper, "wrapper"}},
            {}}),
      "library-selection");
  refusal(
      link({client,
            {{f.root("C"), wrapper, "wrapper"}, {f.root("D"), leaf, "sibling"}},
            {}}),
      "library-selection");
  wrapper->imports = {{f.root("D"), iface}};
  wrapper->dependencies = {{f.root("D"), leaf, "declared"}};
  wrapper->statics["N"] = StaticTerm::project(f.root("D"), "N");
  must(link({client, {{f.root("C"), wrapper, "wrapper"}}, {}}));
}

void checkedRegions() {
  Fixture f;
  auto iface = f.interface();
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type variant = Type::variant(f.id("record"), {"Ready", "Empty"},
                               {opaque, Type::product({})});
  Body b;
  b.id = f.id("client");
  b.signature = {{{variant, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {variant, ""}}, {{1}, {opaque, ""}}};
  auto ready = std::make_shared<Region>();
  ready->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  ready->instructions = {Call{MemberCall{f.root("C"), "step"},
                              "",
                              {{{2}, {}}},
                              {{{7}, {opaque, ""}}},
                              {}},
                         Drop{{{7}, {}}}};
  ready->returns = {{{3}, {}}};
  auto empty = std::make_shared<Region>();
  empty->inputs = {{{4}, {Type::product({}), ""}}, {{5}, {opaque, ""}}};
  empty->returns = {{{5}, {}}};
  Match match{{{0}, {}},
              "",
              {{{1}, {}}},
              {{{6}, {opaque, ""}}},
              {{"Ready", ready}, {"Empty", empty}}};
  b.instructions = {match};
  b.returns = {{{6}, {}}};
  auto checked = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  for (Type rep :
       {f.field(), Type::product({f.field(), f.field()}), Type::product({})}) {
    auto impl = f.implementation(iface, rep);
    auto linked = must(link({checked, {{f.root("C"), impl, "C"}}, {}}));
    expect(linked.functions().back().calls.count({0, 0, 0}) == 1,
           "nested member calls retain stable region path");
    auto lowered = must(lower(linked));
    expect(lowered.functions.back().body->front().get<zkc::source::Match>() !=
               nullptr,
           "active-only match lowers through common carrier");
    const auto &leaf = linked.functions().back().values.at(0).leaves.front();
    expect(leaf.alternatives.size() == 2 && leaf.alternatives[1].empty(),
           "unequal alternatives retain no inactive payload");
    if (rep.elements.empty() && rep.kind == Type::Kind::Product)
      expect(leaf.alternatives[0].size() == 1 &&
                 leaf.alternatives[0][0].kind == LayoutLeaf::Kind::ResourceUnit,
             "zero-storage active payload retains affine token");
  }
  auto bad = b;
  std::get<Match>(bad.instructions[0]).arms.pop_back();
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-match");
  bad = b;
  std::get<Match>(bad.instructions[0]).arms[1].alternative = "Ready";
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-match");
  bad = b;
  std::get<Match>(bad.instructions[0]).captures.push_back({{1}, {}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}),
          "library-resource-use");
  auto invalid = std::make_shared<Region>(*empty);
  invalid->returns = {{{1}, {}}};
  bad = b;
  std::get<Match>(bad.instructions[0]).arms[1].body = invalid;
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-value");
  bad = b;
  bad.instructions.insert(bad.instructions.begin(),
                          Project{{{0}, {0}}, {{7}, {opaque, ""}}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-projection");
  // Matching a variant element under bounded expansion gives each arm and
  // nested call fresh definitions while the carried resource is threaded.
  Body nested;
  nested.id = f.id("client");
  Type variants = Type::array(variant, StaticTerm::natural(2));
  nested.signature = {
      {{variants, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  nested.inputs = {{{20}, {variants, ""}}, {{21}, {opaque, ""}}};
  auto iteration = std::make_shared<Region>();
  iteration->inputs = {{{0}, {variant, ""}}, {{1}, {opaque, ""}}};
  iteration->instructions = {match};
  iteration->returns = {{{6}, {}}};
  nested.instructions = {ArrayTraversal{
      {{20}, {}}, "", {{{21}, {}}}, {}, {{{22}, {opaque, ""}}}, iteration}};
  nested.returns = {{{22}, {}}};
  auto nestedChecked = must(checkBody(nested, f.env, {{f.root("C"), iface}}));
  auto nestedImpl = f.implementation(iface, Type::product({}));
  auto nestedLinked =
      must(link({nestedChecked, {{f.root("C"), nestedImpl, "C"}}, {}}));
  expect(nestedLinked.functions().back().calls.size() == 2,
         "array expansion resolves both nested call sites");
  (void)must(lower(nestedLinked));
  // A checked handle snapshots shared region builders.
  empty->returns = {{{99}, {}}};
  expect(std::get<Match>(checked.body().instructions[0])
                 .arms[1]
                 .body->returns[0]
                 .value.index == 5,
         "checked nested regions are immutable snapshots");

  Type array = Type::array(opaque, f.root("N"));
  Body traversal;
  traversal.id = f.id("client");
  traversal.signature = {
      {{array, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  traversal.inputs = {{{0}, {array, ""}}, {{1}, {opaque, ""}}};
  auto step = std::make_shared<Region>();
  step->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  step->instructions = {Drop{{{2}, {}}}};
  step->returns = {{{3}, {}}};
  traversal.instructions = {ArrayTraversal{
      {{0}, {}}, "", {{{1}, {}}}, {}, {{{4}, {opaque, ""}}}, step}};
  traversal.returns = {{{4}, {}}};
  auto fold = must(checkBody(traversal, f.env, {{f.root("C"), iface}}));
  auto impl = f.implementation(iface, Type::product({}));
  for (uint64_t count : {0, 2}) {
    auto linked =
        must(link({fold,
                   {{f.root("C"), impl, "C"}},
                   {{{f.root("N"), StaticTerm::natural(count)}}, {}}}));
    auto lowered = must(lower(linked));
    expect(!lowered.functions.empty(),
           "symbolic traversal lowers including zero trip");
    const auto &is = linked.functions().back().body.instructions;
    expect(is.size() == count + 1,
           "bounded expansion includes one move per element");
  }
  step->instructions.push_back(Drop{{{2}, {}}});
  refusal(checkBody(traversal, f.env, {{f.root("C"), iface}}),
          "library-resource-use");
  step->instructions.pop_back();
  auto capture = traversal;
  std::get<ArrayTraversal>(capture.instructions[0]).captures = {{{1}, {}}};
  refusal(checkBody(capture, f.env, {{f.root("C"), iface}}),
          "library-resource-use");
}
void genericVariantsAndTraversalBounds() {
  Fixture f;
  const Type t = Type::parameter(f.id("T"));
  const Type sum =
      Type::variant(f.id("record"), {"Ok", "Error"}, {t, Type::product({})});
  Body body;
  body.id = f.id("client");
  body.typeBounds = {{f.id("T"), {false, true}}};
  body.signature = {{{t, ""}, {t, ""}}, {{t, ""}}, {}, {}, {}};
  body.inputs = {{{0}, {t, ""}}, {{1}, {t, ""}}};
  auto ok = std::make_shared<Region>();
  ok->inputs = {{{3}, {t, ""}}, {{4}, {t, ""}}};
  ok->instructions = {Drop{{{3}, {}}}};
  ok->returns = {{{4}, {}}};
  auto error = std::make_shared<Region>();
  error->inputs = {{{5}, {Type::product({}), ""}}, {{6}, {t, ""}}};
  error->returns = {{{6}, {}}};
  body.instructions = {VariantConstruct{{{2}, {sum, ""}}, "Ok", {{0}, {}}},
                       Match{{{2}, {}},
                             "",
                             {{{1}, {}}},
                             {{{7}, {t, ""}}},
                             {{"Error", error}, {"Ok", ok}}}};
  body.returns = {{{7}, {}}};
  Body permissionTest;
  permissionTest.id = f.id("client");
  permissionTest.typeBounds = body.typeBounds;
  permissionTest.signature = {{{sum, ""}}, {{sum, ""}, {sum, ""}}, {}, {}, {}};
  permissionTest.inputs = {{{0}, {sum, ""}}};
  permissionTest.returns = {{{0}, {}}, {{0}, {}}};
  refusal(checkBody(permissionTest, f.env), "library-resource-use");
  permissionTest.typeBounds[0].permissions.drop = false;
  permissionTest.signature.outputs.clear();
  permissionTest.returns.clear();
  permissionTest.instructions = {Drop{{{0}, {}}}};
  refusal(checkBody(permissionTest, f.env), "library-drop");
  permissionTest.instructions.clear();
  refusal(checkBody(permissionTest, f.env), "library-resource-leak");
  auto generic = must(checkBody(body, f.env));
  auto linked = must(link({generic, {}, {{}, {{f.id("T"), f.field()}}}}));
  auto lowered = must(lower(linked));
  const auto &instructions = *lowered.functions.back().body;
  expect(instructions[0].get<zkc::source::VariantConstruct>() != nullptr,
         "generic constructor becomes one logical variant");
  auto *matched = instructions[1].get<zkc::source::Match>();
  expect(matched && matched->arms.front().alternative == "Ok",
         "lowering orders arms by declaration rather than builder order");
  error->instructions = {Project{{{6}, {}}, {{8}, {t, ""}}},
                         Project{{{6}, {}}, {{9}, {t, ""}}}};
  refusal(checkBody(body, f.env), "library-resource-use");
  error->instructions.clear();
  auto bad = body;
  std::get<VariantConstruct>(bad.instructions[0]).alternative = "Missing";
  refusal(checkBody(bad, f.env), "library-variant");

  Type array = Type::array(t, f.root("N"));
  Body fold;
  fold.id = f.id("client");
  fold.typeBounds = body.typeBounds;
  fold.signature = {{{array, ""}, {t, ""}, {t, ""}}, {{t, ""}}, {}, {}, {}};
  fold.inputs = {{{0}, {array, ""}}, {{1}, {t, ""}}, {{2}, {t, ""}}};
  auto step = std::make_shared<Region>();
  step->inputs = {{{3}, {t, ""}}, {{4}, {t, ""}}};
  step->instructions = {Drop{{{3}, {}}}};
  step->returns = {{{4}, {}}};
  fold.instructions = {
      ArrayTraversal{{{0}, {}}, "", {{{1}, {}}}, {}, {{{5}, {t, ""}}}, step}};
  fold.returns = {{{5}, {}}};
  auto checked = must(checkBody(fold, f.env));
  refusal(link({checked,
                {},
                {{{f.root("N"), StaticTerm::natural(f.env.expansionLimit + 1)}},
                 {{f.id("T"), f.field()}}}}),
          "library-limit");
  auto capture = fold;
  std::get<ArrayTraversal>(capture.instructions.front()).captures = {{{2}, {}}};
  refusal(checkBody(capture, f.env), "library-traversal-capture");
  step->returns.clear();
  refusal(checkBody(fold, f.env), "library-return");
  step->returns = {{{4}, {}}};
  fold.instructions.push_back(Drop{{{0}, {0}}});
  // Even zero-selected trips cannot justify an affine element reuse in the
  // symbolic body. The semantic array has already moved into traversal.
  refusal(checkBody(fold, f.env), "library-array-unresolved");
  fold.signature.inputs[0].type = Type::array(t, StaticTerm::natural(2));
  fold.inputs[0].port.type = fold.signature.inputs[0].type;
  refusal(checkBody(fold, f.env), "library-resource-use");

  // A participant-local arm cannot schedule a zero-result call elsewhere.
  Body local = body;
  local.signature.effects = {"local"};
  auto offRole = std::make_shared<Region>(*error);
  offRole->instructions = {
      Call{LogicalCall{"control.require", {}}, "Verifier", {}, {}, {}}};
  std::get<Match>(local.instructions[1]).arms[0].body = offRole;
  refusal(checkBody(local, f.env), "library-role");
}

void privateVariantBoundary() {
  Fixture f;
  auto decl = f.interface().declaration();
  auto resultType = [&](Type payload) {
    return Type::variant(f.id("record"), {"Ok", "Error"},
                         {payload, Type::product({})});
  };
  Type self = Type::abstract(f.root("self"), "Value");
  decl.functions.at("step") = {
      {{self, ""}}, {{resultType(self), ""}}, {}, {}, {}};
  auto iface = must(formInterface(decl, f.env));
  Type abstract = Type::abstract(f.root("C"), "Value");
  Body client;
  client.id = f.id("client");
  client.signature = {
      {{abstract, ""}}, {{resultType(abstract), ""}}, {}, {}, {}};
  client.inputs = {{{0}, {abstract, ""}}};
  client.instructions = {Call{MemberCall{f.root("C"), "step"},
                              "",
                              {{{0}, {}}},
                              {{{1}, {resultType(abstract), ""}}},
                              {}}};
  client.returns = {{{1}, {}}};
  auto checked = must(checkBody(client, f.env, {{f.root("C"), iface}}));
  for (const auto &rep : {f.field(), Type::product({})}) {
    Body implementation;
    implementation.id = f.id("step");
    implementation.signature = {
        {{rep, ""}}, {{resultType(rep), ""}}, {}, {}, {}};
    implementation.inputs = {{{0}, {rep, ""}}};
    implementation.instructions = {
        VariantConstruct{{{1}, {resultType(rep), ""}}, "Ok", {{0}, {}}}};
    implementation.returns = {{{1}, {}}};
    auto concrete = must(checkBody(implementation, f.env));
    auto selected =
        std::make_shared<Implementation>(Implementation{f.root("scalar"),
                                                        iface,
                                                        {{"Value", rep}},
                                                        {},
                                                        {{"step", concrete}},
                                                        {},
                                                        {}});
    auto linked = must(link({checked, {{f.root("C"), selected, "C"}}, {}}));
    auto lowered = must(lower(linked));
    expect(lowered.functions.size() == 2,
           "private variant result retains public nominal boundary");
  }
}
void associatedVariantsAndCounts() {
  Fixture f;
  // Selection is indexed by an association, even when private payload layouts
  // are identical. Substitution must preserve that subject in variant identity.
  f.env.libraries.front().declarations.push_back(f.id("B"));
  f.env.statics.push_back(
      {f.id("B"), Sort::association(), {}, {}, "other-subject"});
  for (auto &d : f.env.statics)
    if (d.id.name == "functor")
      d.parameters = {Sort::association()};
  auto iface = f.interface();
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type variant = Type::variant(f.id("record"), {"Ok", "Error"},
                               {opaque, Type::product({})});
  Body body;
  body.id = f.id("client");
  body.signature = {{{variant, ""}}, {{variant, ""}}, {}, {}, {}};
  body.inputs = {{{0}, {variant, ""}}};
  body.returns = {{{0}, {}}};
  auto checked = must(checkBody(body, f.env, {{f.root("C"), iface}}));
  std::vector<std::string> spellings;
  for (const auto &subject : {f.root("A"), f.root("B")}) {
    auto impl = f.implementation(iface, f.field());
    impl->selection = StaticTerm::apply(f.id("functor"), {subject});
    auto linked = must(link({checked, {{f.root("C"), impl, "C"}}, {}}));
    spellings.push_back(
        must(lower(linked)).functions.back().arguments.front().type);
  }
  expect(spellings[0] != spellings[1],
         "association substitution survives equal opaque payload layouts");

  Fixture counts;
  for (auto &d : counts.env.statics)
    if (d.result.kind == Sort::Kind::Component)
      d.members.emplace("Count", Sort::natural());
  InterfaceDecl decl;
  decl.id = counts.id("Cell");
  decl.self = counts.root("self");
  decl.types.push_back({"Value", {false, true}});
  Type self = Type::abstract(decl.self, "Value");
  decl.functions.emplace("step",
                         Signature{{{self, ""}}, {{self, ""}}, {}, {}, {}});
  decl.statics.push_back({"Count", Sort::natural(), std::nullopt});
  auto counted = must(formInterface(decl, counts.env));
  Type element = Type::abstract(counts.root("C"), "Value");
  Type array =
      Type::array(element, StaticTerm::project(counts.root("C"), "Count"));
  Body fold;
  fold.id = counts.id("client");
  fold.signature = {{{array, ""}, {element, ""}}, {{element, ""}}, {}, {}, {}};
  fold.inputs = {{{0}, {array, ""}}, {{1}, {element, ""}}};
  auto step = std::make_shared<Region>();
  step->inputs = {{{2}, {element, ""}}, {{3}, {element, ""}}};
  step->instructions = {Drop{{{2}, {}}}};
  step->returns = {{{3}, {}}};
  fold.instructions = {ArrayTraversal{
      {{0}, {}}, "", {{{1}, {}}}, {}, {{{4}, {element, ""}}}, step}};
  fold.returns = {{{4}, {}}};
  auto generic =
      must(checkBody(fold, counts.env, {{counts.root("C"), counted}}));
  auto impl = counts.implementation(counted, Type::product({}));
  impl->statics.emplace("Count", StaticTerm::natural(3));
  auto linked = must(link({generic, {{counts.root("C"), impl, "C"}}, {}}));
  expect(linked.functions().back().body.instructions.size() == 4,
         "associated count selects three unique element transfers");
  (void)must(lower(linked));
}
void variantFormationSeam() {
  Fixture f;
  auto variant = Type::variant(f.id("record"), {"Ready", "Empty"},
                               {f.field(), Type::product({})});
  Body body;
  body.id = f.id("client");
  body.signature = {{{variant, ""}}, {{variant, ""}}, {}, {}, {}};
  body.inputs = {{{0}, {variant, ""}}};
  body.returns = {{{0}, {}}};
  auto checked = must(checkBody(body, f.env));
  expect(must(link({checked, {}, {}}))
                 .functions()
                 .back()
                 .values.at(0)
                 .leaves.front()
                 .kind == LayoutLeaf::Kind::Variant,
         "variant retains one active-payload carrier");
  expect(identity(variant) !=
             identity(Type::record(f.id("record"), variant.fields,
                                   variant.elements)),
         "variant and record identities differ");
  variant.fields[1] = "Ready";
  body.signature.inputs[0].type = variant;
  body.inputs[0].port.type = variant;
  refusal(checkBody(body, f.env), "library-variant");
  variant = Type::variant(f.id("record"), {}, {});
  body.signature.inputs[0].type = variant;
  body.inputs[0].port.type = variant;
  refusal(checkBody(body, f.env), "library-variant");
}

const zkc::source::Instruction &last(const zkc::source::Body &body) {
  return body.back();
}
void admissible(const zkc::source::Module &m, llvm::StringRef name) {
  if (auto error = zkc::protocol::admit(m, false)) {
    llvm::errs() << "ADMIT " << name << ": " << llvm::toString(std::move(error))
                 << '\n';
    ++failures;
  }
}
void terminalStops() {
  Fixture f;
  auto iface = f.interface();
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type variant = Type::variant(f.id("record"), {"Ready", "Empty"},
                               {opaque, Type::product({})});
  // One arm stops while holding its payload and capture; the other continues
  // and carries the declared result of the join.
  Body b;
  b.id = f.id("client");
  b.signature = {{{variant, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {variant, ""}}, {{1}, {opaque, ""}}};
  auto ready = std::make_shared<Region>();
  ready->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  ready->instructions = {Stop{"reject"}};
  auto empty = std::make_shared<Region>();
  empty->inputs = {{{4}, {Type::product({}), ""}}, {{5}, {opaque, ""}}};
  empty->returns = {{{5}, {}}};
  Match match{{{0}, {}},
              "",
              {{{1}, {}}},
              {{{6}, {opaque, ""}}},
              {{"Ready", ready}, {"Empty", empty}}};
  b.instructions = {match};
  b.returns = {{{6}, {}}};
  auto checked = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  auto impl = f.implementation(iface, Type::product({}));
  auto linked = must(link({checked, {{f.root("C"), impl, "C"}}, {}}));
  auto lowered = must(lower(linked));
  const auto *matched =
      lowered.functions.back().body->front().get<zkc::source::Match>();
  expect(matched && matched->outputs.size() == 1 && matched->arms.size() == 2,
         "a stopping arm leaves the continuing join result intact");
  expect(matched && matched->arms[0].body.size() == 1 &&
             matched->arms[0].body[0].get<zkc::source::Stop>(),
         "a terminal arm lowers to one stop without a fabricated discard");
  expect(matched && last(matched->arms[1].body).get<zkc::source::Yield>(),
         "the continuing arm still yields");
  expect(last(*lowered.functions.back().body).get<zkc::source::Return>(),
         "a body with a stopping arm still returns");
  admissible(lowered, "mixed arms");

  // Every arm is checked whether or not it can be selected: a stopping arm is
  // not an excuse to skip its contents.
  auto unchecked = std::make_shared<Region>();
  unchecked->inputs = ready->inputs;
  unchecked->instructions = {Drop{{{2}, {}}}, Drop{{{2}, {}}}, Stop{"reject"}};
  auto bad = b;
  std::get<Match>(bad.instructions[0]).arms[0].body = unchecked;
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}),
          "library-resource-use");

  // Nothing may follow a stop, and a stopped region invents no result.
  bad = b;
  std::get<Match>(bad.instructions[0]).arms[0].body = std::make_shared<Region>(
      Region{ready->inputs, {Stop{"reject"}, Drop{{{2}, {}}}}, {}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-stop");
  bad = b;
  std::get<Match>(bad.instructions[0]).arms[0].body = std::make_shared<Region>(
      Region{ready->inputs, {Stop{"reject"}}, {{{3}, {}}}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-stop");
  bad = b;
  std::get<Match>(bad.instructions[0]).arms[0].body =
      std::make_shared<Region>(Region{ready->inputs, {Stop{"catch"}}, {}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-stop");

  // Every arm terminal: the join can carry nothing and ends its own region,
  // so the body promises a result that no path can reach.
  Body all;
  all.id = f.id("client");
  all.signature = {{{variant, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  all.inputs = {{{0}, {variant, ""}}, {{1}, {opaque, ""}}};
  auto stopReady = std::make_shared<Region>();
  stopReady->inputs = {{{2}, {opaque, ""}}};
  stopReady->instructions = {Stop{"abort"}};
  auto stopEmpty = std::make_shared<Region>();
  stopEmpty->inputs = {{{3}, {Type::product({}), ""}}};
  stopEmpty->instructions = {Stop{"exhausted"}};
  all.instructions = {Match{
      {{0}, {}}, "", {}, {}, {{"Ready", stopReady}, {"Empty", stopEmpty}}}};
  auto everyArm = must(checkBody(all, f.env, {{f.root("C"), iface}}));
  auto stopping = must(link({everyArm, {{f.root("C"), impl, "C"}}, {}}));
  auto stoppingLowered = must(lower(stopping));
  const auto &stoppingBody = *stoppingLowered.functions.back().body;
  matched = stoppingBody.front().get<zkc::source::Match>();
  expect(matched && matched->outputs.empty() &&
             last(matched->arms[0].body).get<zkc::source::Stop>() &&
             last(matched->arms[1].body).get<zkc::source::Stop>(),
         "an all-terminal join carries no value");
  // The carrier needs a terminator; every path already stopped inside the
  // match, so the one that closes the block is an unreachable halt.
  expect(stoppingBody.size() == 2 &&
             last(stoppingBody).get<zkc::source::Stop>() &&
             stoppingLowered.functions.back().results.size() == 1,
         "an all-terminal body halts and keeps its promised results");
  admissible(stoppingLowered, "all terminal arms");
  auto invented = all;
  std::get<Match>(invented.instructions[0]).outputs = {{{9}, {opaque, ""}}};
  refusal(checkBody(invented, f.env, {{f.root("C"), iface}}), "library-stop");
  auto continued = all;
  continued.instructions.push_back(Drop{{{1}, {}}});
  refusal(checkBody(continued, f.env, {{f.root("C"), iface}}), "library-stop");
  auto returning = all;
  returning.returns = {{{1}, {}}};
  refusal(checkBody(returning, f.env, {{f.root("C"), iface}}), "library-stop");
  expect(terminal(all.instructions) && !stopped(all.instructions),
         "an all-terminal match cannot continue yet is not itself a stop");
  expect(!terminal(b.instructions) && terminal(ready->instructions),
         "a join with a continuing arm can continue");

  // An arm that itself ends in an all-terminal join is terminal, so the outer
  // join is terminal too: the judgment follows the nesting.
  Body deep;
  deep.id = f.id("client");
  deep.signature = {{{variant, ""}, {variant, ""}}, {{opaque, ""}}, {}, {}, {}};
  deep.inputs = {{{10}, {variant, ""}}, {{11}, {variant, ""}}};
  auto innerReady = std::make_shared<Region>();
  innerReady->inputs = {{{14}, {opaque, ""}}};
  innerReady->instructions = {Stop{"reject"}};
  auto innerEmpty = std::make_shared<Region>();
  innerEmpty->inputs = {{{15}, {Type::product({}), ""}}};
  innerEmpty->instructions = {Stop{"exhausted"}};
  auto outerReady = std::make_shared<Region>();
  outerReady->inputs = {{{12}, {opaque, ""}}, {{13}, {variant, ""}}};
  outerReady->instructions = {Match{
      {{13}, {}}, "", {}, {}, {{"Ready", innerReady}, {"Empty", innerEmpty}}}};
  auto outerEmpty = std::make_shared<Region>();
  outerEmpty->inputs = {{{16}, {Type::product({}), ""}}, {{17}, {variant, ""}}};
  outerEmpty->instructions = {Stop{"refused"}};
  deep.instructions = {Match{{{10}, {}},
                             "",
                             {{{11}, {}}},
                             {},
                             {{"Ready", outerReady}, {"Empty", outerEmpty}}}};
  auto nested = must(checkBody(deep, f.env, {{f.root("C"), iface}}));
  expect(terminal(deep.instructions), "a nested all-terminal join is terminal");
  auto nestedLowered =
      must(lower(must(link({nested, {{f.root("C"), impl, "C"}}, {}}))));
  const auto *outer =
      nestedLowered.functions.back().body->front().get<zkc::source::Match>();
  expect(outer && last(outer->arms[0].body).get<zkc::source::Stop>() &&
             outer->arms[0].body.size() == 2 &&
             outer->arms[0].body.front().get<zkc::source::Match>(),
         "a terminal arm closes on its own nested join");
  admissible(nestedLowered, "nested terminal joins");

  // A member body may stop instead of returning; its declared results survive
  // for every caller, and no caller observes an invented value.
  Body stopStep;
  stopStep.id = f.id("step");
  stopStep.signature = {{{f.field(), ""}}, {{f.field(), ""}}, {}, {}, {}};
  stopStep.inputs = {{{0}, {f.field(), ""}}};
  stopStep.instructions = {Stop{"refused"}};
  auto refuses = std::make_shared<Implementation>(
      Implementation{f.root("scalar"),
                     iface,
                     {{"Value", f.field()}},
                     {},
                     {{"step", must(checkBody(stopStep, f.env))}},
                     {},
                     {}});
  auto stopCall =
      must(link({f.client(iface), {{f.root("C"), refuses, "stop"}}, {}}));
  expect(stopCall.functions().front().body.returns.empty() &&
             stopCall.functions().front().results.size() == 1,
         "a stopping member keeps its declared result boundary");
  auto calling = must(lower(stopCall));
  const zkc::source::Function *callee = nullptr, *caller = nullptr;
  for (const auto &fn : calling.functions)
    (fn.name == stopCall.entry() ? caller : callee) = &fn;
  expect(callee && callee->results.size() == 1 &&
             last(*callee->body).get<zkc::source::Stop>(),
         "the stopping member lowers to a stop with its declared results");
  const auto *call =
      caller ? caller->body->front().get<zkc::source::AlgorithmCall>()
             : nullptr;
  expect(call && call->outputs.size() == 1,
         "the caller still binds the declared result of a stopping callee");
  admissible(calling, "stopping member call");

  // A promised zero-storage result that no linked function ever holds still
  // needs its nominal slot in the lowered boundary.
  auto slotDecl = f.interface().declaration();
  slotDecl.functions.clear();
  auto slotOnly = must(formInterface(slotDecl, f.env));
  auto unheld = std::make_shared<Implementation>(
      Implementation{f.root("zero"),
                     slotOnly,
                     {{"Value", Type::product({})}},
                     {},
                     {},
                     {},
                     {}});
  Body promise;
  promise.id = f.id("client");
  Type held = Type::abstract(f.root("D"), "Value");
  promise.signature = {{}, {{held, ""}}, {}, {}, {}};
  promise.instructions = {Stop{"incomplete"}};
  auto promised = must(checkBody(promise, f.env, {{f.root("D"), slotOnly}}));
  auto zeroStorage =
      must(link({promised, {{f.root("D"), unheld, "unheld"}}, {}}));
  expect(zeroStorage.functions().back().results.size() == 1 &&
             zeroStorage.functions().back().results[0].leaves.size() == 1 &&
             zeroStorage.functions().back().results[0].leaves[0].kind ==
                 LayoutLeaf::Kind::ResourceUnit,
         "a stopping body keeps a zero-storage promised result");
  auto promisedLowered = must(lower(zeroStorage));
  expect(
      promisedLowered.functions.back().results.size() == 1 &&
          last(*promisedLowered.functions.back().body).get<zkc::source::Stop>(),
      "the unheld resource slot survives lowering of a stopping body");
  admissible(promisedLowered, "unheld promised result");
}
void terminalArmFacts() {
  Fixture f;
  auto declaration = f.interface().declaration();
  declaration.functions.at("step").postconditions = {
      {"", {f.root("F"), f.root("G")}}};
  auto iface = must(formInterface(declaration, f.env));
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type variant = Type::variant(f.id("record"), {"Ready", "Empty"},
                               {opaque, Type::product({})});
  Body b;
  b.id = f.id("client");
  b.signature = {{{variant, ""}, {opaque, ""}},
                 {{opaque, ""}},
                 {},
                 {{"", {f.root("F"), f.root("G")}}},
                 {}};
  b.inputs = {{{0}, {variant, ""}}, {{1}, {opaque, ""}}};
  auto ready = std::make_shared<Region>();
  ready->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  ready->instructions = {Call{MemberCall{f.root("C"), "step"},
                              "",
                              {{{2}, {}}},
                              {{{7}, {opaque, ""}}},
                              {}},
                         Drop{{{3}, {}}}};
  ready->returns = {{{7}, {}}};
  auto empty = std::make_shared<Region>();
  empty->inputs = {{{4}, {Type::product({}), ""}}, {{5}, {opaque, ""}}};
  empty->instructions = {Stop{"reject"}};
  b.instructions = {Match{{{0}, {}},
                          "",
                          {{{1}, {}}},
                          {{{6}, {opaque, ""}}},
                          {{"Ready", ready}, {"Empty", empty}}}};
  b.returns = {{{6}, {}}};
  // The join keeps what the continuing arm established; the terminal arm
  // neither weakens it nor invents one of its own.
  must(checkBody(b, f.env, {{f.root("C"), iface}}));
  auto continuing = std::make_shared<Region>(*empty);
  continuing->instructions.clear();
  continuing->returns = {{{5}, {}}};
  auto weakened = b;
  std::get<Match>(weakened.instructions[0]).arms[1].body = continuing;
  refusal(checkBody(weakened, f.env, {{f.root("C"), iface}}), "library-bound");
}
void stopsThroughTraversal() {
  Fixture f;
  auto iface = f.interface();
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type array = Type::array(opaque, f.root("N"));
  Body b;
  b.id = f.id("client");
  b.signature = {{{array, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {array, ""}}, {{1}, {opaque, ""}}};
  auto step = std::make_shared<Region>();
  step->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  step->instructions = {Stop{"exhausted"}};
  b.instructions = {ArrayTraversal{
      {{0}, {}}, "", {{{1}, {}}}, {}, {{{4}, {opaque, ""}}}, step}};
  b.returns = {{{4}, {}}};
  // The symbolic body is checked once, before any count is selected.
  auto checked = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  auto impl = f.implementation(iface, f.field());
  auto zero = must(link({checked,
                         {{f.root("C"), impl, "C"}},
                         {{{f.root("N"), StaticTerm::natural(0)}}, {}}}));
  const auto &noTrip = zero.functions().back();
  expect(noTrip.body.instructions.size() == 1 &&
             std::holds_alternative<Project>(noTrip.body.instructions[0]) &&
             noTrip.body.returns.size() == 1,
         "a zero-trip traversal returns its initial state even when the body "
         "stops");
  auto zeroLowered = must(lower(zero));
  expect(last(*zeroLowered.functions.back().body).get<zkc::source::Return>(),
         "the zero-trip lowering returns rather than stops");
  admissible(zeroLowered, "zero trip");
  auto positive = must(link({checked,
                             {{f.root("C"), impl, "C"}},
                             {{{f.root("N"), StaticTerm::natural(2)}}, {}}}));
  const auto &aborted = positive.functions().back();
  expect(aborted.body.instructions.size() == 1 &&
             std::holds_alternative<Stop>(aborted.body.instructions[0]) &&
             aborted.body.returns.empty() && aborted.results.size() == 1,
         "a positive trip aborts and transfers no carried state");
  auto abortedLowered = must(lower(positive));
  expect(last(*abortedLowered.functions.back().body).get<zkc::source::Stop>() &&
             abortedLowered.functions.back().results.size() == 1,
         "an aborted traversal lowers to a stop with declared results");
  admissible(abortedLowered, "aborted traversal");

  // A trip that only stops on one alternative still completes every trip: each
  // expanded arm keeps its own definitions and its own terminal path.
  Type variant = Type::variant(f.id("record"), {"Ready", "Empty"},
                               {opaque, Type::product({})});
  Body perElement;
  perElement.id = f.id("client");
  Type variants = Type::array(variant, StaticTerm::natural(2));
  perElement.signature = {
      {{variants, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  perElement.inputs = {{{0}, {variants, ""}}, {{1}, {opaque, ""}}};
  auto ready = std::make_shared<Region>();
  ready->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  ready->instructions = {Stop{"reject"}};
  auto other = std::make_shared<Region>();
  other->inputs = {{{4}, {Type::product({}), ""}}, {{5}, {opaque, ""}}};
  other->returns = {{{5}, {}}};
  auto trip = std::make_shared<Region>();
  trip->inputs = {{{6}, {variant, ""}}, {{7}, {opaque, ""}}};
  trip->instructions = {Match{{{6}, {}},
                              "",
                              {{{7}, {}}},
                              {{{8}, {opaque, ""}}},
                              {{"Ready", ready}, {"Empty", other}}}};
  trip->returns = {{{8}, {}}};
  perElement.instructions = {ArrayTraversal{
      {{0}, {}}, "", {{{1}, {}}}, {}, {{{9}, {opaque, ""}}}, trip}};
  perElement.returns = {{{9}, {}}};
  auto conditional =
      must(link({must(checkBody(perElement, f.env, {{f.root("C"), iface}})),
                 {{f.root("C"), impl, "C"}},
                 {}}));
  const auto &trips = conditional.functions().back().body.instructions;
  expect(trips.size() == 3 && std::holds_alternative<Match>(trips[0]) &&
             std::holds_alternative<Match>(trips[1]) &&
             conditional.functions().back().body.returns.size() == 1,
         "a conditionally stopping trip expands once per element");
  expect(std::get<Match>(trips[0]).outputs[0].id.index !=
             std::get<Match>(trips[1]).outputs[0].id.index,
         "each expanded trip defines its own join result");
  auto lowered = must(lower(conditional));
  expect(last(*lowered.functions.back().body).get<zkc::source::Return>(),
         "a conditionally stopping traversal still returns");
  admissible(lowered, "conditionally stopping trips");
}
void terminalResourceObligations() {
  Fixture f;
  const Type t = Type::parameter(f.id("T"));
  const Type sum =
      Type::variant(f.id("record"), {"Ok", "Error"}, {t, Type::product({})});
  Body b;
  b.id = f.id("client");
  b.typeBounds = {{f.id("T"), {false, false}}};
  b.signature = {{{sum, ""}, {t, ""}}, {{t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {sum, ""}}, {{1}, {t, ""}}};
  auto ok = std::make_shared<Region>();
  ok->inputs = {{{2}, {t, ""}}, {{3}, {t, ""}}};
  ok->instructions = {Stop{"reject"}};
  auto error = std::make_shared<Region>();
  error->inputs = {{{4}, {Type::product({}), ""}}, {{5}, {t, ""}}};
  error->returns = {{{5}, {}}};
  b.instructions = {Match{{{0}, {}},
                          "",
                          {{{1}, {}}},
                          {{{6}, {t, ""}}},
                          {{"Ok", ok}, {"Error", error}}}};
  b.returns = {{{6}, {}}};
  // A terminal arm may leave a non-droppable value alive: releasing it is the
  // runtime's work, not a fabricated drop in a path that never continues.
  must(checkBody(b, f.env));
  auto leaking = std::make_shared<Region>();
  leaking->inputs = ok->inputs;
  leaking->returns = {{{3}, {}}};
  auto bad = b;
  std::get<Match>(bad.instructions[0]).arms[0].body = leaking;
  refusal(checkBody(bad, f.env), "library-resource-leak");
}
void checkedConditionals() {
  Fixture f;
  auto iface = f.interface();
  const Type opaque = Type::abstract(f.root("C"), "Value");
  const Type boolean = Type::logical("bool");
  Body b;
  b.id = f.id("client");
  b.signature = {{{boolean, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {boolean, ""}}, {{1}, {opaque, ""}}};
  auto yes = std::make_shared<Region>();
  yes->inputs = {{{2}, {opaque, ""}}};
  yes->instructions = {Call{MemberCall{f.root("C"), "step"},
                            "",
                            {{{2}, {}}},
                            {{{4}, {opaque, ""}}},
                            {}}};
  yes->returns = {{{4}, {}}};
  auto no = std::make_shared<Region>();
  no->inputs = {{{3}, {opaque, ""}}};
  no->returns = {{{3}, {}}};
  b.instructions = {Conditional{LocalBranches{{{0}, {}},
                                              "",
                                              {{{1}, {}}},
                                              {{{5}, {opaque, ""}}},
                                              {{"then", yes}, {"else", no}}}}};
  b.returns = {{{5}, {}}};
  auto checked = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  for (const auto &representation :
       {f.field(), Type::product({}), Type::product({f.field(), f.field()})}) {
    auto impl = f.implementation(iface, representation);
    auto linked = must(link({checked, {{f.root("C"), impl, "C"}}, {}}));
    auto lowered = must(lower(linked));
    const auto *conditional =
        lowered.functions.back().body->front().get<zkc::source::Conditional>();
    expect(conditional && !conditional->captures.empty(),
           "typed conditional retains affine captures including zero-storage "
           "tokens");
    admissible(lowered, "conditional opaque layouts");
  }
  auto bad = b;
  std::get<Conditional>(bad.instructions[0]).branches.input = {{1}, {}};
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-condition");
  bad = b;
  std::get<Conditional>(bad.instructions[0]).branches.arms[1].alternative =
      "then";
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-branch-arm");
  bad = b;
  std::get<Conditional>(bad.instructions[0])
      .branches.captures.push_back({{1}, {}});
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}),
          "library-resource-use");
  auto isolated = std::make_shared<Region>(*no);
  isolated->returns = {{{1}, {}}};
  bad = b;
  std::get<Conditional>(bad.instructions[0]).branches.arms[1].body = isolated;
  refusal(checkBody(bad, f.env, {{f.root("C"), iface}}), "library-value");
  // Checking deep-copies both arms: subsequent builder mutation changes no
  // checked semantics or identity.
  const auto key = checked.identity();
  no->instructions = {Stop{"refused"}};
  no->returns.clear();
  expect(checked.identity() == key &&
             !terminal(std::get<Conditional>(checked.body().instructions[0])
                           .branches.arms[1]
                           .body->instructions),
         "checked conditional owns immutable isolated regions");
  auto mixed = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  expect(mixed.identity() != key,
         "conditional arm semantics enter body identity");
  // Continuing-only fact joins use precisely the same checker as Match.
  auto declaration = iface.declaration();
  declaration.functions.at("step").postconditions = {
      {"", {f.root("F"), f.root("G")}}};
  auto facts = must(formInterface(declaration, f.env));
  b.signature.postconditions = {{"", {f.root("F"), f.root("G")}}};
  must(checkBody(b, f.env, {{f.root("C"), facts}}));
  no->instructions.clear();
  no->returns = {{{3}, {}}};
  refusal(checkBody(b, f.env, {{f.root("C"), facts}}), "library-bound");

  // A selected terminal member must be visible through a Conditional arm.
  b.signature.postconditions.clear();
  Body stopStep;
  stopStep.id = f.id("step");
  stopStep.signature = {{{f.field(), ""}}, {{f.field(), ""}}, {}, {}, {}};
  stopStep.inputs = {{{0}, {f.field(), ""}}};
  stopStep.instructions = {Stop{"reject"}};
  auto stopping = f.implementation(iface, f.field());
  stopping->functions.insert_or_assign("step",
                                       must(checkBody(stopStep, f.env)));
  auto selected = must(link({checked, {{f.root("C"), stopping, "C"}}, {}}));
  const auto &join =
      std::get<Conditional>(selected.functions().back().body.instructions[0])
          .branches;
  expect(
      terminal(join.arms[0].body->instructions) &&
          join.arms[0].body->returns.empty() &&
          !terminal(join.arms[1].body->instructions),
      "selected terminal call loses its dead yield while mixed join continues");
  expect(std::holds_alternative<Call>(join.arms[0].body->instructions[0]),
         "normalization retains the executed stopping call");
  admissible(must(lower(selected)), "selected terminal conditional arm");
  auto alsoCalls = std::make_shared<Region>(*no);
  alsoCalls->instructions = {Call{MemberCall{f.root("C"), "step"},
                                  "",
                                  {{{3}, {}}},
                                  {{{6}, {opaque, ""}}},
                                  {}}};
  alsoCalls->returns = {{{6}, {}}};
  std::get<Conditional>(b.instructions[0]).branches.arms[1].body = alsoCalls;
  b.signature.postconditions = {{"", {f.root("F"), f.root("G")}}};
  must(checkBody(b, f.env, {{f.root("C"), facts}}));
  b.signature.postconditions.clear();
  auto both = must(checkBody(b, f.env, {{f.root("C"), iface}}));
  must(link(
      {both, {{f.root("C"), f.implementation(iface, f.field()), "C"}}, {}}));
  auto stopped = must(link({both, {{f.root("C"), stopping, "C"}}, {}}));
  const auto &closed = *std::find_if(
      stopped.functions().begin(), stopped.functions().end(),
      [&](const auto &fn) { return fn.symbol == stopped.entry(); });
  const auto &stoppedJoin =
      std::get<Conditional>(closed.body.instructions.front()).branches;
  expect(stoppedJoin.outputs.empty() && terminal(closed.body.instructions),
         "selected all-terminal join discards unreachable results");
  admissible(must(lower(stopped)), "selected all-terminal conditional");
}

void conditionalPermissions() {
  Fixture f;
  const Type t = Type::parameter(f.id("T")), boolean = Type::logical("bool");
  Body b;
  b.id = f.id("client");
  b.signature = {{{boolean, ""}, {t, ""}}, {{t, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {boolean, ""}}, {{1}, {t, ""}}};
  auto yes = std::make_shared<Region>();
  yes->inputs = {{{2}, {t, ""}}};
  yes->returns = {{{2}, {}}};
  auto no = std::make_shared<Region>();
  no->inputs = {{{3}, {t, ""}}};
  no->returns = {{{3}, {}}};
  b.instructions = {Conditional{LocalBranches{{{0}, {}},
                                              "",
                                              {{{1}, {}}},
                                              {{{4}, {t, ""}}},
                                              {{"then", yes}, {"else", no}}}}};
  b.returns = {{{4}, {}}};
  for (bool copy : {false, true})
    for (bool drop : {false, true}) {
      b.typeBounds = {{f.id("T"), {copy, drop}}};
      must(checkBody(b, f.env));
    }
  // Mandatory use is independent of copying: a continuing arm cannot silently
  // abandon a copyable, nondroppable capture, but a terminal arm owes no use.
  b.typeBounds = {{f.id("T"), {true, false}}};
  yes->instructions = {Stop{"abort"}};
  yes->returns.clear();
  must(checkBody(b, f.env));
  yes->instructions = {Drop{{{2}, {}}}};
  yes->returns = {{{2}, {}}};
  refusal(checkBody(b, f.env), "library-drop");
  b.typeBounds[0].permissions.drop = true;
  must(checkBody(b, f.env));
  b.typeBounds[0].permissions.copy = false;
  refusal(checkBody(b, f.env), "library-resource-use");
  yes->instructions.clear();
  // Check unused capture inside each arm, independently of its physical size.
  no->inputs.push_back({{6}, {t, ""}});
  yes->inputs.push_back({{7}, {t, ""}});
  b.signature.inputs.push_back({t, ""});
  b.inputs.push_back({{8}, {t, ""}});
  std::get<Conditional>(b.instructions[0])
      .branches.captures.push_back({{8}, {}});
  b.typeBounds[0].permissions = {true, false};
  refusal(checkBody(b, f.env), "library-resource-leak");
  b.typeBounds[0].permissions.drop = true;
  must(checkBody(b, f.env));
}

void variantStaticCaptures() {
  Fixture f;
  // The captured actuals decide identity even when no alternative mentions
  // them and both private layouts agree.
  auto captured = [&](const StaticTerm &subject) {
    auto v = Type::variant(f.id("record"), {"Ok", "Error"},
                           {f.field(), Type::product({})});
    v.arguments = {subject};
    return v;
  };
  Type left = captured(f.root("F")), right = captured(f.root("G"));
  expect(identity(left) != identity(right),
         "phantom captures separate otherwise equal variants");
  Body b;
  b.id = f.id("client");
  b.signature = {{{left, ""}}, {{left, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {left, ""}}};
  b.returns = {{{0}, {}}};
  auto checked = must(checkBody(b, f.env));
  auto sameLayout = b;
  sameLayout.signature.outputs = {{right, ""}};
  refusal(checkBody(sameLayout, f.env), "library-type-mismatch");
  auto spelling = [&](const Type &v) {
    Body one = b;
    one.signature = {{{v, ""}}, {{v, ""}}, {}, {}, {}};
    one.inputs = {{{0}, {v, ""}}};
    auto linked = must(link({must(checkBody(one, f.env)), {}, {}}));
    return must(lower(linked)).functions.back().arguments.front().type;
  };
  expect(spelling(left) != spelling(right),
         "captured actuals reach the lowered nominal descriptor");
  expect(must(link({checked, {}, {}}))
                 .functions()
                 .back()
                 .values.at(0)
                 .leaves.front()
                 .kind == LayoutLeaf::Kind::Variant,
         "a captured variant keeps one active-payload carrier");

  // A phantom component capture is substituted by the selected binding, so two
  // selections with identical private payload layouts stay distinct nominals.
  auto iface = f.interface();
  Type component = captured(f.root("C"));
  Body shared;
  shared.id = f.id("client");
  shared.signature = {{{component, ""}}, {{component, ""}}, {}, {}, {}};
  shared.inputs = {{{0}, {component, ""}}};
  shared.returns = {{{0}, {}}};
  auto client = must(checkBody(shared, f.env, {{f.root("C"), iface}}));
  std::vector<std::string> selected;
  for (const char *selection : {"scalar", "pair"}) {
    auto impl = f.implementation(iface, f.field(), selection);
    auto linked = must(link({client, {{f.root("C"), impl, selection}}, {}}));
    selected.push_back(
        must(lower(linked)).functions.back().arguments.front().type);
  }
  expect(selected[0] != selected[1],
         "a phantom component capture follows its selection into the nominal");

  // Repeated captures remain exact with the scalable carrier. The frontend
  // must not assume the obsolete descriptor byte limit.
  auto oversized = left;
  oversized.arguments.assign(64, f.root("F"));
  Body wide;
  wide.id = f.id("client");
  wide.signature = {{{oversized, ""}}, {{oversized, ""}}, {}, {}, {}};
  wide.inputs = {{{0}, {oversized, ""}}};
  wide.returns = {{{0}, {}}};
  auto wideSource =
      must(lower(must(link({must(checkBody(wide, f.env)), {}, {}}))));
  expect(wideSource.functions.back().arguments.front().type != spelling(left),
         "repeated static captures remain part of exact nominal identity");
  admissible(wideSource, "repeated nominal captures");

  // Every captured term is checked against the captured environment, and a
  // record still admits no static arguments.
  auto illSorted = left;
  illSorted.arguments = {
      StaticTerm::apply(f.id("functor"), {StaticTerm::natural(2)})};
  b.signature = {{{illSorted, ""}}, {{illSorted, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {illSorted, ""}}};
  refusal(checkBody(b, f.env), "library-static-sort");
  auto unknown = left;
  unknown.arguments = {StaticTerm::project(f.root("F"), "absent")};
  b.signature = {{{unknown, ""}}, {{unknown, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {unknown, ""}}};
  refusal(checkBody(b, f.env), "library-member");
  auto record = Type::record(f.id("record"), {"x"}, {f.field()});
  record.arguments = {f.root("F")};
  b.signature = {{{record, ""}}, {{record, ""}}, {}, {}, {}};
  b.inputs = {{{0}, {record, ""}}};
  refusal(checkBody(b, f.env), "library-record");
}
} // namespace
void locatedLoweringBoundary() {
  Fixture f;
  Body body;
  body.id = f.id("client");
  body.signature = {
      {{f.field(), "prover"}}, {{f.field(), "prover"}}, {}, {}, {}};
  body.inputs = {{{0}, {f.field(), "prover"}}};
  body.returns = {{{0}, {}}};
  auto checked = must(checkBody(body, f.env));
  auto linked = must(link({checked, {}, {}}));
  refusal(lower(linked), "library-lowering");
}

void qualifiedOriginCollisions() {
  Fixture f;
  auto body = f.privateBody(Type::logical("bool"));
  auto first = must(link({body, {}, {}}));
  auto foreign = body.body();
  foreign.id.library.name = "other";
  auto environment = f.env;
  environment.libraries.push_back({foreign.id.library, {foreign.id}});
  auto second = must(link({must(checkBody(foreign, environment)), {}, {}}));
  must(lower(first));
  must(lower(second));
  must(lower(std::vector<LinkedProgram>{first, first}));
  refusal(lower(std::vector<LinkedProgram>{first, second}),
          "library-origin-ambiguity");
}

void checkedSourceCalls() {
  Fixture f;
  auto api = f.interface();
  auto helperBody = f.clientBody(api);
  helperBody.id = f.id("Other");
  helperBody.signature.inputLabels = {"state"};
  auto contract = must(formCallable({helperBody.id,
                                     helperBody.signature,
                                     {f.id("C")},
                                     {},
                                     {{f.root("C"), api}}},
                                    f.env));
  auto helper = must(checkBody(helperBody, f.env, {{f.root("C"), api}}));
  auto callerBody = f.clientBody(api);
  auto &call = std::get<Call>(callerBody.instructions.front());
  call.target = SourceCall{contract, {{{f.root("C"), f.root("C")}}, {}}};
  auto caller = must(checkBody(callerBody, f.env, {{f.root("C"), api}}));
  auto selected = f.implementation(api, f.field());
  LinkRequest request{caller, {{f.root("C"), selected, "C"}}, {}, {helper}};
  auto linked = must(link(request));
  expect(linked.functions().size() == 3,
         "source helper emits a closed first-order function");
  auto helperFunction = std::find_if(
      linked.functions().begin(), linked.functions().end(),
      [&](const auto &function) {
        return identity(function.body.id) == identity(helperBody.id);
      });
  expect(helperFunction != linked.functions().end() &&
             helperFunction->logicalSignature.inputLabels ==
                 std::vector<std::string>{"state"} &&
             helperFunction->logicalSignature.inputs.front().type.kind ==
                 Type::Kind::Abstract,
         "closed helper retains its public label and selected abstract type");
  expect(linked.dependencies().size() == 2,
         "source helper carries exact body dependency");
  must(lower(linked));
  auto missing = request;
  missing.helpers.clear();
  refusal(link(missing), "library-open-call");
  auto changed = helperBody;
  changed.signature.inputLabels = {"renamed"};
  auto changedContract = must(formCallable(
      {changed.id, changed.signature, {f.id("C")}, {}, {{f.root("C"), api}}},
      f.env));
  expect(contract.identity() != changedContract.identity(),
         "public labels enter exact callable identity");
  auto drift = request;
  drift.helpers = {must(checkBody(changed, f.env, {{f.root("C"), api}}))};
  refusal(link(drift), "library-source-signature-drift");
  changed = helperBody;
  changed.instructions.clear();
  changed.returns = {{{0}, {}}};
  auto edited = request;
  edited.helpers = {must(checkBody(changed, f.env, {{f.root("C"), api}}))};
  auto editedLink = must(link(edited));
  expect(linked.identity() != editedLink.identity(),
         "helper body edits invalidate executable identity");
  expect(caller.identity() == request.client.identity(),
         "caller contract survives private helper body edit");
  auto recursive = helperBody;
  std::get<Call>(recursive.instructions.front()).target = call.target;
  auto cycle = request;
  cycle.helpers = {must(checkBody(recursive, f.env, {{f.root("C"), api}}))};
  refusal(link(cycle), "library-call-cycle");
  auto malformed = callerBody;
  std::get<SourceCall>(std::get<Call>(malformed.instructions.front()).target)
      .arguments.statics.clear();
  refusal(checkBody(malformed, f.env, {{f.root("C"), api}}),
          "library-source-actual");
  malformed = callerBody;
  std::get<SourceCall>(std::get<Call>(malformed.instructions.front()).target)
      .arguments.statics[0]
      .second = f.root("F");
  refusal(checkBody(malformed, f.env, {{f.root("C"), api}}),
          "library-static-sort");
  malformed = callerBody;
  std::get<Call>(malformed.instructions.front()).attributes = {"hidden"};
  refusal(checkBody(malformed, f.env, {{f.root("C"), api}}),
          "library-call-attributes");
  malformed = callerBody;
  malformed.instructions.push_back(malformed.instructions.front());
  std::get<Call>(malformed.instructions.back()).outputs[0].id = {2};
  refusal(checkBody(malformed, f.env, {{f.root("C"), api}}),
          "library-resource-use");
  auto labels = api.declaration();
  labels.functions.at("step").inputLabels = {"state", "extra"};
  refusal(formInterface(labels, f.env), "library-parameter-label");
  labels.functions.at("step").inputLabels = {""};
  refusal(formInterface(labels, f.env), "library-parameter-label");
}

void checkedHelperTypeActuals() {
  Fixture f;
  const auto parameter = Type::parameter(f.id("T"));
  Body helperBody;
  helperBody.id = f.id("Other");
  helperBody.signature = {{{parameter, ""}}, {{parameter, ""}}, {}, {}, {}};
  helperBody.signature.inputLabels = {"value"};
  helperBody.typeBounds = {{f.id("T"), {true, true}}};
  helperBody.inputs = {{{0}, {parameter, ""}}};
  helperBody.returns = {{{0}, {}}};
  auto contract = must(formCallable({helperBody.id,
                                     helperBody.signature,
                                     {f.id("T")},
                                     helperBody.typeBounds,
                                     {}},
                                    f.env));
  auto helper = must(checkBody(helperBody, f.env));
  Body callerBody;
  callerBody.id = f.id("client");
  const auto boolean = Type::logical("bool");
  callerBody.signature = {{{boolean, ""}}, {{boolean, ""}}, {}, {}, {}};
  callerBody.inputs = {{{0}, {boolean, ""}}};
  callerBody.instructions.push_back(
      Call{SourceCall{contract, {{}, {{f.id("T"), boolean}}}},
           "",
           {{{0}, {}}},
           {{{1}, {boolean, ""}}},
           {}});
  callerBody.returns = {{{1}, {}}};
  auto caller = must(checkBody(callerBody, f.env));
  auto linked = must(link({caller, {}, {}, {helper}}));
  must(lower(linked));
  auto invisible = f.env;
  for (auto &library : invisible.libraries)
    llvm::erase_if(library.declarations, [&](const auto &decl) {
      return identity(decl) == identity(helperBody.id);
    });
  refusal(checkBody(callerBody, invisible), "library-capture");
  auto ownerEnvironment = f.env;
  ownerEnvironment.libraries.front().declarations.push_back(
      f.id("privateSubject"));
  ownerEnvironment.statics.push_back({f.id("privateSubject"),
                                      Sort::association(),
                                      {},
                                      {},
                                      "owner-private-bytes"});
  auto privateContract = must(formCallable({helperBody.id,
                                            helperBody.signature,
                                            {f.id("T")},
                                            helperBody.typeBounds,
                                            {}},
                                           ownerEnvironment));
  auto privateCaller = callerBody;
  std::get<SourceCall>(
      std::get<Call>(privateCaller.instructions.front()).target)
      .callable = privateContract;
  auto privateChecked = must(checkBody(privateCaller, f.env));
  auto privateBody = must(checkBody(helperBody, ownerEnvironment));
  must(link({privateChecked, {}, {}, {privateBody}}));
  expect(privateChecked.environment().statics.size() == f.env.statics.size(),
         "caller need not import helper owner's private static environment");
  auto bad = callerBody;
  std::get<SourceCall>(std::get<Call>(bad.instructions.front()).target)
      .arguments.types.front()
      .second = Type::logical("rng", {f.root("F")});
  refusal(checkBody(bad, f.env), "library-permission-bound");
  auto effectful = helperBody;
  effectful.signature.effects = {"local"};
  auto effectContract = must(formCallable({effectful.id,
                                           effectful.signature,
                                           {f.id("T")},
                                           effectful.typeBounds,
                                           {}},
                                          f.env));
  bad = callerBody;
  std::get<SourceCall>(std::get<Call>(bad.instructions.front()).target)
      .callable = effectContract;
  refusal(checkBody(bad, f.env), "library-effect");
  auto invalid = contract.declaration();
  invalid.parameters.push_back(f.id("T"));
  refusal(formCallable(invalid, f.env), "library-callable-parameter");
  Body fieldHelper;
  fieldHelper.id = f.id("Other");
  fieldHelper.signature = {{{f.field(), ""}}, {{f.field(), ""}}, {}, {}, {}};
  fieldHelper.inputs = {{{0}, {f.field(), ""}}};
  fieldHelper.returns = {{{0}, {}}};
  auto fieldContract = must(
      formCallable({fieldHelper.id, fieldHelper.signature, {}, {}, {}}, f.env));
  auto fieldCaller = fieldHelper;
  fieldCaller.id = f.id("client");
  fieldCaller.instructions.push_back(Call{SourceCall{fieldContract, {}},
                                          "",
                                          {{{0}, {}}},
                                          {{{1}, {f.field(), ""}}},
                                          {}});
  fieldCaller.returns = {{{1}, {}}};
  auto changedEnvironment = f.env;
  for (auto &root : changedEnvironment.statics)
    if (identity(root.id) == identity(f.id("F")))
      root.capturedSubject = "bls12-381.fr";
  refusal(checkBody(fieldCaller, changedEnvironment),
          "library-assumption-drift");
  Signature pair;
  pair.inputs = {{boolean, ""}, {boolean, ""}};
  pair.inputLabels = {"first", "second"};
  expect(must(bindArguments(pair, 2, {"second", "first"})) ==
             std::vector<unsigned>({1, 0}),
         "argument mapping is written order to formal order");
  refusal(bindArguments(pair, 2, {"first", "first"}),
          "library-source-argument-name");
  pair.inputLabels.clear();
  refusal(bindArguments(pair, 2, {"first", "second"}),
          "library-source-argument-name");
  expect(must(bindArguments(pair, 2, {})) == std::vector<unsigned>({0, 1}),
         "unlabeled contracts preserve positional operations");
}

// Refusals that source never reaches, because the frontend resolves the same
// fact before it builds a body, and that a direct caller of the checker does.
void directCallerRefusals() {
  Fixture f;
  auto i = f.interface();
  // A member call on a component for which no interface is imported.
  Body unimported;
  unimported.id = f.id("client");
  unimported.instructions.push_back(
      Call{MemberCall{f.root("C"), "step"}, "", {}, {}, {}});
  refusedWith(checkBody(unimported, f.env), "library-call");
  // A member call naming a function the imported interface does not have.
  Body absent = f.clientBody(i);
  std::get<MemberCall>(std::get<Call>(absent.instructions[0]).target).member =
      "absent";
  refusedWith(checkBody(absent, f.env, {{f.root("C"), i}}), "library-call");
  // A body whose qualified identity has an empty name, or an empty module
  // segment.
  for (auto id : {QualifiedDecl{f.library, {"core"}, ""},
                  QualifiedDecl{f.library, {""}, "client"}}) {
    Body unnamed;
    unnamed.id = id;
    refusedWith(checkBody(unnamed, f.env), "library-identity");
  }
  // An installed logical type given fewer actuals than it declares.
  Body bare;
  bare.id = f.id("client");
  Type field = Type::logical("field");
  bare.signature = {{{field, ""}}, {{field, ""}}, {}, {}, {}};
  bare.inputs = {{{0}, {field, ""}}};
  bare.returns = {{{0}, {}}};
  refusedWith(checkBody(bare, f.env), "library-type-arity");
  // An installed operation given too few and too many static actuals.
  for (auto actuals : {std::vector<StaticTerm>{},
                       std::vector<StaticTerm>{f.root("F"), f.root("F")}}) {
    Body constant;
    constant.id = f.id("client");
    constant.instructions.push_back(Call{LogicalCall{"field.constant", actuals},
                                         "",
                                         {},
                                         {{{0}, {f.field(), ""}}},
                                         {"1"}});
    refusedWith(checkBody(constant, f.env), "library-operation-arity");
  }
}
// Inputs the source frontend never builds, because it forms every body,
// interface, environment and link request itself. A caller of this API can
// build them, and each is refused under its own identifier.
void apiOnlyRefusals() {
  Fixture f;
  auto i = f.interface();
  // A body with fewer input values than its signature has inputs.
  Body arity = f.clientBody(i);
  arity.inputs.clear();
  refusedWith(checkBody(arity, f.env, {{f.root("C"), i}}),
              "library-body-arity");
  // An interface whose Self is a concrete component rather than a parameter.
  auto declaration = i.declaration();
  declaration.self = f.root("scalar");
  refusedWith(formInterface(declaration, f.env), "library-interface-self");
  // An interface that bounds the same type parameter twice.
  declaration = i.declaration();
  declaration.typeBounds = {{f.id("T"), {}}, {f.id("T"), {}}};
  refusedWith(formInterface(declaration, f.env), "library-type-bound");
  // A type parameter used with no permission bound in scope.
  Body unbounded;
  unbounded.id = f.id("client");
  Type parameter = Type::parameter(f.id("T"));
  unbounded.signature = {{{parameter, ""}}, {{parameter, ""}}, {}, {}, {}};
  unbounded.inputs = {{{0}, {parameter, ""}}};
  unbounded.returns = {{{0}, {}}};
  refusedWith(checkBody(unbounded, f.env), "library-type-bound");
  // The same type parameter, bounded, linked without a type actual.
  unbounded.typeBounds = {{f.id("T"), {true, true}}};
  refusedWith(link({must(checkBody(unbounded, f.env)), {}, {}}),
              "library-open-type");
  // A precondition over a static parameter that nothing selects.
  Body open;
  open.id = f.id("client");
  open.signature.preconditions = {{"", {f.root("N"), f.root("N")}}};
  refusedWith(link({must(checkBody(open, f.env)), {}, {}}),
              "library-open-term");
  // A captured declaration whose hidden actuals include itself.
  auto cyclic = f.env;
  for (auto &d : cyclic.statics)
    if (d.id.name == "zero")
      d.capturedDependencies = {f.root("zero")};
  refusedWith(selectionIdentity(f.root("zero"), cyclic),
              "library-selection-cycle");
  // One component parameter imported twice.
  refusedWith(
      checkBody(f.clientBody(i), f.env, {{f.root("C"), i}, {f.root("C"), i}}),
      "library-import");
  // A static actual for a declaration that is not a parameter.
  refusedWith(link({f.privateBody(f.field()),
                    {},
                    {{{f.root("scalar"), f.root("scalar")}}, {}}}),
              "library-substitution");
  // A selection environment capturing a domain differently from the client.
  auto elsewhere = f.env;
  for (auto &d : elsewhere.statics)
    if (d.id.name == "G")
      d.capturedSubject = "koala-bear";
  LinkRequest conflicting{
      f.client(i), {{f.root("C"), f.implementation(i, f.field()), "C"}}, {}};
  conflicting.selectionEnvironment = elsewhere;
  refusedWith(link(conflicting), "library-capture-conflict");
  // An implementation bound as its own dependency.
  auto recursive = f.implementation(i, f.field());
  recursive->imports = {{f.root("D"), i}};
  recursive->dependencies = {{f.root("D"), recursive, "self"}};
  refusedWith(link({f.client(i), {{f.root("C"), recursive, "C"}}, {}}),
              "library-link-cycle");
  // The implementation owns itself through that binding until it is cleared.
  recursive->dependencies.clear();
  // Two helper bodies under one identity with different content.
  refusedWith(
      link({f.privateBody(f.field()),
            {},
            {},
            {f.privateBody(f.field()), f.privateBody(f.field(), true)}}),
      "library-source-body-drift");
  // A traversal carrying out more states than it carries in.
  Type opaque = Type::abstract(f.root("C"), "Value");
  Type array = Type::array(opaque, StaticTerm::natural(2));
  Body traversal;
  traversal.id = f.id("client");
  traversal.signature = {
      {{array, ""}, {opaque, ""}}, {{opaque, ""}}, {}, {}, {}};
  traversal.inputs = {{{0}, {array, ""}}, {{1}, {opaque, ""}}};
  auto step = std::make_shared<Region>();
  step->inputs = {{{2}, {opaque, ""}}, {{3}, {opaque, ""}}};
  step->instructions = {Drop{{{2}, {}}}};
  step->returns = {{{3}, {}}};
  traversal.instructions = {
      ArrayTraversal{{{0}, {}},
                     "",
                     {{{1}, {}}},
                     {},
                     {{{4}, {opaque, ""}}, {{5}, {opaque, ""}}},
                     step}};
  traversal.returns = {{{4}, {}}};
  refusedWith(checkBody(traversal, f.env, {{f.root("C"), i}}),
              "library-traversal");
}

// The installed tables and the requirement checker the environment above is
// built from refuse malformed queries under their own identifiers. The
// compiler's own callers only pass them installed or already checked values.
void installedTableRefusals() {
  // A static scope term that is an application rather than a root.
  zkc::generic::Scope applied{{{"F", std::nullopt, std::vector<unsigned>{}}},
                              {"Field"}};
  refusedWith(zkc::protocol::resolveStaticArguments(applied, {"bls12-381.fr"}),
              "binding-static-application");
  // A bound type spelling longer than any installed type can be.
  refusedWith(zkc::protocol::parseBoundType(std::string(5000, 'a'), false),
              "binding-type-limit");
  // A certificate that answers fewer goals than were asked.
  namespace requirements = zkc::requirements;
  std::vector<requirements::Term> terms = {{"a"}, {"b"}};
  std::vector<requirements::Predicate> facts = {
      requirements::Predicate::equal(0, 1)};
  auto certificate = must(requirements::derive(terms, facts, {}, facts));
  certificate.goals.pop_back();
  refusedWith(
      requirements::checkCertificate(terms, facts, {}, facts, certificate),
      "requirements-goal-count");
}

int main() {
  checkedSourceCalls();
  checkedHelperTypeActuals();
  qualifiedOriginCollisions();
  componentSubstitutionAuthority();
  lexicalSelectionScope();
  capturedDomainAuthority();
  parametricConformance();
  persistentUnusedBounds();
  abstractActualPermissions();
  linkedBindingAndCaptureIdentity();
  locatedLoweringBoundary();
  static_assert(!std::is_default_constructible_v<CheckedComponent>);
  static_assert(!std::is_default_constructible_v<CheckedBody>);
  static_assert(!std::is_default_constructible_v<Interface>);
  static_assert(!std::is_default_constructible_v<LinkedProgram>);
  identityAndSorts();
  abstractClientsAndLayouts();
  resourcesAndNominality();
  diamondsAndInvalidation();
  facetsAndEffects();
  genericsAndArrays();
  capturedClosureAndResources();
  requirementApplications();
  variantFormationSeam();
  checkedRegions();
  checkedConditionals();
  conditionalPermissions();
  genericVariantsAndTraversalBounds();
  privateVariantBoundary();
  associatedVariantsAndCounts();
  variantStaticCaptures();
  terminalStops();
  terminalArmFacts();
  stopsThroughTraversal();
  terminalResourceObligations();
  apiOnlyRefusals();
  directCallerRefusals();
  installedTableRefusals();
  if (!failures)
    llvm::outs() << "checked-library: all adversarial cases passed\n";
  return failures ? 1 : 0;
}
