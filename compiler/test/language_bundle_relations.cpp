// Captured relation bundle declarations: the derived ABI, source checking,
// emitted identity, interface records and the independent readers. Nothing
// here evaluates the relation; the Entry's acceptance is a verifier input.
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Language/RelationABI.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::relation;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
const std::string KB = "koala-bear", EXT = "koala-bear.ext8-binomial3";

/// Small arena builder: every binding is one ring input.
struct Arena {
  std::vector<zkc::ring::Input> inputs;
  std::vector<BundleInput> bindings;
  std::vector<zkc::ring::Node> nodes;
  std::vector<uint32_t> outputs;
  uint32_t bind(const std::string &field, BundleInput binding) {
    inputs.push_back({field});
    bindings.push_back(binding);
    nodes.push_back(zkc::ring::Node::slot(inputs.size() - 1));
    return nodes.size() - 1;
  }
  uint32_t read(const std::string &field, uint32_t group, uint32_t column = 0) {
    return bind(field, BundleInput::read(group, 0, column));
  }
  uint32_t pub(const std::string &field, uint32_t slot) {
    return bind(field, BundleInput::publicSlot(slot));
  }
  uint32_t push(zkc::ring::Node node) {
    nodes.push_back(std::move(node));
    return nodes.size() - 1;
  }
  uint32_t sub(uint32_t a, uint32_t b) {
    return push(zkc::ring::Node::add(a, push(zkc::ring::Node::neg(b))));
  }
  uint32_t out(uint32_t node) {
    outputs.push_back(node);
    return outputs.size() - 1;
  }
  BundleTable table(std::string name, std::vector<BundleGroup> groups,
                    BundleHeight height, bool optional = false) const {
    BundleTable result{
        std::move(name),
        optional,
        height,
        BundleReadModel::Finite,
        std::move(groups),
        take(zkc::ring::Expression::create(inputs, nodes, outputs)),
        bindings,
        {},
        {}};
    for (uint32_t i = 0; i < outputs.size(); ++i)
      result.assertions.push_back({i, {BundleScopeKind::All, 0, 0}});
    return result;
  }
};
/// Publics x0 (KB) and y0 (EXT). Tables in order: rom (required, config
/// height, config + witness groups), cpu (required, instance height, witness
/// KB and public EXT groups), log (optional, instance height, witness EXT
/// group), consts (required, fixed height, config group).
Bundle machine() {
  Arena rom;
  rom.out(rom.push(zkc::ring::Node::mul(rom.read(KB, 0), rom.read(KB, 1))));
  Arena cpu;
  cpu.out(cpu.sub(
      cpu.push(zkc::ring::Node::add(cpu.read(KB, 0, 0), cpu.read(KB, 0, 1))),
      cpu.pub(KB, 0)));
  cpu.out(cpu.sub(cpu.read(EXT, 1), cpu.pub(EXT, 1)));
  Arena log;
  log.out(
      log.push(zkc::ring::Node::add(log.read(EXT, 0, 0), log.read(EXT, 0, 1))));
  Arena consts;
  consts.out(consts.read(KB, 0));
  return take(Bundle::create(
      {{"x0", KB}, {"y0", EXT}}, {},
      {rom.table("rom",
                 {{"fixed", BundleAuthority::Config, KB, 1},
                  {"mult", BundleAuthority::Witness, KB, 1}},
                 {BundleHeightAuthority::Config, 1, 8, false}),
       cpu.table("cpu",
                 {{"trace", BundleAuthority::Witness, KB, 2},
                  {"marker", BundleAuthority::Public, EXT, 1}},
                 {BundleHeightAuthority::Instance, 1, 16, true}),
       log.table("log", {{"pairs", BundleAuthority::Witness, EXT, 2}},
                 {BundleHeightAuthority::Instance, 1, 16, false}, true),
       consts.table("consts", {{"values", BundleAuthority::Config, KB, 1}},
                    {BundleHeightAuthority::Fixed, 4, 4, false})}));
}
AssetBuffer machineAsset(StringRef name = "machine") {
  return {name.str(), "relation-bundle-json",
          zkc::printJson(machine().encode()), "/missing.bundle"};
}
AssetBuffer airAsset() {
  auto relation = take(AIR::create(KB, 1, 0, {}));
  return {"trace", "air-json", zkc::printJson(relation.encode()), "/missing"};
}
constexpr StringLiteral signature =
    "statement x0: Base, statement y0: Ext, parameter rom_height: index, "
    "parameter rom_values: Vector<Base>, witness rom_mult: Vector<Base>, "
    "statement cpu_height: index, witness trace: Vector<Base>, "
    "statement marker: Vector<Ext>, statement log_present: bool, "
    "statement log_height: index, witness pairs: Vector<Ext>, "
    "parameter consts: Vector<Base>";
constexpr StringLiteral ports =
    "x0: Base @V, y0: Ext @V, rom_height: index @V, rom_values: Vector<Base> "
    "@V, rom_mult: Vector<Base> @P, cpu_height: index @V, trace: Vector<Base> "
    "@P, marker: Vector<Ext> @V, log_present: bool @V, log_height: index @V, "
    "pairs: Vector<Ext> @P, consts: Vector<Base> @V, accept: bool @V";
constexpr StringLiteral publics =
    "x0, y0, rom_height, rom_values, cpu_height, marker, log_present, "
    "log_height, consts, accept";
/// A two-role protocol that discloses every witness vector to the verifier and
/// returns a verifier-supplied decision. The target clause states intent only.
std::string source(StringRef relation = signature,
                   StringRef definition = "bundle(asset machine)",
                   StringRef inputs = ports, StringRef publicPorts = publics,
                   StringRef statics = "") {
  return ("module sample;\n"
          "domain Base = field(\"koala-bear\");\n"
          "domain Ext = field(\"koala-bear.ext8-binomial3\");\n"
          "type Vector<F: Field> = builtin(\"vector\", F);\n"
          "relation Machine" +
          statics + "(" + relation + ") = " + definition +
          ";\n"
          "protocol Run roles(P, V)(" +
          inputs +
          ") -> (ok: bool @V)\n"
          "  spec { target proof = Machine(in.x0, in.y0, in.rom_height, "
          "in.rom_values, in.rom_mult, in.cpu_height, in.trace, in.marker, "
          "in.log_present, in.log_height, in.pairs, in.consts) accept out.ok; "
          "}\n"
          "{\n"
          "  let disclosed_mult = send P -> V(rom_mult);\n"
          "  let disclosed_trace = send P -> V(trace);\n"
          "  let disclosed_pairs = send P -> V(pairs);\n"
          "  return (ok = accept);\n"
          "}\n"
          "entry Demo = Run { prover P; verifier V; public { " +
          publicPorts +
          " }; accept ok; target proof; construction authored; }\n")
      .str();
}
Expected<CheckedProject>
check(StringRef text, std::vector<AssetBuffer> assets = {machineAsset()}) {
  auto captured = capture({{"sample", text.str(), {}}}, std::move(assets), {});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<ClosedEntry> close(StringRef text, std::vector<AssetBuffer> assets = {
                                                machineAsset()}) {
  auto project = check(text, std::move(assets));
  if (!project)
    return project.takeError();
  return closeEntry(*project, "sample::Demo");
}
const Declaration &closedDeclaration(const ClosedEntry &entry, StringRef name) {
  for (const auto &decl : entry.declarations())
    if (decl.name == name && decl.origin)
      return decl;
  require(false, "missing closed declaration");
  llvm_unreachable("require throws");
}
std::string substitute(std::string text, StringRef before, StringRef after) {
  auto at = text.find(before.str());
  require(at != std::string::npos, "test substitution missing: " + before);
  text.replace(at, before.size(), after.str());
  return text;
}
template <typename T>
void refusesMentioning(Expected<T> result, StringRef code, StringRef fragment) {
  if (result)
    throw std::runtime_error("expected refusal: " + code.str());
  auto message = toString(result.takeError());
  require(namesIdentifier(message, code) &&
              StringRef(message).contains(fragment),
          "unexpected refusal: " + message);
}
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
Type vectorOf(const std::string &field) {
  Type result(Type::Kind::Builtin, "vector");
  result.arguments = {Type(Type::Kind::Field, field)};
  return result;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "derived formals follow slots tables heights and groups in order", [] {
        using P = RelationPurpose;
        auto bundle = machine();
        auto derived = bundleRelationFormals(bundle);
        std::vector<std::pair<P, Type>> expected{
            {P::Statement, Type(Type::Kind::Field, KB)},
            {P::Statement, Type(Type::Kind::Field, EXT)},
            {P::Parameter, Type(Type::Kind::Index)},
            {P::Parameter, vectorOf(KB)},
            {P::Witness, vectorOf(KB)},
            {P::Statement, Type(Type::Kind::Index)},
            {P::Witness, vectorOf(KB)},
            {P::Statement, vectorOf(EXT)},
            {P::Statement, Type(Type::Kind::Boolean)},
            {P::Statement, Type(Type::Kind::Index)},
            {P::Witness, vectorOf(EXT)},
            {P::Parameter, vectorOf(KB)}};
        require(derived.size() == expected.size(),
                "derived formal count differs");
        for (unsigned i = 0; i < expected.size(); ++i)
          require(derived[i].purpose == expected[i].first &&
                      derived[i].type == expected[i].second,
                  "derived formal " + std::to_string(i) + " differs");
        require(derived[8].label == "table log presence" &&
                    derived[2].label == "table rom height" &&
                    derived[6].label == "table cpu group trace",
                "derived labels differ");
        // An embedded finite AIR derives its public slots, the instance
        // height and one witness column group.
        AIRConstraint every{{AIRScopeKind::Every, 0},
                            {AIRNode::read(0, 0), AIRNode::publicInput(0),
                             AIRNode::neg(1), AIRNode::add(0, 2)},
                            std::nullopt,
                            std::nullopt};
        auto air = bundleRelationFormals(
            take(embedAIR(take(AIR::create(KB, 3, 2, {every})))));
        require(air.size() == 4 && air[0].purpose == P::Statement &&
                    air[0].type == Type(Type::Kind::Field, KB) &&
                    air[1].purpose == P::Statement &&
                    air[2].purpose == P::Statement &&
                    air[2].type == Type(Type::Kind::Index) &&
                    air[3].purpose == P::Witness && air[3].type == vectorOf(KB),
                "embedded AIR derivation differs");
        require(bundleRelationFormals(
                    take(embedAIR(take(AIR::create(KB, 0, 0, {})))))
                        .size() == 1,
                "columnless AIR still derives its height");
      });
  cases.run(
      "captured bundle closes with its canonical identity and no "
      "evaluator retention",
      [] {
        auto entry = take(close(source()));
        const auto &closed = closedDeclaration(entry, "Machine");
        require(closed.relation->kind == RelationDefinition::Kind::Bundle &&
                    closed.relation->asset && closed.inputs.size() == 12,
                "closed bundle relation differs");
        require(entry.project().assets()[*closed.relation->asset].identity() ==
                    machine().identity(),
                "captured asset identity was lost");
        require(entry.assets().size() == 1 &&
                    entry.assets().front().identity() == machine().identity(),
                "a declaration-only bundle must retain its contents");
        // Formal names are free; order, type and purpose are bound.
        take(close(source(
            substitute(signature.str(), "witness trace", "witness columns"))));
      });
  cases.run("original and interface bind the bundle kind key and revision", [] {
    auto entry = take(close(source()));
    auto original = take(prepareOriginal(entry));
    auto identity = machine().identity().str();
    require(original.bytes().contains("kind = \"zkc.relation.bundle/0\"") &&
                original.bytes().contains("key = \"" + identity + "\"") &&
                original.bytes().contains("revision = \"0\""),
            "emitted relation identity differs");
    auto view = take(json::parse(original.interfaceJson()));
    auto *definition = view.getAsObject()
                           ->getArray("relations")
                           ->front()
                           .getAsObject()
                           ->getObject("definition");
    require(definition && definition->size() == 2 &&
                definition->getString("kind") == "bundle" &&
                definition->getString("asset") == identity,
            "interface definition record differs");
    require(original.interface().relations[0].kind ==
                    RelationDefinition::Kind::Bundle &&
                original.interface().relations[0].asset &&
                original.interface().relations[0].asset->identity() == identity,
            "decoded relation view differs");
    take(readInterface(original.bytes(), original.interfaceJson(), {},
                       entry.project().assets()));
    refuses(readInterface(original.bytes(), original.interfaceJson()),
            "source.interface");
    std::vector<Asset> other{take(Asset::read(airAsset()))};
    refuses(
        readInterface(original.bytes(), original.interfaceJson(), {}, other),
        "source.interface");
    auto compiled = take(compileEntry(original));
    auto package = take(packageEntry(compiled));
    auto packaged = take(json::parse(package.bytes()));
    auto *assets = packaged.getAsObject()->getArray("assets");
    require(assets->size() == 1 &&
                (*(*assets)[0].getAsArray())[0].getAsString() ==
                    machine().identity() &&
                (*(*assets)[0].getAsArray())[1].getAsString() ==
                    zkc::printJson(machine().encode()),
            "package lost the declared relation's canonical contents");
  });
  cases.run("declared formals must spell the derived ABI exactly", [] {
    for (auto [before, after] : std::vector<std::pair<StringRef, StringRef>>{
             {"witness trace", "statement trace"},
             {"parameter rom_height", "statement rom_height"},
             {"statement log_present", "parameter log_present"},
             {"statement x0: Base", "statement x0: Ext"},
             {"witness trace: Vector<Base>", "witness trace: Vector<Ext>"},
             {"witness trace: Vector<Base>", "witness trace: Base"},
             {"statement log_present: bool", "statement log_present: index"},
             {", parameter consts: Vector<Base>", ""},
             {"parameter consts: Vector<Base>",
              "parameter consts: Vector<Base>, witness extra: Base"},
             {"witness pairs: Vector<Ext>, parameter consts: Vector<Base>",
              "parameter consts: Vector<Base>, witness pairs: Vector<Ext>"}})
      refusesMentioning(
          check(source(substitute(signature.str(), before, after))),
          "source.relation", "asset ABI");
    refuses(check(source(signature, "bundle(asset machine)", ports, publics,
                         "<N: nat>")),
            "source.relation");
    refuses(check(source(signature, "bundle(asset missing)")),
            "source.relation");
    refuses(check(source(signature, "air(asset machine)")), "source.relation");
    refuses(check(source(signature, "bundle(asset trace)"),
                  {machineAsset(), airAsset()}),
            "source.relation");
    refuses(check(source(signature, "bundle(asset machine)"), {}),
            "source.relation");
    refuses(check(source(signature, "bundle(asset machine);")),
            "source.syntax");
  });
  cases.run("proof target authority follows the derived purposes", [] {
    // A witness group vector cannot be a verifier input, even when the
    // clause selects the prover's component of a shared port.
    refusesMentioning(
        close(
            substitute(source(signature, "bundle(asset machine)",
                              substitute(ports.str(), "trace: Vector<Base> @P",
                                         "trace: Vector<Base> @(P,V)"),
                              substitute(publics.str(), "cpu_height,",
                                         "cpu_height, trace,")),
                       "in.trace,", "in.trace@P,")),
        "source.entry", "purpose");
    // A configuration group vector must be available at the verifier.
    refusesMentioning(
        close(source(signature, "bundle(asset machine)",
                     substitute(ports.str(), "rom_values: Vector<Base> @V",
                                "rom_values: Vector<Base> @P"),
                     substitute(publics.str(), "rom_values, ", ""))),
        "source.entry", "purpose");
    // A public scalar slot must be available at the verifier.
    refusesMentioning(
        close(source(signature, "bundle(asset machine)",
                     substitute(ports.str(), "x0: Base @V", "x0: Base @P"),
                     substitute(publics.str(), "x0, ", ""))),
        "source.entry", "purpose");
  });
  cases.run("mutated original identity or purposes refuse correspondence", [] {
    auto entry = take(close(source()));
    auto original = take(prepareOriginal(entry));
    for (auto [before, after] :
         std::vector<std::pair<std::string, std::string>>{
             {"zkc.relation.bundle/0", "zkc.relation.air/0"},
             {machine().identity().str(), std::string(64, '0')},
             {"\"parameter\", \"parameter\", \"witness\"",
              "\"parameter\", \"parameter\", \"statement\""}})
      refuses(admitOriginal(entry,
                            substitute(original.bytes().str(), before, after),
                            original.interfaceJson()),
              "source.correspondence");
  });
  cases.run("mutated interface records refuse independent reading", [] {
    auto entry = take(close(source()));
    auto original = take(prepareOriginal(entry));
    auto assets = entry.project().assets();
    auto mutate = [&](function_ref<void(json::Object &)> change) {
      auto value = take(json::parse(original.interfaceJson()));
      change(*value.getAsObject());
      return zkc::printJson(value);
    };
    auto relation = [](json::Object &root) {
      return root.getArray("relations")->front().getAsObject();
    };
    refuses(readInterface(original.bytes(), mutate([&](json::Object &root) {
                            (*relation(root)->getObject("definition"))["kind"] =
                                "air";
                          }),
                          {}, assets),
            "source.interface");
    refuses(readInterface(original.bytes(), mutate([&](json::Object &root) {
                            (*relation(root)->getObject(
                                "definition"))["asset"] = std::string(64, '0');
                          }),
                          {}, assets),
            "source.interface");
    refuses(
        readInterface(original.bytes(), mutate([&](json::Object &root) {
                        relation(root)->getObject("definition")->erase("asset");
                      }),
                      {}, assets),
        "source.interface");
    // A purpose that disagrees with the native declaration refuses before
    // the derivation is consulted.
    refuses(readInterface(original.bytes(), mutate([&](json::Object &root) {
                            (*(*relation(root)->getArray("inputs"))[6]
                                  .getAsObject())["purpose"] = "statement";
                          }),
                          {}, assets),
            "source.interface");
    // With the native declaration changed to agree, only the derivation from
    // the admitted bundle can refuse.
    auto agreeing = substitute(original.bytes().str(),
                               "\"parameter\", \"parameter\", \"witness\"",
                               "\"parameter\", \"parameter\", \"statement\"");
    auto purposes = mutate([&](json::Object &root) {
      root["original"] = digest(agreeing);
      (*(*relation(root)->getArray("inputs"))[4].getAsObject())["purpose"] =
          "statement";
    });
    refusesMentioning(readInterface(agreeing, purposes, {}, assets),
                      "source.interface", "asset ABI");
    // The optional-table presence formal cannot become an index. The native
    // statement binds the protocol's Boolean input to that formal, so the
    // retyped declaration is readable only without the statement and its
    // target selection; that control is admitted first.
    auto detached = original.bytes().str();
    auto statement = detached.find("\"protocol.statement\"");
    require(statement != std::string::npos, "native statement missing");
    auto line = detached.rfind('\n', statement);
    detached.erase(line, detached.find('\n', statement) - line);
    auto untargeted = [&](StringRef native,
                          function_ref<void(json::Object &)> change) {
      return mutate([&](json::Object &root) {
        root["original"] = digest(native);
        (*root.getObject("job"))["target"] = nullptr;
        change(root);
      });
    };
    take(readInterface(detached, untargeted(detached, [](json::Object &) {}),
                       {}, assets));
    auto declaration = detached.find("\"relation.declare\"");
    require(declaration != std::string::npos, "relation declaration missing");
    auto retyped = detached;
    auto at = retyped.find(", i1, ui64,", declaration);
    require(at != std::string::npos, "presence formal missing");
    retyped.replace(at, 11, ", ui64, ui64,");
    auto presence = untargeted(retyped, [&](json::Object &root) {
      auto &schema =
          *(*relation(root)->getArray("inputs"))[8].getAsObject()->getObject(
              "schema");
      schema["kind"] = "index";
      schema["type"] = "index";
      schema["leaves"] = json::Array{"index"};
    });
    refusesMentioning(readInterface(retyped, presence, {}, assets),
                      "source.interface", "asset ABI");
    auto compared = checkInterface(original, presence);
    require(bool(compared), "retyped interface escaped source comparison");
    require(namesIdentifier(toString(std::move(compared)), "source.interface"),
            "unexpected source comparison diagnostic");
  });
  return cases.result();
}
