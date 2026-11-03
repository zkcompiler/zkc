#include "support/InterfaceSupply.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/EntryBoundary.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <tuple>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral source = R"(struct State roles(P, V):
    pub statement: index @(P, V)
    pub witness: index @P
    pub empty: () @V
pub protocol Round roles(P, V)(state: State roles(P, V)) -> bool @V:
    received <- send state.witness from P to V
    return received == state.statement
scheme Demo = Round:
    prover P
    verifier V
    public state.statement, state.empty
    accept result
    construction authored
)";
Expected<CheckedProject> check(StringRef text) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", text.str(), "entry-components.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
std::string replace(StringRef before, StringRef after) {
  auto text = source.str();
  auto at = text.find(before.str());
  require(at != std::string::npos, "missing replacement");
  text.replace(at, before.size(), after.str());
  return text;
}
/// Published ordinary data components as (field path, role, native index).
using Component = std::tuple<std::vector<unsigned>, unsigned, unsigned>;
std::vector<Component> dataComponents(const InterfacePort &port) {
  std::vector<Component> result;
  for (const auto &component : port.components)
    if (component.facet == InterfaceComponentFacet::Data)
      result.emplace_back(component.path, component.role, component.native);
  return result;
}
std::vector<std::vector<unsigned>> setupPaths(const LanguageInterface &view) {
  std::vector<std::vector<unsigned>> result;
  for (const auto &setup : view.setups)
    for (const auto &input : setup.inputs)
      result.push_back(input.path);
  return result;
}
const InterfaceSchema &field(const InterfaceSchema &schema,
                             ArrayRef<unsigned> path) {
  const auto *current = &schema;
  for (auto step : path)
    current = current->fields.at(step).schema.get();
  return *current;
}
/// The leaf's setup-key role from the catalog's type row.
std::optional<zkc::protocol::SetupKey> leafKey(const InterfaceSchema &schema) {
  if (schema.leaves.size() != 1)
    return {};
  return zkc::protocol::setupKey(zkc::protocol::typeKind(schema.leaves[0]));
}
} // namespace
int main() {
  Cases cases;
  cases.run("checked public fields retain exact role and empty coverage", [] {
    auto project = take(check(source));
    auto entry = take(closeEntry(project, "m::Demo"));
    const auto &proof = *entry.entry().proof();
    require(proof.publicInputs.size() == 2 &&
                proof.publicInputs[0] == EntryInputSelection{0, {0}, 1, {}} &&
                proof.publicInputs[1] == EntryInputSelection{0, {2}, 1, {}},
            "public paths or verifier role differ");
    auto original = take(prepareOriginal(entry));
    const auto &view = original.interface();
    require(view.proof && view.proof->publicInputs == proof.publicInputs,
            "published public selections differ");
    const auto &port = view.selectedProtocol().inputs[0];
    require(dataComponents(port) ==
                std::vector<Component>{{{0}, 0, 0}, {{0}, 1, 0}, {{1}, 0, 1}},
            "native scatter differs");
    const auto &empty = field(*port.schema, {2});
    require(port.schema->fields[2].name == "empty" &&
                empty.kind == Type::Kind::Unit && empty.leaves.empty(),
            "empty ordinary supply lost its logical field");
    // The generated proof family publishes the role-local aliases.
    auto produce = take(check(source.str() + R"(
entry def Produce(public: Demo::Public, witness: Demo::Witness) -> Demo::Proof:
    result <- Demo::prove(public, witness)
    return result.proof
)"));
    auto host = take(prepareOriginal(take(closeEntry(produce, "m::Produce"))));
    require(host.interface().host &&
                host.interface().host->functions.size() == 1,
            "Host family interface is missing");
    std::vector<std::vector<std::string>> aliases;
    for (const auto &parameter :
         host.interface().host->functions.front().parameters) {
      aliases.emplace_back();
      for (const auto &member : parameter.schema->fields)
        aliases.back().push_back(member.name);
    }
    require(aliases ==
                std::vector<std::vector<std::string>>{
                    {"state_statement", "state_empty"}, {"state_witness"}},
            "published family aliases differ");
  });
  cases.run("written public selectors preserve authored fields and order", [] {
    auto project = take(analyze(take(capture({{"written", R"(
module written;
struct Data {pub flag:bool,pub empty:()}
protocol Run roles(P,V)(state:Data@V)->(accepted:bool@V){return(accepted=state.flag);}
proof Demo=Run{prover P;verifier V;public{state.empty,state.flag};accept accepted;construction authored;}
)",
                                               "written.zkc"}})))
                            .checkedProject());
    auto document = take(json::parse(take(inspectWrittenSource(project))));
    std::vector<std::string> paths;
    for (const auto &declaration :
         *document.getAsObject()->getArray("declarations")) {
      const auto &decl = *declaration.getAsObject();
      if (decl.getString("owner") != "written::Demo")
        continue;
      for (const auto &value : *decl.getArray("nodes")) {
        const auto &node = *value.getAsObject();
        if (node.getString("kind") == "input_selector") {
          require(node.getString("port") == "state", "written port was lost");
          const auto *fields = node.getArray("fields");
          require(fields && fields->size() == 1, "written field path was lost");
          paths.push_back(fields->front().getAsString()->str());
        }
      }
    }
    require(paths == std::vector<std::string>({"empty", "flag"}),
            "checked coordinate sorting replaced authored public syntax");
  });
  for (const auto &item :
       {std::tuple{"missing empty public field", "state.statement, state.empty",
                   "state.statement"},
        std::tuple{"whole logical public field", "state.statement, state.empty",
                   "state"},
        std::tuple{"witness is not verifier public",
                   "state.statement, state.empty",
                   "state.statement, state.witness, state.empty"},
        std::tuple{"duplicate public path", "state.statement, state.empty",
                   "state.statement, state.statement, state.empty"},
        std::tuple{"ancestor public overlap", "state.statement, state.empty",
                   "state, state.statement, state.empty"}})
    cases.run(std::get<0>(item), [&] {
      refuses(check(replace(std::get<1>(item), std::get<2>(item))),
              "source.entry");
    });
  cases.run("public selection through a private field is not publishable", [] {
    // Closure selects no external operation and succeeds. The
    // published statement still cannot select an ordinary value
    // through a privacy barrier, so interface publication refuses.
    auto project = take(check(replace("pub empty", "empty")));
    auto entry = take(closeEntry(project, "m::Demo"));
    refuses(prepareOriginal(entry), "source.interface");
  });
  cases.run("generated proof families bind exact ordinary selections", [] {
    auto project = take(check(source.str() + R"(
entry def Produce(public: Demo::Public, witness: Demo::Witness) -> Demo::Proof:
    result <- Demo::prove(public, witness)
    return result.proof
)"));
    bool publicSeen = false, witnessSeen = false;
    for (const auto &decl : project.declarations()) {
      if (!decl.generated)
        continue;
      if (decl.qualifiedName == "m::Demo::Public") {
        publicSeen =
            decl.fields.size() == 2 &&
            decl.fields[0].name == "state_statement" &&
            decl.fields[1].name == "state_empty" &&
            decl.generated->ports.size() == 2 &&
            decl.generated->ports[1] == EntryInputSelection{0, {2}, 1, {}};
      }
      if (decl.qualifiedName == "m::Demo::Witness")
        witnessSeen =
            decl.fields.size() == 1 && decl.fields[0].name == "state_witness" &&
            decl.generated->ports[0] == EntryInputSelection{0, {1}, 0, {}};
    }
    require(publicSeen && witnessSeen,
            "generated family or retained association differs");
    take(closeEntry(project, "m::Produce"));
  });
  cases.run(
      "nested setup fields preserve ordinary sibling and exact roles", [] {
        auto project = take(check(R"(
domain C = commitment("multilinear.kzg.bls12-381/0")
type VK = builtin("verifier_key", C)
type PK = builtin("prover_key", C)
type Commitment = builtin("commitment", C)
struct State roles(P, V):
    pub vk: VK @V
    pub pk: PK @P
    pub commitment: Commitment @(P, V)
    pub nonce: index @P
pub protocol Round roles(P, V)(state: State roles(P, V)) -> bool @V:
    return true
scheme Demo = Round:
    prover P
    verifier V
    setup pcs {state.vk, state.pk, state.commitment}
    public {state.vk, state.commitment}
    accept result
    construction authored
entry def Produce(public: Demo::Public, witness: Demo::Witness) -> Demo::Proof:
    result <- Demo::prove(public, witness)
    return result.proof
)"));
        auto entry = take(closeEntry(project, "m::Demo"));
        auto original = take(prepareOriginal(entry));
        const auto &view = original.interface();
        const auto &state = *view.selectedProtocol().inputs[0].schema;
        // The verifier key is initialized by its setup, the other setup
        // members arrive through setup context, and the nonce stays an
        // ordinary argument outside every setup.
        require(setupPaths(view) ==
                    std::vector<std::vector<unsigned>>{{0}, {1}, {2}},
                "setup associations differ");
        require(
            leafKey(field(state, {0})) == zkc::protocol::SetupKey::Verifier &&
                leafKey(field(state, {1})) == zkc::protocol::SetupKey::Prover &&
                !leafKey(field(state, {2})) && !leafKey(field(state, {3})),
            "setup-key leaves differ");
        require(dataComponents(view.selectedProtocol().inputs[0]) ==
                    std::vector<Component>{{{0}, 1, 0},
                                           {{1}, 0, 1},
                                           {{2}, 0, 2},
                                           {{2}, 1, 2},
                                           {{3}, 0, 3}},
                "setup routing hid an ordinary sibling or fabricated data");
        bool witness = false;
        for (const auto &decl : project.declarations())
          if (decl.qualifiedName == "m::Demo::Witness")
            witness =
                decl.fields.size() == 1 && decl.fields[0].name == "state_nonce";
        require(witness,
                "generated setup filtering removed an ordinary sibling");
      });
  cases.run("generated fields expand closed logical array specializations", [] {
    auto project = take(check(R"(
struct Pair roles(P, V):
    pub left: index @P
    pub right: index @V
pub protocol Round<N: nat> roles(P, V)(state: [Pair roles(P, V); N]) -> bool @V:
    return true
entry def Run(inputs: Round<2>::Inputs) -> Round<2>::RunResult:
    result <- Round<2>::run(inputs)
    return result
)"));
    auto entry = take(closeEntry(project, "m::Run"));
    Layouts layouts(entry);
    auto inputs = take(layouts.get(entry.root().inputs[0].type));
    require(inputs->fields.size() == 2, "generated participant roster differs");
    const auto &p = *inputs->fields[0].layout;
    const auto &v = *inputs->fields[1].layout;
    require(p.fields.size() == 2 && v.fields.size() == 2 &&
                p.fields[0].name == "state_0_left" &&
                p.fields[1].name == "state_1_left" &&
                v.fields[0].name == "state_0_right" &&
                v.fields[1].name == "state_1_right",
            "closed generated fields reused an open template roster");
  });
  cases.run("ordinary zero arrays retain explicit public supply", [] {
    auto project = take(check(replace("() @V", "[(); 0] @V")));
    auto entry = take(closeEntry(project, "m::Demo"));
    auto original = take(prepareOriginal(entry));
    const auto &view = original.interface();
    const auto &port = view.selectedProtocol().inputs[0];
    const auto &empty = field(*port.schema, {2});
    require(view.proof->publicInputs.back().path == std::vector<unsigned>{2} &&
                llvm::none_of(port.components,
                              [](const auto &component) {
                                return component.path ==
                                       std::vector<unsigned>{2};
                              }) &&
                empty.fields.empty() && empty.element &&
                empty.element->kind == Type::Kind::Unit,
            "zero array lost its template or logical supply");
  });
  cases.run(
      "ordinary structural Product supply uses each role's full intersection",
      [] {
        auto project = take(check(R"(
pub protocol Forward roles(P, V)(state: (index @(P, V), index @P)) -> index @V:
    return state.0
)"));
        auto entry = take(closeNativeRun(project, "m::Forward"));
        auto original = take(prepareOriginal(entry));
        // P holds the whole product, V only its shared component.
        require(
            dataComponents(original.interface().selectedProtocol().inputs[0]) ==
                std::vector<Component>{{{0}, 0, 0}, {{0}, 1, 0}, {{1}, 0, 1}},
            "Product participation union authorized an unavailable sibling");
      });
  cases.run("permuted roles retain original native coordinates", [] {
    auto project = take(check(R"(
struct Pair roles(P, V):
    pub left: index @P
    pub right: index @V
pub protocol Forward roles(A, B)(state: Pair roles(B, A)) -> Pair roles(B, A):
    return state
)"));
    auto entry = take(closeNativeRun(project, "m::Forward"));
    auto original = take(prepareOriginal(entry));
    require(dataComponents(original.interface().selectedProtocol().inputs[0]) ==
                std::vector<Component>{{{0}, 1, 0}, {{1}, 0, 1}},
            "role permutation changed physical operand order");
  });
  cases.run("setup initialization assembles an ordinary product below a "
            "distributed root",
            [] {
              auto project = take(check(R"(
domain C = commitment("multilinear.kzg.bls12-381/0")
type VK = builtin("verifier_key", C)
struct VerifierState:
    pub key: VK
    pub nonce: index
struct State roles(P, V):
    pub verifier: VerifierState @V
    pub witness: index @P
pub protocol Round roles(P, V)(state: State roles(P, V)) -> bool @V:
    return true
scheme Demo = Round:
    prover P
    verifier V
    setup pcs {state.verifier.key}
    public state.verifier
    accept result
    construction authored
entry def Check(public: Demo::Public, proof: Demo::Proof) -> Demo::VerifyResult:
    result <- Demo::verify(public, proof)
    return result
)"));
              auto entry = take(closeEntry(project, "m::Demo"));
              auto original = take(prepareOriginal(entry));
              const auto &view = original.interface();
              const auto &state = *view.selectedProtocol().inputs[0].schema;
              // Only the key is setup-initialized; its ordinary sibling stays
              // a public argument below the same distributed root.
              require(setupPaths(view) ==
                              std::vector<std::vector<unsigned>>{{0, 0}} &&
                          leafKey(field(state, {0, 0})) ==
                              zkc::protocol::SetupKey::Verifier &&
                          !leafKey(field(state, {0, 1})) &&
                          dataComponents(view.selectedProtocol().inputs[0]) ==
                              std::vector<Component>{
                                  {{0, 0}, 1, 0}, {{0, 1}, 1, 1}, {{1}, 0, 2}},
                      "whole-parent constructibility hid a supplied setup key "
                      "or ordinary sibling");
              take(closeEntry(project, "m::Check"));
            });
  for (StringRef restriction : {"sealed", "linear"})
    cases.run(
        "empty distributed wrapper retains assembly authority: " + restriction,
        [&] {
          auto project = take(check(("#[" + restriction + R"(]
struct Empty roles(P, V):
pub protocol Forward roles(P, V)(state: Empty roles(P, V)) -> Empty roles(P, V):
    return state
)")
                                        .str()));
          auto original = take(
              prepareOriginal(take(closeNativeRun(project, "m::Forward"))));
          zkc::test::requireWithheld(
              zkc::test::withheldSupply(original.interface()), {"state"},
              "empty restricted wrapper lost its supply mark");
        });
  cases.run(
      "public child selection cannot bypass a generated product constructor",
      [] {
        auto project = take(check(source.str() + R"(
pub protocol Receive roles(P, V)(candidate: Demo::VerifierOutputs @V) -> bool @V:
    return true
scheme ReceiveJob = Receive:
    prover P
    verifier V
    public candidate.result
    accept result
    construction authored
)"));
        // Closure succeeds. Splitting the generated product for the public
        // statement needs its constructor, so publication refuses, as the
        // SDK's interface reader does for the same selection.
        auto entry = take(closeEntry(project, "m::ReceiveJob"));
        refuses(prepareOriginal(entry), "source.interface");
      });
  cases.run(
      "ordinary inspection beside a handle does not provide its origin", [] {
        auto project = take(check(R"(
domain F = field("bls12-381.fr")
type K = builtin("oracle.table", F, 4)
type O = builtin("oracle", K)
struct State roles(P, V):
    pub point: index @V
    pub table: O @P -> V
pub protocol Forward roles(P, V)(state: State roles(P, V)) -> State roles(P, V):
    return state
)"));
        const Declaration *protocol = nullptr;
        for (const auto &decl : project.declarations())
          if (decl.qualifiedName == "m::Forward")
            protocol = &decl;
        require(protocol, "missing checked protocol");
        Layouts layouts(project);
        auto observed = take(layouts.protocolPort(protocol->inputs[0]));
        auto point = take(observed.select({0}));
        require(point.layout->type.kind == Type::Kind::Index &&
                    point.offset == 0,
                "ordinary inspection lost its exact field slice");
        auto original =
            take(prepareOriginal(take(closeNativeRun(project, "m::Forward"))));
        zkc::test::requireWithheld(
            zkc::test::withheldSupply(original.interface()), {"state.table"},
            "logical handle lost its supply mark");
      });
  cases.run(
      "alias allocation reserves whole names and suffixes collisions", [] {
        std::vector<EntryInputSelection> selections{
            {0, {0}, 0, {}}, {1, {}, 0, {}}, {2, {0}, 0, {}}};
        std::vector<std::string> names{"state_x", "state_x", "state_x"};
        uint64_t remaining = 10000;
        auto aliases =
            take(entrySelectionAliases(selections, names, remaining));
        require(aliases == std::vector<std::string>{"state_x_2", "state_x",
                                                    "state_x_3"},
                "alias collision order differs");
      });
  cases.run("long UTF-8 aliases remain bounded and coordinate-specific", [] {
    std::vector<EntryInputSelection> selections{{0, {0}, 0, {}},
                                                {0, {1}, 0, {}}};
    std::string name;
    for (unsigned i = 0; i < 70; ++i)
      name += "\xc3\xa9";
    uint64_t remaining = 10000;
    auto aliases =
        take(entrySelectionAliases(selections, {name, name}, remaining));
    require(
        aliases[0].size() == 113 && aliases[1].size() == 113 &&
            json::isUTF8(aliases[0]) && aliases[0] != aliases[1],
        "long aliases broke UTF-8, identifier bounds or coordinate identity");
    remaining = 1;
    refuses(entrySelectionAliases(selections, {name, name}, remaining),
            "source.limit");
  });
  return cases.result();
}
