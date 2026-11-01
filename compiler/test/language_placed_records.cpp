#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/SourceTerms.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "placed-records.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &declaration(ArrayRef<Declaration> declarations,
                               StringRef name) {
  auto found = llvm::find_if(declarations, [&](const auto &decl) {
    return decl.qualifiedName == name;
  });
  require(found != declarations.end(), "missing declaration");
  return *found;
}
const ProductPlacement &
product(const std::optional<ValuePlacement> &placement) {
  require(placement &&
              std::holds_alternative<ProductPlacement>(placement->value),
          "missing product placement");
  return std::get<ProductPlacement>(placement->value);
}
const char *data = R"(struct Pair<T: Type> roles(A, B):
    pub first: T @A
    pub second: index @B
    empty: () @A
)";
const char *oracles = R"(domain F = field("bls12-381.fr")
type K = builtin("oracle.table", F, 16)
type O = builtin("oracle", K)
struct Sources<N: nat> roles(A, B, V):
    pub left: O @A -> V
    pub right: O @B -> V
    pub point: index @V
)";
} // namespace
int main() {
  Cases cases;
  cases.run("ordinary-only distributed record and private empty schema", [] {
    auto project = take(check(std::string(data) + R"(
pub protocol Forward roles(P, V)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    x = s.first
    y = s.second
    return s
)"));
    const auto &pair = declaration(project.declarations(), "m::Pair");
    require(pair.logical &&
                pair.roles == std::vector<std::string>({"A", "B"}) &&
                pair.fields.size() == 3 && !pair.fields[2].isPublic,
            "schema lost telescope, order or private empty child");
    const auto &forward = declaration(project.declarations(), "m::Forward");
    const auto &placed = product(forward.inputs[0].placement);
    require(placed.arguments == std::vector<unsigned>({0, 1}) &&
                placed.instance == typeIdentity(forward.inputs[0].type) &&
                placed.fields.size() == 3 && !forward.inputs[0].oracle,
            "product acquired a root oracle family or lost identity");
    bool first = false, second = false;
    for (const auto &operation : forward.body->operations)
      if (const auto *projection = std::get_if<Projection>(&operation.action)) {
        const auto &value = forward.body->values[operation.results[0].index];
        if (projection->path == std::vector<unsigned>{0})
          first = value.components == std::vector<unsigned>{0};
        if (projection->path == std::vector<unsigned>{1})
          second = value.components == std::vector<unsigned>{1};
      }
    require(first && second, "projection used aggregate role union");
  });
  cases.run("two holders, nested map and alias role abstraction", [] {
    auto project = take(check(std::string(oracles) + R"(
type Reversed<N: nat> roles(P, Q, R) = Sources<N> roles(Q, P, R)
struct Batch roles(X, Y, Z):
    pub sources: Reversed<7> roles(X, Y, Z)
    pub count: index @(X, Z)
pub protocol Forward roles(A, B, V)(s: Batch roles(A, B, V)) -> O @B -> V:
    return s.sources.left
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    const auto &root = product(forward.inputs[0].placement);
    const auto &nested = std::get<ProductPlacement>(root.fields[0].value);
    require(nested.arguments == std::vector<unsigned>({1, 0, 2}) &&
                std::get<OraclePlacement>(nested.fields[0].value).holder == 1 &&
                std::get<OraclePlacement>(nested.fields[1].value).holder == 0,
            "nested alias map was sorted or collapsed");
    const auto &result = forward.body->values[forward.body->results[0].index];
    require(result.oracleHolder == 1 &&
                result.components == std::vector<unsigned>({1, 2}),
            "nested direct-handle projection lost family");
  });
  cases.run(
      "constructor equations infer a unique map and preserve evaluation order",
      [] {
        auto project = take(check(std::string(data) + R"(
def keep(x: index) -> index:
    return x
pub protocol Build roles(P, V)(x: index @P, y: index @V) -> Pair<index> roles(P, V):
    result = Pair<index> {second: keep(y), empty: (), first: keep(x)}
    return result
)"));
        const auto &body =
            *declaration(project.declarations(), "m::Build").body;
        bool found = false;
        for (const auto &operation : body.operations)
          if (const auto *construct = std::get_if<Construct>(&operation.action);
              construct && construct->operands.size() == 3) {
            found = true;
            require(construct->operands[1].index < construct->operands[0].index,
                    "constructor changed authored evaluation order");
            require(product(body.values[operation.results[0].index].placement)
                            .arguments == std::vector<unsigned>({0, 1}),
                    "wrong inferred map");
          }
        require(found, "missing constructor");
      });
  cases.run("expected placement resolves otherwise ambiguous literals", [] {
    take(check(std::string(data) + R"(
pub protocol Build roles(P, V)() -> Pair<index> roles(P, V):
    return Pair<index> {first: 1, second: 2, empty: ()}
)"));
  });
  cases.run("explicit constructor role application", [] {
    take(check(std::string(data) + R"(
pub protocol Build roles(P, V)() -> Pair<index> roles(P, V):
    result = Pair<index> roles(P, V) {first: 1, second: 2, empty: ()}
    return result
)"));
  });
  cases.run("calls preserve exact map under reordered protocol roster", [] {
    auto project = take(check(std::string(data) + R"(
protocol Forward roles(V, P)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    return s
pub protocol Run roles(P, V)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    next <- Forward(s) @ (V, P)
    return next
)"));
    const auto &run = declaration(project.declarations(), "m::Run");
    require(product(run.body->values[run.body->results[0].index].placement)
                    .arguments == std::vector<unsigned>({0, 1}),
            "call remapping lost role order");
  });
  cases.run("closed specialization recomputes phantom nominal identity", [] {
    auto project = take(check(R"(
struct Marker<N: nat> roles(P, V):
    pub x: index @P
    pub y: index @V
pub protocol Build<N: nat> roles(P, V)(x: index @P, y: index @V) -> Marker<N> roles(P, V):
    return Marker<N> {x: x, y: y}
)"));
    Type natural(Type::Kind::Natural);
    natural.dimension = Natural::constant(9);
    auto closed = take(closeNativeRun(project, "m::Build", {}, {natural}));
    const auto &forward = closed.protocol();
    require(product(forward.outputs[0].placement).instance ==
                typeIdentity(forward.outputs[0].type),
            "closed port identity stayed symbolic");
    require(
        product(forward.body->values[forward.body->results[0].index].placement)
                .instance ==
            typeIdentity(
                forward.body->values[forward.body->results[0].index].type),
        "closed value identity stayed symbolic");
  });
  cases.run(
      "transparent partial moves keep disjoint role-local Copy fields", [] {
        auto project = take(check(R"(
#[linear]
struct Token:
    pub code: index
struct State roles(P, V):
    pub pending: Token @P
    pub copy: index @V
pub protocol Split roles(P, V)(s: State roles(P, V)) -> (out: Token @P, observed: index @V):
    pending = s.pending
    observed = s.copy
    return (out: pending, observed: observed)
)"));
        const auto &state = declaration(project.declarations(), "m::State");
        const auto &split = declaration(project.declarations(), "m::Split");
        require(!state.sealed && !state.resource && split.body,
                "transparent state lost its source identity");
      });
  cases.run("repeat carries preserve the initial and successor placement", [] {
    auto project = take(check(std::string(data) + R"(
protocol Forward roles(V, P)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    return s
pub protocol Run roles(P, V)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    mut state = s
    for i in 0..0 roles(P, V):
        next <- Forward(state) @(V, P)
        state := next
    return state
)"));
    const auto &body = *declaration(project.declarations(), "m::Run").body;
    bool carried = false;
    for (const auto &operation : body.operations)
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
        carried = true;
        require(body.values[repeat->carried[0].index].placement ==
                    repeat->region->values[repeat->region->results[0].index]
                        .placement,
                "zero-trip carry or continuing successor changed placement");
      }
    require(carried, "missing repeat");
  });
  cases.run("native placement APIs admit structural ordinary roots", [] {
    auto project = take(check(R"(
protocol Forward roles(P, V)(s: (index @P, index @V)) -> (index @P, index @V):
    return s
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    const auto &port = forward.inputs.front();
    Layouts layouts(project);
    auto placed = take(layouts.placement(port.type, *port.placement, 2));
    require(placed == *port.placement,
            "ordinary structural placement changed during reconstruction");
    auto input = take(layouts.protocolPort(port));
    auto output = take(layouts.protocolValue(
        forward.body->values[forward.body->results.front().index]));
    require(input.size() == 2 && output.size() == 2 &&
                input.components.size() == 2 && input.components[0].role == 0 &&
                input.components[1].role == 1,
            "native structural port lost its independent participants");
  });
  cases.run(
      "native formulas distinguish structural unions and nominal maps", [] {
        auto project = take(check(std::string(oracles) + R"(
struct Item roles(A, B):
    pub value: index @A
struct Outer roles(A, B):
    pub pair: (O @A -> B, Item roles(B, A), Item roles(A, B))
protocol Forward roles(P, V)(s: Outer roles(V, P)) -> Outer roles(V, P):
    return s
)"));
        const auto &forward = declaration(project.declarations(), "m::Forward");
        Layouts layouts(project);
        const auto &port = forward.inputs.front();
        auto observed = take(layouts.protocolPort(port));
        const auto &tuple =
            std::get<ProductPlacement>(product(port.placement).fields[0].value);
        const auto &nested = std::get<ProductPlacement>(tuple.fields[1].value);
        const auto &unchanged =
            std::get<ProductPlacement>(tuple.fields[2].value);
        require(tuple.arguments == std::vector<unsigned>({0, 1}) &&
                    nested.arguments == std::vector<unsigned>({0, 1}) &&
                    unchanged.arguments == std::vector<unsigned>({1, 0}) &&
                    observed.size() == 4 && observed.components.size() == 4,
                "reversed outer roles corrupted a structural or nominal child");
        auto wrong = *port.placement;
        auto &wrongTuple = std::get<ProductPlacement>(
            std::get<ProductPlacement>(wrong.value).fields[0].value);
        wrongTuple.arguments = {1, 0};
        uint64_t work = Limits{}.work;
        refuses(observeProtocolPort(observed.body, wrong, work),
                "source.placement");
        wrong = *port.placement;
        auto &wrongNested = std::get<ProductPlacement>(
            std::get<ProductPlacement>(
                std::get<ProductPlacement>(wrong.value).fields[0].value)
                .fields[1]
                .value);
        wrongNested.arguments = {1, 0};
        work = Limits{}.work;
        refuses(observeProtocolPort(observed.body, wrong, work),
                "source.placement");
      });
  cases.run("native zero array retains a logical template without storage", [] {
    auto project = take(check(std::string(data) + R"(
type EmptyBatch roles(P, V) = [Pair<index> roles(V, P); 0]
protocol Forward roles(P, V)(s: EmptyBatch roles(P, V)) -> EmptyBatch roles(P, V):
    return s
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    Layouts layouts(project);
    auto port = take(layouts.protocolPort(forward.inputs.front()));
    auto value = take(layouts.protocolValue(
        forward.body->values[forward.body->results.front().index]));
    require(port.size() == 0 && value.size() == 0 && port.body->element &&
                port.body->element->type.kind == Type::Kind::LogicalRecord,
            "zero array erased its logical element or invented native storage");
  });
  cases.run("fixed array retains its element schema at zero storage", [] {
    auto project = take(check(std::string(data) + R"(
struct Batch roles(P, V):
    pub items: [Pair<index> roles(P, V); 0]
protocol Forward roles(P, V)(s: Batch roles(P, V)) -> Batch roles(P, V):
    return s
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    const auto &array = std::get<ProductPlacement>(
        product(forward.inputs[0].placement).fields[0].value);
    require(array.fields.size() == 1 &&
                std::holds_alternative<ProductPlacement>(array.fields[0].value),
            "zero array erased its logical element schema");
  });
  cases.run("nested fixed arrays and tuples project exact child maps", [] {
    auto project = take(check(std::string(data) + R"(
struct Batch roles(P, V):
    pub items: [Pair<index> roles(P, V); 2]
    pub pair: (Pair<index> roles(V, P), index @P)
protocol First roles(P, V)(s: Batch roles(P, V)) -> index @P:
    return s.items[1].first
)"));
    const auto &first = declaration(project.declarations(), "m::First");
    require(first.body->values[first.body->results[0].index].components ==
                std::vector<unsigned>{0},
            "structural projection used a role summary");
  });
  cases.run("expected structural construction preserves nested placements", [] {
    take(check(std::string(data) + R"(
struct Batch roles(P, V):
    pub items: [Pair<index> roles(P, V); 2]
protocol Build roles(P, V)(s: Pair<index> roles(P, V)) -> Batch roles(P, V):
    return Batch {items: [s, s]}
)"));
  });
  cases.run(
      "empty restricted distributed wrapper retains source root obligation",
      [] {
        auto project = take(check(R"(
#[linear]
struct Token roles(P, V):
protocol Build roles(P, V)() -> Token roles(P, V):
    token: Token roles(P, V) <- Token {}
    return token
)"));
        const auto &build = declaration(project.declarations(), "m::Build");
        require(
            product(build.body->values[build.body->results[0].index].placement)
                .fields.empty(),
            "empty wrapper acquired fields");
      });
  cases.run("multiple receivers retain their exact family", [] {
    auto project = take(check(std::string(oracles) + R"(
struct Multi roles(P, V, W):
    pub word: O @P -> (V, W)
protocol Forward roles(P, V, W)(s: Multi roles(P, V, W)) -> O @P -> (V, W):
    return s.word
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    const auto &word = forward.body->values[forward.body->results[0].index];
    require(std::get<OraclePlacement>(word.placement->value).receivers ==
                std::vector<unsigned>({1, 2}),
            "receiver family collapsed to one member");
  });
  cases.run("public reconstruction derives static and nested identities", [] {
    auto project = take(check(R"(
struct Marker<N: nat> roles(P, V):
    pub value: index @V
struct Outer<N: nat> roles(P, V):
    pub inner: Marker<N> roles(V, P)
protocol Forward roles(P, V)(s: Outer<1> roles(P, V)) -> Outer<1> roles(P, V):
    return s
)"));
    const auto &forward = declaration(project.declarations(), "m::Forward");
    auto type = forward.inputs[0].type;
    type.arguments[0].dimension = Natural::constant(2);
    Layouts layouts(project);
    auto rebuilt =
        take(layouts.placement(type, *forward.inputs[0].placement, 2));
    const auto &root = std::get<ProductPlacement>(rebuilt.value);
    const auto &child = std::get<ProductPlacement>(root.fields[0].value);
    require(root.instance == typeIdentity(type) &&
                root.instance !=
                    product(forward.inputs[0].placement).instance &&
                child.instance !=
                    std::get<ProductPlacement>(
                        product(forward.inputs[0].placement).fields[0].value)
                        .instance &&
                child.arguments == std::vector<unsigned>({1, 0}),
            "reconstruction rewrote or retained stale instance identity");
  });
  cases.run(
      "capture and inspection retain written role applications and private "
      "changes",
      [] {
        const auto source = std::string(data) + R"(
pub type Alias roles(P, V) = Pair<index> roles(V, P)
pub protocol Forward roles(P, V)(s: Alias roles(V, P)) -> Alias roles(V, P):
    return s
)";
        auto project = take(check(source));
        auto written = take(json::parse(take(inspectWrittenSource(project))));
        bool application = false;
        for (const auto &decl :
             *written.getAsObject()->getArray("declarations"))
          for (const auto &node : *decl.getAsObject()->getArray("nodes"))
            application |=
                node.getAsObject()->getArray("role_arguments") != nullptr;
        require(application, "written source omitted type-use roles");
        const auto &forward = declaration(project.declarations(), "m::Forward");
        auto term = take(encodeStaticTerm(forward.inputs[0].type));
        require(term.getAsArray()->back().getAsArray()->size() == 1,
                "roles entered ordinary static arguments");
        auto changed = source;
        changed.replace(changed.find("empty:"), 6, "hidden_empty:");
        require(take(check(changed)).capture().identity() !=
                    project.capture().identity(),
                "private empty field change did not invalidate capture");
        auto api = take(json::parse(take(inspectPublicAPI(project))));
        bool placed = false;
        for (const auto &decl : *api.getAsObject()->getArray("declarations"))
          if (decl.getAsObject()->getString("name") == "m::Alias")
            placed = decl.getAsObject()->getObject("placement") != nullptr &&
                     decl.getAsObject()->getArray("roles") != nullptr;
        require(placed, "public alias inspection lost its role abstraction");
      });
  cases.run("structural aliases retain their abstracted application", [] {
    take(check(std::string(data) + R"(
type EmptyBatch roles(P, V) = [Pair<index> roles(V, P); 0]
protocol Forward roles(P, V)(s: EmptyBatch roles(P, V)) -> EmptyBatch roles(P, V):
    return s
)"));
  });
  cases.run(
      "finite handle tuples and zero arrays retain exact leaf families", [] {
        auto project = take(check(std::string(oracles) + R"(
struct Pair roles(A, B, V):
    pub handles: (O @A -> V, O @B -> V)
    pub empty: [O @A -> V; 0]
protocol Right roles(A, B, V)(s: Pair roles(A, B, V)) -> O @B -> V:
    return s.handles.1
)"));
        const auto &right = declaration(project.declarations(), "m::Right");
        const auto &result = right.body->values[right.body->results[0].index];
        require(result.oracleHolder == 1 &&
                    result.components == std::vector<unsigned>({1, 2}),
                "structural direct handle lost its exact family");
      });
  cases.run(
      "ordinary tuple identity can carry independent field placements", [] {
        auto project = take(check(R"(
struct State roles(P, V):
    pub pair: (index @P, index @V)
protocol Build roles(P, V)(a: index @P, b: index @V) -> State roles(P, V):
    return State {pair: (a, b)}
protocol Forward roles(P, V)(s: (index @P, index @V)) -> (index @P, index @V):
    return s
)"));
        const auto &forward = declaration(project.declarations(), "m::Forward");
        require(forward.inputs[0].type.kind == Type::Kind::Tuple &&
                    product(forward.inputs[0].placement).fields.size() == 2,
                "structural placement changed ordinary tuple identity");
      });
  cases.run("home protocol unpack consumes sealed distributed custody", [] {
    auto project = take(check(R"(
module Owner:
    #[linear]
    #[sealed]
    pub struct State roles(P, V):
        hidden: index @P
        observed: index @V
    pub protocol Consume roles(P, V)(s: State roles(P, V)) -> index @V:
        fields <- unpack(s)
        return fields.1
)"));
    const auto &consume =
        declaration(project.declarations(), "m::Owner::Consume");
    bool unpacked = false;
    for (const auto &operation : consume.body->operations)
      if (const auto *construct = std::get_if<Construct>(&operation.action);
          construct && construct->kind == Construct::Kind::Unpack) {
        unpacked = true;
        require(
            product(consume.body->values[operation.results[0].index].placement)
                    .fields.size() == 2,
            "unpack lost field placements");
      }
    require(
        unpacked &&
            consume.body->values[consume.body->results[0].index].components ==
                std::vector<unsigned>{1},
        "home unpack replaced field placement by a role union");
  });
  cases.run("role-abstract aliases preserve ordinary placed structural targets",
            [] {
              take(check(R"(
type Split roles(P, V) = (index @P, index @V)
protocol Forward roles(P, V)(s: Split roles(P, V)) -> Split roles(P, V):
    return s
)"));
            });
  cases.run(
      "structural alias remapping keeps canonical scopes and ordered children",
      [] {
        auto project = take(check(R"(
type Split roles(P, V) = (index @P, index @V)
protocol Forward roles(A, B)(s: Split roles(A, B)) -> Split roles(A, B):
    return s
protocol Run roles(P, V)(s: Split roles(V, P)) -> Split roles(V, P):
    next <- Forward(s) @(V, P)
    return next
)"));
        const auto &run = declaration(project.declarations(), "m::Run");
        const auto &placed =
            product(run.body->values[run.body->results[0].index].placement);
        require(placed.arguments == std::vector<unsigned>({0, 1}) &&
                    std::get<DataPlacement>(placed.fields[0].value).roles ==
                        std::vector<unsigned>{1},
                "structural scope or ordered child substitution was lost");
      });
  cases.run(
      "protocol boundary refuses an aggregate arrow in place of a product tree",
      [] {
        auto project = take(check(std::string(data) + R"(
protocol Forward roles(P, V)(s: Pair<index> roles(P, V)) -> Pair<index> roles(P, V):
    return s
)"));
        auto port = declaration(project.declarations(), "m::Forward").inputs[0];
        port.placement.reset();
        port.oracle = OraclePort{0, {}};
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Limits limits;
        zkc::language::detail::Work work{limits};
        zkc::language::detail::Semantics semantics(declarations,
                                                   project.assets(), work);
        require(!semantics.oraclePort(port) && semantics.diagnostic &&
                    semantics.diagnostic->code == "source.placement",
                "new product was admitted through the legacy aggregate family "
                "seam");
      });
  cases.run("direct oracle boundary requires matching holder metadata", [] {
    auto project = take(check(std::string(oracles) + R"(
protocol Forward roles(P, V)(s: O @P -> V) -> O @P -> V:
    return s
)"));
    auto port = declaration(project.declarations(), "m::Forward").inputs[0];
    port.placement = OraclePlacement{1, {0}};
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    Limits limits;
    zkc::language::detail::Work work{limits};
    zkc::language::detail::Semantics semantics(declarations, project.assets(),
                                               work);
    require(!semantics.oraclePort(port) && semantics.diagnostic &&
                semantics.diagnostic->code == "source.placement",
            "direct legacy and placed holder metadata disagreed silently");
  });
  cases.run(
      "affine distributed restrictions intersect linear child permissions", [] {
        auto project = take(check(R"(
#[linear]
struct Token:
    pub empty: ()
#[affine]
struct State roles(P, V):
    pub pending: Token @P
    pub observed: index @V
protocol Extract roles(P, V)(s: State roles(P, V)) -> Token @P:
    return s.pending
)"));
        const auto &extract = declaration(project.declarations(), "m::Extract");
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Limits limits;
        zkc::language::detail::Work work{limits};
        zkc::language::detail::Semantics semantics(declarations,
                                                   project.assets(), work);
        auto permissions = semantics.permissions(extract.inputs[0].type, {});
        require(permissions && !permissions->copy && !permissions->drop,
                "affine restriction granted Drop to a mandatory linear child");
      });
  for (const auto &[name, source, diagnostic] :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {"wrong nominal",
            std::string(data) +
                "struct Other roles(P, V):\n    pub first: index @P\n    pub "
                "second: index @V\nprotocol Run roles(P, V)(s: Other roles(P, "
                "V)) -> Pair<index> roles(P, V):\n    return s\n",
            "source.type"},
           {"wrong phantom static",
            std::string(oracles) +
                "protocol Run roles(A, B, V)(s: Sources<1> roles(A, B, V)) -> "
                "Sources<2> roles(A, B, V):\n    return s\n",
            "source.type"},
           {"ordinary enum hides logical",
            std::string(data) + "enum Bad:\n    Some(Pair<index>)\n",
            "source.oracle-aggregate"},
           {"associated representation hides logical",
            std::string(data) +
                "interface CarrierType:\n    type Item: Type\nmodule Carrier: "
                "CarrierType:\n    type Item = Pair<index>\n",
            "source.oracle-boundary"},
           {"private empty projection",
            "module Owner:\n    pub struct State roles(P, V):\n        pub "
            "visible: index @V\n        secret: () @P\nprotocol Run roles(P, "
            "V)(s: Owner::State roles(P, V)) -> () @P:\n    return s.secret\n",
            "source.private"},
           {"private empty construction",
            "module Owner:\n    pub struct State roles(P, V):\n        pub "
            "visible: index @V\n        secret: () @P\nprotocol Run roles(P, "
            "V)() -> Owner::State roles(P, V):\n    return Owner::State "
            "{visible: 1, secret: ()}\n",
            "source.private"},
           {"sealed projection",
            "#[sealed]\nstruct State roles(P, V):\n    pub visible: index "
            "@V\nprotocol Run roles(P, V)(s: State roles(P, V)) -> index @V:\n "
            "   return s.visible\n",
            "source.private"},
           {"field role cannot be gained",
            std::string(data) +
                "protocol Run roles(P, V)(s: Pair<index> roles(P, V)) -> index "
                "@P:\n    return s.second\n",
            "source.roles"},
           {"empty record cannot infer phantom roles",
            "struct Empty roles(P, V):\nprotocol Run roles(P, V)() -> bool "
            "@P:\n    s = Empty {}\n    return true\n",
            "source.placement-inference"},
           {"wrong nested role application",
            std::string(data) +
                "struct Outer roles(P, V):\n    pub pair: Pair<index> roles(V, "
                "P)\nprotocol Run roles(P, V)(s: Pair<index> roles(P, V)) -> "
                "Outer roles(P, V):\n    return Outer {pair: s}\n",
            "source.placement"},
           {"missing alias role application",
            std::string(data) + "type Alias roles(P, V) = Pair<index>\n",
            "source.roles"},
           {"restricted ordinary field cannot share components",
            "#[linear]\nstruct Token:\n    pub empty: ()\nstruct Bad roles(P, "
            "V):\n    pub token: Token @(P, V)\n",
            "source.participants"},
           {"wrong oracle holder",
            std::string(oracles) +
                "struct Wrong roles(A, B, V):\n    pub word: O @B -> "
                "V\nprotocol Run roles(A, B, V)(h: O @A -> V) -> Wrong "
                "roles(A, B, V):\n    return Wrong {word: h}\n",
            "source.placement"},
           {"duplicate oracle receivers",
            std::string(oracles) +
                "struct Wrong roles(P, V):\n    pub word: O @P -> (V, V)\n",
            "source.roles"},
           {"holder in oracle receivers",
            std::string(oracles) +
                "struct Wrong roles(P, V):\n    pub word: O @P -> (P, V)\n",
            "source.roles"},
           {"empty explicit telescope", "struct Wrong roles():\n",
            "source.roles"},
           {"copied linear child",
            "#[linear]\nstruct Token:\n    pub empty: ()\nstruct State "
            "roles(P, V):\n    pub token: Token @P\nprotocol Run roles(P, "
            "V)(s: State roles(P, V)) -> Token @P:\n    first = s.token\n    "
            "second = s.token\n    return second\n",
            "source.move"},
           {"dropped linear child",
            "#[linear]\nstruct Token:\n    pub empty: ()\nstruct State "
            "roles(P, V):\n    pub token: Token @P\nprotocol Run roles(P, "
            "V)(s: State roles(P, V)) -> bool @P:\n    return true\n",
            "source.drop"},
           {"dropped empty restricted root",
            "#[linear]\nstruct Token roles(P, V):\nprotocol Run roles(P, V)(s: "
            "Token roles(P, V)) -> bool @P:\n    return true\n",
            "source.drop"},
           {"duplicate placement annotation",
            std::string(oracles) +
                "struct Bad roles(P, V):\n    pub word: O @P -> V @V\n",
            "source.placement"},
           {"generic multi-role field admission survives specialization",
            "#[linear]\nstruct Token:\n    pub empty: ()\nstruct Shared<T: "
            "Type> roles(P, V):\n    pub payload: T @(P, V)\ntype Bad = "
            "Shared<Token>\n",
            "source.participants"},
           {"ordinary helper cannot read a placed tuple summary",
            "def keep(s: (index, index)) -> (index, index):\n    return "
            "s\nprotocol Run roles(P, V)(s: (index @P, index @V)) -> bool "
            "@P:\n    x = keep(s)\n    return true\n",
            "source.placement"},
           {"ordinary struct cannot hide placed tuple syntax",
            "struct Bad:\n    pair: (index @P, index @V)\n",
            "source.oracle-aggregate"},
           {"ordinary generic cannot erase a placed structural alias",
            "type Split roles(P, V) = (index @P, index @V)\nstruct Box<T: "
            "Type>:\n    pub value: T\ntype Bad = Box<Split>\n",
            "source.oracle-aggregate"},
           {"foreign protocol cannot unpack a sealed placed record",
            "module Owner:\n    #[linear]\n    #[sealed]\n    pub struct Token "
            "roles(P, V):\n        private: () @P\nprotocol Run roles(P, V)(s: "
            "Owner::Token roles(P, V)) -> bool @P:\n    fields <- unpack(s)\n  "
            "  return true\n",
            "source.private"},
           {"distributed resource unpack requires an ordered root",
            "#[linear]\nstruct Token roles(P, V):\nprotocol Run roles(P, V)(s: "
            "Token roles(P, V)) -> bool @P:\n    fields = unpack(s)\n    "
            "return true\n",
            "source.action"},
           {"affine wrapper does not discard a linear child",
            "#[linear]\nstruct Token:\n    pub empty: ()\n#[affine]\nstruct "
            "State roles(P, V):\n    pub pending: Token @P\nprotocol Run "
            "roles(P, V)(s: State roles(P, V)) -> bool @P:\n    return true\n",
            "source.drop"},
           {"duplicate declaration roles",
            "struct S roles(P, P):\n    x: index @P\n", "source.roles"},
           {"ordinary field omission", "struct S roles(P, V):\n    x: index\n",
            "source.roles"},
           {"ordinary struct hides zero-array logical",
            std::string(data) + "struct Bad:\n    x: [Pair<index>; 0]\n",
            "source.oracle-aggregate"},
           {"generic type sort hides logical",
            std::string(data) +
                "struct Box<T: Type>:\n    x: T\ntype Bad = Box<Pair<index>>\n",
            "source.oracle-boundary"},
           {"noninjective application",
            std::string(data) +
                "protocol Run roles(P, V)(s: Pair<index> roles(P, P)) -> "
                "Pair<index> roles(P, V):\n    return s\n",
            "source.roles"},
           {"wrong return map",
            std::string(data) +
                "protocol Run roles(P, V)(s: Pair<index> roles(P, V)) -> "
                "Pair<index> roles(V, P):\n    return s\n",
            "source.placement"},
           {"outer product override",
            std::string(data) +
                "protocol Run roles(P, V)(s: Pair<index> roles(P, V) @P) -> "
                "bool @P:\n    return true\n",
            "source.placement"},
           {"ambiguous constructor",
            std::string(data) +
                "protocol Run roles(P, V)() -> bool @P:\n    s = Pair<index> "
                "{first: 1, second: 2, empty: ()}\n    return true\n",
            "source.placement-inference"},
           {"no implicit port roster",
            std::string(data) + "protocol Run roles(P, V)(s: Pair<index>) -> "
                                "bool @P:\n    return true\n",
            "source.roles"},
           {"omitted shared roster needs selector availability",
            std::string(data) +
                "protocol Run roles(P, V)(s: Pair<index> roles(P, V), b: bool "
                "@P) -> Pair<index> roles(P, V):\n    return if b:\n        "
                "s\n    else:\n        s\n",
            "source.roles"}})
    cases.run(name, [source = source, diagnostic = diagnostic] {
      refuses(check(source), diagnostic);
    });
  return cases.result();
}
