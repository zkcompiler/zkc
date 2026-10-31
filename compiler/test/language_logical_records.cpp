#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace source_detail = zkc::language::detail;
namespace {
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Oracles<K:OracleKind,M:nat>=builtin("oracle_sequence",K,M);
type O=Oracle<Fixed<F,16>>;
#[logical] pub struct State<K:OracleKind,M:nat>{
  pub word:Oracle<K>,pub layers:Oracles<K,M>,pub first:index,pub second:index
}
type S=State<Fixed<F,16>,2>;
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture(
      {{"m", std::string(prefix) + source.str(), "logical-records.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<CheckedProject> checkLayout(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", source.str(), "logical-records.layout.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &findDeclaration(const CheckedProject &project, StringRef name) {
  auto declaration = llvm::find_if(project.declarations(), [&](const auto &d) {
    return d.qualifiedName == name;
  });
  require(declaration != project.declarations().end(), "missing declaration");
  return *declaration;
}
const char *ordered = R"(
protocol Run roles(P,V)(h:O@P->V)->(out:S@P->V){
  let layers=oracle.empty<Fixed<F,16>,2> roles(P,V)();
  let state=S{second:index<2>(),layers:layers,word:h,first:index<1>()};
  let selected=state.word;let ordinary=state.first;
  let copied=state;return(out=copied);
}
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "distinct nominal kind, authored evaluation and declaration storage", [] {
        auto project = take(check(ordered));
        const auto &state = findDeclaration(project, "m::State");
        require(state.logical && !state.sealed && !state.resource,
                "logical metadata was conflated with sealing or resources");
        const auto &alias = findDeclaration(project, "m::S");
        require(alias.domain.kind == Type::Kind::LogicalRecord &&
                    typeKindName(alias.domain.kind) == "logical_record",
                "alias lost the nominal logical kind");
        const auto &run = findDeclaration(project, "m::Run");
        require(run.body && run.outputs.front().oracle &&
                    run.outputs.front().oracle->holder == 0,
                "checked port lost custody metadata");
        const auto &body = *run.body;
        const Construct *constructor = nullptr;
        unsigned constructions = 0, constants = 0;
        bool oracleProjection = false, ordinaryProjection = false;
        for (const auto &operation : body.operations) {
          if (const auto *math = std::get_if<MathValue>(&operation.action);
              math &&
              math->identity == zkc::MathematicalIdentity::IndexConstant)
            ++constants;
          if (const auto *aggregate = std::get_if<Construct>(&operation.action);
              aggregate && !operation.results.empty() &&
              body.values[operation.results.front().index].type.kind ==
                  Type::Kind::LogicalRecord) {
            constructor = aggregate;
            ++constructions;
            const auto &value = body.values[operation.results.front().index];
            require(value.oracleHolder == 0 &&
                        value.components == std::vector<unsigned>({0, 1}),
                    "construction lost its inferred family");
          }
          if (const auto *projection =
                  std::get_if<Projection>(&operation.action)) {
            const auto &value = body.values[operation.results.front().index];
            if (isOracleHandle(value.type)) {
              oracleProjection = true;
              require(value.oracleHolder == 0, "oracle projection lost holder");
            } else if (value.type.kind == Type::Kind::LogicalRecord) {
              require(projection->path.empty() && value.oracleHolder == 0,
                      "identity projection lost holder");
            } else {
              ordinaryProjection = true;
              require(!value.oracleHolder,
                      "ordinary projection acquired custody");
            }
          }
        }
        require(constructions == 1 && constants == 2 && constructor &&
                    constructor->operands.size() == 4,
                "constructor reevaluated or omitted fields");
        const auto &operands = constructor->operands;
        require(operands[3].index < operands[2].index,
                "authored evaluation order was replaced by declaration order");
        require(
            body.values[operands[0].index].type.kind == Type::Kind::Oracle &&
                body.values[operands[1].index].type.kind ==
                    Type::Kind::OracleSequence &&
                body.values[operands[2].index].type.kind == Type::Kind::Index,
            "stored operands are not in declaration order");
        require(oracleProjection && ordinaryProjection,
                "projection coverage missing");
      });
  cases.run("generic nominal state, reordered role mapping and loop carry", [] {
    auto project = take(check(R"(
protocol Forward<K:OracleKind,M:nat> roles(B,A)
  (state:State<K,M>@A->B)->(out:State<K,M>@A->B){return(out=state);}
protocol Run roles(P,V)(h:O@P->V,n:index@(P,V))->(out:S@P->V){
  let layers=oracle.empty<Fixed<F,16>,2> roles(P,V)();
  let mut state=S{word:h,layers:layers,first:0,second:1};
  for i in 0..n roles(P,V) max 2 {
    state=Forward<Fixed<F,16>,2> roles(V,P)(state);
  }
  return(out=state);
})"));
    const auto &body = *findDeclaration(project, "m::Run").body;
    bool carried = false;
    for (const auto &operation : body.operations)
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
        carried = true;
        require(repeat->carried.size() == 1 && repeat->region &&
                    body.values[repeat->carried.front().index].oracleHolder ==
                        0,
                "loop omitted logical state custody");
        const auto &region = *repeat->region;
        require(region.values[region.results.front().index].oracleHolder == 0,
                "loop successor lost holder");
        bool remapped = false;
        for (const auto &inner : region.operations)
          if (const auto *call =
                  std::get_if<ProtocolApplication>(&inner.action)) {
            remapped = call->roles == std::vector<unsigned>({1, 0});
            require(region.values[inner.results.front().index].oracleHolder ==
                        0,
                    "call result holder was not remapped");
          }
        require(remapped, "call role remapping was lost");
      }
    require(carried, "missing protocol loop");
  });
  cases.run("zero capacity alone supplies a family within a wider roster", [] {
    auto project = take(check(R"(
#[logical] struct Empty{pub words:Oracles<Fixed<F,16>,0>,secret:()}
protocol Run roles(P,V,W)()->(out:Empty@P->V){
  let words=oracle.empty<Fixed<F,16>,0> roles(P,V)();
  let out=Empty{secret:(),words:words};return(out=out);
})"));
    const auto &body = *findDeclaration(project, "m::Run").body;
    const auto &value = body.values[body.results.front().index];
    require(value.components == std::vector<unsigned>({0, 1}) &&
                value.oracleHolder == 0,
            "empty sequence family was inferred from the ambient roster");
  });
  cases.run("Copy and Drop preserve identity across repeated uses", [] {
    take(check(R"(
protocol Run roles(P,V)(s:S@P->V)->(left:S@P->V,right:S@P->V){
  let unused=s;let a=s;let b=s;return(left=a,right=b);
})"));
  });
  cases.run("generic ordinary payloads retain recursive shared data", [] {
    take(check(R"(
struct Payload<T:Type+Copy+Drop>{pub pair:(T,()),pub empty:[T;0]}
#[logical] struct WithPayload<T:Type+Copy+Drop>{pub word:O,pub data:Payload<T>}
protocol Run roles(P,V)(h:O@P->V,data:Payload<index>@(P,V))
  ->(out:WithPayload<index>@P->V){
  let state=WithPayload<index>{data:data,word:h};return(out=state);
}
interface Carrier{type Item;}
#[logical] struct AssociatedPayload<C:Carrier> where Copy(C::Item) {
  pub word:O,pub data:C::Item
}
)"));
  });
  cases.run("record patterns project handles without giving ordinary custody",
            [] {
              auto project = take(check(R"(
protocol Run roles(P,V)(state:S@P->V)->(out:O@P->V){
  let S{second,word,layers,first}=state;return(out=word);
})"));
              const auto &body = *findDeclaration(project, "m::Run").body;
              require(body.values[body.results.front().index].oracleHolder == 0,
                      "record pattern lost oracle custody");
            });
  cases.run("sealing remains independent of logical Copy and Drop", [] {
    take(check(R"(
#[sealed] #[logical] struct Sealed{pub word:O}
protocol Run roles(P,V)(state:Sealed@P->V)->(out:Sealed@P->V){
  let unused=state;return(out=state);
})"));
  });
  cases.run("all ordinary boundary profiles reject logical records", [] {
    auto project = take(check(""));
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    const Limits limits;
    source_detail::Work work{limits};
    source_detail::Semantics semantics(declarations, project.assets(), work);
    const auto &state = findDeclaration(project, "m::S").domain;
    for (auto boundary :
         {Boundary::Participants, Boundary::Message, Boundary::Construction}) {
      auto admission = semantics.admission(state, boundary, {});
      require(admission &&
                  *admission == source_detail::Semantics::Admission::Rejected,
              "logical record passed an ordinary boundary profile");
    }
    require(!semantics.hostData(state, {}),
            "logical record passed the Host data boundary");
  });
  cases.run("ordinary components are independently assembled without equality",
            [] {
              take(checkLayout(R"(
domain F = field("bls12-381.fr")
type Kind = builtin("oracle.table", F, 16)
type O = builtin("oracle", Kind)
#[logical]
struct State:
    pub word: O
    pub position: index
pub protocol Run roles(P, V)(h: O @P -> V; a: index @P; b: index @V) -> State @P -> V:
    position = @(P = a, V = b)
    return State {position: position, word: h}
)"));
            });
  cases.run(
      "layout annotations retain private field bounds and zero capacity", [] {
        auto project = take(checkLayout(R"(
domain F = field("bls12-381.fr")
type Table = builtin("oracle.table", F)
type Words = builtin("oracle_sequence", Table, 0)
#[shape(words.rows, bound = Maximum)]
#[logical]
pub struct State<Maximum: nat>:
    words: Words
    pub note: ()
pub protocol Forward<Maximum: nat> roles(A, B)(state: State<Maximum> @A -> B) -> State<Maximum> @A -> B:
    return state
)"));
        const auto &state = findDeclaration(project, "m::State");
        require(
            state.logical && state.fields.front().maximumRows &&
                !state.fields.front().isPublic,
            "layout projection lost logical attributes or private field bound");
      });
  cases.run("logical records cannot enter ordinary role assembly", [] {
    refuses(checkLayout(R"(
type Kind = builtin("oracle.table", bool, 4)
type O = builtin("oracle", Kind)
#[logical]
struct State:
    pub word: O
pub protocol Invalid roles(P, V)(state: State @P -> V) -> bool @P:
    merged = @(P = state, V = state)
    return true
)"),
            "source.oracle-boundary");
  });
  cases.run(
      "private constructor and field remain usable in the defining module", [] {
        take(check(R"(
#[logical] struct Secret{word:O,pub note:index}
protocol Run roles(P,V)(h:O@P->V)->(out:O@P->V){
  let state=Secret{note:0,word:h};let out=state.word;return(out=out);
})"));
      });
  for (StringRef body : {"let state=Secret{word:h,note:0};return(out=state);",
                         "let word=state.word;return(out=state);"}) {
    bool constructing = body.starts_with("let state=");
    cases.run(
        constructing ? "private cross-module constructor"
                     : "private cross-module projection",
        [=] {
          auto captured = take(capture(
              {{"lib", R"(module lib;
pub type O=builtin("oracle",builtin("oracle.table",bool,16));
#[logical] pub struct Secret{word:O,pub note:index})",
                "lib.zkc"},
               {"m",
                "module m;use lib::{Secret,O};protocol Run roles(P,V)(" +
                    std::string(constructing ? "h:O@P->V"
                                             : "state:Secret@P->V") +
                    ")->(out:Secret@P->V){" + body.str() + "}",
                "m.zkc"}}));
          refuses(analyze(captured).checkedProject(), "source.private");
        });
  }
  cases.run("source inspection retains logical declaration and field shapes",
            [] {
              auto project = take(check(R"(
#[logical]
#[shape(words.rows,bound=Rows)]
pub struct Dynamic<Rows:nat>{pub words:Oracles<Table<F>,0>,hidden:()}
)"));
              const auto &dynamic = findDeclaration(project, "m::Dynamic");
              require(dynamic.fields.front().maximumRows &&
                          dynamic.fields.front().maximumRows->kind ==
                              Type::Kind::Natural,
                      "checked declaration dropped field bound");
              auto api = take(inspectPublicAPI(project));
              auto written = take(inspectWrittenSource(project));
              require(api.find("logical_record") != std::string::npos &&
                          api.find("maximum_rows") != std::string::npos &&
                          written.find("\"logical\"") != std::string::npos &&
                          written.find("declaration.logical_record") !=
                              std::string::npos &&
                          written.find("oracle_shape") != std::string::npos,
                      "source inspection dropped logical metadata");
            });
  cases.run("field bounds substitute independently of sequence capacity", [] {
    auto project = take(check(R"(
#[logical] #[shape(words.rows,bound=Rows)]
struct Dynamic<K:OracleKind,Rows:nat,Capacity:nat>{pub words:Oracles<K,Capacity>}
)"));
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    const Limits limits;
    source_detail::Work work{limits};
    source_detail::Semantics semantics(declarations, project.assets(), work);
    Type kind(Type::Kind::OracleKind, "table");
    kind.arguments = {Type(Type::Kind::Field, "bls12-381.fr")};
    Type rows(Type::Kind::Natural), capacity(Type::Kind::Natural);
    rows.dimension = Natural::constant(37);
    capacity.dimension = Natural::constant(0);
    Type state(Type::Kind::LogicalRecord, "m::Dynamic");
    state.arguments = {kind, rows, capacity};
    require(semantics.logicalRecord(state, {}),
            "unsized field did not specialize");
    auto fields = semantics.fields(state, {});
    require(fields && fields->front().maximumRows &&
                fields->front().maximumRows->dimension == rows.dimension &&
                fields->front().type.arguments[1].dimension ==
                    capacity.dimension,
            "capacity and per-element rows were conflated");
    kind.arguments.push_back(rows);
    state.arguments.front() = kind;
    require(!semantics.logicalRecord(state, {}) && semantics.diagnostic &&
                semantics.diagnostic->code == "source.oracle-shape",
            "specialization retained an illegal sized field bound");
  });
  cases.run(
      "symbolic kind rechecks a missing bound when it becomes unsized", [] {
        auto project = take(check(
            "#[logical] struct Generic<K:OracleKind>{pub word:Oracle<K>}"));
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        const Limits limits;
        source_detail::Work work{limits};
        source_detail::Semantics semantics(declarations, project.assets(),
                                           work);
        Type kind(Type::Kind::OracleKind, "table");
        kind.arguments = {Type(Type::Kind::Boolean)};
        Type state(Type::Kind::LogicalRecord, "m::Generic");
        state.arguments = {kind};
        require(!semantics.protocolValue(state, {}) && semantics.diagnostic &&
                    semantics.diagnostic->code == "source.oracle-shape",
                "unsized specialization omitted its row bound check");
      });
  cases.run("nested alias retains logical identity without a data carrier", [] {
    auto project = take(check("module Wrapper{type Hidden=S;}"));
    require(findDeclaration(project, "m::Wrapper::Hidden").domain.kind ==
                Type::Kind::LogicalRecord,
            "nested alias erased logical identity");
  });
  const std::pair<const char *, const char *> negatives[] = {
      {R"(#[logical] struct Empty{pub ordinary:()})",
       "source.oracle-aggregate"},
      {R"(#[logical] struct Nested{pub inner:S,pub word:O})",
       "source.oracle-boundary"},
      {R"(struct Wrapper{pub inner:S})", "source.oracle-aggregate"},
      {R"(type Wrapped=(S,);)", "source.oracle-aggregate"},
      {R"(type Wrapped=[S;0];)", "source.oracle-aggregate"},
      {R"(type Hidden=S;struct Wrapper{pub inner:Hidden})",
       "source.oracle-aggregate"},
      {R"(struct Wrapper<T:Type>{pub inner:T}type Hidden=Wrapper<S>;)",
       "source.oracle-boundary"},
      {R"(type Zero<T:Type>=[T;0];type Hidden=Zero<S>;)",
       "source.oracle-boundary"},
      {R"(enum Wrapper{Some(S)})", "source.oracle-aggregate"},
      {R"(type Wrapper=builtin("sequence",S);)", "source.builtin"},
      {R"(#[affine] #[logical] struct Restricted{pub word:O})",
       "source.resource"},
      {R"(#[linear] #[logical] struct Restricted{pub word:O})",
       "source.resource"},
      {R"(#[sealed] #[logical] struct Sealed{pub word:O}protocol Invalid roles(P,V)(state:Sealed@P->V)->(out:O@P->V){let word=state.word;return(out=word);})",
       "source.private"},
      {R"(#[logical] type Wrong=O;)", "source.oracle-aggregate"},
      {R"(#[logical] struct Missing{pub word:Oracle<Table<F>>})",
       "source.oracle-shape"},
      {R"(#[logical] struct Missing{pub words:Oracles<Table<F>,0>})",
       "source.oracle-shape"},
      {R"(type Missing=State<Table<F>,0>;)", "source.oracle-shape"},
      {R"(#[logical] #[shape(word.rows,bound=8)] struct Generic<K:OracleKind>{pub word:Oracle<K>}type Wrong=Generic<Fixed<F,16>>;)",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(word.rows,bound=8)] struct Sized{pub word:O})",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(word.rows,bound=bool)] struct Wrong{pub word:Oracle<Table<F>>})",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(note.rows,bound=8)] struct Wrong{pub word:O,pub note:()})",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(missing.rows,bound=8)] struct Wrong{pub word:O})",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(word.columns,bound=8)] struct Wrong{pub word:Oracle<Table<F>>})",
       "source.oracle-shape"},
      {R"(#[logical] #[shape(word.rows,bound=8)] #[shape(word.rows,bound=9)] struct Wrong{pub word:Oracle<Table<F>>})",
       "source.oracle-shape"},
      {R"(protocol Invalid roles(P,V)(state:S@(P,V))->(out:S@P->V){return(out=state);})",
       "source.oracle-port"},
      {R"(#[shape(state.rows,bound=8)] protocol Invalid roles(P,V)(state:S@P->V)->(out:S@P->V){return(out=state);})",
       "source.oracle-shape"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V)->(out:S@V->P){return(out=state);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V)(a:O@P->V,b:O@V->P)->(out:S@P->V){let layers=oracle.empty<Fixed<F,16>,2> roles(V,P)();let out=S{word:a,layers:layers,first:0,second:1};return(out=out);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V,W)(a:O@P->(V,W))->(out:S@P->V){let layers=oracle.empty<Fixed<F,16>,2> roles(P,V)();let out=S{word:a,layers:layers,first:0,second:1};return(out=out);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V)(a:O@P->V,i:index@P)->(out:S@P->V){let layers=oracle.empty<Fixed<F,16>,2> roles(P,V)();let out=S{word:a,layers:layers,first:i,second:1};return(out=out);})",
       "source.roles"},
      {R"(#[logical] struct Empty{pub words:Oracles<Fixed<F,16>,0>,secret:()}protocol Invalid roles(P,V)(unit:()@P)->(out:Empty@P->V){let words=oracle.empty<Fixed<F,16>,0> roles(P,V)();let out=Empty{secret:unit,words:words};return(out=out);})",
       "source.roles"},
      {R"(fn invalid(state:S)->S{return state;})", "source.oracle-boundary"},
      {R"(math fn invalid(state:S)->S{return state;})",
       "source.oracle-boundary"},
      {R"(interface Invalid{math fn take(state:S)->S;})",
       "source.oracle-boundary"},
      {R"(fn invalid(callback:math fn(S)->S)->(){return ();})",
       "source.oracle-boundary"},
      {R"(domain fn invalid(items:domain<S>)->domain<S>=domain("product");)",
       "source.oracle-boundary"},
      {R"(entry fn invalid(state:S)->S{return state;})",
       "source.oracle-boundary"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V)->(out:S@P->V){let narrowed@P=state;return(out=state);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V)->(out:bool@V){let copy=send P->V(state);return(out=true);})",
       "source.oracle-boundary"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V)->(out:S@P->V){let packed=(state,);return(out=state);})",
       "source.oracle-boundary"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V)->(out:S@P->V){let packed=[state];return(out=state);})",
       "source.oracle-boundary"},
      {R"(protocol Forward roles(P,V)(state:S@P->V)->(out:S@P->V){return(out=state);}protocol Invalid roles(P,V)(state:S@P->V)->(out:S@P->V){let out=Forward roles(V,P)(state);return(out=out);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V,W)(state:S@P->(V,W))->(out:S@P->V){return(out=state);})",
       "source.oracle-role"},
      {R"(protocol Forward roles(P,V)(state:S@P->V)->(out:S@P->V){return(out=state);}protocol Invalid roles(P,V,W)(state:S@P->(V,W))->(out:S@P->(V,W)){let next=Forward roles(P,V)(state);return(out=state);})",
       "source.oracle-role"},
      {R"(protocol Invalid roles(P,V)(state:S@P->V,reverse:S@V->P,n:index@(P,V))->(out:S@P->V){let mut current=state;for i in 0..n roles(P,V) max 2 {current=reverse;}return(out=current);})",
       "source.oracle-role"},
  };
  for (auto [source, diagnostic] : negatives)
    cases.run(std::string("refuse ") + source,
              [source = source, diagnostic = diagnostic] {
                refuses(check(source), diagnostic);
              });
  return cases.result();
}
