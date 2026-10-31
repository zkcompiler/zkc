#include "../lib/Compiler/ComponentContracts.h"
#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source_detail = zkc::language::detail;
namespace {
using A = json::Array;
using J = json::Value;
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Oracles<K:OracleKind,M:nat>=builtin("oracle_sequence",K,M);
type O=Oracle<Fixed<F,16>>;
type Kind=Fixed<F,16>;
type Data=Kind::Data;
struct Empty{hidden:()}
struct Meta{before:index,empty:(),pub after:index}
enum Choice{Some(index,()),None()}
#[logical] struct State{
  secret:(),pub meta:Meta,word:O,pub choice:Choice,
  pub layers:Oracles<Fixed<F,16>,0>,pub tail:[Empty;0]
}
relation Holds(witness data:Data){return true;}
relation Position(statement value:index){return true;}
)";
Expected<CheckedProject> check(StringRef code) {
  auto captured = capture({{"m", std::string(prefix) + code.str(),
                            "logical-record-contracts.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
ClosedEntry close(StringRef code) {
  return take(closeNativeRun(take(check(code)), "m::Run"));
}
void accept(Error result) {
  if (result)
    throw std::runtime_error(toString(std::move(result)));
}
void refuse(Error result, StringRef code) {
  require(bool(result), "expected refusal: " + code);
  auto message = toString(std::move(result));
  require(namesIdentifier(message, code), "unexpected diagnostic: " + message);
}
const char *relay = R"(
protocol Run roles(P,V)(state:State@P->V,other:O@P->V)
  ->(out:State@P->V,accepted:bool@V)
  spec{input valid=Holds(in.state.word);
       input position=Position(in.state.meta.after@V);
       output returned=Holds(out.out.word);}
  {return(out=state,accepted=true);}
)";
J declarations(const ClosedEntry &entry) {
  return take(json::parse(take(inspectComponentDeclarations(entry))));
}
A &row(J &declarations, StringRef name) {
  for (auto &value : *(*declarations.getAsArray())[0].getAsArray()) {
    auto &record = *value.getAsArray();
    if ((*record[0].getAsArray())[2].getAsString() == name)
      return record;
  }
  throw std::runtime_error("missing retained nominal: " + name.str());
}
} // namespace
int main() {
  Cases cases;
  cases.run("retained rows preserve logical and ordinary nominal members", [] {
    auto entry = close(relay);
    auto retained = declarations(entry);
    accept(checkComponentDeclarations(retained));
    auto &state = row(retained, "m::State");
    require((*state[0].getAsArray())[1] == J("logical_record") &&
                state[1] == J("ordinary") && state.size() == 4 &&
                state[3].getAsArray()->size() == 6,
            "logical declaration kind or private/empty fields disappeared");
    require(row(retained, "m::Empty")[3].getAsArray()->size() == 1 &&
                row(retained, "m::Meta")[3].getAsArray()->size() == 3,
            "zero-length element or ordinary record fields disappeared");
    const auto &arms = *row(retained, "m::Choice")[3].getAsArray();
    require(arms.size() == 2 &&
                (*arms[0].getAsArray())[1].getAsArray()->size() == 2 &&
                (*arms[1].getAsArray())[1].getAsArray()->empty(),
            "variant alternative or zero-leaf payload disappeared");
    const auto &owner =
        *(*(*retained.getAsArray())[1].getAsArray())[0].getAsArray();
    Layouts layouts(entry);
    for (unsigned side : {1u, 2u}) {
      unsigned offset = 0;
      const auto &ports =
          side == 1 ? entry.protocol().inputs : entry.protocol().outputs;
      const auto &rows = *owner[side].getAsArray();
      require(rows.size() == ports.size(), "source port count differs");
      for (unsigned i = 0; i < ports.size(); ++i) {
        auto observed = take(layouts.protocolPort(ports[i]));
        const auto &port = *rows[i].getAsArray();
        require(port[3].getAsUINT64() == offset &&
                    port[4].getAsUINT64() == observed.size(),
                "retained offset counts body handles instead of ABI pairs");
        offset += observed.size();
      }
    }
    require(take(inspectComponentDeclarations(entry)) != "[[],[]]",
            "logical-only declarations were cleared");
  });
  cases.run("singleton field anchors share the expanded layout observer", [] {
    auto entry = close(relay);
    const auto &protocol = entry.protocol();
    const auto &anchor = protocol.specifications[0].subject.operands[0];
    const auto &ordinary = protocol.specifications[1].subject.operands[0];
    require(anchor.anchor && anchor.role == 0 &&
                anchor.path == std::vector<unsigned>{2} && !ordinary.anchor &&
                ordinary.role == 1 &&
                ordinary.path == std::vector<unsigned>({1, 2}),
            "source field path, anchor, or ordinary participant was lost");
    Layouts layouts(entry);
    require(take(layouts.select(protocol, anchor)).offset == 3 &&
                take(layouts.select(protocol, ordinary)).offset == 1,
            "anchor selector used body offsets");
    auto source = take(prepareOriginal(entry));
    auto view = take(readInterface(source.bytes(), source.interfaceJson()));
    accept(compareInterface(entry, view));
    const auto &selected =
        view.selectedProtocol().clauses[0].subject.operands[0];
    require(selected.anchor && selected.native == std::vector<unsigned>{3},
            "interface selector lost its field anchor");
  });
  cases.run("generic and remapped logical fields retain anchor types", [] {
    auto entry = close(R"(
type KindData<K:OracleKind>=K::Data;
#[logical] struct Generic<K:OracleKind>{pub word:Oracle<K>}
relation Valid<K:OracleKind>(witness data:KindData<K>){return true;}
protocol Forward<K:OracleKind> roles(B,A)(state:Generic<K>@A->B)
  ->(out:Generic<K>@A->B)
  spec{input valid=Valid<K>(in.state.word);
       output returned=Valid<K>(out.out.word);}{return(out=state);}
protocol Run roles(P,V)(state:Generic<Fixed<F,16>>@P->V)
  ->(out:Generic<Fixed<F,16>>@P->V){
  let out=Forward<Fixed<F,16>> roles(V,P)(state);return(out=out);
}
)");
    auto source = take(prepareOriginal(entry));
    auto view = take(readInterface(source.bytes(), source.interfaceJson()));
    accept(compareInterface(entry, view));
  });
  cases.run("direct anchors defer symbolic port row bounds", [] {
    auto entry = close(R"(
type Table=builtin("oracle.table",F);
type Dynamic=Oracle<Table>;
protocol Forward<M:nat> roles(A,B)(word:Dynamic@A->B max M)
  ->(out:Dynamic@A->B max M)
  spec{input valid=Holds(in.word);output returned=Holds(out.out);}
  {return(out=word);}
protocol Run roles(P,V)(word:Dynamic@P->V max 8)
  ->(out:Dynamic@P->V max 8){
  let out=Forward<8> roles(P,V)(word);return(out=out);
}
)");
    auto source = take(prepareOriginal(entry));
    auto view = take(readInterface(source.bytes(), source.interfaceJson()));
    accept(compareInterface(entry, view));
  });
  for (StringRef selected :
       {"in.state", "in.state.layers", "in.state.word@P", "in.state.word@V"})
    cases.run("singleton anchor refuses " + selected, [&] {
      std::string code = relay;
      auto at = code.find("in.state.word");
      code.replace(at, StringRef("in.state.word").size(), selected.str());
      refuses(check(code), "source.specification");
    });
  cases.run(
      "retained selectors cannot give ordinary fields anchor custody", [] {
        auto entry = close(relay);
        std::vector<Declaration> declarations(entry.declarations().begin(),
                                              entry.declarations().end());
        const Limits limits;
        for (auto path : {std::vector<unsigned>{1}, std::vector<unsigned>{1, 2},
                          std::vector<unsigned>{4}}) {
          source_detail::Work work{limits};
          source_detail::Semantics semantics(declarations, {}, work);
          require(!semantics.selectedType(
                      entry.protocol(),
                      SpecificationSelector{false, 0, 0, path, {}, true}),
                  "ordinary field or sequence acquired an anchor selector");
          refuse(semantics.takeError(), "source.specification");
        }
      });
  cases.run("field anchor cannot bypass another module's privacy", [] {
    auto captured = take(capture({{"lib", R"(
module lib;
domain F=field("bls12-381.fr");
type O=builtin("oracle",builtin("oracle.table",F,16));
#[logical] pub struct State{hidden:O,pub visible:O}
)",
                                   "lib.zkc"},
                                  {"m", R"(
module m;use lib::State;
domain F=field("bls12-381.fr");
type Kind=builtin("oracle.table",F,16);
type Data=Kind::Data;
relation Holds(witness data:Data){return true;}
protocol Run roles(P,V)(state:State@P->V)->(out:State@P->V)
  spec{input valid=Holds(in.state.hidden);}{return(out=state);}
)",
                                   "private-anchor.zkc"}}));
    refuses(analyze(captured).checkedProject(), "source.private");
  });
  cases.run("closed body value types retain nominal declarations", [] {
    auto entry = close(R"(
struct BodyRecord{hidden:(),pub value:index}
enum BodyVariant{Value(index,())}
protocol Run roles(P,V)(a:O@P->V,b:O@P->V)->(out:O@P->V){
  let note=BodyRecord{hidden=(),value=0};
  let choice=BodyVariant::Value(1,());
  let layers=oracle.empty<Fixed<F,16>,0> roles(P,V)();
  let state=State{secret=(),meta=Meta{before=0,empty=(),after=1},
                  word=a,choice=Choice::Some(2,()),layers=layers,tail=[]};
  return(out=state.word);
}
)");
    auto retained = declarations(entry);
    require(row(retained, "m::State")[3].getAsArray()->size() == 6 &&
                row(retained, "m::Choice")[3].getAsArray()->size() == 2 &&
                row(retained, "m::BodyRecord")[3].getAsArray()->size() == 2 &&
                row(retained, "m::BodyVariant")[3].getAsArray()->size() == 1,
            "body-only nominal declarations were omitted");
    accept(checkComponentDeclarations(retained));
    Limits limits;
    limits.work = 1;
    refuses(inspectComponentDeclarations(entry, limits), "source.limit");
    limits = Limits{};
    limits.typeDepth = 1;
    refuses(inspectComponentDeclarations(entry, limits), "source.limit");
  });
  for (StringRef mutation :
       {"duplicate-row", "duplicate-field", "duplicate-alternative",
        "duplicate-payload", "malformed-payload", "wrong-kind", "resource",
        "child-resource", "empty-child-resource", "missing-child",
        "conflicting-kind"})
    cases.run("retained declarations reject " + mutation, [&] {
      auto retained = declarations(close(relay));
      auto &records = *(*retained.getAsArray())[0].getAsArray();
      auto &state = row(retained, "m::State");
      auto &choice = row(retained, "m::Choice");
      StringRef diagnostic = "component-declaration-duplicate";
      if (mutation == "duplicate-row") {
        J copy = A(state);
        records.push_back(std::move(copy));
      } else if (mutation == "duplicate-field") {
        auto &fields = *state[3].getAsArray();
        J copy = fields[0];
        fields.push_back(std::move(copy));
      } else if (mutation == "duplicate-alternative") {
        auto &arms = *choice[3].getAsArray();
        J copy = arms[0];
        arms.push_back(std::move(copy));
      } else if (mutation == "duplicate-payload") {
        auto &fields =
            *(*(*choice[3].getAsArray())[0].getAsArray())[1].getAsArray();
        J copy = fields[0];
        fields.push_back(std::move(copy));
      } else if (mutation == "malformed-payload") {
        (*(*choice[3].getAsArray())[0].getAsArray())[1] = true;
        diagnostic = "component-declaration";
      } else {
        diagnostic = "component-declaration-record";
        if (mutation == "resource")
          state[1] = "affine";
        else if (mutation == "child-resource")
          choice[1] = "affine";
        else if (mutation == "empty-child-resource")
          row(retained, "m::Empty")[1] = "affine";
        else if (mutation == "wrong-kind")
          (*state[0].getAsArray())[1] = "associated";
        else if (mutation == "missing-child") {
          auto found = llvm::find_if(records, [](const J &value) {
            return (*(*value.getAsArray())[0].getAsArray())[2] ==
                   J("m::Choice");
          });
          records.erase(found);
        } else {
          J copy = A(state);
          (*(*copy.getAsArray())[0].getAsArray())[1] = "record";
          records.push_back(std::move(copy));
        }
      }
      refuse(checkComponentDeclarations(retained), diagnostic);
    });
  cases.run(
      "ordinary source record declarations retain existing semantics", [] {
        auto entry = close(R"(
struct Plain{pub value:index,pub empty:()}
protocol Run roles(P)(value:Plain@P)->(out:Plain@P){return(out=value);}
)");
        require(take(inspectComponentDeclarations(entry)) == "[[],[]]",
                "ordinary records alone enabled the retained carrier");
        auto ordinary = take(json::parse(R"([
      [[["nominal","record","m::Pending",[]],"linear",true,
        [["value",["bool"]]]]],[]])"));
        accept(checkComponentDeclarations(ordinary));
        (*(*(*ordinary.getAsArray())[0].getAsArray())[0].getAsArray())[2] =
            false;
        refuse(checkComponentDeclarations(ordinary),
               "component-declaration-record");
      });
  return cases.result();
}
