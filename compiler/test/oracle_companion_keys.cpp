#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Companions.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/SourceTerms.h"
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Oracle<K:OracleKind>=builtin("oracle",K);
type O=Oracle<Fixed<F,16>>;
math fn same(a:index,b:index)->bool{return intrinsic("index.equal",a,b);}
)";
const char *bounded = R"(
#[shape(source.rows,bound=Max)]
#[shape(result.rows,value=rows,bound=Max)]
pub oracle def Bounded<T:Field,Max:nat>(source:Oracle<Table<T>>,rows:index)
    ->Oracle<Table<T>> {
  requires exact: same(oracle.rows(source),rows);
  requires true;
  query(position:index){let answer <- query source at position;return answer;}
}
)";
const char *identitySource = R"(
pub oracle def Identity(source:O)->O {
  query(position:index){let answer <- query source at position;return answer;}
}
)";
CheckedProject check(StringRef source) {
  return take(analyze(take(capture({{"m", std::string(prefix) + source.str(),
                                     "oracle-companions.zkc"}})))
                  .checkedProject());
}
json::Value instances(const ClosedEntry &entry) {
  return take(json::parse(take(inspectSourceInstances(entry))));
}
const json::Object &find(const json::Array &array, StringRef key,
                         StringRef value) {
  for (const auto &item : array)
    if (item.getAsObject()->getString(key) == value)
      return *item.getAsObject();
  throw std::runtime_error("missing export record: " + value.str());
}
std::string key(StringRef owner, std::optional<StringRef> instance = {}) {
  return take(companionIdentity(owner, instance,
                                ObligationRole::OracleAdmissibility, {}, 0));
}
const json::Object &definition(const json::Value &report, StringRef name) {
  return *find(*report.getAsArray(), "name", name)
              .getObject("oracle_definition");
}
} // namespace
int main() {
  Cases cases;
  cases.run("whole predicate has a distinct canonical companion role", [] {
    require(
        key("m::Bounded") ==
            R"(["zkc.companion/0","m::Bounded",["template"],"oracle-admissibility",["ordinal","0"]])",
        "whole-predicate address changed");
    require(key("m::Bounded") !=
                    take(companionIdentity("m::Bounded", {},
                                           ObligationRole::Request, {}, 0)) &&
                key("m::Bounded") != key("m::Bounded", "closed") &&
                key("m::Bounded") !=
                    take(companionIdentity("m::Bounded", {},
                                           ObligationRole::OracleAdmissibility,
                                           "0", 0)),
            "role, label or closed selection collided");
    refuses(
        companionIdentity("", {}, ObligationRole::OracleAdmissibility, {}, 0),
        "source.companion");
    refuses(companionIdentity("m::Bounded", "",
                              ObligationRole::OracleAdmissibility, {}, 0),
            "source.companion");
    refuses(companionIdentity(StringRef("\xff", 1), {},
                              ObligationRole::OracleAdmissibility, {}, 0),
            "source.companion");
    auto limits = Limits{};
    limits.apiInspectionBytes = key("m::Bounded").size();
    require(take(companionIdentity("m::Bounded", {},
                                   ObligationRole::OracleAdmissibility, {}, 0,
                                   limits)) == key("m::Bounded"),
            "exact companion byte ceiling refused");
    --limits.apiInspectionBytes;
    refuses(companionIdentity("m::Bounded", {},
                              ObligationRole::OracleAdmissibility, {}, 0,
                              limits),
            "source.limit");
  });
  cases.run(
      "public inspections retain clauses and bounds under one address", [] {
        auto project = check(bounded);
        auto declarations =
            take(json::parse(take(inspectDeclarations(project))));
        auto api = take(json::parse(take(inspectPublicAPI(project))));
        const auto &plan = definition(declarations, "m::Bounded");
        require(*plan.getObject("admissibility_companions") ==
                    *find(*api.getAsObject()->getArray("declarations"), "name",
                          "m::Bounded")
                         .getObject("oracle_definition")
                         ->getObject("admissibility_companions"),
                "API and declaration inspection disagree");
        const auto &companions = *plan.getObject("admissibility_companions");
        const auto &clauses = *plan.getArray("predicates");
        require(
            companions.getString("template") == key("m::Bounded") &&
                *companions.get("instance") == json::Value(nullptr) &&
                clauses.size() == 2 &&
                clauses[0].getAsObject()->getString("label") == "exact" &&
                clauses[0].getAsObject()->getInteger("ordinal") == 0 &&
                clauses[1].getAsObject()->getInteger("ordinal") == 1 &&
                *clauses[1].getAsObject()->get("label") ==
                    json::Value(nullptr) &&
                plan.getArray("source_bounds")->size() == 1 &&
                plan.getArray("result_shape")->size() == 1 &&
                plan.getArray("admissibility_inputs")->size() == 2,
            "clauses, generated bounds or whole-predicate lookup disappeared");
        for (const auto &clause : clauses)
          require(!clause.getAsObject()->get("companion"),
                  "a clause gained independent proof authority");
      });
  cases.run(
      "body and source edits preserve lookup without asserting evidence", [] {
        auto before =
            take(json::parse(take(inspectDeclarations(check(bounded)))));
        std::string edited = bounded;
        edited.insert(0, "// unrelated source edit\n");
        auto at = edited.find("requires true;");
        require(at != std::string::npos, "missing fixture clause");
        edited.replace(at, std::string("requires true;").size(),
                       "requires false;");
        auto after =
            take(json::parse(take(inspectDeclarations(check(edited)))));
        const auto &a = definition(before, "m::Bounded");
        const auto &b = definition(after, "m::Bounded");
        require(*a.getObject("admissibility_companions") ==
                        *b.getObject("admissibility_companions") &&
                    *a.getArray("predicates") != *b.getArray("predicates") &&
                    !b.get("status"),
                "lookup absorbed source coordinates or implied discharge");
      });
  cases.run("empty and bound-only predicates still have whole addresses", [] {
    std::string boundsOnly = bounded;
    auto begin = boundsOnly.find("  requires exact:");
    auto end = boundsOnly.find("  query(", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "missing fixture clauses");
    boundsOnly.erase(begin, end - begin);
    auto report = take(json::parse(take(
        inspectDeclarations(check(std::string(identitySource) + boundsOnly)))));
    const auto &empty = definition(report, "m::Identity");
    const auto &bounds = definition(report, "m::Bounded");
    require(empty.getArray("predicates")->empty() &&
                empty.getArray("source_bounds")->empty() &&
                empty.getObject("admissibility_companions")
                        ->getString("template") == key("m::Identity") &&
                bounds.getArray("predicates")->empty() &&
                bounds.getArray("source_bounds")->size() == 1 &&
                bounds.getObject("admissibility_companions")
                        ->getString("template") == key("m::Bounded"),
            "whole-predicate lookup depends on an authored clause");
  });
  cases.run(
      "every construction keeps exact actuals without security selection", [] {
        auto project = check(std::string(bounded) + R"(
#[shape(source.rows,bound=64)]
#[shape(out.rows,bound=16)]
protocol Run roles(V,W,P)(source:Oracle<Table<F>>@P->V,
                         a:index@(P,V),b:index@(P,V))
    ->(out:Oracle<Table<F>>@P->V) {
  let first <- Bounded<F,16>(rows=a,source=source);
  let unused <- Bounded<F,16>(source,b);
  let third <- Bounded<F,32>(source,a);
  return(out=first);
}
)");
        auto entry = take(closeNativeRun(project, "m::Run"));
        auto report = instances(entry);
        const auto &all = *report.getAsObject()->getArray("instances");
        const auto &root = find(all, "symbol", entry.root().symbol);
        const auto &obligations = *root.getArray("oracle_obligations");
        unsigned occurrence = 0;
        std::set<std::string> selections;
        for (unsigned i = 0; i < entry.root().body->operations.size(); ++i) {
          const auto &operation = entry.root().body->operations[i];
          const auto *call =
              std::get_if<OracleInstantiation>(&operation.action);
          if (!call)
            continue;
          require(occurrence < obligations.size(),
                  "construction obligation omitted");
          const auto &obligation = *obligations[occurrence++].getAsObject();
          const auto &selected = entry.declarations()[call->callee.index];
          const auto &plan = *find(all, "symbol", selected.symbol)
                                  .getObject("oracle_definition");
          const auto &companions = *obligation.getObject("companions");
          selections.insert(companions.getString("instance")->str());
          require(
              *obligation.get("path") == json::Value(json::Array{i}) &&
                  obligation.getString("definition") == selected.symbol &&
                  obligation.getString("admissibility") ==
                      plan.getString("admissibility_symbol") &&
                  companions == *plan.getObject("admissibility_companions") &&
                  companions.getString("template") == key("m::Bounded") &&
                  companions.getString("instance") ==
                      key("m::Bounded", selected.symbol) &&
                  obligation.getString("status") == "unresolved" &&
                  obligation.getInteger("holder") == 2 &&
                  *obligation.get("receivers") == json::Value(json::Array{0}) &&
                  *obligation.get("results") ==
                      json::Value(json::Array{operation.results.front().index}),
              "definition selection, custody or occurrence identity changed");
          const auto &substitution = *obligation.getArray("substitution");
          require(substitution.size() == call->operands.size(),
                  "actuals omitted");
          for (unsigned input = 0; input < substitution.size(); ++input) {
            const auto &actual = *substitution[input].getAsObject();
            require(
                actual.getInteger("input") == input &&
                    actual.getInteger("value") == call->operands[input].index &&
                    actual.getString("projection") ==
                        (input ? "value" : "data") &&
                    *actual.get("type") ==
                        take(encodeStaticTerm(
                            entry.root()
                                .body->values[call->operands[input].index]
                                .type)),
                "constructor order or typed anchor/capture substitution lost");
          }
        }
        require(occurrence == 3 && obligations.size() == 3 &&
                    selections.size() == 2,
                "repeated or unused constructions were merged");
        require(
            (*obligations[0].getAsObject()->getArray("substitution"))[1] !=
                (*obligations[1].getAsObject()->getArray("substitution"))[1],
            "different actual captures became the same obligation");
        auto bytes = take(inspectSourceInstances(entry));
        take(inspectDeclarations(project));
        require(take(inspectSourceInstances(entry)) == bytes,
                "companion inspection mutated the checked source");
        auto limits = Limits{};
        limits.apiInspectionBytes = bytes.size();
        require(take(inspectSourceInstances(entry, limits)) == bytes,
                "exact export byte ceiling refused");
        --limits.apiInspectionBytes;
        refuses(inspectSourceInstances(entry, limits), "source.limit");
        limits = Limits{};
        for (const auto &decl : entry.declarations())
          if (decl.origin && decl.oracleDefinition) {
            limits.symbolBytes = decl.symbol.size() - 1;
            break;
          }
        refuses(inspectSourceInstances(entry, limits), "source.limit");
      });
  cases.run(
      "equal representations retain distinct nominal specializations", [] {
        auto project = check(R"(
struct Left {pub flag:bool}
struct Right {pub flag:bool}
pub oracle def Tagged<T:Type+Copy+Drop>(source:O,tag:T)->O {
  requires true;
  query(position:index){let answer <- query source at position;return answer;}
}
protocol Run roles(P,V)(source:O@P->V,a:Left@(P,V),b:Right@(P,V))->(out:O@P->V){
  let left <- Tagged<Left>(source,a);
  let right <- Tagged<Right>(source,b);
  return(out=source);
}
)");
        auto entry = take(closeNativeRun(project, "m::Run"));
        auto report = instances(entry);
        std::set<std::string> types, keys;
        for (const auto &item : *report.getAsObject()->getArray("instances")) {
          const auto &instance = *item.getAsObject();
          if (instance.getObject("template")->getString("owner") != "m::Tagged")
            continue;
          const auto &statics = *instance.getArray("statics");
          require(statics.size() == 1, "nominal static argument omitted");
          const auto &term = *(*statics.front().getAsArray())[1].getAsArray();
          require(term[0] == json::Value("nominal") &&
                      term[1] == json::Value("record"),
                  "nominal static argument became a representation");
          types.insert(term[2].getAsString()->str());
          const auto &companions = *instance.getObject("oracle_definition")
                                        ->getObject("admissibility_companions");
          require(companions.getString("template") == key("m::Tagged"),
                  "nominal selection changed the template address");
          keys.insert(companions.getString("instance")->str());
        }
        std::set<std::string> actualTypes;
        const auto &root = find(*report.getAsObject()->getArray("instances"),
                                "symbol", entry.root().symbol);
        for (const auto &value : *root.getArray("oracle_obligations")) {
          const auto &substitution =
              *value.getAsObject()->getArray("substitution");
          require(substitution.size() == 2, "nominal capture omitted");
          const auto &type = *substitution[1].getAsObject()->getArray("type");
          require(type[0] == json::Value("nominal") &&
                      type[1] == json::Value("record"),
                  "actual nominal capture became a representation");
          actualTypes.insert(type[2].getAsString()->str());
        }
        require(types.size() == 2 && types == actualTypes &&
                    types.count("m::Left") && types.count("m::Right") &&
                    keys.size() == 2,
                "nominal specializations shared a closed lookup address");
      });
  cases.run("nested construction paths select their own region SSA values", [] {
    auto project = check(std::string(identitySource) + R"(
protocol Run roles(P,V)(source:O@P->V,n:index@(P,V))->(out:O@P->V){
  for _ in 0..n roles(P,V) max 2 {
    let unused <- Identity(source);
  }
  return(out=source);
}
)");
    auto entry = take(closeNativeRun(project, "m::Run"));
    auto report = instances(entry);
    const auto &obligations =
        *find(*report.getAsObject()->getArray("instances"), "symbol",
              entry.root().symbol)
             .getArray("oracle_obligations");
    require(obligations.size() == 1, "nested construction omitted");
    const auto &obligation = *obligations.front().getAsObject();
    const auto &path = *obligation.getArray("path");
    require(path.size() == 3 && path[1] == json::Value(0),
            "repeat path lost its region selector");
    const auto &repeat = std::get<ProtocolRepeat>(
        entry.root().body->operations[*path[0].getAsInteger()].action);
    const auto &call = std::get<OracleInstantiation>(
        repeat.region->operations[*path[2].getAsInteger()].action);
    require(obligation.getArray("substitution")
                    ->front()
                    .getAsObject()
                    ->getInteger("value") == call.operands.front().index,
            "nested actual was interpreted in the outer SSA space");
    auto limits = Limits{};
    limits.expressionDepth = 1;
    refuses(inspectSourceInstances(entry, limits), "source.limit");
  });
  cases.run("fallible identity limits reach both inspection callers", [] {
    auto project = check(bounded);
    auto limits = Limits{};
    limits.apiInspectionBytes = key("m::Bounded").size() - 1;
    refuses(inspectDeclarations(project, limits), "source.limit");
    refuses(inspectPublicAPI(project, limits), "source.limit");
    limits = Limits{};
    limits.identifierBytes = 1;
    limits.moduleBytes = 1;
    refuses(inspectDeclarations(project, limits), "source.limit");
    refuses(inspectPublicAPI(project, limits), "source.limit");
    limits = Limits{};
    limits.work = 1;
    refuses(inspectDeclarations(project, limits), "source.limit");
    limits = Limits{};
    ++limits.symbolBytes;
    refuses(inspectDeclarations(project, limits), "source.limit");
  });
  return cases.result();
}
