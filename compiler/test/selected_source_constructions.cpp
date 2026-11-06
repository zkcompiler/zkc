#include "../lib/Translation/Language/ConstructionSites.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Language/Project.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
constexpr StringLiteral provider = R"zkc(module m;
domain F=field("bls12-381.fr");
interface History<T:Field>{
  type State:Copy+Drop;
  fn initialize()->State effects(stop,opaque);
  fn observe(t:State,value:T)->State effects(stop,opaque);
  fn draw(t:State)->(State,T) effects(stop,opaque);
}
module Provider:History<F>{
  type State:Copy+Drop=index;
  fn initialize()->State{return State(0);}
  fn observe(t:State,value:F)->State{return t;}
  fn draw(t:State)->(State,F){return(t,1);}
}
)zkc";
constexpr StringLiteral events = R"zkc(
  #[site(commitment)] let message=send P->V(secret);
  #[site(query)] let challenge=random.draw();
  #[site(delivery)] let actual=send V->P(challenge);
  accepted=message==public+challenge;
)zkc";
constexpr StringLiteral handlers = R"zkc(
  on message {commitment,delivery}(t,value){return H::observe(t,value);}
  on query query(t){return H::draw(t);}
)zkc";
constexpr StringLiteral entry = R"zkc(
proof Demo=Selected<F>{prover P;verifier V;public{choice,rounds,public};
  accept ok;construction Derived<F,Provider>;}
)zkc";
std::string changed(StringRef source, StringRef from, StringRef to) {
  auto result = source.str();
  auto at = result.find(from.str());
  require(at != std::string::npos, "source replacement exists");
  result.replace(at, from.size(), to.str());
  return result;
}
std::string direct(StringRef thenBody = events, StringRef elseBody = "",
                   StringRef rules = handlers, bool custom = true) {
  std::string result = provider.str();
  result += R"zkc(
protocol Selected<T:Field> roles(P,V)
  (choice:bool@(P,V),rounds:index@(P,V),public:T@(P,V),secret:T@P,
   spare:Random<T>@V,random:Random<T>@V)->(ok:bool@V){
  let mut accepted@V=true;
  #[site(select)] if choice roles(P,V){
)zkc";
  result += thenBody;
  result += "} else {\n";
  result += elseBody;
  result += "} return accepted; }\n";
  if (custom) {
    result += R"zkc(
construction Derived<T:Field,H:History<T>> for Selected<T>{
  transcript H;replace random;
  on start(t,public){return H::observe(t,public);}
)zkc";
    result += rules;
    result += "}\n";
    result += entry;
  } else
    result += changed(entry, "Derived<F,Provider>",
                      "fiat_shamir(\"merlin3.bls12-381.fr64be/0\",random)");
  return result;
}
std::string otherEvents() {
  auto result = changed(events, "site(commitment)", "site(other_message)");
  result = changed(result, "site(query)", "site(other_query)");
  return changed(result, "site(delivery)", "site(other_delivery)");
}
constexpr StringLiteral otherHandlers = R"zkc(
  on message {other_message,other_delivery}(t,value){return H::observe(t,value);}
  on query other_query(t){return H::draw(t);}
)zkc";
constexpr StringLiteral child = R"zkc(
protocol Leaf<T:Field> roles(B,A)
  (public:T@(B,A),secret:T@A,spare:Random<T>@B,random:Random<T>@B)
  ->(ok:bool@B){
  #[site(message)] let message=send A->B(secret);
  #[site(query)] let challenge=random.draw();
  #[site(delivery)] let actual=send B->A(challenge);
  return message==public+challenge;
}
construction Child<T:Field,H:History<T>> for Leaf<T>{
  transcript H;replace random;
  on start(t,public){return H::observe(t,public);}
  on message {message,delivery}(t,value){return H::observe(t,value);}
  on query query(t){return H::draw(t);}
}
protocol Outer<S:Field> roles(P,V)
  (choice:bool@(P,V),public:S@(P,V),secret:S@P,
   spare:Random<S>@V,random:Random<S>@V)->(ok:bool@V){
  let mut accepted@V=true;
  #[site(select)] if choice roles(P,V){
    #[site(left)] let result=Leaf<S> roles(V,P)(public,secret,spare,random);
    accepted=result;
  } else {}
  return accepted;
}
construction Parent<S:Field,H:History<S>> for Outer<S>{
  transcript H;replace random;
  on start(t){return t;}
  apply Child<S,H> at left;
}
proof Demo=Outer<F>{prover P;verifier V;public{choice,public};
  accept ok;construction Parent<F,Provider>;}
)zkc";
std::string delegated() { return (provider + child).str(); }
std::string nestedDelegated() {
  auto text = changed(delegated(), "protocol Outer<S:Field>", R"zkc(
protocol Middle<T:Field> roles(B,A)
  (public:T@(B,A),secret:T@A,spare:Random<T>@B,random:Random<T>@B)
  ->(ok:bool@B){
  let mut accepted@B=true;
  if public==public roles(B,A){
    #[site(inner_call)] let result=Leaf<T> roles(B,A)(public,secret,spare,random);
    accepted=result;
  } else {}
  return accepted;
}
construction MiddleChild<T:Field,H:History<T>> for Middle<T>{
  transcript H;replace random;
  on start(t){return t;}
  apply Child<T,H> at inner_call;
}
protocol Outer<S:Field>
)zkc");
  text = changed(text, "Leaf<S> roles(V,P)", "Middle<S> roles(V,P)");
  return changed(text, "apply Child<S,H> at left;",
                 "apply MiddleChild<S,H> at left;");
}
Expected<CheckedProject> checked(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", source.str(), "selected-constructions.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
ClosedEntry closed(StringRef source, StringRef name = "m::Demo") {
  auto project = take(checked(source));
  success(checkScopedElaboration(project));
  auto result = take(closeEntry(project, name));
  success(checkScopedSpecialization(result));
  return result;
}
const Declaration &construction(const ClosedEntry &entry) {
  auto selected = entry.entry().proof()->selectedConstruction;
  require(selected.has_value(), "selected construction remains explicit");
  return entry.declarations()[selected->index];
}
const Control &control(const Body &body) {
  for (const auto &op : body.operations)
    if (const auto *selected = std::get_if<Control>(&op.action))
      return *selected;
  throw std::runtime_error("missing checked source control");
}
mlir::OwningOpRef<mlir::ModuleOp> original(const ClosedEntry &entry,
                                           mlir::MLIRContext &context) {
  auto bytes = take(emitOriginal(entry, context));
  auto result = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(result), "actual source original parses");
  take(compareOriginal(entry, *result));
  if (entry.entry().proof()->selectedConstruction) {
    mlir::SymbolTableCollection symbols;
    auto unit = mlir::cast<pir::ProtocolModuleOp>(result->getBody()->front());
    auto record = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
        unit, mlir::StringAttr::get(&context, construction(entry).symbol));
    auto resolved =
        take(zkc::protocol::resolveConstructionPlan(record, symbols));
    require(!resolved.definitions.empty(),
            "actual source construction resolves against native body events");
  }
  return result;
}
ClosedEntry translated(StringRef source, mlir::MLIRContext &context,
                       StringRef name = "m::Demo") {
  auto entry = closed(source, name);
  original(entry, context);
  return entry;
}
pir::ConstructionOp selectedConstruction(const ClosedEntry &entry,
                                         mlir::ModuleOp module) {
  mlir::SymbolTableCollection symbols;
  auto unit = mlir::cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto record = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
      unit,
      mlir::StringAttr::get(module.getContext(), construction(entry).symbol));
  require(bool(record), "selected source construction record exists");
  return record;
}
void replaceRuleSite(pir::ConstructionOp record, StringRef kind,
                     StringRef site) {
  SmallVector<mlir::Attribute> rules;
  bool replaced = false;
  for (auto rule : record.getRules()) {
    auto row = mlir::cast<mlir::DictionaryAttr>(rule);
    mlir::NamedAttrList fields(row);
    if (!replaced &&
        mlir::cast<mlir::StringAttr>(row.get("kind")).getValue() == kind) {
      auto name = mlir::StringAttr::get(record.getContext(), site);
      fields.set("sites", mlir::ArrayAttr::get(record.getContext(), {name}));
      replaced = true;
    }
    rules.push_back(fields.getDictionary(record.getContext()));
  }
  require(replaced, "candidate construction rule exists");
  record->setAttr("rules", mlir::ArrayAttr::get(record.getContext(), rules));
}
void replaceApplicationSite(pir::ConstructionOp record, StringRef site) {
  require(record.getApplications().size() == 1,
          "candidate has exactly one selected child call");
  auto row = mlir::cast<mlir::DictionaryAttr>(record.getApplications()[0]);
  mlir::NamedAttrList fields(row);
  fields.set("site", mlir::StringAttr::get(record.getContext(), site));
  record->setAttr(
      "applications",
      mlir::ArrayAttr::get(record.getContext(),
                           {fields.getDictionary(record.getContext())}));
}
pir::QueryOp query(mlir::Block &body, StringRef label) {
  for (auto actual : body.getOps<pir::QueryOp>())
    if (actual.getSite().ends_with(label))
      return actual;
  throw std::runtime_error("missing actual source query");
}
constexpr StringLiteral codec = R"zkc(
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
interface Codec{
  type Record:Copy+Drop;
  fn initialize(layout:F)->Record effects(stop,opaque);
  fn write(r:Record)->Bytes effects(stop,opaque);
  fn finish(r:Record,proof:Bytes)->() effects(stop,opaque);
}
module Packing:Codec{
  type Record:Copy+Drop=();
  fn initialize(layout:F)->Record{return Record(());}
  fn write(r:Record)->Bytes{return empty();}
  fn finish(r:Record,proof:Bytes)->(){return ();}
}
construction Encoded for Selected<F>{
  base Derived<F,Provider>;format Packing(public);
  on encode commitment(r,value){return(r,empty());}
  on receive commitment(r,proof){return(r,(0,32));}
  on decode commitment(chunk){return 0;}
  on wire commitment(t,chunk){return t;}
}
proof Packed=Selected<F>{prover P;verifier V;public{choice,rounds,public};
  accept ok;construction Encoded;}
)zkc";
std::string siblingMessage(bool inherited) {
  auto text = changed(delegated(), "} else {}", R"zkc(
    } else { #[site(left)] let ignored=send P->V(secret); }
  )zkc");
  text = changed(text, "apply Child<S,H> at left;", R"zkc(
    apply Child<S,H> at left;
    on message left(t,value){return H::observe(t,value);}
  )zkc");
  if (inherited) {
    text = changed(text, "proof Demo=Outer<F>", R"zkc(
      construction Inherited<S:Field,H:History<S>> for Outer<S>{
        base Parent<S,H>;
      }
      proof Demo=Outer<F>
    )zkc");
    text = changed(text, "construction Parent<F,Provider>;",
                   "construction Inherited<F,Provider>;");
  }
  return text;
}
std::string longLabels() {
  std::string body, selectors;
  for (unsigned i = 0; i < 16; ++i) {
    auto label = std::string(116, 'a') + std::to_string(i);
    if (i)
      selectors += ',';
    selectors += label;
    body += "#[site(" + label + ")] let value" + std::to_string(i) +
            "=send P->V(secret);";
  }
  return direct(body, "",
                "on message {" + selectors +
                    "}(t,value){return H::observe(t,value);}");
}
// A small authored DAG expands into many call occurrences. Every managed port
// is forwarded, and the leaf optionally captures the whole map in a repeat.
std::string wideCaptures(unsigned width, bool repeated) {
  std::string text = provider.str();
  std::string ports = "rounds:index@(P,V)", arguments = "rounds";
  for (unsigned i = 0; i < width; ++i) {
    auto port = "r" + std::to_string(i);
    ports += ',' + port + ":Random<F>@V";
    arguments += ',' + port;
  }
  for (unsigned level = 0; level <= 4; ++level) {
    text += "protocol Layer" + std::to_string(level) + " roles(P,V)(" + ports +
            ")->(ok:bool@V){";
    if (level) {
      auto call = "Layer" + std::to_string(level - 1) + " roles(P,V)(" +
                  arguments + ");";
      text += "#[site(left)] let first=" + call;
      text += "#[site(right)] let second=" + call;
    } else {
      if (repeated)
        text += "for _ in 0..rounds roles(P,V) max 2 {";
      for (unsigned i = 0; i < width; ++i)
        text += "#[site(query" + std::to_string(i) + ")] let value" +
                std::to_string(i) + "=r" + std::to_string(i) + ".draw();";
      if (repeated)
        text += '}';
    }
    text += "return true;}";
  }
  // The explicit override makes translation collect the actual occurrences;
  // the other equal-typed service roots remain outside replacement authority.
  text += R"zkc(
    construction Derived for Layer4{
      base fiat_shamir("merlin3.bls12-381.fr64be/0",r0);
      on start(t){return t;}
      on query left.left.left.left.query0(t){return (t,0);}
    }
    proof Demo=Layer4{prover P;verifier V;public{rounds};
      accept ok;construction Derived;}
  )zkc";
  return text;
}
// Only the leaf has formal type parameters. Expanded callers always supply
// concrete index types, so their type complexity is independent of name width.
std::string genericCalls(unsigned nameWidth, unsigned levels) {
  std::string text = provider.str(), parameters, arguments;
  for (unsigned i = 0; i < 12; ++i) {
    if (i) {
      parameters += ',';
      arguments += ',';
    }
    parameters +=
        std::string(nameWidth, 'a') + '_' + std::to_string(i) + ":Type";
    arguments += "index";
  }
  text += "protocol Leaf<" + parameters + R"zkc(> roles(P,V)
    (random:Random<F>@V)->(ok:bool@V){
    #[site(query)] let value=random.draw();
    return true;
  })zkc";
  std::string path;
  for (unsigned level = 0; level < levels; ++level) {
    auto callee =
        level ? "Layer" + std::to_string(level - 1) : "Leaf<" + arguments + '>';
    text += "protocol Layer" + std::to_string(level) + R"zkc( roles(P,V)
      (random:Random<F>@V)->(ok:bool@V){
    )zkc";
    auto call = callee + " roles(P,V)(random);";
    text += "#[site(left)] let first=" + call;
    text += "#[site(right)] let second=" + call;
    text += "return true;}";
    path += "left.";
  }
  auto target = "Layer" + std::to_string(levels - 1);
  text += "construction Derived for " + target + R"zkc({
    base fiat_shamir("merlin3.bls12-381.fr64be/0",random);
    on start(t){return t;}
    on query )zkc" +
          path + R"zkc(query(t){return (t,0);}
  }
  proof Demo=)zkc" +
          target + R"zkc({prover P;verifier V;public{};
    accept ok;construction Derived;}
  )zkc";
  return text;
}
std::string layoutCalls() {
  std::string text = provider.str();
  text += "enum Choice<T:Type>{First(),Second()}";
  std::string payload = "(";
  for (unsigned i = 0; i < 48; ++i)
    payload += i ? ",F" : "F";
  payload += ')';
  std::string ports =
      "choice:Choice<" + payload + ">@(P,V),secret:F@P,random:Random<F>@V";
  text += "protocol Leaf roles(P,V)(" + ports + R"zkc()->(ok:bool@V){
    #[site(select)] let ()=match choice {
      First()=>{#[site(message)] let value=send P->V(secret); ()},
      Second()=>{()}
    };
    return true;
  })zkc";
  for (unsigned level = 0; level < 3; ++level) {
    auto callee = level ? "Layer" + std::to_string(level - 1) : "Leaf";
    text += "protocol Layer" + std::to_string(level) + " roles(P,V)(" + ports +
            ")->(ok:bool@V){";
    auto call = callee + " roles(P,V)(choice,secret,random);";
    text += "#[site(left)] let first=" + call;
    text += "#[site(right)] let second=" + call;
    text += "return true;}";
  }
  text += R"zkc(
    construction Derived for Layer2{
      base fiat_shamir("merlin3.bls12-381.fr64be/0",random);
      on message left.left.left.message(t,value){return t;}
    }
    proof Demo=Layer2{prover P;verifier V;public{choice};
      accept ok;construction Derived;}
  )zkc";
  return text;
}
uint64_t inventoryWork(const ClosedEntry &entry) {
  Limits limits;
  auto remaining = limits.work;
  zkc::language::detail::ConstructionSites sites(entry, limits, remaining,
                                                 construction(entry));
  success(sites.collect());
  return limits.work - remaining;
}
void refusesLimit(Error refusal) {
  require(bool(refusal), "expected source.limit refusal");
  auto message = toString(std::move(refusal));
  require(namesIdentifier(message, "source.limit"),
          "budget control reached an unexpected refusal: " + message);
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("arm-local handlers retain compact captured authority", [&] {
    auto entry = translated(direct(), context);
    const auto &plan = *construction(entry).construction;
    require(plan.services == std::vector<unsigned>{1} && plan.rules.size() == 4,
            "custom rules select the actual second service root");
    const auto &selected = control(*entry.protocol().body);
    require(selected.regions.size() == 2 && selected.services.size() == 1 &&
                selected.services.front().index == 1,
            "arm capture lost the selected root coordinate");
    const auto &arm = *selected.regions.front();
    require(arm.services.size() == 1, "arm service slots were not compacted");
    unsigned queries = 0;
    for (const auto &op : arm.operations)
      if (const auto *query = std::get_if<ServiceQuery>(&op.action)) {
        ++queries;
        require(query->service.index == 0,
                "query is not relative to the captured service inventory");
      }
    require(queries == 1, "selected query was skipped");
    for (const auto &rule : plan.rules)
      if (rule.kind != ConstructionRule::Kind::Start)
        require(rule.payload == entry.protocol().inputs[2].type,
                "handler payload did not retain closed field substitution");
  });
  cases.run("nested arms preserve substitutions and managed aliases", [&] {
    auto body = "let alias=random; #[site(inner)] if choice roles(P,V){" +
                changed(events, "random.draw()", "alias.draw()") + "} else {}";
    auto entry = translated(direct(body), context);
    require(construction(entry).construction->rules.size() == 4,
            "nested selected events were not discovered");
  });
  cases.run(
      "match uses checked nominal arm order rather than source order", [&] {
        auto text = changed(direct(), "module m;",
                            "module m; enum Choice{First(),Second()}");
        text = changed(text, "choice:bool", "choice:Choice");
        text = changed(text, "#[site(select)] if choice roles(P,V){",
                       "#[site(select)] let ()=match choice {Second()=>{");
        text = changed(text, "} else {\n} return accepted; }",
                       "()},First()=>{()}}; return accepted; }");
        auto entry = translated(text, context);
        const auto &selected = control(*entry.protocol().body);
        require(
            selected.kind == Control::Kind::Match &&
                selected.alternatives ==
                    std::vector<std::string>({"First", "Second"}) &&
                construction(entry).construction->rules.size() == 4,
            "authored match arms did not retain checked nominal identities");
        require(llvm::count_if(selected.regions[1]->operations,
                               [](const auto &op) {
                                 return std::holds_alternative<ServiceQuery>(
                                     op.action);
                               }) == 1,
                "selected events moved to the wrong nominal alternative");
      });
  for (bool repeatOutside : {false, true})
    cases.run(repeatOutside ? "repeat captures enclose selected arms"
                            : "selected arms enclose repeat captures",
              [&] {
                auto repeated = "for _ in 0..rounds roles(P,V) max 2 {" +
                                events.str() + "}";
                auto text = direct(repeated);
                if (repeatOutside) {
                  text = changed(direct(), "#[site(select)] if choice",
                                 "for _ in 0..rounds roles(P,V) max 2 { "
                                 "#[site(select)] if choice");
                  text = changed(text, "} return accepted; }",
                                 "}} return accepted; }");
                }
                auto entry = translated(text, context);
                require(construction(entry).construction->rules.size() == 4,
                        "repeat/arm composition lost occurrence coverage");
              });
  cases.run("distinct arm labels cover both continuing arms", [&] {
    auto rules = (handlers + otherHandlers).str();
    auto entry = translated(direct(events, otherEvents(), rules), context);
    require(construction(entry).construction->rules.size() == 7,
            "dormant arm handlers were not retained");
  });
  cases.run("same event labels in distinct arms refuse ambiguity", [] {
    refuses(checked(direct(events, events)), "source.construction");
  });
  cases.run("outer and arm-local labels cannot first-match", [] {
    auto text = changed(direct(), "return accepted; }",
                        "#[site(commitment)] let extra=send P->V(secret); "
                        "return accepted; }");
    refuses(checked(text), "source.construction");
  });
  cases.run("every selected arm requires complete event coverage", [] {
    refuses(checked(direct(events, otherEvents())), "source.construction");
  });
  cases.run("the selected root is not inferred from an equal service type", [] {
    refuses(checked(changed(direct(), "replace random;", "replace spare;")),
            "source.construction");
  });
  cases.run("unselected same-typed queries retain their own authority", [&] {
    auto body = events.str() + "#[site(private_query)] let extra=spare.draw();";
    auto entry = translated(direct(body), context);
    require(construction(entry).construction->rules.size() == 4 &&
                control(*entry.protocol().body).services.size() == 2,
            "unselected query was mistaken for a replaced service root");
  });
  cases.run("equal query labels cannot confer replacement authority", [&] {
    auto entry = translated(
        direct(events, "#[site(query)] let unselected=spare.draw();", handlers),
        context);
    require(construction(entry).construction->rules.size() == 4,
            "an unselected sibling query changed the selected authority");
  });
  cases.run("query selectors also refuse same-authority arm ambiguity", [] {
    auto alternate = changed(otherEvents(), "site(other_query)", "site(query)");
    auto rules = (handlers + otherHandlers).str();
    refuses(checked(direct(events, alternate, rules)), "source.construction");
  });
  for (StringRef selector : {"select.commitment", "select.then.commitment",
                             "select.other_arm.commitment", "absent.commitment",
                             "branch_6_select_arm_4_then_commitment"})
    cases.run("source refuses forged selector " + selector, [&] {
      auto text = changed(direct(), "{commitment,delivery}",
                          "{" + selector.str() + ",delivery}");
      refuses(checked(text), "source.construction");
    });
  cases.run("each arm supplies its own handler payload type", [] {
    auto alternate =
        changed(otherEvents(), "send P->V(secret)", "send P->V(choice)");
    alternate = changed(alternate, "accepted=message==public+challenge;",
                        "accepted=message;");
    auto rules = handlers.str() + R"zkc(
      on message other_message(t,value:T){return t;}
      on message other_delivery(t,value){return t;}
      on query other_query(t){return H::draw(t);}
    )zkc";
    refuses(checked(direct(events, alternate, rules)), "source.construction");
  });
  cases.run("delegated child retains static arguments and reversed roles", [&] {
    auto entry = translated(delegated(), context);
    const auto &plan = *construction(entry).construction;
    require(plan.rules.size() == 1 && plan.applications.size() == 1 &&
                plan.services == std::vector<unsigned>{1},
            "parent flattened or lost its selected child");
    const auto &application = plan.applications.front();
    const auto &child = entry.declarations()[application.construction.index];
    require(child.parameters.empty() && child.construction->rules.size() == 4 &&
                child.construction->services == std::vector<unsigned>{1},
            "child handlers were not independently specialized");
    const auto &selected = control(*entry.protocol().body);
    unsigned calls = 0;
    for (const auto &op : selected.regions.front()->operations)
      if (const auto *call = std::get_if<ProtocolApplication>(&op.action)) {
        ++calls;
        require(call->roles == std::vector<unsigned>({1, 0}),
                "participant mapping was sorted or replaced by the roster");
      }
    require(calls == 1, "missing actual selected child call");
  });
  cases.run(
      "call-local handlers substitute payloads through selected arms", [&] {
        auto text = changed(delegated(), "apply Child<S,H> at left;", R"zkc(
      on message {left.message,left.delivery}(t,value){
        return H::observe(t,value);
      }
      on query left.query(t){return H::draw(t);}
    )zkc");
        auto entry = translated(text, context);
        const auto &plan = *construction(entry).construction;
        require(plan.applications.empty() && plan.rules.size() == 4,
                "parent handlers did not select actual child events");
        for (const auto &rule : plan.rules)
          if (rule.kind != ConstructionRule::Kind::Start)
            require(
                rule.payload == entry.protocol().inputs[1].type,
                "callee payload was not substituted in the caller environment");
      });
  cases.run("a delegated child can contain its own selected control", [&] {
    auto text = changed(delegated(), "->(ok:bool@B){", R"zkc(
      ->(ok:bool@B){
        let mut accepted@B=true;
        #[site(inner)] if public==public roles(B,A){
    )zkc");
    text = changed(text, "return message==public+challenge;",
                   "accepted=message==public+challenge; } else {} "
                   "return accepted;");
    auto entry = translated(text, context);
    const auto &plan = *construction(entry).construction;
    const auto &child =
        entry.declarations()[plan.applications.front().construction.index];
    require(child.construction->rules.size() == 4,
            "selected child control was omitted from source coverage");
  });
  cases.run(
      "distinct calls can delegate identical leaf labels in both arms", [&] {
        auto text =
            changed(delegated(), "} else {}",
                    "} else { #[site(right)] let result=Leaf<S> roles(V,P)"
                    "(public,secret,spare,random); accepted=result; }");
        text = changed(text, "apply Child<S,H> at left;",
                       "apply Child<S,H> at left; "
                       "apply Child<S,H> at right;");
        auto entry = translated(text, context);
        require(construction(entry).construction->applications.size() == 2,
                "existing dotted application syntax lost arm distinction");
      });
  cases.run("identically labelled calls in distinct arms refuse ambiguity", [] {
    auto text = changed(delegated(), "} else {}",
                        "} else { #[site(left)] let result=Leaf<S> roles(V,P)"
                        "(public,secret,spare,random); accepted=result; }");
    refuses(checked(text), "source.construction");
  });
  cases.run("a child cannot hide another captured alias of selected authority",
            [] {
              auto text = changed(delegated(), "(public,secret,spare,random);",
                                  "(public,secret,random,random);");
              refuses(checked(text), "source.construction");
            });
  for (StringRef selector :
       {"select.left", "select.then.left", "select.other_arm.left", "right"})
    cases.run("child refuses wrong-arm selector " + selector, [&] {
      refuses(checked(changed(delegated(), "at left;",
                              "at " + selector.str() + ";")),
              "source.construction");
    });
  cases.run("child coverage does not discharge sibling arm messages", [] {
    auto text = changed(delegated(), "} else {}",
                        "} else { #[site(message)] let ignored="
                        "send P->V(secret); }");
    refuses(checked(text), "source.construction");
  });
  for (bool inherited : {false, true})
    cases.run(inherited ? "inherited sibling message can share a call label"
                        : "authored sibling message can share a call label",
              [&] {
                auto entry = translated(siblingMessage(inherited), context);
                const auto &plan = *construction(entry).construction;
                require(plan.applications.size() == 1 && plan.rules.size() == 2,
                        "sibling event and child retain separate ownership");
                auto module = original(entry, context);
                mlir::SymbolTableCollection symbols;
                take(zkc::protocol::resolveConstructionPlan(
                    selectedConstruction(entry, *module), symbols));
                auto record = take(zkc::protocol::readConstructionPlan(
                    selectedConstruction(entry, *module), symbols));
                require(record.applications.size() == 1,
                        "native child selection remains explicit");
                auto rule = llvm::find_if(record.rules, [](const auto &rule) {
                  return rule.kind == ConstructionRule::Kind::Message;
                });
                require(rule != record.rules.end() && rule->sites.size() == 1 &&
                            rule->sites.front() != record.applications[0].site,
                        "independent sibling message resolved to the child");
              });
  for (bool inherited : {false, true})
    cases.run(inherited ? "inherited child leaf still refuses parent ownership"
                        : "authored child leaf still refuses parent ownership",
              [&] {
                auto text = delegated();
                constexpr StringLiteral leafRules = R"zkc(
                  on message {left.message,left.delivery}(t,value){
                    return H::observe(t,value);
                  }
                  on query left.query(t){return H::draw(t);}
                )zkc";
                if (inherited) {
                  text = changed(text, "apply Child<S,H> at left;", leafRules);
                  // The base is valid on its own. Adding a child in a derived
                  // plan cannot inherit mathematical rules inside that child.
                  take(checked(text));
                  text = changed(text, "proof Demo=Outer<F>", R"zkc(
                    construction Inherited<S:Field,H:History<S>> for Outer<S>{
                      base Parent<S,H>; apply Child<S,H> at left;
                    }
                    proof Demo=Outer<F>
                  )zkc");
                  text = changed(text, "construction Parent<F,Provider>;",
                                 "construction Inherited<F,Provider>;");
                } else
                  text = changed(text, "apply Child<S,H> at left;",
                                 "apply Child<S,H> at left;" + leafRules.str());
                refuses(checked(text), "source.construction");
              });
  cases.run("arm-local codec handlers cover the actual producer message", [&] {
    auto entry = translated(direct() + codec.str(), context, "m::Packed");
    require(construction(entry).construction->rules.size() == 8,
            "codec selectors lost inherited selected event coverage");
  });
  cases.run("record codec cannot omit a dormant arm producer message", [] {
    auto rules = (handlers + otherHandlers).str();
    refuses(checked(direct(events, otherEvents(), rules) + codec.str()),
            "source.construction");
  });

  cases.run("unlabelled selected control retains definition ordinals", [&] {
    auto text = changed(direct("let ignored=public+public;", events),
                        "#[site(select)] ", "");
    auto entry = translated(text, context);
    auto module = original(entry, context);
    pir::BranchOp branch;
    module->walk([&](pir::BranchOp actual) { branch = actual; });
    require(bool(branch) && branch.getSite().starts_with("s"),
            "source branch must use its actual unlabelled ordinal");
    auto actual =
        query(branch->getRegion(1).front(), nativeSiteName("query", 0));
    require(actual.getSite() == nativeSelectedSite(branch.getSite(), "else",
                                                   nativeSiteName("query", 0)),
            "dormant-arm work changed native selected event qualification");
  });
  cases.run("message selectors expand all actual payload lanes", [&] {
    auto body =
        changed(events, "send P->V(secret)", "send P->V((secret,secret))");
    body =
        changed(body, "accepted=message==public+challenge;", "accepted=true;");
    auto rules = changed(handlers, "{commitment,delivery}", "delivery");
    rules += "on message commitment(t,value){return t;}";
    auto entry = translated(direct(body, "", rules), context);
    auto module = original(entry, context);
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(
        selectedConstruction(entry, *module), symbols));
    require(llvm::count_if(plan.rules,
                           [](const auto &rule) {
                             return rule.kind ==
                                        ConstructionRule::Kind::Message &&
                                    rule.sites.size() == 2 &&
                                    rule.payload.size() == 2;
                           }) == 1,
            "logical producer message did not retain both native leaves");
  });
  for (StringRef selection : {"delegated", "nested-call", "nested-rules"})
    cases.run("selected call ancestry resolves " + selection, [&] {
      auto text = nestedDelegated();
      if (selection == "nested-call")
        text = changed(text, "apply MiddleChild<S,H> at left;",
                       "apply Child<S,H> at left.inner_call;");
      else if (selection == "nested-rules")
        text = changed(text, "apply MiddleChild<S,H> at left;", R"zkc(
          on message {left.inner_call.message,left.inner_call.delivery}(t,value){
            return H::observe(t,value);
          }
          on query left.inner_call.query(t){return H::draw(t);}
        )zkc");
      translated(text, context);
    });

  cases.run("long common-prefix labels have a source work boundary", [&] {
    auto text = longLabels();
    auto entry = translated(text, context);
    require(construction(entry).construction->rules.size() == 17,
            "all distinct long-label message rules must resolve");
    auto project = take(checked(text));
    Limits low;
    low.work = project.checkedWork() - 1;
    // Normal checking/emission/comparison/resolution above authenticates the
    // fixture. Parser ambiguity or a missing selector cannot satisfy this.
    refuses(checked(text, low), "source.limit");
    auto work = inventoryWork(entry);
    require(work > 16 * 116, "long paths must debit more than entry counts");
    auto remaining = work - 1;
    Limits inventoryLimits;
    inventoryLimits.work = remaining;
    zkc::language::detail::ConstructionSites sites(
        entry, inventoryLimits, remaining, construction(entry));
    refusesLimit(sites.collect());
  });
  cases.run("dotted occurrence lookup charges every path byte", [&] {
    auto text = nestedDelegated();
    auto outer = std::string(112, 'a') + "_outer";
    auto inner = std::string(112, 'a') + "_inner";
    text = changed(text, "site(left)", "site(" + outer + ")");
    text = changed(text, "site(inner_call)", "site(" + inner + ")");
    text = changed(text, "apply Child<T,H> at inner_call;",
                   "apply Child<T,H> at " + inner + ';');
    text = changed(text, "apply MiddleChild<S,H> at left;",
                   "apply Child<S,H> at " + outer + '.' + inner + ';');
    auto entry = translated(text, context);
    Limits limits;
    auto remaining = limits.work;
    zkc::language::detail::ConstructionSites sites(entry, limits, remaining,
                                                   construction(entry));
    success(sites.collect());
    const auto &selection = construction(entry).construction->applications[0];
    take(sites.application(selection));
    remaining = outer.size() + inner.size() - 1;
    refuses(sites.application(selection), "source.limit");
  });
  cases.run("repeated generic calls retain ordinary concrete substitutions",
            [&] { translated(genericCalls(112, 5), context); });
  cases.run("expanded generic keys charge bytes and comparison depth", [&] {
    uint64_t shallowDifference = 0;
    for (unsigned levels : {2, 5}) {
      auto narrowText = genericCalls(8, levels);
      auto wideText = genericCalls(112, levels);
      auto narrow = take(checked(narrowText));
      auto wide = take(checked(wideText));
      const auto &ledger = wide.workObservation().charged;
      auto narrowWork =
          narrow.workObservation().charged.used(SourceWorkPhase::Signatures);
      auto wideWork = ledger.used(SourceWorkPhase::Signatures);
      // A selected construction is checked while the proof Entry signature
      // is formed. Charge its repeated map keys in that actual phase, not the
      // later no-op constructions() call in EntriesAndClaims. The width cost
      // must exceed one copy or a fixed four comparisons per expanded key.
      auto copyDifference = (uint64_t(1) << levels) * 12 * (112 - 8);
      require(wideWork > narrowWork &&
                  wideWork - narrowWork > 8 * copyDifference,
              "formal byte width lost repeated tree comparison work");
      auto difference = wideWork - narrowWork;
      if (levels == 2) {
        shallowDifference = difference;
        continue;
      }
      require(difference > 4 * shallowDifference,
              "formal key work must scale with expanded occurrences");
      uint64_t throughSignatures = 0;
      for (unsigned phase = 0; phase <= unsigned(SourceWorkPhase::Signatures);
           ++phase)
        throughSignatures += ledger.used(SourceWorkPhase(phase));
      require(throughSignatures > 4 * copyDifference,
              "fixture must reach construction checking before refusal");
      Limits low;
      low.work = throughSignatures - 4 * copyDifference;
      // Equal actual types and call topology still fit with short formal names.
      // The wider fixture exhausts construction work, before retained views
      // and authority hashing can run.
      take(checked(narrowText, low));
      auto captured =
          take(capture({{"m", wideText, "selected-constructions.zkc"}}));
      auto failed = analyze(captured, low);
      refuses(failed.checkedProject(), "source.limit");
      require(
          any_of(
              failed.diagnostics(),
              [](const auto &diagnostic) {
                return diagnostic.code == "source.limit" &&
                       StringRef(diagnostic.message).contains("in signatures");
              }),
          "formal key budget must exhaust during signature-time construction "
          "checking");
    }
  });
  for (bool repeated : {false, true})
    cases.run(repeated ? "expanded repeats charge wide managed captures"
                       : "expanded calls charge wide managed captures",
              [&] {
                auto text = wideCaptures(48, repeated);
                auto entry = closed(text);
                auto module = original(entry, context);
                auto work = inventoryWork(entry);
                require(work > 48 * 30,
                        "expanded capture maps must consume cumulative work");
                auto remaining = work - 1;
                Limits low;
                low.work = remaining;
                zkc::language::detail::ConstructionSites sites(
                    entry, low, remaining, construction(entry));
                refusesLimit(sites.collect());
                refuses(emitOriginal(entry, context, low), "source.limit");
                refuses(compareOriginal(entry, *module, low), "source.limit");
                auto project = take(checked(text));
                low.work = project.checkedWork() - 1;
                refuses(checked(text, low), "source.limit");
              });
  cases.run("match layouts and traversal exhaust the same allowance", [&] {
    auto entry = translated(layoutCalls(), context);
    auto module = original(entry, context);
    const Type *subject = nullptr;
    for (const auto &decl : entry.declarations())
      if (decl.name == "Leaf" && decl.body) {
        const auto &match = control(*decl.body);
        subject = &decl.body->values[match.operands.front().index].type;
        break;
      }
    require(subject, "actual called protocol contains a nominal match");
    Limits limits;
    auto remaining = limits.work;
    zkc::language::detail::ConstructionSites measured(entry, limits, remaining,
                                                      construction(entry));
    take(measured.observer().get(*subject));
    auto layoutWork = limits.work - remaining;
    auto beforeWalk = remaining;
    success(measured.collect());
    auto walkWork = beforeWalk - remaining;
    require(layoutWork > 0 && walkWork > 0,
            "both layout observation and occurrence traversal must be charged");
    // Each operation fits separately. Their sum must exceed one shared budget,
    // even when the nominal layout is already cached before traversal starts.
    Limits low;
    low.work = std::max(layoutWork, walkWork);
    remaining = low.work;
    zkc::language::detail::ConstructionSites combined(entry, low, remaining,
                                                      construction(entry));
    take(combined.observer().get(*subject));
    refusesLimit(combined.collect());
    refuses(emitOriginal(entry, context, low), "source.limit");
    refuses(compareOriginal(entry, *module, low), "source.limit");
  });

  for (StringRef mutation : {"wrong-arm", "wrong-authority", "forged-selector",
                             "unqualified-selector"})
    cases.run(
        "source comparison refuses admitted construction rule " + mutation,
        [&] {
          auto body =
              events.str() + "#[site(private_query)] let extra=spare.draw();";
          auto alternate =
              mutation == "wrong-arm" ? otherEvents() : std::string();
          auto rules = mutation == "wrong-arm"
                           ? (handlers + otherHandlers).str()
                           : handlers.str();
          auto entry = closed(direct(body, alternate, rules));
          auto module = original(entry, context);
          auto record = selectedConstruction(entry, *module);
          pir::BranchOp branch;
          module->walk([&](pir::BranchOp actual) { branch = actual; });
          if (mutation == "wrong-arm") {
            SmallVector<mlir::Attribute> rows(record.getRules().begin(),
                                              record.getRules().end());
            SmallVector<unsigned> indices;
            for (auto [i, row] : enumerate(rows))
              if (mlir::cast<mlir::DictionaryAttr>(row)
                      .getAs<mlir::StringAttr>("kind")
                      .getValue() == "query")
                indices.push_back(i);
            require(indices.size() == 2,
                    "two distinct actual arm query handlers exist");
            auto first = mlir::cast<mlir::DictionaryAttr>(rows[indices[0]]);
            auto second = mlir::cast<mlir::DictionaryAttr>(rows[indices[1]]);
            mlir::NamedAttrList left(first), right(second);
            left.set("sites", second.get("sites"));
            right.set("sites", first.get("sites"));
            rows[indices[0]] = left.getDictionary(&context);
            rows[indices[1]] = right.getDictionary(&context);
            record->setAttr("rules", mlir::ArrayAttr::get(&context, rows));
            // Both selectors still name real, equal-typed, selected-authority
            // events. Only the immutable source determines which handler owns
            // each.
            mlir::SymbolTableCollection symbols;
            take(zkc::protocol::resolveConstructionPlan(record, symbols));
          } else if (mutation == "wrong-authority")
            replaceRuleSite(record, "query",
                            query(branch->getRegion(0).front(),
                                  nativeSiteName("private_query", 0))
                                .getSite());
          else
            replaceRuleSite(record, "query",
                            mutation == "forged-selector"
                                ? "forged_construction_selector"
                                : nativeSiteName("query", 0));
          require(
              mlir::succeeded(zkc::admitStage(*module)),
              "construction rule mutation must pass ordinary native admission");
          refuses(compareOriginal(entry, *module), "source.correspondence");
        });

  for (StringRef mutation :
       {"wrong-arm", "unqualified-selector", "forged-selector"})
    cases.run(
        "source comparison refuses admitted child selector " + mutation, [&] {
          auto entry = closed(delegated());
          auto module = original(entry, context);
          auto record = selectedConstruction(entry, *module);
          pir::BranchOp branch;
          module->walk([&](pir::BranchOp actual) { branch = actual; });
          auto site = mutation == "wrong-arm"
                          ? nativeSelectedSite(branch.getSite(), "else",
                                               nativeSiteName("left", 0))
                      : mutation == "unqualified-selector"
                          ? nativeSiteName("left", 0)
                          : "forged_child_selector";
          replaceApplicationSite(record, site);
          require(
              mlir::succeeded(zkc::admitStage(*module)),
              "child selector mutation must pass ordinary native admission");
          refuses(compareOriginal(entry, *module), "source.correspondence");
        });
  for (StringRef mutation : {"call-authority", "call-site"})
    cases.run("source comparison refuses admitted actual " + mutation, [&] {
      auto entry = closed(delegated());
      auto module = original(entry, context);
      pir::ApplyOp call;
      module->walk([&](pir::ApplyOp actual) { call = actual; });
      require(bool(call) && call.getInputs().size() >= 2,
              "source produces an actual protocol call with managed arguments");
      if (mutation == "call-authority")
        call->setOperand(call->getNumOperands() - 1,
                         call->getOperand(call->getNumOperands() - 2));
      else
        call->setAttr("site",
                      mlir::StringAttr::get(&context, "forged_call_site"));
      require(mlir::succeeded(zkc::admitStage(*module)),
              "actual call mutation must pass ordinary native admission");
      refuses(compareOriginal(entry, *module), "source.correspondence");
    });

  // Native shorthand keeps its separate selected-body comparison controls.
  cases.run("original comparison retains both arm namespaces", [&] {
    auto entry = closed(direct(events, events, {}, false));
    auto module = original(entry, context);
    unsigned queries = 0;
    std::set<std::string> sites;
    module->walk([&](pir::QueryOp actual) {
      ++queries;
      sites.insert(actual.getSite().str());
    });
    require(queries == 2 && sites.size() == 2,
            "same source labels lost distinct checked native arm identities");
  });
  for (StringRef mutation : {"wrong-arm", "wrong-authority", "forged-selector"})
    cases.run("independent original comparison refuses " + mutation, [&] {
      auto body =
          events.str() + "#[site(private_query)] let extra=spare.draw();";
      auto entry = closed(direct(body, body, {}, false));
      auto module = original(entry, context);
      pir::BranchOp selected;
      module->walk([&](pir::BranchOp actual) { selected = actual; });
      require(bool(selected), "missing source-produced selected body");
      auto actual =
          query(selected->getRegion(0).front(), nativeSiteName("query", 0));
      if (mutation == "wrong-authority") {
        auto other = query(selected->getRegion(0).front(),
                           nativeSiteName("private_query", 0));
        actual->setOperand(0, other->getOperand(0));
      } else if (mutation == "wrong-arm") {
        auto other =
            query(selected->getRegion(1).front(), nativeSiteName("query", 0));
        auto site = actual.getSite().str();
        actual->setAttr("site", other.getSiteAttr());
        other->setAttr("site", mlir::StringAttr::get(&context, site));
      } else {
        actual->setAttr(
            "site", mlir::StringAttr::get(&context, "forged_source_selector"));
      }
      require(mlir::succeeded(zkc::admitStage(*module)),
              "mutation must reach the independent original comparator");
      refuses(compareOriginal(entry, *module), "source.correspondence");
    });
  return cases.result();
}
