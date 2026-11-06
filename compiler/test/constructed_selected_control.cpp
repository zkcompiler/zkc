#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
#include <cstdlib>
#include <filesystem>
#include <fstream>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
std::filesystem::path captureDirectory;
unsigned captureOrdinal = 0;
void retainText(const std::filesystem::path &path, StringRef text) {
  std::ofstream output(path, std::ios::binary);
  output.write(text.data(), text.size());
  output.close();
  require(bool(output), "failed to retain export fixture");
}
const json::Array &array(const json::Value &value) {
  auto *result = value.getAsArray();
  require(result != nullptr, "expected JSON array");
  return *result;
}
const json::Array &array(const json::Value &value, size_t size) {
  const auto &result = array(value);
  require(result.size() == size, "wrong closed record arity");
  return result;
}
StringRef string(const json::Value &value) {
  auto result = value.getAsString();
  require(result.has_value(), "expected JSON string");
  return *result;
}
unsigned referenceIndex(const json::Value &value) {
  auto result = value.getAsUINT64();
  require(result.has_value() && *result <= 100000,
          "expected bounded reference");
  return *result;
}
void same(const json::Value &left, const json::Value &right) {
  require(equalNaturalJson(left, right), "unexpected structured value");
}
const json::Value &attribute(const json::Array &row, StringRef name) {
  for (const auto &value : array(row[1])) {
    const auto &pair = array(value, 2);
    if (string(pair[0]) == name)
      return pair[1];
  }
  throw std::runtime_error("missing semantic attribute: " + name.str());
}
StringRef textAttribute(const json::Array &row, StringRef name) {
  const auto &value = array(attribute(row, name), 2);
  require(string(value[0]) == "string", "attribute is not structured text");
  return string(value[1]);
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
std::string replaceText(std::string text, StringRef from, StringRef to) {
  auto at = text.find(from.str());
  require(at != std::string::npos, "fixture replacement is missing");
  text.replace(at, from.size(), to.str());
  return text;
}
struct Subject {
  OwningOpRef<ModuleOp> source;
  std::string bytes;
  NativeProofPolicy policy;
  NativeProofConstruction built;
  std::string authored = {};
  json::Value record(
      ConstructedParticipantRole role = ConstructedParticipantRole::Validator) {
    auto result = take(exportConstructedParticipant(*source, *built.module,
                                                    bytes, policy, {}, role));
    if (!captureDirectory.empty()) {
      auto prefix = captureDirectory /
                    ("participant-" + std::to_string(captureOrdinal++));
      retainText(prefix.string() + ".json", printJson(result));
      retainText(prefix.string() + ".source.txt", bytes);
      std::string candidate;
      raw_string_ostream stream(candidate);
      built.module->print(stream);
      retainText(prefix.string() + ".candidate.mlir", candidate);
      retainText(prefix.string() + ".policy.json",
                 printJson(encodeNativeProofPolicy(policy)));
      if (!authored.empty()) {
        retainText(prefix.string() + ".zkc", authored);
        auto original = protocol::exportStructuredSource(bytes, policy.entry,
                                                         *source->getContext());
        if (original)
          retainText(prefix.string() + ".original.json", original->bytes);
        else {
          // The separate formal-source profile currently excludes some
          // genuine transcript/codec primitives. Preserve its exact refusal
          // alongside the actual native fixture; never fabricate its export.
          auto diagnostic = toString(original.takeError());
          require(namesIdentifier(diagnostic, "structured-source-binding"),
                  "unexpected formal-source fixture refusal: " + diagnostic);
          retainText(prefix.string() + ".original-refusal.txt",
                     diagnostic + "\n");
        }
        auto pair =
            take(exportConstructedPair(*source, *built.module, bytes, policy));
        retainText(prefix.string() + ".pair.json", printJson(pair));
        retainText(prefix.string() + ".descriptor.json",
                   printJson(built.descriptor));
      }
    }
    return result;
  }
};
Subject build(MLIRContext &context, StringRef bytes, NativeProofPolicy policy) {
  auto source = parseSourceString<ModuleOp>(bytes, &context);
  require(bool(source) && succeeded(admitStage(*source)), "source admission");
  policy = take(selectNativeProofDraws(*source, policy));
  auto built = take(constructNativeProof(*source, policy));
  success(checkNativeProof(*source, *built.module, policy));
  return {std::move(source), bytes.str(), std::move(policy), std::move(built)};
}
NativeProofPolicy plainPolicy(std::vector<unsigned> inputs) {
  NativeProofPolicy policy;
  policy.entry = "main";
  policy.producer = "P";
  policy.validator = "V";
  policy.publicInputs = std::move(inputs);
  return policy;
}
constexpr StringLiteral plain = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%x:ui64,%y:ui64,%go:i1):
  %a:2 = "protocol.branch"(%choice,%x,%y,%go) ({
  ^then(%left:ui64,%right:ui64,%enabled:i1):
   THEN
   "protocol.yield"(%left,%right) : (ui64,ui64)->()
  }, { ^else(%left:ui64,%right:ui64,%enabled:i1):
   ELSE
   "protocol.yield"(%right,%left) : (ui64,ui64)->()
  }) {site="choose",roles=["P","V"],output_roles=[["V"],["V"]],alternatives=["then","else"]} : (i1,ui64,ui64,i1)->(ui64,ui64)
  %ok = "data.index_equal"(%a#0,%a#1) : (ui64,ui64)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(i1,ui64,ui64,i1)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
std::string plainText(StringRef thenBody = "", StringRef elseBody = "") {
  return replaceText(replaceText(plain.str(), "THEN", thenBody), "ELSE",
                     elseBody);
}
constexpr StringLiteral variant = R"mlir(
!Choice = !data.variant<#data.identity<["tuple", [["atom", "Selected"], ["atom", "nominal"]]]>, [#data.alternative<"none">, #data.alternative<"some", [ui64,ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:!Choice,%x:ui64,%y:ui64):
  %a:2 = "data.branch"(%choice,%x,%y) ({
  ^none(%left:ui64,%right:ui64):
   "data.yield"(%left,%right) : (ui64,ui64)->()
  }, { ^some(%first:ui64,%second:ui64,%left:ui64,%right:ui64):
   %sum = "data.index_wrapping_add"(%first,%left) : (ui64,ui64)->ui64
   "data.yield"(%sum,%second) : (ui64,ui64)->()
  }) {alternatives=["none","some"]} : (!Choice,ui64,ui64)->(ui64,ui64)
  %ok = "data.index_equal"(%a#0,%a#1) : (ui64,ui64)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!Choice,ui64,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral transcript = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%x:!F,%random:!R,%go:i1,%enabled:i1):
  %ok = "protocol.branch"(%choice,%x,%random,%go,%enabled) ({
  ^then(%secret:!F,%coins:!R,%finish:i1,%guard:i1):
   %first = protocol.exchange %secret {site="commitment",sender="P",receiver="V"} : !F
   protocol.guard %guard {site="guard",owner="V"}
   %challenge = "protocol.query"(%coins) {site="draw",owner="V",method="draw"} : (!R)->!F
   %actual = protocol.exchange %challenge {site="delivery",sender="V",receiver="P"} : !F
   %response = protocol.exchange %actual {site="response",sender="P",receiver="V"} : !F
   %same = "algebra.field_equal"(%response,%challenge) : (!F,!F)->i1
   "protocol.finish_if"(%finish) {site="complete_P",owner="P"} : (i1)->()
   "protocol.finish_if"(%finish,%same) {site="complete_V",owner="V"} : (i1,i1)->()
   "protocol.yield"(%same) : (i1)->()
  }, { ^else(%unused:!F,%unreached:!R,%continuing:i1,%permitted:i1):
   %yes = arith.constant true
   "protocol.yield"(%yes) : (i1)->()
  }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,!F,!R,i1,i1)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(i1,!F,!R,i1,i1)->i1,roles=["P","V"],input_roles=[["P","V"],["P"],["V"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral localQueries = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%count:ui64,%random:!R):
  %yes = arith.constant true
  %ok = "protocol.repeat"(%count,%yes,%choice,%random) ({
  ^loop(%i:ui64,%state:i1,%select:i1,%coins:!R):
   %joined = "protocol.branch"(%select,%coins,%i,%state) ({
   ^then(%rng:!R,%coordinate:ui64,%previous:i1):
    %draw = "protocol.query"(%rng) {site="draw_then",owner="V",method="draw"} : (!R)->!F
    %same = "algebra.field_equal"(%draw,%draw) : (!F,!F)->i1
    "protocol.yield"(%same) : (i1)->()
   }, { ^else(%rng:!R,%coordinate:ui64,%previous:i1):
    %draw = "protocol.query"(%rng) {site="draw_else",owner="V",method="draw"} : (!R)->!F
    %same = "algebra.field_equal"(%draw,%draw) : (!F,!F)->i1
    "protocol.yield"(%same) : (i1)->()
   }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,!R,ui64,i1)->i1
   "protocol.yield"(%joined) : (i1)->()
  }) {site="rounds",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,i1,i1,!R)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(i1,ui64,!R)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral encodedSource = R"zkc(module m;
domain F=field("bls12-381.fr");
interface Transcript {
  type State:Copy+Drop;
  fn initialize()->State effects(stop,opaque);
  fn observe(t:State,v:F)->State effects(stop,opaque);
  fn draw(t:State)->(State,F) effects(stop,opaque);
}
module History:Transcript {
  type State:Copy+Drop=index;
  fn initialize()->State{return State(0);}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return(t,1);}
}
protocol Selected roles(P,V)(choice:bool@(P,V),finish:bool@(P,V),
  public:F@(P,V),secret:F@P,random:Random<F>@V)->(ok:bool@V) completes {
  #[site(commitment)] let first=send P->V(secret);
  #[site(query)] let challenge=random.draw();
  #[site(delivery)] let actual=send V->P(challenge);
  let mut accepted@V=first==public;
  #[site(choose)] if choice roles(P,V) {
    require @V(finish);
    let ()=finish_if @P(finish)();
    let _=finish_if @V(finish)(ok=accepted);
  } else {}
  return accepted;
}
construction Derived for Selected {
  transcript History;replace random;
  on start(t,public){return History::observe(t,public);}
  on message {commitment,delivery}(t,value){return History::observe(t,value);}
  on query query(t){return History::draw(t);}
}
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
interface Codec {
  type Record:Copy+Drop;
  fn initialize(layout:F)->Record effects(stop,opaque);
  fn write(r:Record)->Bytes effects(stop,opaque);
  fn finish(r:Record,proof:Bytes)->() effects(stop,opaque);
}
module Packing:Codec {
  type Record:Copy+Drop=();
  fn initialize(layout:F)->Record{return Record(());}
  fn write(r:Record)->Bytes{return empty();}
  fn finish(r:Record,proof:Bytes)->(){return ();}
}
construction Encoded for Selected {
  base Derived;format Packing(public);
  on encode commitment(r,value){return(r,empty());}
  on receive commitment(r,proof){return(r,(0,32));}
  on decode commitment(chunk){return 0;}
  on wire commitment(t,chunk){return t;}
}
proof Demo=Selected{prover P;verifier V;public{choice,finish,public};
  accept ok;construction Encoded;}
)zkc";
Subject authoredConstruction(MLIRContext &context, StringRef text, bool codec,
                             bool requireTarget = false) {
  auto captured =
      take(language::capture({{"m", text.str(), "selected-export.zkc"}}));
  auto project = take(language::analyze(captured).checkedProject());
  success(language::checkScopedElaboration(project));
  auto closed = take(language::closeEntry(project, "m::Demo"));
  success(language::checkScopedSpecialization(closed));
  auto bytes = take(language::emitOriginal(closed, context));
  auto source = parseSourceString<ModuleOp>(bytes, &context);
  require(bool(source), "authored construction source parses");
  take(language::compareOriginal(closed, *source));
  require(succeeded(admitStage(*source)), "authored source admission");
  auto unit = cast<pir::ProtocolModuleOp>(source->getBody()->front());
  // The selected declaration, rather than declaration order, supplies
  // authority.
  auto selected = closed.entry().proof()->selectedConstruction;
  require(selected.has_value(), "authored construction selection missing");
  SymbolTable table(unit);
  auto declaration = table.lookup<pir::ConstructionOp>(
      closed.declarations()[selected->index].symbol);
  require(bool(declaration), "selected construction not emitted");
  SymbolTableCollection symbols;
  auto plan = take(protocol::readConstructionPlan(declaration, symbols));
  auto resolved = take(protocol::resolveConstructionPlan(declaration, symbols));
  require(!resolved.definitions.empty(),
          "construction needs actual source-owned definitions");
  auto target = table.lookup<pir::MathematicalOp>(plan.target.getValue());
  require(bool(target) && plan.codec.has_value() == codec,
          "actual construction/codec plan missing");
  require(!plan.services.empty(),
          "construction lost its typed service premise");
  for (unsigned input : plan.services) {
    require(input < target.getFunctionType().getNumInputs(),
            "service premise is outside the actual source signature");
    auto service = dyn_cast<pir::ServiceReferenceType>(
        target.getFunctionType().getInput(input));
    require(service && service.getContract() == "random.bls12-381.fr/0",
            "construction does not replace the actual nominal field service");
  }
  NativeProofPolicy policy;
  policy.entry = plan.target.getValue().str();
  policy.construction = plan.symbol.getValue().str();
  policy.suite = plan.suite;
  policy.format =
      codec ? protocol::ProofFormat::RawBytes : protocol::ProofFormat::Native;
  policy.producer = cast<StringAttr>(target.getRoles()[0]).str();
  policy.validator = cast<StringAttr>(target.getRoles()[1]).str();
  policy.services.assign(plan.services.begin(), plan.services.end());
  // Source declarations own public/acceptance selections. These fixtures have
  // whole input selections and one Boolean output, not guessed ABI positions.
  const auto &proof = *closed.entry().proof();
  require(!requireTarget || (proof.target.has_value() &&
                             !closed.protocol().specifications.empty()),
          "fixture requires an actual source-owned target relation");
  for (const auto &input : proof.publicInputs) {
    require(input.path.empty(), "fixture requires a whole public input");
    policy.publicInputs.push_back(input.port);
  }
  require(proof.acceptance.output && proof.acceptance.port == 0 &&
              proof.acceptance.path.empty() &&
              target.getFunctionType().getNumResults() == 1 &&
              target.getFunctionType().getResult(0).isSignlessInteger(1),
          "fixture needs the actual source-owned Boolean acceptance");
  policy = take(selectNativeProofDraws(*source, policy));
  auto built = take(constructNativeProof(*source, policy));
  success(checkNativeProof(*source, *built.module, policy));
  return {std::move(source), std::move(bytes), std::move(policy),
          std::move(built), text.str()};
}
Subject encoded(MLIRContext &context) {
  return authoredConstruction(context, encodedSource, true);
}

// The selector is a real prover message, not a shared/public Entry input.
// The construction and proof declaration own the handlers, service selection,
// public inputs and acceptance. Native tests do not supply their Lean laws.
std::string receivedSelectorText(bool nominal, bool repeatOutside) {
  std::string prefix = R"zkc(module m;
domain F=field("bls12-381.fr");
interface Transcript {
  type State:Copy+Drop;
  fn initialize()->State effects(stop,opaque);
  fn observe(t:State,v:F)->State effects(stop,opaque);
  fn draw(t:State)->(State,F) effects(stop,opaque);
}
module History:Transcript {
  type State:Copy+Drop=index;
  fn initialize()->State{return State(0);}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return(t,1);}
}
fn stopped()->(){stop "reject";}
)zkc";
  if (nominal)
    prefix += "enum Choice{None(),Some(F,F)}\n";
  prefix +=
      "relation SelectedValues(parameter rounds:index,parameter public:F,"
      "witness choice:" +
      std::string(nominal ? "Choice" : "bool") +
      ",witness secret:F){let active=" +
      (nominal
           ? "match choice {None()=>{false},Some(a,b)=>{secret+a==public+b}}"
           : "choice && secret==public") +
      ";return rounds==0 || active;}\n";
  prefix += "protocol Selected roles(P,V)(choice:" +
            std::string(nominal ? "Choice" : "bool") + R"zkc(@P,
    rounds:index@(P,V),public:F@(P,V),secret:F@P,random:Random<F>@V)
    ->(ok:bool@V) spec {
      target values=SelectedValues(in.rounds@V,in.public@V,in.choice@P,in.secret@P) accept out.ok;
    } {
  #[site(selector)] let received=send P->V(choice);
  let selector=@(P=choice,V=received);
  let mut accepted@V=true;
)zkc";
  std::string events = R"zkc(
    #[site(commitment)] let first=send P->V(secret);
    #[site(query)] let challenge=random.draw();
    #[site(delivery)] let actual=send V->P(challenge);
    #[site(response)] let response=send P->V(secret+actual);
    accepted=EXPRESSION;
  )zkc";
  events = replaceText(std::move(events), "EXPRESSION",
                       nominal ? "response+a==public+challenge+b"
                               : "response==public+challenge");
  std::string loop = "#[site(rounds)] for _ in 0..rounds roles(P,V) max 2 {";
  std::string active = repeatOutside ? events : loop + events + "}";
  if (repeatOutside)
    prefix += loop;
  if (nominal)
    // Deliberately write arms in reverse declaration order. Production source
    // construction, rather than the test, must restore None/Some order.
    prefix += "#[site(choose)] let ()=match selector {Some(a,b)=>{" + active +
              "()},None()=>{let _@V=stopped();()}};";
  else
    prefix += "#[site(choose)] if selector roles(P,V){" + active +
              "} else {let _@V=stopped();}";
  if (repeatOutside)
    prefix += '}';
  prefix += R"zkc(
  return accepted;
}
construction Derived for Selected {
  transcript History;replace random;
  on start(t,public){return History::observe(t,public);}
  on message selector(t,value){return t;}
  on message {commitment,delivery,response}(t,value){return History::observe(t,value);}
  on query query(t){return History::draw(t);}
}
proof Demo=Selected{prover P;verifier V;public{rounds,public};
  accept ok;target values;construction Derived;}
)zkc";
  return prefix;
}

// The only path to an enclosing induction here is an explicit capture. Every
// nested arm uses the SECOND alias. An optional inner repeat forwards both
// distinct aliases, then the query's closed frame captures the SECOND formal.
std::string aliasedQueryText(unsigned depth, bool forwardedLoop,
                             bool selectionOutside) {
  auto selection = [&](auto &&self, unsigned level, StringRef selector,
                       StringRef service, StringRef coordinate, StringRef state,
                       StringRef count, StringRef inner) -> std::string {
    auto id = std::to_string(level);
    auto coin = "%coins_" + id, first = "%first_" + id,
         second = "%second_" + id, flag = "%flag_" + id,
         previous = "%state_" + id, rounds = "%count_" + id,
         induction = "%inner_" + id;
    std::string types = "!R,ui64,ui64,i1,i1,ui64";
    std::string formals = coin + ":!R," + first + ":ui64," + second + ":ui64," +
                          flag + ":i1," + previous + ":i1," + rounds + ":ui64";
    std::string inputs = selector.str() + "," + service.str() + "," +
                         coordinate.str() + "," + coordinate.str() + "," +
                         selector.str() + "," + state.str() + "," + count.str();
    if (!inner.empty()) {
      types += ",ui64";
      formals += "," + induction + ":ui64";
      inputs += "," + inner.str();
    }
    std::string body, result;
    if (forwardedLoop && level == 0) {
      // Neither initial carried state nor the count is an induction alias.
      body = "%forwarded = \"protocol.repeat\"(" + rounds + "," + previous +
             "," + first + "," + second + "," + flag + "," + coin + "," +
             rounds + R"mlir() ({
        ^forward(%j:ui64,%held:i1,%savedFirst:ui64,%savedSecond:ui64,
                 %chooseAgain:i1,%rng:!R,%limit:ui64):
      )mlir" +
             self(self, level + 1, "%chooseAgain", "%rng", "%savedSecond",
                  "%held", "%limit", "%j") +
             "\"protocol.yield\"(%selected_1) : (i1)->()\n"
             "}) {site=\"forward\",carried=1:i64,maximum=2:i64,"
             "roles=[\"P\",\"V\"],carried_roles=[[\"V\"]]} : "
             "(ui64,i1,ui64,ui64,i1,!R,ui64)->i1\n";
      result = "%forwarded";
    } else if (level + 1 < depth) {
      body = self(self, level + 1, flag, coin, second, previous, rounds,
                  inner.empty() ? StringRef() : StringRef(induction));
      result = "%selected_" + std::to_string(level + 1);
    } else {
      body = "%draw = \"protocol.query\"(" + coin +
             ") {site=\"draw_deep\",owner=\"V\",method=\"draw\"} : (!R)->!F\n"
             "%equal = \"algebra.field_equal\"(%draw,%draw) : (!F,!F)->i1\n"
             "%index = \"data.index_equal\"(" +
             second + "," + second +
             ") : (ui64,ui64)->i1\n"
             "%answer = arith.andi %equal, %index : i1\n";
      result = "%answer";
    }
    // Distinct formals in each sibling keep the source SSA association
    // explicit.
    std::string dormant;
    for (auto name : {"coins", "first", "second", "flag", "state", "count"}) {
      if (!dormant.empty())
        dormant += ',';
      dormant +=
          "%unused_" + std::string(name) + "_" + id + ":" +
          (StringRef(name) == "coins"                                ? "!R"
           : StringRef(name) == "flag" || StringRef(name) == "state" ? "i1"
                                                                     : "ui64");
    }
    if (!inner.empty())
      dormant += ",%unused_inner_" + id + ":ui64";
    return "%selected_" + id + " = \"protocol.branch\"(" + inputs +
           ") ({ ^active_" + id + "(" + formals + "):\n" + body +
           "\"protocol.yield\"(" + result +
           ") : (i1)->()\n"
           "}, { ^dormant_" +
           id + "(" + dormant +
           "):\n"
           "\"protocol.yield\"(%unused_state_" +
           id +
           ") : (i1)->()\n"
           "}) {site=\"alias_" +
           id +
           "\",roles=[\"P\",\"V\"],output_roles=[[\"V\"]],"
           "alternatives=[\"then\",\"else\"]} : (i1," +
           types + ")->i1\n";
  };
  std::string repeated =
      R"mlir(
    %yes = arith.constant true
    %repeated = "protocol.repeat"(%count,%yes,%choice,%random,%count) ({
    ^loop(%i:ui64,%state:i1,%select:i1,%coins:!R,%n:ui64):
  )mlir" +
      selection(selection, 0, "%select", "%coins", "%i", "%state", "%n", "") +
      R"mlir(
    "protocol.yield"(%selected_0) : (i1)->()
    }) {site="rounds",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,i1,i1,!R,ui64)->i1
  )mlir";
  if (selectionOutside)
    repeated = R"mlir(
      %ok = "protocol.branch"(%inputChoice,%inputCount,%inputChoice,%inputRandom) ({
      ^selected(%count:ui64,%choice:i1,%random:!R):
    )mlir" + repeated +
               R"mlir(
      "protocol.yield"(%repeated) : (i1)->()
      }, { ^unselected(%unused:ui64,%unusedChoice:i1,%unusedRandom:!R):
      %no = arith.constant false
      "protocol.yield"(%no) : (i1)->()
      }) {site="outside",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,ui64,i1,!R)->i1
    )mlir";
  else
    repeated += "%ok = arith.andi %repeated, %repeated : i1\n";
  return R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry()mlir" +
         std::string(selectionOutside
                         ? "%inputChoice:i1,%inputCount:ui64,%inputRandom:!R"
                         : "%choice:i1,%count:ui64,%random:!R") +
         R"mlir():
  )mlir" +
         repeated + R"mlir(
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(i1,ui64,!R)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
}

// This reader only inspects the record's static shape, lexical references,
// sorts and occurrence associations. It does not execute candidate operations.
struct Inspection {
  struct Slot {
    json::Value type;
    std::string coordinate;
    std::string received = {};
  };
  using Environment = std::vector<Slot>;
  unsigned selected = 0, queries = 0, completions = 0, stops = 0;
  std::vector<std::string> receivedSelectorSites;
  SmallVector<std::pair<std::string, std::string>> branches;
  const json::Array &outputs;
  explicit Inspection(const json::Value &record)
      : outputs(array(array(record, 11)[6])) {}
  static void references(const json::Array &refs,
                         const Environment &environment,
                         const json::Array &types) {
    require(refs.size() == types.size(), "terminal arity changed");
    for (auto [index, type] : zip(refs, types)) {
      unsigned slot = referenceIndex(index);
      require(slot < environment.size(), "reference escaped its lexical frame");
      same(environment[slot].type, type);
    }
  }
  Environment body(const json::Array &instructions, Environment environment) {
    for (const auto &value : instructions) {
      const auto &row = array(value);
      StringRef name = string(row[0]);
      require(row.size() == (name == "protocol.service_query" ? 7u : 6u),
              "instruction arity changed");
      const auto &operands = array(row[3]);
      const auto &results = array(row[4]);
      const auto &regions = array(row[5]);
      for (const auto &operand : operands)
        require(referenceIndex(operand) < environment.size(),
                "uncaptured reference");
      if (name == "protocol.loop") {
        require(regions.size() == 1, "loop region count");
        const auto &region = array(regions[0], 3);
        const auto &arguments = array(region[0]);
        require(arguments.size() == operands.size(), "loop ABI changed");
        Environment local = environment;
        for (auto [i, type] : enumerate(arguments)) {
          std::string coordinate =
              !i ? textAttribute(row, "site").str()
              : i > results.size()
                  ? environment[referenceIndex(operands[i])].coordinate
                  : "";
          std::string received =
              i > results.size()
                  ? environment[referenceIndex(operands[i])].received
                  : "";
          local.push_back({type, std::move(coordinate), std::move(received)});
        }
        local = body(array(region[1]), std::move(local));
        references(array(region[2]), local, results);
      } else if (name == "protocol.participant_branch" ||
                 name == "data.branch" || name == "exec.test" ||
                 name == "exec.match") {
        ++selected;
        require(!operands.empty(), "selector is missing");
        if (!environment[referenceIndex(operands[0])].received.empty())
          receivedSelectorSites.push_back(
              environment[referenceIndex(operands[0])].received);
        const auto &selector =
            array(environment[referenceIndex(operands[0])].type);
        bool nominal = string(selector[0]) == "variant";
        if (nominal)
          array(environment[referenceIndex(operands[0])].type, 3);
        else
          same(environment[referenceIndex(operands[0])].type,
               json::Array{"apply", "bool", json::Array{}});
        const json::Array *alternatives =
            nominal ? &array(selector[2]) : nullptr;
        require(regions.size() == (nominal ? alternatives->size() : 2),
                "selection is not exhaustive");
        const json::Array *labels = nullptr;
        if (name != "exec.test") {
          const auto &encodedLabels = array(attribute(row, "alternatives"), 2);
          require(string(encodedLabels[0]) == "array",
                  "alternative attribute kind");
          labels = &array(encodedLabels[1]);
          require(labels->size() == regions.size(),
                  "alternative attribute arity");
        }
        for (auto [i, encoded] : enumerate(regions)) {
          const auto &region = array(encoded, 5);
          StringRef label = nominal ? string(array((*alternatives)[i], 2)[0])
                            : i     ? "else"
                                    : "then";
          require(string(region[3]) == label, "alternative order changed");
          if (labels) {
            const auto &encodedLabel = array((*labels)[i], 2);
            require(string(encodedLabel[0]) == "string" &&
                        string(encodedLabel[1]) == label,
                    "region disagrees with actual alternatives attribute");
          }
          const auto &payloads = array(region[4]);
          if (nominal)
            same(region[4], array((*alternatives)[i], 2)[1]);
          else
            require(payloads.empty(), "Boolean acquired a payload");
          const auto &arguments = array(region[0]);
          require(arguments.size() == payloads.size() + operands.size() - 1,
                  "payload/capture ABI changed");
          Environment local;
          for (const auto &type : payloads)
            local.push_back({type, ""});
          for (const auto &capture :
               ArrayRef<json::Value>(operands.data(), operands.size())
                   .drop_front())
            local.push_back(environment[referenceIndex(capture)]);
          for (auto [slot, type] : zip(local, arguments))
            same(slot.type, type);
          if (name == "protocol.participant_branch")
            branches.emplace_back(textAttribute(row, "site").str(),
                                  label.str());
          local = body(array(region[1]), std::move(local));
          if (name == "protocol.participant_branch")
            branches.pop_back();
          const auto &ending = array(region[2], 2);
          StringRef terminal = string(ending[0]);
          if (terminal == "exec.reject") {
            require(name == "exec.test" || name == "exec.match",
                    "foreign stop terminal");
            require(array(ending[1]).empty() && !array(region[1]).empty(),
                    "stop has fabricated values");
            require(string(array(array(region[1]).back())[0]) == "exec.reject",
                    "stop reason instruction is missing");
          } else {
            require(terminal == (name == "data.branch" ? "data.yield"
                                 : name == "protocol.participant_branch"
                                     ? "protocol.yield"
                                     : "exec.complete"),
                    "normal yield became completion or stop");
            references(array(ending[1]), local, results);
          }
        }
      } else {
        require(regions.empty(), "unknown regions accepted");
      }
      if (name == "protocol.service_query") {
        ++queries;
        const auto &annotation = array(row[6], 2);
        auto origin =
            take(protocol::decodeNativeOriginTemplate(string(annotation[0])));
        auto *event = std::get_if<protocol::NativeQueryOrigin>(&origin.event);
        require(event && event->protocol == "main" &&
                    event->serviceInput == 2 &&
                    event->service == "random.bls12-381.fr/0" &&
                    event->owner == "V" &&
                    event->method == textAttribute(row, "method") &&
                    event->site == textAttribute(row, "site"),
                "local-query fixture lost its actual original authority/event");
        const auto &coordinates = array(annotation[1]);
        unsigned repeat = 0, branch = 0;
        for (const auto &step : origin.path) {
          if (step.kind == protocol::NativeOriginStep::Kind::Repeat) {
            require(repeat < coordinates.size(), "missing repeat coordinate");
            unsigned reference = referenceIndex(coordinates[repeat++]);
            require(reference < environment.size() &&
                        environment[reference].coordinate == step.site,
                    "coordinate belongs to another frame or value");
          } else if (step.kind == protocol::NativeOriginStep::Kind::Branch) {
            require(branch < branches.size() &&
                        branches[branch].first == step.site &&
                        branches[branch].second == step.alternative,
                    "origin belongs to a different declared arm");
            ++branch;
          }
        }
        require(repeat == coordinates.size() && branch == branches.size(),
                "branch added a coordinate or lost an origin frame");
      } else if (name == "protocol.finish_if") {
        ++completions;
        require(!operands.empty(), "completion condition missing");
        same(environment[referenceIndex(operands[0])].type,
             json::Array{"apply", "bool", json::Array{}});
        json::Array returned;
        for (const auto &operand :
             ArrayRef<json::Value>(operands.data(), operands.size())
                 .drop_front())
          returned.push_back(operand);
        references(returned, environment, outputs);
      } else if (name == "exec.reject") {
        ++stops;
        require(operands.empty() && results.empty(), "stop produced a value");
        textAttribute(row, "reason");
        textAttribute(row, "site");
      }
      for (const auto &type : results)
        environment.push_back({type, "",
                               name == "protocol.receive"
                                   ? textAttribute(row, "site").str()
                                   : ""});
    }
    return environment;
  }
  void run(const json::Value &record) {
    const auto &envelope = array(record, 11);
    require(string(envelope[0]) == "zkc.constructed-participant/0",
            "wrong format");
    Environment environment;
    for (const auto &type : array(envelope[5]))
      environment.push_back({type, ""});
    environment = body(array(envelope[7]), std::move(environment));
    references(array(envelope[8]), environment, outputs);
  }
};
const json::Array &findInstruction(const json::Array &instructions,
                                   StringRef name) {
  for (const auto &value : instructions) {
    const auto &row = array(value);
    if (string(row[0]) == name)
      return row;
    for (const auto &region : array(row[5])) {
      try {
        return findInstruction(array(array(region)[1]), name);
      } catch (const std::runtime_error &) {
      }
    }
  }
  throw std::runtime_error("instruction missing: " + name.str());
}
const json::Array &findSite(const json::Array &instructions, StringRef site) {
  for (const auto &value : instructions) {
    const auto &row = array(value);
    for (const auto &attribute : array(row[1])) {
      const auto &pair = array(attribute, 2);
      if (string(pair[0]) == "site" && textAttribute(row, "site") == site)
        return row;
    }
    for (const auto &region : array(row[5])) {
      try {
        return findSite(array(array(region)[1]), site);
      } catch (const std::runtime_error &) {
      }
    }
  }
  throw std::runtime_error("site missing: " + site.str());
}
const json::Array &findCall(const json::Array &instructions, StringRef symbol) {
  for (const auto &value : instructions) {
    const auto &row = array(value);
    if (string(row[0]) == "protocol.local_call" ||
        string(row[0]) == "func.call") {
      const auto &callee = array(attribute(row, "callee"), 2);
      if (string(callee[0]) == "symbol" && array(callee[1]).size() == 1 &&
          string(array(callee[1])[0]) == symbol)
        return row;
    }
    for (const auto &region : array(row[5])) {
      try {
        return findCall(array(array(region)[1]), symbol);
      } catch (const std::runtime_error &) {
      }
    }
  }
  throw std::runtime_error("call missing: " + symbol.str());
}
void rejected(Subject &subject) {
  require(succeeded(verify(*subject.built.module)),
          "mutation is not well typed");
  auto error =
      checkNativeProof(*subject.source, *subject.built.module, subject.policy);
  require(bool(error), "same-typed candidate mutation was accepted");
  require(namesIdentifier(toString(std::move(error)),
                          "native-proof-correspondence"),
          "mutation did not reach the correspondence checker");
  refuses(exportConstructedParticipant(*subject.source, *subject.built.module,
                                       subject.bytes, subject.policy),
          "native-proof-correspondence");
}
} // namespace

int main() {
  if (auto *directory = std::getenv("ZKC_CONSTRUCTED_EXPORT_FIXTURES")) {
    captureDirectory = directory;
    require(!captureDirectory.empty() &&
                !std::filesystem::exists(captureDirectory),
            "export fixture directory must be new");
    require(std::filesystem::create_directories(captureDirectory),
            "failed to create export fixture directory");
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "Boolean selected record preserves captures, arm frames and joins", [&] {
        auto subject = build(context, plainText(), plainPolicy({0, 1, 2, 3}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        require(inspector.selected == 1, "missing actual participant branch");
        const auto &instructions = array(array(record)[7]);
        const auto &branch =
            findInstruction(instructions, "protocol.participant_branch");
        same(branch[3], json::Array{0, 1, 2, 3});
        const auto &arms = array(branch[5], 2);
        same(array(array(arms[0], 5)[2], 2)[1], json::Array{0, 1});
        same(array(array(arms[1], 5)[2], 2)[1], json::Array{1, 0});
        same(findInstruction(instructions, "data.index_equal")[3],
             json::Array{4, 5});
        same(array(record)[8], json::Array{6});
      });
  cases.run(
      "nominal sum retains payload identity and ordered capture suffix", [&] {
        auto subject = build(context, variant, plainPolicy({0, 1, 2}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        const auto &branch =
            findInstruction(array(array(record)[7]), "data.branch");
        const auto &arms = array(branch[5], 2);
        const auto &some = array(arms[1], 5);
        same(findInstruction(array(some[1]), "data.index_wrapping_add")[3],
             json::Array{0, 2});
        same(array(some[2], 2)[1], json::Array{4, 1});
        auto input = subject.source->getOperation();
        pir::MathematicalOp original;
        input->walk([&](pir::MathematicalOp op) { original = op; });
        same(array(array(record)[5])[0],
             take(exportLogicalTypeData(
                 original.getFunctionType().getInput(0))));
      });
  cases.run(
      "nominal Protocol selection keeps the actual participant operation", [&] {
        auto text = replaceText(variant.str(), "\"data.branch\"",
                                "\"protocol.branch\"");
        for (unsigned i = 0; i < 2; ++i)
          text = replaceText(std::move(text), "\"data.yield\"",
                             "\"protocol.yield\"");
        text =
            replaceText(std::move(text), "{alternatives=[\"none\",\"some\"]}",
                        "{site=\"choose\",roles=[\"P\",\"V\"],output_roles=[["
                        "\"V\"],[\"V\"]],alternatives=[\"none\",\"some\"]}");
        auto subject = build(context, text, plainPolicy({0, 1, 2}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        const auto &branch = findInstruction(array(array(record)[7]),
                                             "protocol.participant_branch");
        require(array(array(branch[5], 2)[1], 5).size() == 5,
                "nominal participant arm was not exported");
      });
  cases.run("aliased Copy captures retain distinct arm positions", [&] {
    auto text =
        replaceText(plainText(), "\"protocol.branch\"(%choice,%x,%y,%go)",
                    "\"protocol.branch\"(%choice,%x,%x,%go)");
    auto subject = build(context, text, plainPolicy({0, 1, 2, 3}));
    auto record = subject.record();
    Inspection(record).run(record);
    const auto &branch =
        findInstruction(array(array(record)[7]), "protocol.participant_branch");
    same(branch[3], json::Array{0, 1, 1, 3});
    same(array(array(array(branch[5])[0])[2], 2)[1], json::Array{0, 1});
  });
  cases.run("sequential selected joins retain separate lexical frames", [&] {
    auto text = replaceText(plainText(),
                            "%ok = \"data.index_equal\"(%a#0,%a#1)", R"mlir(
      %b:2 = "data.branch"(%choice,%a#0,%a#1) ({
      ^then(%left:ui64,%right:ui64): "data.yield"(%left,%right) : (ui64,ui64)->()
      }, { ^else(%left:ui64,%right:ui64): "data.yield"(%right,%left) : (ui64,ui64)->()
      }) {alternatives=["then","else"]} : (i1,ui64,ui64)->(ui64,ui64)
      %ok = "data.index_equal"(%b#0,%b#1))mlir");
    auto subject = build(context, text, plainPolicy({0, 1, 2, 3}));
    auto record = subject.record();
    Inspection inspector(record);
    inspector.run(record);
    require(inspector.selected == 2, "sequential branch missing");
    const auto &instructions = array(array(record)[7]);
    same(findInstruction(instructions, "data.branch")[3], json::Array{0, 4, 5});
    same(findInstruction(instructions, "data.index_equal")[3],
         json::Array{6, 7});
    same(array(record)[8], json::Array{8});
  });
  cases.run("straight-line empty-suite encoding is unchanged", [&] {
    auto subject = build(context, R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%ok:i1): "protocol.return"(%ok) : (i1)->()
      }) {sym_name="main",function_type=(i1)->i1,roles=["P","V"],input_roles=[["P","V"]],output_roles=[["V"]]} : ()->()
      }) {profile=#protocol.profile<protocol>} : ()->() })mlir",
                         plainPolicy({0}));
    auto record = subject.record();
    require(array(array(record)[7]).empty(),
            "straight-line instructions changed");
    same(array(record)[8], json::Array{0});
    Inspection(record).run(record);
  });
  cases.run(
      "legacy loop triple and absolute reference numbering are unchanged", [&] {
        auto subject = build(context, R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%count:ui64,%x:ui64):
        %sum = "protocol.repeat"(%count,%x) ({
        ^loop(%i:ui64,%carried:ui64):
          %next = "data.index_wrapping_add"(%carried,%i) : (ui64,ui64)->ui64
          "protocol.yield"(%next) : (ui64)->()
        }) {site="rounds",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,ui64)->ui64
        %ok = "data.index_equal"(%sum,%x) : (ui64,ui64)->i1
        "protocol.return"(%ok) : (i1)->()
      }) {sym_name="main",function_type=(ui64,ui64)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
      }) {profile=#protocol.profile<protocol>} : ()->() })mlir",
                             plainPolicy({0, 1}));
        auto record = subject.record();
        Inspection(record).run(record);
        const auto &instructions = array(array(record)[7]);
        const auto &loop = findInstruction(instructions, "protocol.loop");
        same(loop[3], json::Array{0, 1});
        const auto &region = array(array(loop[5], 1)[0], 3);
        same(findInstruction(array(region[1]), "data.index_wrapping_add")[3],
             json::Array{3, 2});
        same(region[2], json::Array{4});
        same(findInstruction(instructions, "data.index_equal")[3],
             json::Array{2, 1});
        same(array(record)[8], json::Array{3});
      });
  cases.run(
      "selected stopping original helper retains its checked call identity",
      [&] {
        auto text = plainText(R"mlir(
      "protocol.local_call"() {callee=@stopped,site="selected_stop",role="V"} : ()->()
    )mlir");
        text = replaceText(std::move(text), "\"protocol.func\"()", R"mlir(
      func.func private @stopped(%scope:!runtime.scope)->!exec.outcome<> attributes {no_inline,runtime.origin=["stopped",[]]} {
        %stop = "exec.reject"(%scope) {site="stop",reason="reject"} : (!runtime.scope)->!exec.stop
        cf.br ^failed(%stop : !exec.stop)
      ^failed(%cause:!exec.stop):
        %outcome = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<>
        func.return %outcome : !exec.outcome<>
      }
      "protocol.func"())mlir");
        auto subject = build(context, text, plainPolicy({0, 1, 2, 3}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        const auto &branch = findInstruction(array(array(record)[7]),
                                             "protocol.participant_branch");
        const auto &arms = array(branch[5], 2);
        const auto &call =
            findInstruction(array(array(arms[0])[1]), "protocol.local_call");
        same(attribute(call, "callee"),
             json::Array{"symbol", json::Array{"stopped"}});
        require(array(call[3]).empty() && array(call[4]).empty(),
                "stopping helper fabricated successful values");
        require(array(array(arms[1])[1]).empty(),
                "stopping call moved to dormant arm");
        // The static yield is retained; a stopped call never reaches it.
        // Mutating the actual source helper body with the same ABI must still
        // fail checking.
        subject.built.module->walk([&](exec::RejectOp op) {
          op->setAttr("reason", StringAttr::get(&context, "abort"));
        });
        rejected(subject);
      });
  for (auto role : {ConstructedParticipantRole::Producer,
                    ConstructedParticipantRole::Validator})
    cases.run(
        role == ConstructedParticipantRole::Producer
            ? "producer selected completion ABI"
            : "validator selected completion ABI",
        [&] {
          auto policy = plainPolicy({0, 3, 4});
          policy.suite = "merlin3.bls12-381.fr64be/0";
          policy.services = {2};
          auto subject = build(context, transcript, policy);
          auto record = subject.record(role);
          Inspection inspector(record);
          inspector.run(record);
          require(inspector.completions == 1, "conditional completion lost");
          const auto &row =
              findInstruction(array(array(record)[7]), "protocol.finish_if");
          require(array(row[4]).size() == 1, "affine continuation was dropped");
          const auto &branch = findInstruction(array(array(record)[7]),
                                               "protocol.participant_branch");
          const auto &active = array(array(branch[5])[0], 5);
          const auto &ending = array(active[2], 2);
          require(referenceIndex(array(ending[1]).back()) >=
                      array(active[0]).size(),
                  "normal yield used stale incoming state");
          pir::FinishIfOp completion;
          subject.built.module->walk([&](pir::ParticipantOp participant) {
            if (participant.getRole() ==
                (role == ConstructedParticipantRole::Producer ? "P" : "V"))
              participant.walk([&](pir::FinishIfOp op) { completion = op; });
          });
          require(bool(completion), "actual completion missing");
          same(row[4],
               take(exportLogicalTypesData(completion.getResultTypes())));
          auto pair =
              take(exportConstructedPair(*subject.source, *subject.built.module,
                                         subject.bytes, subject.policy));
          const auto &children = array(pair, 3);
          same(array(children[1], 11)[1], array(children[2], 11)[1]);
          same(array(children[1])[2], array(children[2])[2]);
          same(array(children[1])[3], array(children[2])[3]);
          same(record,
               children[role == ConstructedParticipantRole::Producer ? 1 : 2]);
        });
  cases.run(
      "all-arm local queries retain origins and rebased repeat coordinates",
      [&] {
        auto subject = build(context, localQueries, plainPolicy({0, 1}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        require(inspector.selected == 1 && inspector.queries == 2,
                "dormant query arm was omitted");
        const auto &loop =
            findInstruction(array(array(record)[7]), "protocol.loop");
        const auto &body = array(array(loop[5], 1)[0], 3);
        const auto &branch =
            findInstruction(array(body[1]), "protocol.participant_branch");
        for (const auto &arm : array(branch[5], 2)) {
          const auto &query = findInstruction(array(array(arm, 5)[1]),
                                              "protocol.service_query");
          // Service formals are removed by projection; the actual index capture
          // is local slot zero, rather than the original service-plus-index
          // slot one.
          same(array(query[6], 2)[1], json::Array{0});
        }
      });
  cases.run(
      "selected loop arm and dormant query have different coordinate arities",
      [&] {
        auto subject = build(context, R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%count:ui64,%random:!R):
  %ok = "protocol.branch"(%choice,%count,%random) ({
  ^then(%n:ui64,%rng:!R):
   %yes = arith.constant true
   %result = "protocol.repeat"(%n,%yes,%rng) ({
   ^loop(%i:ui64,%state:i1,%coins:!R):
    %draw = "protocol.query"(%coins) {site="draw_then",owner="V",method="draw"} : (!R)->!F
    %same = "algebra.field_equal"(%draw,%draw) : (!F,!F)->i1
    "protocol.yield"(%same) : (i1)->()
   }) {site="rounds",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,i1,!R)->i1
   "protocol.yield"(%result) : (i1)->()
  }, { ^else(%n:ui64,%rng:!R):
   %draw = "protocol.query"(%rng) {site="draw_else",owner="V",method="draw"} : (!R)->!F
   %same = "algebra.field_equal"(%draw,%draw) : (!F,!F)->i1
   "protocol.yield"(%same) : (i1)->()
  }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,ui64,!R)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(i1,ui64,!R)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir",
                             plainPolicy({0, 1}));
        auto record = subject.record();
        Inspection inspector(record);
        inspector.run(record);
        require(inspector.queries == 2, "dormant query lost");
        const auto &branch = findInstruction(array(array(record)[7]),
                                             "protocol.participant_branch");
        const auto &arms = array(branch[5], 2);
        const auto &activeQuery =
            findInstruction(array(array(arms[0])[1]), "protocol.service_query");
        const auto &dormantQuery =
            findInstruction(array(array(arms[1])[1]), "protocol.service_query");
        same(array(activeQuery[6], 2)[1], json::Array{2});
        require(array(array(dormantQuery[6], 2)[1]).empty(),
                "branch introduced induction");
      });
  for (bool selectionOutside : {false, true})
    for (bool forwarded : {false, true})
      for (unsigned depth : {2u, 5u, 12u})
        cases.run(
            std::string(selectionOutside ? "selection around repeat: "
                                         : "repeat around selection: ") +
                (forwarded ? "loop-forwarded second alias at depth "
                           : "second capture alias at depth ") +
                std::to_string(depth),
            [&] {
              auto subject = build(
                  context, aliasedQueryText(depth, forwarded, selectionOutside),
                  plainPolicy({0, 1}));
              auto record = subject.record();
              Inspection inspector(record);
              inspector.run(record);
              require(inspector.queries == 1 &&
                          inspector.selected == depth + selectionOutside,
                      "nested query or closed selected frame was omitted");
              const auto &instructions = array(array(record)[7]);
              const auto &first = findSite(instructions, "alias_0");
              const auto &captures = array(first[3]);
              same(captures[1], captures[2]);
              // Each nested selection uses the second alias (local slot one),
              // rather than the exporter's canonical first coordinate slot.
              for (unsigned level = forwarded ? 2 : 1; level < depth; ++level) {
                const auto &nested =
                    findSite(instructions, "alias_" + std::to_string(level));
                same(array(nested[3])[1], json::Value(1));
                same(array(nested[3])[2], json::Value(1));
              }
              const auto &query = findSite(instructions, "draw_deep");
              same(array(query[6], 2)[1],
                   forwarded ? json::Array{0, 5} : json::Array{0});
              if (forwarded) {
                const auto &loop = findSite(instructions, "forward");
                // Distinct SSA aliases survive the loop's capture slicing.
                // The nested branch uses the SECOND invariant formal, whose
                // actual operand is the selected arm's SECOND alias.
                same(loop[3], json::Array{4, 3, 0, 1, 2, 4});
                const auto &nested = findSite(instructions, "alias_1");
                same(nested[3], json::Array{9, 8, 8, 9, 6, 10, 5});
              }
            });
  cases.run("equal-sort captures cannot replace a real induction lineage", [&] {
    auto text = aliasedQueryText(3, false, false);
    text = replaceText(std::move(text),
                       "\"protocol.branch\"(%select,%coins,%i,%i,",
                       "\"protocol.branch\"(%select,%coins,%n,%n,");
    auto subject = build(context, text, plainPolicy({0, 1}));
    refuses(exportConstructedParticipant(*subject.source, *subject.built.module,
                                         subject.bytes, subject.policy),
            "constructed-participant-service-origin");
  });
  cases.run("a carried seed is not an invariant induction forwarding", [&] {
    auto text = aliasedQueryText(3, true, false);
    text = replaceText(std::move(text), "%forwarded =", "%forwarded:2 =");
    text = replaceText(std::move(text),
                       "%held:i1,%savedFirst:ui64,%savedSecond:ui64,",
                       "%held:i1,%savedSecond:ui64,%savedFirst:ui64,");
    text = replaceText(std::move(text),
                       "\"protocol.yield\"(%selected_1) : (i1)->()",
                       "%next = \"data.index_wrapping_add\"(%savedSecond,%j) : "
                       "(ui64,ui64)->ui64\n"
                       "\"protocol.yield\"(%selected_1,%next) : (i1,ui64)->()");
    text = replaceText(std::move(text), "site=\"forward\",carried=1:i64",
                       "site=\"forward\",carried=2:i64");
    text = replaceText(
        std::move(text),
        "carried_roles=[[\"V\"]]} : (ui64,i1,ui64,ui64,i1,!R,ui64)->i1",
        "carried_roles=[[\"V\"],[\"V\"]]} : "
        "(ui64,i1,ui64,ui64,i1,!R,ui64)->(i1,ui64)");
    text = replaceText(std::move(text),
                       "\"protocol.yield\"(%forwarded) : (i1)->()",
                       "\"protocol.yield\"(%forwarded#0) : (i1)->()");
    auto subject = build(context, text, plainPolicy({0, 1}));
    refuses(exportConstructedParticipant(*subject.source, *subject.built.module,
                                         subject.bytes, subject.policy),
            "constructed-participant-service-origin");
  });
  for (bool nominal : {false, true})
    for (bool repeatOutside : {false, true})
      cases.run(
          std::string(nominal ? "received nominal selector: "
                              : "received Boolean selector: ") +
              (repeatOutside ? "selection inside repeat"
                             : "repeat inside selection"),
          [&] {
            auto subject = authoredConstruction(
                context, receivedSelectorText(nominal, repeatOutside), false,
                true);
            auto record = subject.record();
            Inspection inspector(record);
            inspector.run(record);
            // The source emitter owns occurrence spelling. Identify the
            // unique entry-level exchange of the private choice, then
            // compare the exported selector's exact receive lineage.
            auto unit =
                cast<pir::ProtocolModuleOp>(subject.source->getBody()->front());
            auto original = cast<pir::MathematicalOp>(
                SymbolTable::lookupSymbolIn(unit, subject.policy.entry));
            pir::ExchangeOp selectorMessage;
            for (auto message :
                 original.getBody().front().getOps<pir::ExchangeOp>()) {
              require(!selectorMessage,
                      "source selector message must be unique");
              selectorMessage = message;
            }
            require(
                selectorMessage &&
                    selectorMessage.getInput() ==
                        original.getBody().front().getArgument(0) &&
                    selectorMessage.getSender() == subject.policy.producer &&
                    selectorMessage.getReceiver() == subject.policy.validator,
                "selector receive lost its actual source message");
            auto selectorSite = selectorMessage.getSite();
            require(inspector.receivedSelectorSites ==
                        std::vector<std::string>{selectorSite.str()},
                    "selection does not use the actual selector receive");
            const auto &instructions = array(array(record)[7]);
            const auto &receive = findSite(instructions, selectorSite);
            require(string(receive[0]) == "protocol.receive" &&
                        textAttribute(receive, "peer") ==
                            subject.policy.producer,
                    "selector message is not received from the prover");
            same(array(receive[4], 1)[0],
                 take(exportLogicalTypeData(
                     selectorMessage.getInput().getType())));
            const auto &branch =
                findInstruction(instructions, "protocol.participant_branch");
            const auto &arms = array(branch[5], 2);
            const auto &active = array(arms[nominal ? 1 : 0], 5);
            const auto &stopped = array(arms[nominal ? 0 : 1], 5);
            require(array(active[4]).size() == (nominal ? 2u : 0u),
                    "ordered nominal payload signature was lost");
            if (nominal) {
              auto sourceType = take(
                  exportLogicalTypeData(selectorMessage.getInput().getType()));
              const auto &alternatives = array(array(sourceType, 3)[2], 2);
              require(
                  string(stopped[3]) == string(array(alternatives[0], 2)[0]) &&
                      string(active[3]) == string(array(alternatives[1], 2)[0]),
                  "received nominal alternatives lost source order");
              auto field = take(exportLogicalTypeData(
                  algebra::FieldType::get(&context, "bls12-381.fr")));
              same(array(active[4])[0], field);
              same(array(active[4])[1], field);
              // The first two local slots are actual payloads. Captures
              // follow them even when they have exactly the same type.
              const auto &types = array(active[0]);
              require(types.size() > 2,
                      "nominal fixture has no explicit ordered captures");
              same(types[0], field);
              same(types[1], field);
            }
            auto pair = take(
                exportConstructedPair(*subject.source, *subject.built.module,
                                      subject.bytes, subject.policy));
            same(array(pair, 3)[2], record);
            same(array(array(pair)[1], 11)[1], array(record)[1]);
            same(array(array(pair)[1])[3], array(record)[3]);

            // This is an actual source helper with the real reject
            // reason, retained as a call in the rejected selected arm.
            // Its static normal yield/suffix remain published.
            std::string stoppedSymbol;
            subject.source->walk([&](exec::RejectOp reject) {
              require(reject.getReason() == "reject",
                      "source stop reason changed");
              auto function = reject->getParentOfType<func::FuncOp>();
              require(function && stoppedSymbol.empty(),
                      "fixture must have one actual rejecting helper");
              stoppedSymbol = function.getSymName().str();
            });
            require(!stoppedSymbol.empty(),
                    "rejected selected arm has no source-owned stop");
            const auto &call = findCall(array(stopped[1]), stoppedSymbol);
            require(array(call[3]).empty() && array(call[4]).empty(),
                    "stopping source helper invented successful values");
            require(string(array(stopped[2], 2)[0]) == "protocol.yield",
                    "dead static arm yield became a fabricated stop tag");
            const auto &loop = findInstruction(instructions, "protocol.loop");
            if (repeatOutside)
              findInstruction(array(array(array(loop[5], 1)[0], 3)[1]),
                              "protocol.participant_branch");
            else
              findInstruction(array(active[1]), "protocol.loop");
            // These are native source/candidate fixtures. The source's
            // acceptance and typed draw premise need independent Lean
            // source connections and service laws before formal use.
          });
  for (auto role : {ConstructedParticipantRole::Producer,
                    ConstructedParticipantRole::Validator})
    cases.run(
        role == ConstructedParticipantRole::Producer
            ? "actual conditional write helper"
            : "actual conditional finish helper",
        [&] {
          auto subject = encoded(context);
          auto record = subject.record(role);
          Inspection inspector(record);
          inspector.run(record);
          require(inspector.selected >= 2 && inspector.completions == 1,
                  "generated helper control or participant completion missing");
          const auto &selected =
              findInstruction(array(array(record)[7]), "exec.test");
          const auto &arms = array(selected[5], 2);
          for (const auto &arm : arms)
            require(string(array(array(arm, 5)[2], 2)[0]) == "exec.complete",
                    "codec helper yield became participant completion");
          // The reached original codec handler remains a borrowed source call.
          const auto &call =
              findInstruction(array(array(arms[0])[1]), "func.call");
          const auto &symbol = array(attribute(call, "callee"), 2);
          require(string(symbol[0]) == "symbol" && array(symbol[1]).size() == 1,
                  "original helper identity lost");
          if (role == ConstructedParticipantRole::Producer)
            findInstruction(array(array(arms[1])[1]), "exec.apply");
          else
            require(array(array(arms[1])[1]).empty(),
                    "false finish arm acquired effects");
        });
  for (bool rejecting : {false, true})
    cases.run(
        rejecting
            ? "source-emitted rejecting match keeps the original call boundary"
            : "source-emitted codec match keeps the original call boundary",
        [&] {
          auto text =
              replaceText(encodedSource.str(), "module Packing:Codec {",
                          "enum PackingChoice{Empty(),Payload(index,index)}\n"
                          "module Packing:Codec {");
          text = replaceText(
              std::move(text), "fn write(r:Record)->Bytes{return empty();}",
              std::string("fn write(r:Record)->Bytes{"
                          "let choice=PackingChoice::Payload(0,1);"
                          "return match choice {"
                          "Payload(first,second)=>{empty()},Empty()=>{") +
                  (rejecting ? "stop \"abort\";" : "empty()") + "}};}");
          auto subject = authoredConstruction(context, text, true);
          exec::MatchOp actual;
          subject.source->walk([&](exec::MatchOp match) {
            require(!actual, "fixture must have one actual source match");
            actual = match;
          });
          require(bool(actual),
                  "production source emission did not produce exec.match");
          auto type = cast<data::VariantType>(actual.getInput().getType());
          require(type.getAlternatives().size() == 2 &&
                      type.getAlternatives()[1].getPayload().size() == 2,
                  "source match lost its nominal payload signature");
          auto function = actual->getParentOfType<func::FuncOp>();
          require(bool(function), "source match has no actual helper");
          unsigned rejections = 0;
          subject.source->walk([&](exec::RejectOp reject) {
            ++rejections;
            require(reject.getReason() == "abort" &&
                        reject->getParentOfType<func::FuncOp>()->hasAttr(
                            "runtime.region"),
                    "rejection must be in the actual source-outlined arm");
          });
          require(rejections == unsigned(rejecting),
                  "source match rejection was fabricated or omitted");
          auto record = subject.record(ConstructedParticipantRole::Producer);
          Inspection(record).run(record);
          const auto &instructions = array(array(record)[7]);
          const auto &call = findCall(instructions, function.getSymName());
          require(string(call[0]) == "func.call",
                  "original codec match was not retained as a source call");
          const auto &conditional = findInstruction(instructions, "exec.test");
          for (const auto &arm : array(conditional[5], 2))
            require(string(array(array(arm)[2], 2)[0]) == "exec.complete",
                    "source handler stop became a generated-arm terminal");
          // This guards the real production boundary. Native codec
          // construction creates only exec.test wrappers with complete
          // terminals. It does not synthesize an exec.match or rejecting
          // region; the source's match/reject remain original helpers.
        });
  for (StringRef mutation :
       {"selector", "capture order", "dormant yield", "sibling payload"})
    cases.run("well-typed candidate association rejects " + mutation, [&] {
      bool payload = mutation == "sibling payload";
      auto subject =
          build(context, payload ? variant.str() : plainText(),
                plainPolicy(payload ? std::vector<unsigned>{0, 1, 2}
                                    : std::vector<unsigned>{0, 1, 2, 3}));
      Operation *branch = nullptr;
      subject.built.module->walk([&](pir::ParticipantOp participant) {
        if (participant.getRole() == "V")
          participant.walk([&](Operation *op) {
            if (isa<pir::ParticipantBranchOp, data::BranchOp>(op))
              branch = op;
          });
      });
      require(branch != nullptr, "candidate branch missing");
      if (mutation == "selector")
        branch->setOperand(0, branch->getOperand(3));
      else if (mutation == "capture order") {
        Value first = branch->getOperand(1);
        branch->setOperand(1, branch->getOperand(2));
        branch->setOperand(2, first);
      } else if (mutation == "dormant yield") {
        auto &arm = branch->getRegion(1).front();
        arm.back().setOperand(0, arm.getArgument(0));
      } else {
        auto &arm = branch->getRegion(1).front();
        arm.front().setOperand(0, arm.getArgument(1));
      }
      rejected(subject);
    });
  cases.run(
      "completion condition cannot be replaced by a same-sort returned value",
      [&] {
        auto policy = plainPolicy({0, 3, 4});
        policy.suite = "merlin3.bls12-381.fr64be/0";
        policy.services = {2};
        auto subject = build(context, transcript, policy);
        pir::FinishIfOp completion;
        subject.built.module->walk([&](pir::ParticipantOp participant) {
          if (participant.getRole() == "V")
            participant.walk([&](pir::FinishIfOp op) { completion = op; });
        });
        require(bool(completion), "actual completion missing");
        completion->setOperand(0, completion.getValues().front());
        rejected(subject);
      });
  for (bool bytes : {false, true})
    cases.run(
        bytes ? "byte allowance is cumulative across dormant arms"
              : "instruction allowance is cumulative across dormant arms",
        [&] {
          std::string bodies[2];
          unsigned count = bytes ? 300 : 1050;
          for (unsigned arm = 0; arm < 2; ++arm) {
            for (unsigned i = 0; i < count; ++i) {
              if (bytes) {
                // Shared MLIR storage does not reset the exporter's expanded
                // byte allowance. Every demanded box retains its full nominal
                // type in JSON, without consuming long source occurrence sites.
                bodies[arm] +=
                    "%boxed" + std::to_string(i) + " = \"data.make\"(" +
                    (i ? "%extra" + std::to_string(i - 1) : "%left") +
                    ") {alternative=\"value\"} : (ui64)->!Large\n" + "%extra" +
                    std::to_string(i) + " = \"data.get\"(%boxed" +
                    std::to_string(i) + ") {index=0:i64} : (!Large)->ui64\n";
              } else {
                // Every addition reaches the selected result. This exceeds
                // the export row limit without exhausting the independent
                // source action limit through thousands of guard sites.
                bodies[arm] +=
                    "%extra" + std::to_string(i) +
                    " = \"data.index_wrapping_add\"(" +
                    (i ? "%extra" + std::to_string(i - 1) : "%left") +
                    ",%right) : (ui64,ui64)->ui64\n";
              }
            }
          }
          auto text = plainText(bodies[0], bodies[1]);
          auto last = "%extra" + std::to_string(count - 1);
          {
            text =
                replaceText(std::move(text), "\"protocol.yield\"(%left,%right)",
                            "\"protocol.yield\"(" + last + ",%right)");
            text =
                replaceText(std::move(text), "\"protocol.yield\"(%right,%left)",
                            "\"protocol.yield\"(%right," + last + ")");
          }
          if (bytes) {
            text = "!Large = !data.variant<#data.identity<[\"atom\",\"" +
                   std::string(2000, 'L') +
                   "\"]>, [#data.alternative<\"value\", [ui64]>]>\n" + text;
          }
          auto subject = build(context, text, plainPolicy({0, 1, 2, 3}));
          if (!bytes) {
            pir::ParticipantOp validator;
            subject.built.module->walk([&](pir::ParticipantOp participant) {
              if (participant.getRole() == subject.policy.validator)
                validator = participant;
            });
            require(bool(validator), "capacity fixture lost its validator");
            unsigned rows = 0, arms = 0;
            validator.walk([&](Operation *op) {
              if (op != validator.getOperation() &&
                  !op->hasTrait<OpTrait::IsTerminator>())
                ++rows;
              if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op))
                for (Region &arm : branch.getArms()) {
                  unsigned instructions = 0;
                  for (Operation &child : arm.front())
                    instructions += !child.hasTrait<OpTrait::IsTerminator>();
                  require(
                      instructions == count && instructions < 2048,
                      "each dormant arm must fit the instruction allowance");
                  ++arms;
                }
            });
            require(
                arms == 2 && rows > 2048 && rows < 4096,
                "capacity fixture must exceed only the cumulative row bound");
          }
          refuses(exportConstructedParticipant(*subject.source,
                                               *subject.built.module,
                                               subject.bytes, subject.policy),
                  "constructed-participant-limit");
        });
  return cases.result();
}
