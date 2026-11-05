#include "../lib/Compiler/NativeConstructionPreparation.h"
#include "../lib/Compiler/NativeRequest.h"
#include "../lib/Transforms/OracleCommonRealization.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
using Kind = zkc::detail::ConstructionDependencyKind;
namespace {
// Real source, ordinary scoped handlers and the admitted fixed Record ABI.
// Both Record and transcript have nonempty state in this fixture. The observer
// intentionally ignores its payload; opaque dependence must still retain it.
constexpr StringLiteral program = R"zkc(module m;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State effects(stop,opaque);
  fn observe(t:State,v:T)->State effects(stop,opaque);
  fn draw(t:State)->(State,T) effects(stop,opaque);
}
protocol Round<T:Field> roles(P,V)
  (public:T@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
  #[site(commitment)] let first=send P->V(secret);
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  #[site(response)] let last=send P->V(secret+actual);
  return last==first+c;
}
construction Derived<T:Field,H:TestTranscript<T>> for Round<T>{
  transcript H;
  replace challenges;
  on start(t,public){return H::observe(t,public);}
  on message {commitment,response}(t,value){return H::observe(t,value);}
  on message delivery(t,value){return t;}
  on query challenge(t){return H::draw(t);}
}
module Provider:TestTranscript<F>{
  type State:Copy+Drop=(index,index);
  fn initialize()->State{return State((0,0));}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return (t,1);}
}
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
interface RecordCodec<L:Type+Copy+Drop> {
  type Record:Copy+Drop;
  fn initialize(layout:L)->Record effects(stop,opaque);
  fn write(record:Record)->Bytes effects(stop,opaque);
  fn finish(record:Record,proof:Bytes)->() effects(stop,opaque);
  fn receive(record:Record,proof:Bytes)->(Record,(index,index)) effects(stop,opaque);
}
module Packing:RecordCodec<F> {
  type Record:Copy+Drop=index;
  fn initialize(layout:F)->Record{return Record(0);}
  fn write(record:Record)->Bytes{return empty();}
  fn finish(record:Record,proof:Bytes)->(){return ();}
  fn receive(record:Record,proof:Bytes)->(Record,(index,index)){
    let offset=unpack(record);return (Record(offset+32),(offset,32));
  }
}
pub construction Encoded<C:RecordCodec<F>> for Round<F> {
  base Derived<F,Provider>;
  format C(public);
  on encode {commitment,response}(r,value){return (r,empty());}
  on receive {commitment,response}(r,proof){return C::receive(r,proof);}
  on decode {commitment,response}(wire){return 0;}
  on wire {commitment,response}(t,wire){return t;}
}
proof Packed=Round<F>{prover P;verifier V;public{public};accept ok;
  construction Encoded<Packing>;}
)zkc";
void replaceSource(std::string &source, StringRef from, StringRef to) {
  auto position = source.find(from.str());
  require(position != std::string::npos, "fixture replacement missing");
  source.replace(position, from.size(), to.str());
}
pir::ProtocolModuleOp unit(ModuleOp source) {
  return cast<pir::ProtocolModuleOp>(source.getBody()->front());
}
std::string print(ModuleOp source) {
  std::string result;
  raw_string_ostream stream(result);
  source.print(stream);
  return result;
}
struct Fixture {
  OwningOpRef<ModuleOp> source;
  protocol::ResolvedConstruction selected;
  protocol::SourceExecutionClosure execution;
  NativeProofPolicy policy;
  pir::MathematicalOp entry;
  Fixture(MLIRContext &context, StringRef text = program) {
    auto captured =
        take(language::capture({{"m", text.str(), "preparation.zkc"}}));
    auto checked = take(language::analyze(captured).checkedProject());
    auto closed = take(language::closeEntry(checked, "m::Packed"));
    source = parseSourceString<ModuleOp>(
        take(language::emitOriginal(closed, context)), &context);
    require(bool(source), "actual original must parse");
    take(language::compareOriginal(closed, *source));
    require(succeeded(admitStage(*source)), "original must pass admission");
    SymbolTableCollection symbols;
    const auto &definition =
        closed.declarations()
            [closed.entry().proof()->selectedConstruction->index];
    auto record = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
        unit(*source), StringAttr::get(&context, definition.symbol));
    require(bool(record), "actual selected construction must exist");
    selected = take(protocol::resolveConstructionPlan(record, symbols));
    policy.entry = selected.plan.target.getValue().str();
    policy.construction = selected.plan.symbol.getValue().str();
    policy.suite = selected.plan.suite;
    policy.services.assign(selected.plan.services.begin(),
                           selected.plan.services.end());
    policy.publicInputs = {0};
    policy.producer = "P";
    policy.validator = "V";
    policy.format = selected.plan.codec ? protocol::ProofFormat::RawBytes
                                        : protocol::ProofFormat::Native;
    SymbolTable table(unit(*source));
    entry = table.lookup<pir::MathematicalOp>(policy.entry);
    require(bool(entry), "actual entry must resolve");
    policy.producer = cast<StringAttr>(entry.getRoles()[0]).str();
    policy.validator = cast<StringAttr>(entry.getRoles()[1]).str();
    refresh();
  }
  void refresh() {
    require(succeeded(admitStage(*source)), "changed actual source must admit");
    execution = take(protocol::readSourceExecutionClosure(unit(*source)));
  }
  Expected<zkc::detail::NativeConstructionPreparation>
  prepare(uint64_t budget = 1000000) {
    return zkc::detail::prepareNativeConstruction(*source, entry, execution,
                                                  policy, &selected.plan,
                                                  selected.invocations, budget);
  }
};
size_t
dependencyCount(const zkc::detail::NativeConstructionPreparation &prepared,
                Kind kind) {
  return count_if(prepared.dependencies(),
                  [&](const auto &item) { return item.kind == kind; });
}
// Close and compare the actual Language source before selecting a native
// proof. This exercises prepareProof, materialization and independent reading.
struct NativeFixture {
  OwningOpRef<ModuleOp> source;
  protocol::SourceExecutionClosure execution;
  NativeProofPolicy policy;
  pir::MathematicalOp entry;
  NativeFixture(MLIRContext &context, StringRef text) {
    auto captured =
        take(language::capture({{"m", text.str(), "requests.zkc"}}));
    auto checked = take(language::analyze(captured).checkedProject());
    auto closed = take(closeNativeRun(checked, "m::Run"));
    source = parseSourceString<ModuleOp>(
        take(language::emitOriginal(closed, context)), &context);
    require(bool(source), "closed native source must parse");
    take(language::compareOriginal(closed, *source));
    require(succeeded(admitStage(*source)), "closed native source must admit");
    auto entries =
        unit(*source).getBody().front().getOps<pir::MathematicalOp>();
    require(hasSingleElement(entries), "native fixture has one actual entry");
    entry = *entries.begin();
    policy.entry = entry.getSymName().str();
    policy.producer = cast<StringAttr>(entry.getRoles()[0]).str();
    policy.validator = cast<StringAttr>(entry.getRoles()[1]).str();
    policy.suite = "merlin3.bls12-381.fr64be/0";
    // Source lowering places ordinary data before managed service ports.
    // Derive the policy from the actual admitted entry, not authored ordering.
    for (auto [index, type] : enumerate(entry.getFunctionType().getInputs())) {
      auto owners = cast<ArrayAttr>(entry.getInputRoles()[index]);
      if (!is_contained(owners, StringAttr::get(&context, policy.validator)))
        continue;
      if (isa<pir::ServiceReferenceType>(type)) {
        if (policy.services.empty())
          policy.services.push_back(index);
      } else {
        policy.publicInputs.push_back(index);
      }
    }
    execution = take(protocol::readSourceExecutionClosure(unit(*source)));
  }
  zkc::detail::NativeConstructionPreparation prepare() {
    return take(zkc::detail::prepareNativeConstruction(*source, entry,
                                                       execution, policy));
  }
  void construct() {
    auto before = print(*source);
    auto selected = take(selectNativeProofDraws(*source, policy));
    auto built = take(constructNativeProof(*source, selected));
    require(succeeded(admitStage(*built.module)),
            "constructed proof admission");
    if (auto error = checkNativeProof(*source, *built.module, selected))
      throw std::runtime_error(toString(std::move(error)));
    require(print(*source) == before, "production preparation mutated source");
  }
};
constexpr StringLiteral requestSource = R"zkc(module m;
domain F=field("bls12-381.fr");
math fn choose(flag:bool,x:F,y:F)->F {
  return if flag {if flag {x+y}else{x}}else{y};
}
fn request(flag:bool,x:F,y:F)->F {return choose(flag,x,y);}
protocol Run roles(P,V)(public:F@(P,V),secret:F@P,
    challenges:Random<F>@V,flag:bool@(P,V))->(ok:bool@V) {
  #[site(commitment)] let first=send P->V(secret);
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  // REQUEST_BEGIN
  let value@V=request(flag,first,public);
  #[site(request)] let received=send V->P(value);
  #[site(answer)] let answer=send P->V(received+actual);
  // REQUEST_END
  return first==public+c;
})zkc";
// A genuine ordinary Local function, including its scope/outcome CFG. It is
// deliberately unused until inserted at a concrete Protocol source frontier.
func::FuncOp stopping(ModuleOp module) {
  OpBuilder builder(module.getContext());
  builder.setInsertionPointToEnd(&unit(module).getBody().front());
  auto f = func::FuncOp::create(
      builder, module.getLoc(), "preparation_stop",
      builder.getFunctionType(
          {runtime::ScopeType::get(module.getContext())},
          {exec::OutcomeType::get(module.getContext(), {})}));
  f.setPrivate();
  f.setNoInline(true);
  f->setAttr("runtime.origin",
             builder.getArrayAttr({builder.getStringAttr("preparation_stop"),
                                   builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(f.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, f);
  control.reject("reject", "stopped");
  return f;
}
void insertStop(ModuleOp module, Operation *before, StringRef role) {
  auto f = stopping(module);
  OpBuilder builder(before);
  pir::LocalCallOp::create(builder, before->getLoc(), TypeRange{}, ValueRange{},
                           FlatSymbolRefAttr::get(f),
                           builder.getStringAttr("prior_stop"),
                           builder.getStringAttr(role));
}
// No construction is needed to exercise actual source captures and bounded
// selected control. This is admitted Protocol, not a graph invented by tests.
std::string controlSource(uint64_t maximum = 2) {
  return (Twine(R"mlir(module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%n:ui64,%a:i1,%b:i1):
    %result = "protocol.repeat"(%n,%a,%b) ({
    ^body(%i:ui64,%carried:i1,%capture:i1):
      %chosen = "protocol.branch"(%capture,%carried,%capture) ({
      ^yes(%x:i1,%y:i1):
        "protocol.yield"(%x) : (i1)->()
      }, {
      ^no(%x:i1,%y:i1):
        "protocol.yield"(%y) : (i1)->()
      }) {site="choose",roles=["P","V"],output_roles=[["P","V"]],alternatives=["then","else"]} : (i1,i1,i1)->i1
      "protocol.yield"(%chosen) : (i1)->()
    }) {site="loop",carried=1:i64,maximum=)mlir") +
          Twine(maximum) +
          R"mlir(:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,i1)->i1
    "protocol.return"(%result) : (i1)->()
  }) {sym_name="main",function_type=(ui64,i1,i1)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"]],output_roles=[["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir")
      .str();
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "actual callbacks and record layout share one borrowed preparation", [&] {
        Fixture fixture(context);
        auto before = print(*fixture.source);
        auto prepared = take(fixture.prepare());
        require(prepared.source() == *fixture.source &&
                    &prepared.execution() == &fixture.execution,
                "preparation must borrow its exact owners");
        require(print(*fixture.source) == before,
                "preparation mutated original source");
        for (Kind kind : {Kind::Callback, Kind::Capture, Kind::Root,
                          Kind::Start, Kind::Query, Kind::Omission,
                          Kind::Encode, Kind::Receive, Kind::Range,
                          Kind::RawObservation, Kind::Decode, Kind::Observation,
                          Kind::RecordInitialization, Kind::Finalization})
          require(dependencyCount(prepared, kind) != 0,
                  "missing actual dependency class");
        auto moved = std::move(prepared);
        require(&moved.execution() == &fixture.execution,
                "move changed borrow");
      });
  cases.run(
      "child start borrows actual application inputs with substituted roles",
      [&] {
        std::string text = program.str();
        auto first = text.find("protocol Round");
        auto last = text.find("construction Derived", first);
        auto child = text.substr(first, last - first);
        for (char &c : child) {
          // This fixture fragment uses uppercase P and V only as role names.
          if (c == 'P')
            c = 'A';
          else if (c == 'V')
            c = 'B';
        }
        text.replace(first, last - first, child);
        replaceSource(
            text,
            "proof Packed=Round<F>{prover P;verifier V;public{public};accept "
            "ok;\n  construction Encoded<Packing>;}",
            R"zkc(protocol Outer roles(P,V)
        (public:F@(P,V),secret:F@P,challenges:Random<F>@V)->(ok:bool@V){
        #[site(step)] let ok=Round<F> roles(P,V)(public,secret,challenges);
        return ok;
      }
      construction Parent for Outer {
        transcript Provider;
        replace challenges;
        on start(t){return t;}
        apply Derived<F,Provider> at step;
      }
      proof Packed=Outer{prover P;verifier V;public{public};accept ok;
        construction Parent;})zkc");
        Fixture fixture(context, text);
        require(fixture.selected.invocations.size() == 1,
                "actual child construction start must resolve");
        auto prepared = take(fixture.prepare());
        bool childStart = false;
        for (const auto &item : prepared.dependencies())
          childStart |= item.kind == Kind::Start && item.source &&
                        isa<pir::ApplyOp>(item.source);
        require(childStart, "child start lost its actual source application");
      });
  cases.run("opaque observer retains ignored payload and both state inputs",
            [&] {
              Fixture fixture(context);
              auto prepared = take(fixture.prepare());
              bool observed = false;
              for (const auto &item : prepared.dependencies()) {
                if (item.kind != Kind::Callback || !item.callback)
                  continue;
                auto signature = protocol::scopedDataSignature(item.callback);
                if (!signature || signature.getNumInputs() < 3)
                  continue;
                // Invocation/exit rows both retain all actual inputs, including
                // ignored payloads. Formal capture rows point at the real
                // function arguments.
                require(item.predecessors.size() >= signature.getNumInputs(),
                        "opaque call discarded an actual input dependency");
                observed = true;
              }
              require(observed,
                      "fixture must exercise an actual multi-input handler");
            });
  cases.run(
      "current receive ABI refuses a proposed transcript-state input", [&] {
        Fixture fixture(context);
        auto changed = fixture.selected.plan;
        auto receive = find_if(changed.rules, [](const auto &rule) {
          return rule.kind == protocol::ConstructionRuleKind::Receive;
        });
        require(receive != changed.rules.end(), "fixture receive");
        SymbolTable table(unit(*fixture.source));
        auto f = table.lookup<func::FuncOp>(receive->handler.getValue());
        // Change actual signature AND body argument list. This is the proposed
        // dynamic receive boundary, not an expressible cycle in the current
        // ABI.
        auto argument = f.getArgument(1).getType();
        require(succeeded(f.insertArgument(1, argument, DictionaryAttr{},
                                           f.getLoc())),
                "fixture input insertion failed");
        fixture.execution =
            take(protocol::readSourceExecutionClosure(unit(*fixture.source)));
        refuses(fixture.prepare(), "native-construction-preparation-signature");
        SymbolTableCollection symbols;
        auto record =
            table.lookup<pir::ConstructionOp>(fixture.policy.construction);
        refuses(protocol::readConstructionPlan(record, symbols),
                "protocol-construction");
      });
  cases.run(
      "one phase budget includes setup closure traversal and output growth",
      [&] {
        Fixture fixture(context);
        refuses(fixture.prepare(0), "native-construction-preparation-capacity");
        auto prepared = take(fixture.prepare());
        require(prepared.workUsed() > prepared.dependencies().size(),
                "setup not charged");
        auto exact = prepared.workUsed();
        take(fixture.prepare(exact));
        refuses(fixture.prepare(exact - 1),
                "native-construction-preparation-capacity");
      });
  cases.run(
      "closure from a different actual source cannot authorize preparation",
      [&] {
        Fixture fixture(context), other(context);
        refuses(zkc::detail::prepareNativeConstruction(
                    *fixture.source, fixture.entry, other.execution,
                    fixture.policy, &fixture.selected.plan),
                "native-construction-preparation-closure");
      });
  cases.run("multi-leaf codec cannot cross a reached stopping callback", [&] {
    std::string text = program.str();
    replaceSource(text, "send P->V(secret)", "send P->V((secret,secret))");
    replaceSource(text, "send P->V(secret+actual)",
                  "send P->V((secret+actual,secret+actual))");
    replaceSource(text, "return last==first+c;",
                  "let (a,b)=first;let (x,y)=last;return x==a+c;");
    replaceSource(text, "return H::observe(t,value);",
                  "let (x,y)=value;return H::observe(t,x);");
    replaceSource(text, "on decode {commitment,response}(wire){return 0;}",
                  "on decode {commitment,response}(wire){return (0,0);}");
    Fixture fixture(context, text);
    take(fixture.prepare());
    auto encoded = find_if(fixture.selected.plan.rules, [](const auto &r) {
      return r.kind == protocol::ConstructionRuleKind::Encode;
    });
    require(encoded != fixture.selected.plan.rules.end() &&
                encoded->sites.size() == 2,
            "tuple codec must select two actual leaves");
    Operation *second = nullptr;
    fixture.entry.walk([&](pir::ExchangeOp exchange) {
      if (exchange.getSite() == encoded->sites[1])
        second = exchange;
    });
    require(second != nullptr, "actual second leaf");
    insertStop(*fixture.source, second, fixture.policy.validator);
    fixture.refresh();
    refuses(fixture.prepare(), "native-construction-preparation-order");
  });
  cases.run(
      "source stop before transport remains in the dependency prefix", [&] {
        Fixture fixture(context);
        insertStop(*fixture.source, &fixture.entry.getBody().front().front(),
                   fixture.policy.validator);
        fixture.refresh();
        auto prepared = take(fixture.prepare());
        bool retained = false;
        for (const auto &item : prepared.dependencies())
          retained |=
              item.source && isa<exec::RejectOp>(item.source) && item.stopped;
        require(retained, "stopped callback body was discarded");
      });
  cases.run("bounded repeat reads one body and all selected arms", [&] {
    size_t nodes = 0;
    uint64_t work = 0;
    for (uint64_t maximum : {2ULL, 1000000ULL}) {
      auto source =
          parseSourceString<ModuleOp>(controlSource(maximum), &context);
      require(bool(source) && succeeded(admitStage(*source)),
              "selected source must admit");
      auto execution =
          take(protocol::readSourceExecutionClosure(unit(*source)));
      auto entry = *unit(*source)
                        .getBody()
                        .front()
                        .getOps<pir::MathematicalOp>()
                        .begin();
      NativeProofPolicy policy;
      policy.entry = "main";
      policy.producer = "P";
      policy.validator = "V";
      auto prepared = take(zkc::detail::prepareNativeConstruction(
          *source, entry, execution, policy));
      require(dependencyCount(prepared, Kind::Iteration) &&
                  dependencyCount(prepared, Kind::Join),
              "missing symbolic iteration and all-arm join");
      if (!nodes) {
        nodes = prepared.dependencies().size();
        work = prepared.workUsed();
      } else
        require(nodes == prepared.dependencies().size() &&
                    work == prepared.workUsed(),
                "repeat was expanded by its iteration bound");
      llvm::DenseSet<Value> actualCaptures;
      for (const auto &item : prepared.dependencies())
        if (item.kind == Kind::Capture && item.value)
          actualCaptures.insert(item.value);
      require(actualCaptures.size() >= 7,
              "distinct actual arm formals were merged by type");
    }
  });
  cases.run(
      "zero state and Record still retain ordered callbacks and conditional "
      "finalization",
      [&] {
        std::string text = program.str();
        replaceSource(text, "type State:Copy+Drop=(index,index);",
                      "type State:Copy+Drop=();");
        replaceSource(text, "return State((0,0));", "return State(());");
        replaceSource(text, "type Record:Copy+Drop=index;",
                      "type Record:Copy+Drop=();");
        replaceSource(text, "return Record(0);", "return Record(());");
        replaceSource(
            text,
            "let offset=unpack(record);return (Record(offset+32),(offset,32));",
            "return (record,(0,32));");
        Fixture fixture(context, text);
        require(fixture.selected.plan.state.empty() &&
                    fixture.selected.plan.codec->record.empty(),
                "fixture must use actual zero-slot ABIs");
        auto *returned = fixture.entry.getBody().front().getTerminator();
        require(returned->getNumOperands() == 1, "actual Boolean result");
        OpBuilder builder(returned);
        pir::FinishIfOp::create(builder, returned->getLoc(), TypeRange{},
                                returned->getOperand(0),
                                returned->getOperands(), "conditional_finish",
                                fixture.policy.validator);
        fixture.refresh();
        auto prepared = take(fixture.prepare());
        bool conditional = false, unconditional = false;
        for (const auto &item : prepared.dependencies()) {
          if (item.kind != Kind::Finalization || !item.validator)
            continue;
          conditional |= item.conditional;
          unconditional |= !item.conditional;
        }
        require(
            conditional && unconditional,
            "selected completion and ordinary return need distinct finalizers");
        require(dependencyCount(prepared, Kind::Observation) != 0,
                "zero-slot observer must retain ordered work");
      });
  cases.run("uncovered selected handler is a named refusal", [&] {
    Fixture fixture(context);
    fixture.selected.plan.rules.erase(
        std::remove_if(fixture.selected.plan.rules.begin(),
                       fixture.selected.plan.rules.end(),
                       [](const auto &r) {
                         return r.kind ==
                                protocol::ConstructionRuleKind::Receive;
                       }),
        fixture.selected.plan.rules.end());
    refuses(fixture.prepare(), "native-construction-preparation-coverage");
  });
  cases.run("uncovered custom reverse message cannot bypass its observer", [&] {
    Fixture fixture(context);
    auto *before = fixture.entry.getBody().front().getTerminator();
    OpBuilder builder(before);
    Value value = fixture.entry.getBody().front().getArgument(0);
    pir::ExchangeOp::create(builder, before->getLoc(), value.getType(), value,
                            "extra_request", fixture.policy.validator,
                            fixture.policy.producer);
    fixture.refresh();
    refuses(fixture.prepare(), "native-construction-preparation-coverage");
  });
  cases.run(
      "private same-typed codec layout input is unavailable to the validator",
      [&] {
        Fixture fixture(context);
        // Deliberately corrupt a checked selector while retaining its type.
        fixture.selected.plan.codec->inputs = {1};
        refuses(fixture.prepare(),
                "native-construction-preparation-dependency");
      });
  cases.run("entry from another source is a named source refusal", [&] {
    Fixture fixture(context), other(context);
    refuses(zkc::detail::prepareNativeConstruction(
                *fixture.source, other.entry, fixture.execution, fixture.policy,
                &fixture.selected.plan),
            "native-construction-preparation-source");
  });
  cases.run(
      "same-typed alias cannot replace the actual omitted query result", [&] {
        Fixture fixture(context);
        pir::ExchangeOp delivery;
        fixture.entry.walk([&](pir::ExchangeOp op) {
          if (op.getSender() == fixture.policy.validator)
            delivery = op;
        });
        require(bool(delivery), "actual reverse delivery");
        // Keep its type and availability, but change semantic identity to a
        // distinct shared input. It is no longer the selected draw's exact
        // value.
        delivery->setOperand(0, fixture.entry.getBody().front().getArgument(0));
        fixture.refresh();
        refuses(fixture.prepare(), "native-proof-reverse-message");
      });
  cases.run(
      "ordinary provider and codec use production joint preparation", [&] {
        Fixture fixture(context);
        auto selected =
            take(selectNativeProofDraws(*fixture.source, fixture.policy));
        auto built = take(constructNativeProof(*fixture.source, selected));
        if (auto error =
                checkNativeProof(*fixture.source, *built.module, selected))
          throw std::runtime_error(toString(std::move(error)));
      });
  cases.run(
      "closed selected Math request reaches production and independent reader",
      [&] {
        NativeFixture fixture(context, requestSource);
        auto prepared = fixture.prepare();
        require(!prepared.complete() &&
                    dependencyCount(prepared, Kind::Replica) &&
                    dependencyCount(prepared, Kind::Join),
                "selected request needs its real source and request relation");
        zkc::detail::NativeRequestPlan unrelated;
        auto missing = prepared.dischargeRequests(unrelated);
        require(bool(missing) &&
                    namesIdentifier(toString(std::move(missing)),
                                    "native-construction-preparation-replica"),
                "missing actual request relation discharged an obligation");
        bool selectedCallback = false;
        for (const auto &item : prepared.dependencies())
          selectedCallback |= item.source && isa<data::BranchOp>(item.source);
        require(selectedCallback,
                "actual selected Math body was not traversed");
        fixture.construct();
      });
  cases.run("closed reverse requests retain nested Protocol loops and branches",
            [&] {
              std::string text = requestSource.str();
              replaceSource(text, "// REQUEST_BEGIN", R"zkc(
      for i in 0..2 roles(P,V) max 2 {
        #[site(choose)] if flag roles(P,V) {
    )zkc");
              replaceSource(text, "// REQUEST_END", "} else {} }");
              NativeFixture fixture(context, text);
              auto prepared = fixture.prepare();
              require(dependencyCount(prepared, Kind::Iteration) &&
                          dependencyCount(prepared, Kind::Join) &&
                          dependencyCount(prepared, Kind::Replica),
                      "nested selected request dependencies missing");
              fixture.construct();
            });
  cases.run(
      "same-typed private request input cannot discharge the joint relation",
      [&] {
        std::string text = requestSource.str();
        replaceSource(text, "flag:bool@(P,V))->",
                      "flag:bool@(P,V),hidden:Random<F>@V)->");
        replaceSource(text, "let value@V=request(flag,first,public);",
                      "let private@V=hidden.draw();\n"
                      "  let value@V=request(flag,first,private);");
        NativeFixture fixture(context, text);
        auto prepared = fixture.prepare();
        require(!prepared.complete(),
                "private source request was assumed public");
        refuses(selectNativeProofDraws(*fixture.source, fixture.policy),
                "native-request-reconstruction");
      });
  cases.run("actual selected provider callback retains dormant Math arms", [&] {
    std::string text = program.str();
    replaceSource(text, "module Provider:TestTranscript<F>{", R"zkc(
      math fn choose(flag:bool,x:F,y:F)->F {
        return if flag {if flag {x+y}else{x}}else{y};
      }
      module Provider:TestTranscript<F>{
    )zkc");
    replaceSource(text, "return (t,1);", "return (t,choose(true,1,2));");
    Fixture fixture(context, text);
    auto prepared = take(fixture.prepare());
    require(dependencyCount(prepared, Kind::Join) >= 4,
            "nested selected callback arms were discarded");
    auto selected =
        take(selectNativeProofDraws(*fixture.source, fixture.policy));
    auto built = take(constructNativeProof(*fixture.source, selected));
    if (auto error = checkNativeProof(*fixture.source, *built.module, selected))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run(
      "ordered finite collect and fold retain actual domains and callbacks",
      [&] {
        std::string text = requestSource.str();
        replaceSource(text, "math fn choose", R"zkc(
      type Vector<T:Field>=builtin("vector",T);
      domain fn range(lo:index,hi:index)->domain<index>=domain("range");
      domain fn elements<T:Field>(xs:Vector<T>)->domain<T>=domain("elements");
      fn collect<I:Type+Copy+Drop,T:Field>(rows:domain<I>,
        body:fn(item:I)->T effects(stop) where item_from(item,rows))
        ->Vector<T> effects(stop)=finite("local.collect.vector");
      fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
        step:fn(S,item:I)->S effects(stop) where item_from(item,rows))
        ->S effects(stop)=finite("local.fold");
      math fn choose)zkc");
        replaceSource(text, "return choose(flag,x,y);", R"zkc(
      let values=collect(range(0,2),fn(i)=>choose(flag,x,y));
      return fold(elements(values),x,fn(s,v)=>s+v);
    )zkc");
        NativeFixture fixture(context, text);
        auto prepared = fixture.prepare();
        bool fold = false, collect = false, domain = false;
        for (const auto &item : prepared.dependencies()) {
          fold |= item.source && isa<exec::FoldOp>(item.source);
          collect |= item.source && isa<exec::CollectOp>(item.source);
          domain |= item.source && isa<data::DomainRangeOp>(item.source);
        }
        require(fold && collect && domain &&
                    dependencyCount(prepared, Kind::Iteration),
                "finite source computation was replaced by a signature");
        fixture.construct();
      });
  cases.run(
      "logical oracle source requires concrete realization before emission",
      [&] {
        std::string text = requestSource.str();
        replaceSource(text, "math fn choose", R"zkc(
      type Vec=builtin("vector",F);
      type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
      math fn choose)zkc");
        replaceSource(text, "flag:bool@(P,V))->",
                      "flag:bool@(P,V),xs:Vec@P)->");
        replaceSource(text, "// REQUEST_BEGIN", R"zkc(
      #[site(table)] let handle=send P->V(xs) as oracle<Fixed<F,2>>;
      #[site(opening)] let opened@V=query handle at 0;
    )zkc");
        NativeFixture fixture(context, text);
        auto prepared = fixture.prepare();
        require(prepared.needsRealization() && !prepared.complete() &&
                    dependencyCount(prepared, Kind::Realization),
                "logical handle was treated as an already realized store");
        zkc::detail::NativeRequestPlan missing;
        auto refused = prepared.dischargeRequests(missing);
        require(
            bool(refused) &&
                namesIdentifier(toString(std::move(refused)),
                                "native-construction-preparation-closure"),
            "request discharge bypassed the logical realization obligation");
        fixture.construct();
        auto realized = take(protocol::emitOracleRealization(*fixture.source));
        take(protocol::checkOracleRealization(*fixture.source, realized));
        data::BranchOp helper;
        realized.module->walk([&](data::BranchOp selected) {
          if (!helper && selected->getParentOfType<func::FuncOp>())
            helper = selected;
        });
        require(bool(helper), "selected helper was not retained");
        auto &arm = helper->getRegion(0).front();
        auto *yield = arm.getTerminator();
        Value replacement;
        for (Value argument : arm.getArguments())
          if (argument.getType() == yield->getOperand(0).getType() &&
              argument != yield->getOperand(0)) {
            replacement = argument;
            break;
          }
        require(bool(replacement), "missing equal-typed helper mutation");
        yield->setOperand(0, replacement);
        require(succeeded(admitStage(*realized.module)),
                "retained helper mutation must remain ordinarily admitted");
        refuses(protocol::checkOracleRealization(*fixture.source, realized),
                "oracle-common-body");
      });
  for (unsigned depth : {62u, 64u})
    cases.run(
        Twine("semantic repeat depth ignores native wrappers ") + Twine(depth),
        [&] {
          std::string text = R"mlir(module { "protocol.module"() ({
        "protocol.func"() ({
        ^entry(%count:ui64,%accepted:i1):
      )mlir";
          std::string count = "%count";
          for (unsigned i = 0; i < depth; ++i) {
            auto next = "%count" + std::to_string(i);
            text += "\"protocol.repeat\"(" + count + "," + count + ") ({\n";
            text += "^body" + std::to_string(i) + "(%i" + std::to_string(i) +
                    ":ui64," + next + ":ui64):\n";
            count = next;
          }
          for (unsigned i = depth; i > 0; --i) {
            text += "\"protocol.yield\"() : ()->()\n";
            text += "}) {site=\"r" + std::to_string(i) +
                    "\",carried=0:i64,maximum=1:i64,roles=[\"P\",\"V\"],"
                    "carried_roles=[]} : (ui64,ui64)->()\n";
          }
          text += R"mlir(
        "protocol.return"(%accepted) : (i1)->()
        }) {sym_name="main",function_type=(ui64,i1)->i1,roles=["P","V"],
            input_roles=[["P","V"],["V"]],output_roles=[["V"]]} : ()->()
        }) {profile=#protocol.profile<protocol>} : ()->() })mlir";
          auto original = parseSourceString<ModuleOp>(text, &context);
          require(bool(original) && succeeded(admitStage(*original)),
                  "semantic-depth original must admit");
          auto entry = *unit(*original)
                            .getBody()
                            .front()
                            .getOps<pir::MathematicalOp>()
                            .begin();
          NativeProofPolicy policy;
          policy.entry = "main";
          policy.producer = "P";
          policy.validator = "V";
          policy.publicInputs = {0, 1};
          auto execution =
              take(protocol::readSourceExecutionClosure(unit(*original)));
          auto joint = take(zkc::detail::prepareNativeConstruction(
              *original, entry, execution, policy));
          require(dependencyCount(joint, Kind::Iteration) >= depth,
                  "semantic-depth body was omitted");
          auto selected = take(selectNativeProofDraws(*original, policy));
          auto built = take(constructNativeProof(*original, selected));
          if (auto error = checkNativeProof(*original, *built.module, selected))
            throw std::runtime_error(toString(std::move(error)));
        });
  return cases.result();
}
