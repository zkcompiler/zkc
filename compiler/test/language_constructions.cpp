#include "../lib/Compiler/NativeCodec.h"
#include "../lib/Compiler/NativeProofVerification.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Language.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
constexpr StringLiteral program = R"(module m;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State effects(stop, opaque);
  fn observe(t:State,v:T)->State effects(stop, opaque);
  fn draw(t:State)->(State,T) effects(stop, opaque);
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
)";
constexpr StringLiteral deployment = R"(
      module Provider:TestTranscript<F>{
        type State:Copy+Drop=(index,index);
        fn initialize()->State{return State((0,0));}
        fn observe(t:State,v:F)->State{return t;}
        fn draw(t:State)->(State,F){return (t,1);}
      }
      proof Demo=Round<F>{prover P;verifier V;public{public};accept ok;
        construction Derived<F,Provider>;}
    )";
constexpr StringLiteral codec = R"(
  type Bytes=builtin("bytes");
  fn empty()->Bytes=primitive("bytes.empty");
  interface RecordCodec<L:Type+Copy+Drop> {
    type Record:Copy+Drop;
    fn initialize(layout:L)->Record effects(stop, opaque);
    fn write(record:Record)->Bytes effects(stop, opaque);
    fn finish(record:Record,proof:Bytes)->() effects(stop, opaque);
  }
  module Packing:RecordCodec<F> {
    type Record:Copy+Drop=();
    fn initialize(layout:F)->Record{return Record(());}
    fn write(record:Record)->Bytes{return empty();}
    fn finish(record:Record,proof:Bytes)->(){return ();}
  }
  pub construction Encoded<C:RecordCodec<F>> for Round<F> {
    base Derived<F,Provider>;
    format C(public);
    on encode {commitment,response}(r,value){return (r,empty());}
    on receive {commitment,response}(r,proof){return (r,(0,32));}
    on decode {commitment,response}(wire){return 0;}
    on wire {commitment,response}(t,wire){return t;}
  }
  proof Packed=Round<F>{prover P;verifier V;public{public};accept ok;
    construction Encoded<Packing>;}
)";
Expected<CheckedProject> checked(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", source.str(), "construction.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
std::string replace(StringRef from, StringRef to) {
  auto text = program.str();
  auto position = text.find(from.str());
  require(position != std::string::npos, "fixture replacement exists");
  text.replace(position, from.size(), to.str());
  return text;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("construction targets use completed protocol contracts", [] {
    refuses(checked(R"(module m;
protocol Dup<T:Type> roles(P)(x:T@P)->(a:T@P,b:T@P){return(a=x,b=x);}
#[affine] struct Ticket{}
construction Bad for Dup<Ticket>{base authored;}
)"),
            "source.permission");
    refuses(checked(R"(module m;
protocol Relay<T:Type> roles(P,V)(x:T@P)->(r:T@V){let y=send P->V(x);return y;}
struct Secret{value:bool}
construction Bad for Relay<Secret>{base authored;}
)"),
            "source.ingress");
    refuses(checked(R"(module m;
protocol First<N:nat> roles(P)(xs:[bool;N]@P)->(r:bool@P){return xs[0];}
construction Bad for First<0>{base authored;}
)"),
            "source.bound");
  });
  cases.run("generic constructions retain target usage and admission", [] {
    auto project = take(checked(R"(module m;
protocol Relay<T:Type> roles(P,V)(x:T@P)->(a:T@P,b:T@V){
 let delivered=send P->V(x);return(a=x,b=delivered);
}
construction Base<T:Type> for Relay<T>{base authored;}
construction Derived<T:Type> for Relay<T>{base Base<T>;}
)"));
    for (const auto &decl : project.declarations()) {
      if (decl.kind != Declaration::Kind::Construction)
        continue;
      require(decl.permissionBounds.size() == 1 &&
                  decl.permissionBounds.front().permissions.copy,
              "construction lost inferred target usage");
      require(decl.admissions.size() == 2,
              "construction lost target boundary obligations");
    }
    refuses(checked(R"(module m;
protocol Dup<T:Type> roles(P)(x:T@P)->(a:T@P,b:T@P){return(a=x,b=x);}
construction Restricted<T:Type> for Dup<T> where (){base authored;}
)"),
            "source.permission");
  });
  cases.run("generic constructions retain target natural requirements", [] {
    auto project = take(checked(R"(module m;
protocol First<N:nat> roles(P)(xs:[bool;N]@P)->(r:bool@P){return xs[0];}
construction Base<N:nat> for First<N>{base authored;}
)"));
    for (const auto &decl : project.declarations())
      if (decl.kind == Declaration::Kind::Construction)
        require(decl.bounds.size() == 1, "construction lost target bound");
  });
  cases.run("start handlers require a state parameter", [&] {
    refuses(checked(replace("on start(t,public)", "on start()")),
            "source.construction");
  });
  for (bool addSelection : {false, true})
    cases.run(
        addSelection ? "closure cannot add a construction selection"
                     : "closure cannot change a run into a proof",
        [&] {
          std::string source =
              "module m;protocol R roles(P)()->(ok:bool@P){return true;}entry "
              "fn Run(inputs: R::Inputs) { return R::run(inputs); }";
          if (addSelection) {
            source = (program + deployment).str();
            auto at = source.find("construction Derived<F,Provider>;");
            require(at != std::string::npos, "source construction selection");
            source.replace(
                at, StringRef("construction Derived<F,Provider>;").size(),
                "construction "
                "fiat_shamir(\"merlin3.bls12-381.fr64be/0\",challenges);");
          }
          auto project = take(checked(source));
          auto closed =
              take(closeEntry(project, addSelection ? "m::Demo" : "m::Run"));
          auto &entry = const_cast<Declaration &>(closed.entry());
          if (addSelection) {
            require(entry.proof() && !entry.proof()->selectedConstruction,
                    "native proof starts without a source construction");
            std::get<ProofEntry>(entry.configuration).selectedConstruction =
                DeclarationId{0};
          } else {
            entry.configuration = ProofEntry{};
          }
          auto error = checkScopedSpecialization(closed);
          require(bool(error) &&
                      namesIdentifier(toString(std::move(error)),
                                      "source.scoped-specialization"),
                  "changed entry configuration accepted");
        });
  for (StringRef mutation : {"factory", "handler", "codec", "body"})
    cases.run(
        "independent construction closure refuses changed " + mutation, [&] {
          auto project = take(checked((program + deployment + codec).str()));
          auto closed = take(closeEntry(project, "m::Packed"));
          auto &selected = const_cast<Declaration &>(
              closed.declarations()
                  [closed.entry().proof()->selectedConstruction->index]);
          auto &plan = *selected.construction;
          if (mutation == "factory")
            plan.initializer->declaration = plan.rules.front().handler;
          else if (mutation == "handler")
            plan.rules.front().path.push_back("unexpected");
          else if (mutation == "codec")
            plan.codec->write.target = plan.codec->finish.target;
          else {
            auto &handler = const_cast<Declaration &>(
                closed.declarations()[plan.rules.front().handler.index]);
            auto changed = std::make_shared<Body>(*handler.body);
            changed->stopReason = "changed";
            handler.body = std::move(changed);
          }
          auto error = checkScopedSpecialization(closed);
          require(bool(error), "corrupted construction closure accepted");
          require(
              toString(std::move(error)).find("source.scoped-specialization") !=
                  std::string::npos,
              "wrong construction closure refusal");
        });
  cases.run("record codecs close ordinary module methods and typed rules", [&] {
    auto project = take(checked((program + deployment + codec).str()));
    auto closed = take(closeEntry(project, "m::Packed"));
    const auto &plan =
        *closed
             .declarations()
                 [closed.entry().proof()->selectedConstruction->index]
             .construction;
    require(plan.codec.has_value() &&
                plan.codec->inputs == std::vector<unsigned>{0},
            "codec retains the actual shared layout input");
    for (const auto *method :
         {&plan.codec->initialize, &plan.codec->write, &plan.codec->finish}) {
      const auto &function =
          closed.declarations()[method->target.declaration.index];
      require(function.body && function.parameters.empty(),
              "codec method is closed ordinary Local code");
    }
    require(plan.rules.size() == 13,
            "codec groups use the checked selector inventory");
    auto original = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
    require(bool(parsed), "codec PIR parses with checked method signatures");
    take(compareOriginal(closed, *parsed));
    auto module = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    auto record = *module.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto native = take(zkc::protocol::readConstructionPlan(record, symbols));
    require(native.codec && native.codec->record.empty() &&
                native.codec->inputs == SmallVector<unsigned>{0},
            "unit Record has zero slots and layout retains original port");
    mlir::OpBuilder builder(&context);
    auto saved = record.getCodecAttr();
    mlir::NamedAttrList changed(saved);
    changed.set("inputs", builder.getDenseI64ArrayAttr({1}));
    record.setCodecAttr(changed.getDictionary(&context));
    refuses(zkc::protocol::readConstructionPlan(record, symbols),
            "protocol-construction");
    record.setCodecAttr(saved);
    zkc::NativeProofPolicy policy;
    policy.entry = native.target.getValue().str();
    policy.construction = native.symbol.getValue().str();
    policy.services.assign(native.services.begin(), native.services.end());
    policy.suite = native.suite;
    policy.format = zkc::protocol::ProofFormat::RawBytes;
    policy.publicInputs = {0};
    mlir::SymbolTable table(module);
    auto protocol =
        table.lookup<zkc::protocol_ir::MathematicalOp>(policy.entry);
    policy.producer =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
    policy.validator =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
    auto selected = take(zkc::selectNativeProofDraws(*parsed, policy));
    auto constructed = take(zkc::constructNativeProof(*parsed, selected));
    unsigned communication = 0;
    constructed.module->walk([&](mlir::Operation *op) {
      communication +=
          mlir::isa<zkc::protocol_ir::EmitOp, zkc::protocol_ir::AwaitOp>(op);
    });
    require(communication == 0, "codec endpoints contain no typed transport");

    for (const auto &rule : plan.rules)
      if (zkc::protocol::isCodecRule(rule.kind))
        require(rule.chunks && rule.payload,
                "codec keeps byte shape and logical payload separately");
    auto inventory = take(inspectDeclarations(project));
    require(StringRef(inventory).contains("\"codec\"") &&
                StringRef(inventory).contains("\"decode\""),
            "inspection exposes codec selection and rule kind");
  });
  cases.run(
      "record codecs support disjoint byte ranges without message enums", [&] {
        auto source = (program + deployment + codec).str();
        for (auto [from, to] :
             {std::pair<StringRef, StringRef>{"return (r,empty());",
                                              "return (r,(empty(),empty()));"},
              {"return (r,(0,32));", "return (r,((0,32),(64,32)));"},
              {"on decode {commitment,response}(wire)",
               "on decode {commitment,response}(wire:(Bytes,Bytes))"}}) {
          auto at = source.find(from.str());
          require(at != std::string::npos, "range fixture replacement");
          source.replace(at, from.size(), to.str());
        }
        auto closed = take(closeEntry(take(checked(source)), "m::Packed"));
        const auto &plan =
            *closed
                 .declarations()
                     [closed.entry().proof()->selectedConstruction->index]
                 .construction;
        for (const auto &rule : plan.rules)
          if (zkc::protocol::isCodecRule(rule.kind))
            require(rule.chunks && rule.chunks->kind == Type::Kind::Tuple &&
                        rule.chunks->arguments.size() == 2,
                    "all codec rules share the two-chunk shape");
        auto original = take(emitOriginal(closed, context));
        auto parsed =
            mlir::parseSourceString<mlir::ModuleOp>(original, &context);
        require(bool(parsed), "disjoint codec PIR parses");
        take(compareOriginal(closed, *parsed));
      });
  cases.run(
      "a bare format uses unit layout and inherited format stays fixed", [&] {
        auto source = (program + deployment + codec).str();
        for (auto [from, to] :
             {std::pair<StringRef, StringRef>{"RecordCodec<F>",
                                              "RecordCodec<()>"},
              {"initialize(layout:F)", "initialize(layout:())"},
              {"format C(public);", "format C;"}}) {
          size_t at = 0;
          while ((at = source.find(from.str(), at)) != std::string::npos) {
            source.replace(at, from.size(), to.str());
            at += to.size();
          }
        }
        auto closed = take(closeEntry(take(checked(source)), "m::Packed"));
        const auto &plan =
            *closed
                 .declarations()
                     [closed.entry().proof()->selectedConstruction->index]
                 .construction;
        require(plan.codec && plan.codec->inputs.empty(),
                "unit layout selects no input");
        auto original = take(emitOriginal(closed, context));
        auto parsed =
            mlir::parseSourceString<mlir::ModuleOp>(original, &context);
        require(bool(parsed), "unit layout PIR parses");
        take(compareOriginal(closed, *parsed));
        source += R"(
      construction ChangedFormat for Round<F> {
        base Encoded<Packing>; format Native;
      }
    )";
        refuses(checked(source), "source.construction");
      });
  for (auto change :
       {std::pair<StringRef, StringRef>{"format C(public);",
                                        "format C(secret);"},
        {"format C(public);", "format C(public,public);"},
        {"format C(public);", "format Native;"},
        {"on decode {commitment,response}(wire)",
         "on decode {commitment,response}(wire:F)"},
        {"on decode {commitment,response}(wire){return 0;}", ""},
        {"on encode {commitment,response}", "on encode {commitment,delivery}"}})
    cases.run(("codec refuses " + change.second).str(), [&, from = change.first,
                                                         to = change.second] {
      auto source = (program + deployment + codec).str();
      auto at = source.find(from.str());
      require(at != std::string::npos, "codec invalid fixture replacement");
      source.replace(at, from.size(), to.str());
      refuses(checked(source), "source.construction");
    });
  cases.run("typed handlers use ordinary Local declarations", [&] {
    auto project = take(checked(program));
    unsigned handlers = 0;
    for (const auto &decl : project.declarations()) {
      if (decl.anonymous && decl.kind == Declaration::Kind::Local) {
        require(bool(decl.body), "handler body checked");
        ++handlers;
      }
      if (decl.name == "Derived") {
        require(bool(decl.construction), "checked association retained");
        require(decl.construction->rules.size() == 5,
                "group expands to exact selectors");
        require(decl.construction->initializer.has_value(),
                "provider factory resolved");
      }
    }
    require(handlers == 5, "one typed Local body per occurrence");
  });
  cases.run("partial overrides inherit provider and unchanged rules", [&] {
    auto project = take(checked((program + R"(
      construction Changed<T:Field,H:TestTranscript<T>> for Round<T>{
        base Derived<T,H>;
        on message response(t,value){return t;}
      })")
                                    .str()));
    auto found = llvm::find_if(project.declarations(), [](const auto &decl) {
      return decl.name == "Changed";
    });
    require(found != project.declarations().end(), "derived definition exists");
    require(found->construction->rules.size() == 5,
            "override replaces one rule");
  });
  cases.run(
      "inspection reports checked selections and hides anonymous bodies", [&] {
        auto project = take(checked(
            replace("construction Derived", "pub construction Derived")));
        auto report = take(json::parse(take(inspectDeclarations(project))));
        unsigned constructors = 0;
        for (const auto &value : *report.getAsArray()) {
          const auto &declaration = *value.getAsObject();
          require(!declaration.getString("name")->contains("handler_"),
                  "anonymous construction functions are not public inventory "
                  "entries");
          if (declaration.getString("kind") == "construction") {
            ++constructors;
            require(declaration.get("replace") &&
                        *declaration.get("replace") ==
                            json::Value(json::Array{"challenges"}) &&
                        declaration.getString("root") == "local" &&
                        declaration.getArray("rules")->size() == 5,
                    "inspection retains checked authority, root and complete "
                    "rule set");
          }
        }
        require(constructors == 1, "selected public construction appears once");
      });
  cases.run("Entry closes the selected factory and every handler", [&] {
    auto project = take(checked((program + deployment).str()));
    auto closed = take(closeEntry(project, "m::Demo"));
    const auto *proof = closed.entry().proof();
    require(proof->construction == ProofEntry::Construction::Derived,
            "custom construction kind retained");
    const auto &definition =
        closed.declarations()[proof->selectedConstruction->index];
    require(definition.parameters.empty(), "construction is specialized");
    require(definition.target->index == closed.protocol().id.index,
            "construction targets the selected protocol instance");
    const auto &plan = *definition.construction;
    require(closed.declarations()[plan.initializer->declaration.index].body !=
                nullptr,
            "closed factory retained before templates are erased");
    for (const auto &rule : plan.rules) {
      const auto &handler = closed.declarations()[rule.handler.index];
      require(handler.parameters.empty() && handler.body != nullptr,
              "closed handler retained before templates are erased");
    }
    auto bytes = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(parsed), "typed construction IR parses");
    take(compareOriginal(closed, *parsed));
    auto module = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    auto record = *module.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto native = take(zkc::protocol::readConstructionPlan(record, symbols));
    require(native.state.size() == 2 && native.rules.size() == 5,
            "logical construction state and rules lower explicitly");
    {
      auto candidate = mlir::OwningOpRef<mlir::ModuleOp>(
          mlir::cast<mlir::ModuleOp>(parsed->clone()));
      mlir::PassManager prepare(&context);
      prepare.addPass(zkc::protocol::createPrepareProtocolPass());
      require(mlir::succeeded(prepare.run(*candidate)),
              "preparation preserves selected construction");
      auto prepared = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
          candidate->getBody()->front());
      auto preserved = *prepared.getBody()
                            .front()
                            .getOps<zkc::protocol_ir::ConstructionOp>()
                            .begin();
      require(preserved->getAttrDictionary() == record->getAttrDictionary(),
              "preparation cannot change construction metadata");
      bool refused = false;
      mlir::ScopedDiagnosticHandler diagnostic(
          &context, [&](mlir::Diagnostic &diagnostic) {
            refused |=
                StringRef(diagnostic.str()).contains("protocol-construction");
            return mlir::success();
          });
      mlir::PassManager project(&context);
      project.addPass(zkc::protocol::createProjectProtocolPass());
      require(mlir::failed(project.run(*candidate)) && refused,
              "ordinary projection must not discard the selected construction");
    }
    auto original = record.getRules();
    mlir::OpBuilder builder(&context);
    SmallVector<mlir::Attribute> rules(original.getValue());
    mlir::NamedAttrList changed(mlir::cast<mlir::DictionaryAttr>(rules[1]));
    changed.set("handler", native.rules[2].handler);
    rules[1] = changed.getDictionary(&context);
    record.setRulesAttr(builder.getArrayAttr(rules));
    refuses(compareOriginal(closed, *parsed), "source.correspondence");
    record.setRulesAttr(original);
    auto wrongStart =
        mlir::NamedAttrList(mlir::cast<mlir::DictionaryAttr>(original[0]));
    wrongStart.set("inputs", builder.getDenseI64ArrayAttr({1}));
    rules.assign(original.begin(), original.end());
    rules[0] = wrongStart.getDictionary(&context);
    record.setRulesAttr(builder.getArrayAttr(rules));
    refuses(compareOriginal(closed, *parsed), "target.admission");
    record.setRulesAttr(original);
    changed = mlir::NamedAttrList(mlir::cast<mlir::DictionaryAttr>(rules[1]));
    changed.set("sites", builder.getStrArrayAttr({"other-occurrence"}));
    rules.assign(original.begin(), original.end());
    rules[1] = changed.getDictionary(&context);
    record.setRulesAttr(builder.getArrayAttr(rules));
    refuses(compareOriginal(closed, *parsed), "source.correspondence");
    record.setRulesAttr(original);
    record.setProvider("another-provider");
    refuses(compareOriginal(closed, *parsed), "source.correspondence");
  });
  cases.run("tuple messages select one handler over all native leaves", [&] {
    auto source = program.str();
    for (auto [from, to] :
         {std::pair<StringRef, StringRef>{"send P->V(secret)",
                                          "send P->V((secret,secret))"},
          {"send P->V(secret+actual)",
           "send P->V((secret+actual,secret+actual))"},
          {"return last==first+c;",
           "let (a,b)=first;let (x,y)=last;return x==a+c;"},
          {"return H::observe(t,value);",
           "let (x,y)=value;return H::observe(t,x);"}}) {
      auto position = source.find(from.str());
      require(position != std::string::npos, "tuple fixture replacement");
      source.replace(position, from.size(), to.str());
    }
    auto closed =
        take(closeEntry(take(checked(source + deployment.str())), "m::Demo"));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(
        take(emitOriginal(closed, context)), &context);
    require(bool(parsed), "parse tuple construction");
    take(compareOriginal(closed, *parsed));
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    auto record = *unit.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(record, symbols));
    require(plan.rules[1].sites.size() == 2 &&
                plan.rules[2].sites.size() == 2 &&
                plan.rules[1].payload.size() == 2 && plan.rules.size() == 5,
            "two wire leaves belong to one logical handler invocation");
    zkc::NativeProofPolicy policy;
    policy.entry = plan.target.getValue().str();
    policy.construction = plan.symbol.getValue().str();
    policy.services.assign(plan.services.begin(), plan.services.end());
    policy.publicInputs = {0};
    mlir::SymbolTable table(unit);
    auto protocol =
        table.lookup<zkc::protocol_ir::MathematicalOp>(policy.entry);
    policy.producer =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
    policy.validator =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
    auto selected = take(zkc::selectNativeProofDraws(*parsed, policy));
    require(
        selected.draws.size() == 1 &&
            selected.construction == policy.construction,
        "construction selection admits logical groups and selected authority");
    auto constructed = take(zkc::constructNativeProof(*parsed, selected));
    if (auto error =
            zkc::checkNativeProof(*parsed, *constructed.module, selected))
      throw std::runtime_error(toString(std::move(error)));
    for (bool simplify : {false, true}) {
      zkc::NativeProofOptions options;
      options.policy = zkc::NativeProofSelection{policy};
      options.simplify = simplify;
      options.releaseStorage = simplify;
      auto compiled =
          take(zkc::compileNativeProof(take(emitOriginal(closed, context)),
                                       "construction.mlir", options, registry));
      require(compiled.policy.construction == policy.construction,
              "physical compilation retains selected construction");
    }
    auto changed = policy;
    changed.construction = "absent";
    refuses(zkc::selectNativeProofDraws(*parsed, changed),
            "native-proof-construction-selection");
    changed = policy;
    changed.construction.clear();
    refuses(zkc::selectNativeProofDraws(*parsed, changed),
            "native-proof-policy");
    auto rules = record.getRules();
    SmallVector<mlir::Attribute> missing(rules.getValue());
    missing.erase(missing.begin() + 1);
    mlir::Builder builder(&context);
    record.setRulesAttr(builder.getArrayAttr(missing));
    refuses(zkc::selectNativeProofDraws(*parsed, policy),
            "protocol-construction");
    record.setRulesAttr(rules);
  });
  auto compileSource = [&](StringRef source, bool collideSites = false,
                           StringRef entry = "m::Demo") {
    auto closed = take(closeEntry(take(checked(source)), entry));
    auto text = take(emitOriginal(closed, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
    require(bool(parsed), "parse construction source");
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    if (collideSites) {
      unsigned count = 0;
      unit.walk([&](zkc::local::FuncOp function) {
        bool changed = false;
        function.walk([&](mlir::Operation *op) {
          if (!changed && op->hasAttr("site")) {
            op->setAttr("site", mlir::StringAttr::get(&context, "bound"));
            changed = true;
            ++count;
          }
        });
      });
      require(count != 0, "raw Local functions contain sites to collide");
      text.clear();
      raw_string_ostream stream(text);
      parsed->print(stream);
    }
    auto record = *unit.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(record, symbols));
    mlir::SymbolTable table(unit);
    auto protocol =
        table.lookup<zkc::protocol_ir::MathematicalOp>(plan.target.getValue());
    zkc::NativeProofPolicy policy;
    policy.entry = plan.target.getValue().str();
    policy.construction = plan.symbol.getValue().str();
    policy.services.assign(plan.services.begin(), plan.services.end());
    policy.suite = plan.suite;
    policy.format = plan.codec ? zkc::protocol::ProofFormat::RawBytes
                               : zkc::protocol::ProofFormat::Native;
    policy.producer =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
    policy.validator =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
    for (auto [i, roles] : enumerate(protocol.getInputRoles()))
      if (!is_contained(plan.services, i) &&
          is_contained(mlir::cast<mlir::ArrayAttr>(roles),
                       protocol.getRoles()[1]))
        policy.publicInputs.push_back(i);
    auto selected = take(zkc::selectNativeProofDraws(*parsed, policy));
    auto result = take(zkc::constructNativeProof(*parsed, selected));
    for (bool simplify : {false, true}) {
      zkc::NativeProofOptions options;
      options.policy = zkc::NativeProofSelection{policy};
      options.simplify = simplify;
      options.releaseStorage = simplify;
      take(zkc::compileNativeProof(text, "construction.mlir", options,
                                   registry));
    }
    return std::make_tuple(std::move(parsed), std::move(result),
                           std::move(selected));
  };
  cases.run("record codecs lower through physical compilation", [&] {
    compileSource((program + deployment + codec).str(), false, "m::Packed");
  });
  cases.run(
      "record correspondence indexes many independent message sites", [&] {
        std::string source = (program + deployment + codec).str();
        std::string messages, selectors = "{commitment,response";
        for (unsigned i = 0; i < 200; ++i) {
          auto site = "extra_" + std::to_string(i);
          messages +=
              "#[site(" + site + ")] let " + site + "=send P->V(secret);\n";
          selectors += "," + site;
        }
        selectors += "}";
        auto at = source.find("#[site(commitment)]");
        require(at != std::string::npos, "message insertion anchor exists");
        source.insert(at, messages);
        for (at = 0; (at = source.find("{commitment,response}", at)) !=
                     std::string::npos;) {
          source.replace(at, StringRef("{commitment,response}").size(),
                         selectors);
          at += selectors.size();
        }
        compileSource(source, false, "m::Packed");
      });
  for (StringRef mutation :
       {"provider", "record", "layout", "group", "slice", "helper",
        "calculation", "large-body", "action-order", "helper-selection",
        "unknown-metadata", "reader-calculation"})
    cases.run(
        ("independent record checker refuses changed " + mutation).str(),
        [&, mutation] {
          auto input = (program + deployment + codec).str();
          if (mutation == "reader-calculation") {
            for (auto change :
                 {std::pair<StringRef, StringRef>{
                      "send P->V(secret);", "send P->V((secret,secret));"},
                  {"send P->V(secret+actual);",
                   "send P->V((secret+actual,secret));"},
                  {"last==first+c", "last.0==first.0+c"},
                  {"H::observe(t,value);", "H::observe(t,value.0);"},
                  {"(wire){return 0;}", "(wire){return (0,0);}"}}) {
              auto at = input.find(change.first.str());
              require(at != std::string::npos, "tuple fixture anchor exists");
              input.replace(at, change.first.size(), change.second.str());
            }
          }
          auto closed = take(closeEntry(take(checked(input)), "m::Packed"));
          auto text = take(emitOriginal(closed, context));
          auto source = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
          mlir::PassManager prepare(&context);
          prepare.addPass(zkc::protocol::createPrepareProtocolPass(false));
          require(mlir::succeeded(prepare.run(*source)),
                  "prepare codec reference");
          auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
              source->getBody()->front());
          auto record = *unit.getBody()
                             .front()
                             .getOps<zkc::protocol_ir::ConstructionOp>()
                             .begin();
          mlir::SymbolTableCollection symbols;
          auto plan =
              take(zkc::protocol::readConstructionPlan(record, symbols));
          mlir::SymbolTable table(unit);
          auto protocol = table.lookup<zkc::protocol_ir::MathematicalOp>(
              plan.target.getValue());
          zkc::NativeProofPolicy policy;
          policy.entry = plan.target.getValue().str();
          policy.construction = plan.symbol.getValue().str();
          policy.services.assign(plan.services.begin(), plan.services.end());
          policy.publicInputs = {0};
          policy.producer =
              mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
          policy.validator =
              mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
          SmallVector<mlir::Attribute> mathematical;
          for (auto rule : record.getRules())
            if (!zkc::protocol::isCodecRule(
                    *zkc::protocol::parseConstructionRuleKind(
                        mlir::cast<mlir::DictionaryAttr>(rule)
                            .getAs<mlir::StringAttr>("kind")
                            .getValue())))
              mathematical.push_back(rule);
          record.setRulesAttr(mlir::ArrayAttr::get(&context, mathematical));
          record.removeCodecAttr();
          policy = take(zkc::selectNativeProofDraws(*source, policy));
          auto transcript = take(zkc::constructNativeProof(*source, policy));
          SmallVector<zkc::detail::NativeTranscriptEvent> events;
          const auto &sequence =
              *(*transcript.descriptor.getAsArray())[3].getAsArray();
          protocol.walk<mlir::WalkOrder::PreOrder>([&](mlir::Operation *op) {
            auto query = mlir::dyn_cast<zkc::protocol_ir::QueryOp>(op);
            auto message = mlir::dyn_cast<zkc::protocol_ir::ExchangeOp>(op);
            if (!query && !message)
              return;
            auto origin =
                (*sequence[events.size()].getAsArray())[1].getAsString()->str();
            events.push_back({op->getAttrOfType<mlir::StringAttr>("site").str(),
                              origin,
                              query ? query.getResult(0).getType()
                                    : message.getInput().getType(),
                              bool(query), 0, std::nullopt});
          });
          if (mutation == "large-body") {
            // A long ordinary block should consume linear correspondence work.
            // Repeated full environment copies used to exhaust the budget here.
            transcript.module->walk(
                [&](zkc::protocol_ir::ParticipantOp participant) {
                  mlir::Operation *calculation = nullptr;
                  for (auto &op : participant.getBody().front())
                    if (op.getName().getStringRef() == "algebra.field_add") {
                      calculation = &op;
                      break;
                    }
                  require(calculation,
                          "participant has an ordinary calculation");
                  mlir::OpBuilder builder(&context);
                  builder.setInsertionPoint(
                      &participant.getBody().front().back());
                  for (unsigned i = 0; i < 2000; ++i)
                    builder.clone(*calculation);
                });
          }
          if (mutation == "reader-calculation") {
            transcript.module->walk(
                [&](zkc::protocol_ir::ParticipantOp participant) {
                  if (participant.getRole() != policy.validator)
                    return;
                  auto &body = participant.getBody().front();
                  auto first =
                      *body.getOps<zkc::protocol_ir::AwaitOp>().begin();
                  mlir::Operation *calculation = nullptr;
                  for (auto &op : body)
                    if (op.getName().getStringRef() == "algebra.field_add") {
                      calculation = &op;
                      break;
                    }
                  require(calculation, "verifier has an ordinary calculation");
                  mlir::OpBuilder builder(&context);
                  builder.setInsertionPointAfter(first);
                  auto *interleaved = builder.clone(*calculation);
                  interleaved->setOperand(0, first.getResult());
                  interleaved->setOperand(1, body.getArgument(0));
                  calculation->setOperand(0, interleaved->getResult(0));
                });
          }
          auto candidate = mlir::OwningOpRef<mlir::ModuleOp>(
              mlir::cast<mlir::ModuleOp>(transcript.module->clone()));
          auto exported =
              *(*transcript.descriptor.getAsArray())[6].getAsArray();
          exported.pop_back(); // The transport pass receives the
                               // transcript-only plan.
          auto transport = take(zkc::detail::constructNativeCodec(
              *candidate, policy, plan, events, exported));
          if (auto error = zkc::detail::verifyNativeCodec(
                  *transcript.module, *candidate, policy, plan, events,
                  exported, transport))
            throw std::runtime_error(toString(std::move(error)));
          if (mutation == "large-body" || mutation == "reader-calculation")
            return;
          bool metadata = mutation == "action-order" ||
                          mutation == "helper-selection" ||
                          mutation == "unknown-metadata";
          if (metadata) {
            auto module = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
                candidate->getBody()->front());
            auto projection = *module.getBody()
                                   .front()
                                   .getOps<zkc::protocol_ir::ProjectionOp>()
                                   .begin();
            auto original =
                mlir::cast<mlir::DictionaryAttr>(projection.getInterfaces()[0]);
            mlir::NamedAttrList construction(
                original.getAs<mlir::DictionaryAttr>("construction"));
            mlir::Builder builder(&context);
            if (mutation == "unknown-metadata")
              construction.set("unexpected", builder.getUnitAttr());
            else if (mutation == "helper-selection")
              construction.set("helpers", builder.getArrayAttr({}));
            else {
              auto actions =
                  mlir::cast<mlir::ArrayAttr>(construction.get("actions"));
              SmallVector<mlir::Attribute> reversed(llvm::reverse(actions));
              construction.set("actions", builder.getArrayAttr(reversed));
            }
            mlir::NamedAttrList interface(original);
            interface.set("construction", construction.getDictionary(&context));
            projection.setInterfacesAttr(
                builder.getArrayAttr({interface.getDictionary(&context)}));
          } else if (mutation == "provider")
            transport[0] = "different-provider";
          else if (mutation == "record")
            transport[1] = json::Array{"index"};
          else if (mutation == "layout")
            transport[5] = json::Array{"1"};
          else if (mutation == "group")
            (*(*transport[6].getAsArray())[0].getAsArray())[5] = json::Array{};
          else if (mutation == "slice") {
            auto name = (*(*transport[6].getAsArray())[0].getAsArray())[4]
                            .getAsString()
                            ->str();
            auto module = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
                candidate->getBody()->front());
            auto f = mlir::SymbolTable(module).lookup<zkc::local::FuncOp>(name);
            auto &op = f.getBody().front().front();
            op.setOperand(1, op.getOperand(2));
          } else if (mutation == "helper") {
            auto module = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
                candidate->getBody()->front());
            auto f = mlir::SymbolTable(module).lookup<zkc::local::FuncOp>(
                plan.codec->finish.getValue());
            // Preserve the function type and add an unrelated data operation.
            mlir::OpBuilder builder(&context);
            builder.setInsertionPoint(&f.getBody().front().back());
            zkc::local::BoolConstantOp::create(
                builder, f.getLoc(), builder.getI1Type(),
                builder.getBoolAttr(true), builder.getStringAttr("extra"));
          } else {
            bool changed = false;
            candidate->walk([&](zkc::protocol_ir::ParticipantOp participant) {
              participant.walk([&](mlir::Operation *op) {
                if (!changed &&
                    op->getName().getStringRef() == "algebra.field_add") {
                  op->setOperand(0, op->getOperand(1));
                  changed = true;
                }
              });
            });
            require(changed, "fixture contains a retained calculation");
          }
          auto error = zkc::detail::verifyNativeCodec(
              *transcript.module, *candidate, policy, plan, events, exported,
              transport);
          require(bool(error) &&
                      namesIdentifier(toString(std::move(error)),
                                      metadata ? "native-codec-subject"
                                               : "native-codec-correspondence"),
                  "independent codec checker refuses mutation");
        });
  cases.run("index adapters allocate fresh sites around existing Local code",
            [&] {
              compileSource(R"(module m;
      domain F=field("koala-bear.ext8-binomial3");
      math fn less(x:index,y:index)->bool=primitive("index.less");
      interface ProviderType {type State:Copy+Drop;fn initialize()->State effects(stop, opaque);}
      module Provider:ProviderType {
        type State:Copy+Drop=();
        fn initialize()->State{return State(());}
      }
      protocol Choose roles(P,V)(challenges:Random<F>@V)->(ok:bool@V){
        #[site(pick)] let chosen=challenges.index<8>();
        #[site(delivery)] let received=send V->P(chosen);
        return true;
      }
      construction Custom for Choose {
        transcript Provider;replace challenges;
        on start(t){return t;}
        on query pick(t,bound){require less(0,bound);return(t,0);}
        on message delivery(t,value){return t;}
      }
      proof Demo=Choose{prover P;verifier V;public{};accept ok;construction Custom;}
    )",
                            true);
            });
  cases.run("managed methods retain selected handler authority", [&] {
    auto source =
        program.take_front(program.find("construction Derived")).str();
    source += R"(
      domain NativeSuite=transcript("merlin3.bls12-381.fr64be/0");
      type State=builtin("transcript",NativeSuite);
      type Bytes=builtin("bytes");
      fn empty()->Bytes=primitive("bytes.empty");
      fn sample(t:State,label:Bytes)->(State,F)=primitive("transcript.challenge");
      construction Managed for Round<F> {
        base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);
        on query challenge(t){let (t,v)=sample(t,empty());return(t,v);}
      }
      proof Demo=Round<F>{prover P;verifier V;public{public};accept ok;
        construction Managed;}
    )";
    auto [original, built, policy] = compileSource(source);
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        original->getBody()->front());
    auto record = *unit.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(record, symbols));
    mlir::SymbolTable table(unit);
    auto handler =
        table.lookup<zkc::local::FuncOp>(plan.rules.front().handler.getValue());
    auto clone = mlir::cast<zkc::local::FuncOp>(handler->clone());
    mlir::SymbolTable::setSymbolName(clone, "unselected_managed_handler");
    unit.getBody().front().push_back(clone);
    require(mlir::succeeded(mlir::verify(*original)),
            "unselected affine function remains well typed");
    policy.draws.clear();
    refuses(zkc::selectNativeProofDraws(*original, policy),
            "native-proof-authored-transcript");
  });
  cases.run("local state crosses nested protocol loops", [&] {
    auto source = replace("  #[site(commitment)]", R"(
      let mut accepted @V = true;
      for _ in 0..rounds roles(P,V) max 2 {
        for _ in 0..rounds roles(P,V) max 2 {
          #[site(commitment)])");
    source.insert(source.find("secret:T@P"), "rounds:index@(P,V),");
    auto at = source.find("return last==first+c;");
    source.replace(at, StringRef("return last==first+c;").size(),
                   "accepted = last==first+c;}} return accepted;");
    auto provider = deployment.str();
    provider.replace(provider.find("public{public}"),
                     StringRef("public{public}").size(),
                     "public{public,rounds}");
    compileSource(source + provider);
  });
  cases.run("zero-slot local state still has ordered transitions", [&] {
    auto provider = deployment.str();
    auto at = provider.find("(index,index)");
    provider.replace(at, StringRef("(index,index)").size(), "()");
    at = provider.find("State((0,0))");
    provider.replace(at, StringRef("State((0,0))").size(), "State(())");
    compileSource(program.str() + provider);
  });
  cases.run("same-typed state substitution fails source correspondence", [&] {
    auto [original, built, policy] =
        compileSource((program + deployment).str());
    auto before = mlir::OwningOpRef<mlir::ModuleOp>(
        mlir::cast<mlir::ModuleOp>(original->clone()));
    mlir::PassManager prepare(&context);
    prepare.addPass(zkc::protocol::createPrepareProtocolPass(false));
    require(mlir::succeeded(prepare.run(*before)), "prepare reference subject");
    auto reference = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        before->getBody()->front());
    auto record = *reference.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(record, symbols));
    SmallVector<zkc::detail::NativeTranscriptEvent> events;
    const auto &sequence = *(*built.descriptor.getAsArray())[3].getAsArray();
    reference.walk<mlir::WalkOrder::PreOrder>([&](mlir::Operation *op) {
      auto query = mlir::dyn_cast<zkc::protocol_ir::QueryOp>(op);
      auto message = mlir::dyn_cast<zkc::protocol_ir::ExchangeOp>(op);
      if (!query && !message)
        return;
      auto origin =
          (*sequence[events.size()].getAsArray())[1].getAsString()->str();
      events.push_back(
          {op->getAttrOfType<mlir::StringAttr>("site").str(), origin,
           query ? query.getResult(0).getType() : message.getInput().getType(),
           bool(query), 0, std::nullopt});
    });
    record.erase();
    mlir::PassManager project(&context);
    project.addPass(zkc::protocol::createProjectProtocolPass(false));
    require(mlir::succeeded(project.run(*before)), "project reference subject");
    if (auto error = zkc::detail::verifyNativeTranscript(*before, *built.module,
                                                         policy, events, &plan))
      throw std::runtime_error(toString(std::move(error)));
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        built.module->getBody()->front());
    auto participant = *unit.getBody()
                            .front()
                            .getOps<zkc::protocol_ir::ParticipantOp>()
                            .begin();
    auto calls = participant.getBody().front().getOps<zkc::local::CallOp>();
    auto iterator = calls.begin();
    auto factory = *iterator++;
    auto start = *iterator++;
    auto observation = *iterator;
    require(factory.getNumResults() == 2 && start.getNumResults() == 2 &&
                observation.getInputs()[0] == start.getResult(0),
            "fixture contains distinct factory, start and observation states");
    observation->setOperand(0, factory.getResult(0));
    require(mlir::succeeded(mlir::verify(*built.module)),
            "copyable-state substitution remains well typed");
    auto error = zkc::checkNativeProof(*original, *built.module, policy);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "native-proof-correspondence"),
            "bypassed start successor must refuse");
    error = zkc::detail::verifyNativeTranscript(*before, *built.module, policy,
                                                events, &plan);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "native-transcript-correspondence"),
            "independent checker refuses bypassed start state");
    observation->setOperand(0, start.getResult(0));
    mlir::SymbolTable table(unit);
    auto helper = table.lookup<zkc::local::FuncOp>(observation.getCallee());
    auto returned =
        mlir::cast<zkc::local::ReturnOp>(helper.getBody().front().back());
    require(returned.getNumOperands() == 2 &&
                returned.getInputs()[0] != returned.getInputs()[1],
            "handler returns two distinct state slots");
    returned->setOperand(0, returned.getInputs()[1]);
    require(mlir::succeeded(mlir::verify(*built.module)),
            "changed copyable handler remains well typed");
    error = zkc::detail::verifyNativeTranscript(*before, *built.module, policy,
                                                events, &plan);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "native-transcript-correspondence"),
            "independent checker refuses changed selected handler body");
  });
  cases.run("inherited construction checking respects the work budget", [&] {
    std::string source = program.str();
    for (unsigned i = 0; i < 24; ++i) {
      auto parent = i ? "Layer" + std::to_string(i - 1) : "Derived";
      source += "construction Layer" + std::to_string(i) +
                "<T:Field,H:TestTranscript<T>> for Round<T>{base " + parent +
                "<T,H>;}";
    }
    auto project = take(checked(source));
    Limits limits;
    limits.work = project.checkedWork() - 1;
    refuses(checked(source, limits), "source.limit");
  });
  cases.run("repeated handler copies have a separate construction budget", [&] {
    std::string messages, labels;
    for (unsigned i = 0; i < 24; ++i) {
      auto label = "extra" + std::to_string(i);
      messages += "#[site(" + label + ")] let ignored" + std::to_string(i) +
                  "=send P->V(secret);";
      labels += "," + label;
    }
    auto source =
        replace("return last==first+c;", messages + "return last==first+c;");
    auto at = source.find("{commitment,response}");
    require(at != std::string::npos, "message selectors exist");
    source.replace(at, StringRef("{commitment,response}").size(),
                   "{commitment,response" + labels + "}");
    auto project = take(checked(source + deployment.str()));
    auto closed = take(closeEntry(project, "m::Demo"));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(
        take(emitOriginal(closed, context)), &context);
    require(bool(parsed), "budget fixture parses");
    auto unit = mlir::cast<zkc::protocol_ir::ProtocolModuleOp>(
        parsed->getBody()->front());
    auto record = *unit.getBody()
                       .front()
                       .getOps<zkc::protocol_ir::ConstructionOp>()
                       .begin();
    mlir::SymbolTableCollection symbols;
    auto plan = take(zkc::protocol::readConstructionPlan(record, symbols));
    mlir::SymbolTable table(unit);
    auto message = llvm::find_if(plan.rules, [](const auto &rule) {
      return rule.kind == zkc::protocol::ConstructionRuleKind::Message;
    });
    require(message != plan.rules.end(), "message handler exists");
    auto handler =
        table.lookup<zkc::local::FuncOp>(message->handler.getValue());
    mlir::OpBuilder builder(&context);
    builder.setInsertionPoint(&handler.getBody().front().back());
    for (unsigned i = 0; i < 12000; ++i) {
      zkc::local::BoolConstantOp::create(
          builder, handler.getLoc(), builder.getBoolAttr(false),
          builder.getStringAttr("cost" + std::to_string(i)));
    }
    SmallVector<mlir::Attribute> rules;
    for (auto item : record.getRules()) {
      mlir::NamedAttrList rule(mlir::cast<mlir::DictionaryAttr>(item));
      if (rule.get("kind") == builder.getStringAttr("message"))
        rule.set("handler", message->handler);
      rules.push_back(rule.getDictionary(&context));
    }
    record.setRulesAttr(builder.getArrayAttr(rules));
    require(mlir::succeeded(mlir::verify(*parsed)),
            "one large handler remains well formed before repeated copying");
    zkc::NativeProofPolicy policy;
    policy.entry = plan.target.getValue().str();
    policy.construction = plan.symbol.getValue().str();
    policy.services.assign(plan.services.begin(), plan.services.end());
    policy.publicInputs = {0};
    auto protocol =
        table.lookup<zkc::protocol_ir::MathematicalOp>(policy.entry);
    policy.producer =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
    policy.validator =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
    auto selected = take(zkc::selectNativeProofDraws(*parsed, policy));
    refuses(zkc::constructNativeProof(*parsed, selected),
            "native-proof-construction-limit");
  });
  cases.run("selectors descend through labelled protocol applications", [&] {
    auto text = replace("protocol Round<T:", "protocol Child<T:");
    const auto declaration = text.find("construction Derived");
    text.insert(declaration, R"(
      protocol Round<T:Field> roles(P,V)
          (public:T@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
        #[site(part)] let accepted=Child<T> roles(P,V)(public,secret,challenges);
        return accepted;
      }
    )");
    for (StringRef name : {"commitment", "response", "delivery", "challenge"}) {
      auto start = text.find("construction Derived");
      auto position = text.find(name.str(), start);
      // Authority replacement precedes the challenge selector.
      if (name == "challenge")
        position = text.find("challenge(t)", start);
      require(position != std::string::npos, "selector found");
      text.insert(position, "part.");
    }
    take(checked(text));
  });
  cases.run("native base keeps its provider", [&] {
    auto text = replace(
        "transcript H;\n  replace challenges;",
        "base "
        "fiat_shamir(\"merlin3.bls12-381.fr64be/0\",challenges);transcript H;");
    refuses(checked(text), "source.construction");
  });
  const std::vector<std::pair<std::string, std::string>> invalid = {
      {"on query challenge(t)", "on query absent(t)"},
      {"on query challenge(t)", "on message challenge(t,value)"},
      {"on query challenge(t)", "on query challenge(t,extra)"},
      {"on start(t,public)", "on start(t,secret)"},
      {"on start(t,public)", "on start(t,absent)"},
      {"on message {commitment,response}",
       "on message {commitment,commitment}"},
      {"on message {commitment,response}", "on message commitment"},
      {"transcript H;", ""},
      {"replace challenges;", "replace absent;"},
      {"replace challenges;",
       "replace challenges; base "
       "fiat_shamir(\"merlin3.bls12-381.fr64be/0\",challenges);"},
      {"on message delivery(t,value)", "on message delivery(t,value:bool)"},
      {"fn initialize()->State effects(stop, opaque);",
       "fn initialize(v:T)->State effects(stop, opaque);"},
  };
  for (const auto &change : invalid)
    cases.run(change.second, [&] {
      refuses(checked(replace(change.first, change.second)),
              "source.construction");
    });
  cases.run("invalid handler body is checked as Local code", [&] {
    refuses(checked(replace("return H::draw(t);", "return true;")),
            "source.type");
  });
  cases.run("base cycles refuse", [&] {
    refuses(checked((program + R"(
      construction A<T:Field,H:TestTranscript<T>> for Round<T>{base B<T,H>;}
      construction B<T:Field,H:TestTranscript<T>> for Round<T>{base A<T,H>;}
    )")
                        .str()),
            "source.construction");
  });
  cases.run("named authored bases retain the format-only contract", [&] {
    take(checked(R"(module m;
      protocol P roles(A,B)(ok:bool@B)->(ok:bool@B){return ok;}
      construction A for P{base authored;format RawBytes;}
      construction B for P{base A;}
    )"));
  });
  cases.run("construction depth is independent of declaration order", [&] {
    std::vector<std::string> definitions{
        "construction C0 for P{base authored;}"};
    for (unsigned i = 1; i <= 70; ++i)
      definitions.push_back("construction C" + std::to_string(i) +
                            " for P{base C" + std::to_string(i - 1) + ";}");
    auto source = [&](ArrayRef<std::string> ordered) {
      std::string text = "module m; protocol P roles(A,B)(ok:bool@B)"
                         "->(ok:bool@B){return ok;}";
      for (const auto &definition : ordered)
        text += definition;
      return text;
    };
    take(checked(source(ArrayRef<std::string>(definitions).take_front(5))));
    refuses(checked(source(definitions)), "source.limit");
    std::reverse(definitions.begin(), definitions.end());
    refuses(checked(source(definitions)), "source.limit");
  });
  cases.run("provider helpers do not extend an interface contract", [&] {
    auto text = replace("fn initialize()->State effects(stop, opaque);", "");
    refuses(checked(text + deployment.str()), "source.construction");
  });
  cases.run("codec helpers do not extend an interface contract", [&] {
    auto text = (program + deployment + codec).str();
    auto begin =
        text.find("fn write(record:Record)->Bytes effects(stop, opaque);");
    require(begin != std::string::npos,
            "codec interface fixture member missing");
    text.erase(
        begin,
        StringRef("fn write(record:Record)->Bytes effects(stop, opaque);")
            .size());
    refuses(checked(text), "source.construction");
  });
  for (StringRef argument :
       {"callback:fn()->bool effects()", "rows:domain<bool>"}) {
    auto addArgument = [&](StringRef source, StringRef method) {
      std::string text = source.str(), prefix = "fn " + method.str() + "(";
      size_t position = 0;
      unsigned changed = 0;
      while ((position = text.find(prefix, position)) != std::string::npos) {
        position += prefix.size();
        std::string addition = argument.str();
        if (text[position] != ')')
          addition += ',';
        text.insert(position, addition);
        position += addition.size();
        ++changed;
      }
      require(changed == 2, "interface and implementation method not found");
      return text;
    };
    cases.run("transcript factory rejects extra " + argument.str(), [&] {
      refuses(checked(addArgument((program + deployment).str(), "initialize")),
              "source.construction");
    });
    for (StringRef method : {"initialize", "write", "finish"})
      cases.run("codec " + method.str() + " rejects extra " + argument.str(),
                [&] {
                  refuses(checked(program.str() + deployment.str() +
                                  addArgument(codec, method)),
                          "source.construction");
                });
  }
  return cases.result();
}
