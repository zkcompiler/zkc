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
  fn initialize()->State;
  fn observe(t:State,v:T)->State;
  fn draw(t:State)->(State,T);
}
protocol Round<T:Field+Share+Wire> roles(P,V)
    (public:T@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
  #[site(commitment)] let first=send P->V(secret);
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  #[site(response)] let last=send P->V(secret+actual);
  return last==first+c;
}
construction Derived<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{
  transcript H;
  replace challenges;
  on start(t,public){return H::observe(t,public);}
  on message {commitment,response}(t,value){return H::observe(t,value);}
  on message delivery(t,value){return t;}
  on query challenge(t){return H::draw(t);}
}
)";
constexpr StringLiteral deployment = R"(
      component Provider:TestTranscript<F>{
        type State:Copy+Drop=(index,index);
        fn initialize()->State{return State((0,0));}
        fn observe(t:State,v:F)->State{return t;}
        fn draw(t:State)->(State,F){return (t,1);}
      }
      proof Demo=Round<F>{prover P;verifier V;public{public};accept ok;
        construction Derived<F,Provider>;}
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
      construction Changed<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{
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
            require(declaration.getString("replace") == "challenges" &&
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
    policy.service = plan.service;
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
            "native-proof-construction-coverage");
    record.setRulesAttr(rules);
  });
  auto compileSource = [&](StringRef source, bool collideSites = false) {
    auto closed = take(closeEntry(take(checked(source)), "m::Demo"));
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
    policy.service = plan.service;
    policy.suite = plan.suite;
    policy.producer =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[0]).str();
    policy.validator =
        mlir::cast<mlir::StringAttr>(protocol.getRoles()[1]).str();
    for (auto [i, roles] : enumerate(protocol.getInputRoles()))
      if (i != plan.service && is_contained(mlir::cast<mlir::ArrayAttr>(roles),
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
  cases.run("index adapters allocate fresh sites around existing Local code",
            [&] {
              compileSource(R"(module m;
      domain F=field("koala-bear.ext8-binomial3");
      fn less(x:index,y:index)->bool=primitive("index.less");
      interface ProviderType {type State:Copy+Drop;fn initialize()->State;}
      component Provider:ProviderType {
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
                "<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{base " +
                parent + "<T,H>;}";
    }
    auto project = take(checked(source));
    Limits limits;
    limits.work = project.checkedWork() - 1;
    refuses(checked(source, limits), "source.limit");
  });
  cases.run("selectors descend through labelled protocol applications", [&] {
    auto text = replace("protocol Round<T:", "protocol Child<T:");
    const auto declaration = text.find("construction Derived");
    text.insert(declaration, R"(
      protocol Round<T:Field+Share+Wire> roles(P,V)
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
      {"fn initialize()->State;", "fn initialize(v:T)->State;"},
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
      construction A<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{base B<T,H>;}
      construction B<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{base A<T,H>;}
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
  return cases.result();
}
