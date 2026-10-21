#include "../lib/Language/BindingWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace source_detail = zkc::language::detail;
namespace {
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"sample", source.str(), "sample.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Expected<ClosedEntry> close(StringRef source, StringRef name = "sample::Demo",
                            const Limits &limits = {}) {
  auto checked = check(source, limits);
  if (!checked)
    return checked.takeError();
  return closeEntry(*checked, name, limits, EntryKind::Function);
}
const Declaration &definition(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}
constexpr StringLiteral protocol = R"(
module sample;
domain F=field("bls12-381.fr");
pub protocol Work<C:Field> roles(P,V)(x:C@(P,V),y:C@P)->(value:C@P,ok:bool@V){
  let ok@V=true;return(value=x,ok=ok);
}
)";
constexpr StringLiteral proof = R"(
module sample;
protocol Work roles(P,V)(x:bool@(P,V),y:bool@P)->(value:bool@P,ok:bool@V){
  let ok@V=x;return(value=y,ok=ok);
}
pub proof Family=Work{prover P;verifier V;public{x};accept ok;construction authored;}
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("concrete protocols expose their generated run as an Entry", [] {
    auto project = take(check(R"(module sample;
      protocol Echo roles(P,V)(value:bool@P)->(received:bool@V){
        let received=send P->V(value);return received;
      }
    )"));
    require(project.entries().size() == 1,
            "default run entry is absent or duplicated");
    for (StringRef name : {"", "Echo", "sample::Echo"}) {
      auto entry = take(closeEntry(project, name, {}, EntryKind::Function));
      require(entry.entry().entryName() == "sample::Echo" &&
                  entry.root().qualifiedName == "sample::Echo::run" &&
                  entry.root().body->stage == Body::Stage::Host &&
                  entry.invocations().size() == 1 &&
                  entry.invocations().front().kind == HostInvocation::Kind::Run,
              "default run bypassed the entry-function closure");
    }
    refuses(closeEntry(project, "Echo", {}, EntryKind::Proof),
            "source.entry-kind");
    refuses(selectEntry(project, "sample::Echo::run"), "source.entry");
  });
  cases.run("generic protocols require an explicit closed Entry", [] {
    auto project = take(check(protocol));
    require(project.entries().empty(),
            "generic protocol acquired an implicit specialization");
    refuses(selectEntry(project, "Work"), "source.entry");
    take(close((protocol + R"(
      entry fn Demo(inputs:Work<F>::Inputs){return Work<F>::run(inputs);}
    )")
                   .str()));
  });
  cases.run("an unused protocol does not enter a calculation closure", [] {
    auto entry = take(close(R"(module sample;
      protocol Unused roles(P)(value:bool@P)->(out:bool@P){return value;}
      entry fn Demo(value:index){return value+1;}
    )"));
    require(entry.invocations().empty() && !entry.protocolOrNull(),
            "default run body introduced an unreachable deployment");
    require(entry.entry().entryName() == "sample::Demo" &&
                entry.root().qualifiedName == "sample::Demo",
            "default run body replaced the authored root");
  });
  cases.run("standalone calculation closes without a protocol", [] {
    auto entry =
        take(close("module sample; entry fn Demo(x:index){return x+1;}"));
    require(!entry.protocolOrNull() && entry.invocations().empty(),
            "calculation acquired a protocol");
    require(entry.entry().entryKind() == EntryKind::Function &&
                entry.root().body &&
                entry.root().body->mode == Body::Mode::Local &&
                entry.root().body->stage == Body::Stage::Host,
            "entry body lost Local operations or Host stage");
  });
  cases.run("generated inputs complete bound module members lazily", [] {
    auto entry = take(close(R"(module sample;
      entry fn Demo(inputs: Work<Identity>::Inputs) {
        return Work<Identity>::run(inputs);
      }
      interface Algebra { fn identity(value:index)->index effects(); }
      module Identity:Algebra {
        fn identity(value:index)->index{return value;}
      }
      protocol Work<A:Algebra> roles(P)(value:index@P)->(result:index@P) {
        let result@P=A::identity(value);return(result=result);
      }
    )"));
    require(entry.invocations().size() == 1,
            "generated protocol constructor lost its bound member closure");
  });
  cases.run("ordinary static entry calls share closure and infer results", [] {
    auto entry = take(close(R"(module sample;
      entry fn Twice(x:index){return x+x;}
      entry fn Demo(x:index){return Twice(Twice(x));}
    )"));
    unsigned functions = 0;
    for (const auto &decl : entry.declarations())
      functions +=
          decl.kind == Declaration::Kind::EntryFunction && bool(decl.body);
    require(functions == 2, "static closure duplicated or omitted functions");
  });
  cases.run("entry recursion is refused including dormant calls", [] {
    refuses(
        check("module sample; entry fn Demo(x:bool)->bool{return Demo(x);}"),
        "source.cycle");
    refuses(check("module sample; entry fn A(x:bool)->bool{return B(x);} entry "
                  "fn B(x:bool)->bool{return A(x);}"),
            "source.cycle");
  });
  cases.run("ordinary Local and Math cannot invoke entry functions", [] {
    refuses(check("module sample; entry fn E(x:bool){return x;} fn "
                  "Bad(x:bool){return E(x);}"),
            "source.stage");
    refuses(check("module sample; entry fn E(x:bool){return x;} math fn "
                  "Bad(x:bool){return E(x);}"),
            "source.stage");
  });
  cases.run("independent call witnesses require the Host owner stage", [] {
    auto checked = take(check(R"(module sample;
      entry fn Echo(x:bool){return x;}
      entry fn Demo(x:bool){return Echo(x);}
    )"));
    std::vector<Declaration> declarations(checked.declarations().begin(),
                                          checked.declarations().end());
    Body body = *definition(checked, "sample::Demo").body;
    body.stage = Body::Stage::Computation;
    source_detail::Work work{Limits{}};
    source_detail::Semantics types(declarations, checked.assets(), work);
    require(!source_detail::checkCallAction(types, declarations, body,
                                            body.operations.front()) &&
                types.diagnostic &&
                types.diagnostic->code == "source.binding-witness",
            "call witness granted Host stage to a computation body");
  });
  cases.run("participant code cannot invoke entry functions", [] {
    refuses(check(R"(module sample; entry fn E(x:bool){return x;}
      protocol Bad roles(P)(x:bool@P)->(y:bool@P){let y@P=E(x);return(y=y);})"),
            "source.stage");
  });
  cases.run("Host stage propagates through structured control", [] {
    take(close("module sample; entry fn E(x:bool){return x;} entry fn "
               "Demo(x:bool){return if x {E(x)} else {false};}"));
  });
  cases.run("generic protocol API parses with natural member syntax", [] {
    auto entry = take(close((protocol + R"(
      entry fn Demo(inputs:Work<F>::Inputs)->Work<F>::RunResult{
        return Work<F>::run(inputs);
      })")
                                .str()));
    require(entry.invocations().size() == 1, "missing closed invocation");
    const auto &call = entry.invocations().front();
    require(call.kind == HostInvocation::Kind::Run &&
                call.arguments.size() == 1 && call.deployment &&
                call.deployment->protocolOrNull() &&
                call.deployment->invocationKind() == HostInvocation::Kind::Run,
            "joint deployment lost operation or closed arguments");
  });
  cases.run("generated inputs retain independent participant copies", [] {
    auto checked =
        take(check((protocol + "entry fn Demo(){return ();}").str()));
    const auto &inputs = definition(checked, "sample::Work::Inputs");
    const auto &p = definition(checked, "sample::Work::Inputs::P");
    const auto &v = definition(checked, "sample::Work::Inputs::V");
    require(inputs.fields.size() == 2 && p.fields.size() == 2 &&
                v.fields.size() == 1,
            "input schema collapsed participant copies");
    require(p.generated->role == 0 && v.generated->role == 1 &&
                p.generated->ports.front().port ==
                    v.generated->ports.front().port,
            "role mapping lost shared logical port identity");
  });
  cases.run(
      "generated role inputs can be constructed with generic owner syntax", [] {
        take(close((protocol + R"(
      entry fn Demo(x:F,y:F)->Work<F>::RunResult{
        let p=Work<F>::Inputs::P{x:x,y:y};
        let v=Work<F>::Inputs::V{x:x};
        return Work<F>::run(Work<F>::Inputs{P:p,V:v});
      })")
                       .str()));
      });
  cases.run("generated operations require the Host stage", [] {
    refuses(
        check((protocol + "fn Bad(x:Work<F>::Inputs){return Work<F>::run(x);}")
                  .str()),
        "source.stage");
  });
  cases.run("joint invocation closure preserves native message refusals", [] {
    refuses(close(R"(module sample;
      protocol Work roles(P,V)(x:()@P)->(ok:bool@V){
        let delivered=send P->V(x);let ok@V=true;return(ok=ok);}
      entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);}
    )"),
            "source.wire");
  });
  cases.run("generated operations retain ordered failure effects", [] {
    refuses(check((protocol + R"(
      entry fn Demo(x:Work<F>::Inputs)->Work<F>::RunResult effects(){
        return Work<F>::run(x);
      })")
                      .str()),
            "source.effect");
  });
  cases.run("native result records cannot be forged in their owner module", [] {
    refuses(check((protocol + R"(entry fn Demo(x:F){
      return Work<F>::RunResult::P{value:x};})")
                      .str()),
            "source.host-result");
  });
  cases.run("static generated calls enforce target nominal identity", [] {
    refuses(check((protocol + R"(
      protocol Other<C:Field> roles(P,V)(x:C@(P,V),y:C@P)->(value:C@P,ok:bool@V){
        let ok@V=true;return(value=x,ok=ok);}
      entry fn Demo(x:Other<F>::Inputs){return Work<F>::run(x);})")
                      .str()),
            "source.type");
  });
  cases.run(
      "candidate proof is data and verifier has no witness parameter", [] {
        auto entry = take(close((proof + R"(
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);
      })")
                                    .str()));
        require(entry.invocations().size() == 1 &&
                    entry.invocations()[0].kind ==
                        HostInvocation::Kind::Verify &&
                    entry.invocations()[0].deployment->invocationKind() ==
                        HostInvocation::Kind::Verify,
                "verifier acquired another operation policy");
        auto &verify = definition(entry.project(), "sample::Family::verify");
        require(verify.inputs.size() == 2 && verify.inputs[1].name == "proof",
                "verifier requires producer data");
      });
  cases.run(
      "verifier closure does not require producer input constructors", [] {
        auto source = R"(module sample;
      #[sealed] struct Secret{pub value:bool}
      protocol Work roles(P,V)(x:bool@(P,V),secret:Secret@P)->(ok:bool@V){
        let ok@V=x;return(ok=ok);}
      proof Family=Work{prover P;verifier V;public{x};accept ok;construction authored;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);}
    )";
        auto entry = take(close(source));
        require(entry.invocations().size() == 1, "verifier closure missing");
        refuses(
            closeEntry(entry.project(), "sample::Family", {}, EntryKind::Proof),
            "source.ingress");
      });
  cases.run("lazy proof APIs retain ordinary arithmetic operator resolution",
            [] {
              take(close(R"(module sample;
      domain F=field("bls12-381.fr");
      protocol Work roles(P,V)(x:F@(P,V),y:F@P)->(ok:bool@V){
        let ok@V=x==x;return(ok=ok);}
      proof Family=Work{prover P;verifier V;public{x};accept ok;construction authored;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);}
    )"));
            });
  cases.run(
      "generated verifier APIs retain a selected transcript construction", [] {
        auto entry = take(close(R"(module sample;
      domain F=field("bls12-381.fr");
      interface RoundTranscript<T:Field>{
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
      construction Derived<T:Field,H:RoundTranscript<T>> for Round<T>{
        transcript H;replace challenges;
        on start(t,public){return H::observe(t,public);}
        on message {commitment,response}(t,value){return H::observe(t,value);}
        on message delivery(t,value){return t;}
        on query challenge(t){return H::draw(t);}
      }
      module Provider:RoundTranscript<F>{
        type State:Copy+Drop=(index,index);
        fn initialize()->State{return State((0,0));}
        fn observe(t:State,v:F)->State{return t;}
        fn draw(t:State)->(State,F){return (t,1);}
      }
      proof Family=Round<F>{prover P;verifier V;public{public};accept ok;
        construction Derived<F,Provider>;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);}
    )"));
        const auto &deployment = *entry.invocations().front().deployment;
        require(deployment.entry().proof()->selectedConstruction &&
                    deployment.invocationKind() == HostInvocation::Kind::Verify,
                "verifier lost the checked construction selection");
      });
  cases.run(
      "lazy proof specifications resolve later generic relation signatures",
      [] {
        auto entry = take(close(R"(module sample;
      proof Family=Work<F>{prover P;verifier V;public{x};accept ok;
        target claim;construction authored;}
      domain F=field("bls12-381.fr");
      protocol Work<T:Field> roles(P,V)(x:T@(P,V),y:T@P)->(ok:bool@V)
        spec{target claim=Equal<T>(in.x@V,in.y) accept out.ok;}
        {let ok@V=x==x;return(ok=ok);}
      relation Equal<T:Field>(statement x:T,witness y:T){return x==y;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);}
    )"));
        require(entry.invocations()
                        .front()
                        .deployment->protocol()
                        .specifications.size() == 1,
                "closed verifier lost its generic specification");
      });
  cases.run("verification rejection has no success outputs", [] {
    auto checked = take(check((proof + "entry fn Demo(){return ();}").str()));
    auto &result = definition(checked, "sample::Family::VerifyResult");
    require(result.kind == Declaration::Kind::Variant &&
                result.alternatives.size() == 2 &&
                result.alternatives[0].name == "Accepted" &&
                result.alternatives[0].fields.size() == 1 &&
                result.alternatives[1].name == "Rejected" &&
                result.alternatives[1].fields.empty(),
            "rejection conflated with Boolean data or outputs");
  });
  cases.run(
      "verification results are inspectable through exhaustive match", [] {
        take(close(
            (proof +
             R"(entry fn Demo(public:Family::Public,candidate:Family::Proof){
      let result=Family::verify(public,candidate);
      return match result {Accepted(outputs)=>{true},Rejected()=>{false}};
    })")
                .str()));
      });
  cases.run("native results can cross ordinary static entry calls in memory",
            [] {
              take(close((proof + R"(
      entry fn Retain(x:Family::VerifyResult){return x;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Retain(Family::verify(public,candidate));
      })")
                             .str()));
            });
  cases.run("candidate import does not grant native result construction", [] {
    refuses(check((proof +
                   "entry fn Demo(){return Family::VerifyResult::Rejected();}")
                      .str()),
            "source.host-result");
    refuses(
        check((proof +
               "entry fn Demo(p:Family::Proof,o:Family::ProverOutputs){return "
               "Family::ProveResult{proof:p,outputs:o};}")
                  .str()),
        "source.host-result");
  });
  cases.run("distinct proof declarations retain distinct nominal candidates",
            [] {
              refuses(check((proof + R"(
      proof Other=Work{prover P;verifier V;public{x};accept ok;construction authored;}
      entry fn Demo(public:Family::Public,p:Other::Proof){return Family::verify(public,p);})")
                                .str()),
                      "source.type");
            });
  cases.run(
      "source discovery exposes entry signatures and generated constructors",
      [] {
        auto checked =
            take(check((proof + "pub entry fn Demo(x:bool){return x;}").str()));
        auto entries = take(inspectEntries(checked));
        auto api = take(inspectPublicAPI(checked));
        auto graph = take(json::parse(api));
        auto *nodes = graph.getAsObject()->getArray("declarations");
        require(nodes, "public API declaration graph missing");
        const json::Object *function = nullptr, *verify = nullptr,
                           *result = nullptr;
        for (const auto &node : *nodes) {
          auto *object = node.getAsObject();
          if (!object)
            continue;
          if (object->getString("name") == "sample::Demo")
            function = object;
          if (object->getString("name") == "sample::Family::verify")
            verify = object;
          if (object->getString("name") == "sample::Family::VerifyResult")
            result = object;
        }
        require(
            entries.find("function") != std::string::npos && function &&
                function->getString("stage") == "host" &&
                function->getString("entry_kind") == "function" &&
                function->getArray("inputs") &&
                function->getArray("inputs")->size() == 1 &&
                function->getArray("outputs") &&
                function->getArray("outputs")->size() == 1 && verify &&
                verify->getString("stage") == "host" &&
                verify->getArray("inputs")->size() == 2 && result &&
                result->getString("constructor") == "native",
            "discovery omitted callable signatures or constructor permissions");
      });
  cases.run("generated schemas are bound to the exact captured family", [] {
    auto a = take(check((proof + "entry fn Demo(){return ();}").str()));
    auto b = take(check((proof + "entry fn Demo(){return false;}").str()));
    auto type = [](const Declaration &decl) {
      return Type(Type::Kind::Record, decl.qualifiedName);
    };
    Layouts first(a), second(b);
    auto x = take(first.get(type(definition(a, "sample::Family::Proof"))));
    auto y = take(second.get(type(definition(b, "sample::Family::Proof"))));
    uint64_t budget = 100000;
    LayoutIdentities identities(budget);
    require(take(identities.get(*x)) != take(identities.get(*y)),
            "candidate identity erased source family binding");
  });
  cases.run("generated traversal is bounded by declared limits", [] {
    Limits limits;
    limits.declarations = 25;
    refuses(check((protocol + "entry fn Demo(){return ();}").str(), limits),
            "source.limit");
  });
  cases.run(
      "producer and verifier operations retain distinct child policies", [] {
        auto entry = take(close((proof + R"(
      entry fn Demo(public:Family::Public,witness:Family::Witness){
        let produced=Family::prove(public,witness);
        return Family::verify(public,produced.proof);
      })")
                                    .str()));
        require(entry.invocations().size() == 2 &&
                    entry.invocations()[0].kind ==
                        HostInvocation::Kind::Prove &&
                    entry.invocations()[1].kind == HostInvocation::Kind::Verify,
                "operation-specific child closure was merged");
      });
  cases.run(
      "protocol setup associations exclude authority from role inputs", [] {
        auto source = R"(module sample;
      domain C=commitment("multilinear.kzg.bls12-381/0");
      type PK=builtin("prover_key",C);type VK=builtin("verifier_key",C);
      protocol Work roles(P,V)(pk:PK@P,vk:VK@V,x:bool@P)->(ok:bool@V)
      setup pcs{pk,vk};
      {let ok@V=true;return(ok=ok);}
      entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);}
    )";
        auto entry = take(close(source));
        auto &p = definition(entry.project(), "sample::Work::Inputs::P");
        auto &v = definition(entry.project(), "sample::Work::Inputs::V");
        require(p.fields.size() == 1 && p.fields[0].name == "x" &&
                    v.fields.empty(),
                "setup authority leaked into ordinary inputs");
        require(entry.invocations()[0].deployment->entry().setups.size() == 1,
                "joint invocation dropped protocol setup association");
      });
  cases.run("setup authority cannot cross an ordinary entry boundary", [] {
    auto prefix = R"(module sample;
      domain C=commitment("multilinear.kzg.bls12-381/0");
      type VK=builtin("verifier_key",C);
    )";
    refuses(check(std::string(prefix) + "entry fn Demo(x:VK){return x;}"),
            "source.host-data");
    refuses(check(std::string(prefix) +
                  "enum Candidate{Key(VK),Empty()} "
                  "entry fn Demo(x:Candidate){return x;}"),
            "source.host-data");
  });
  cases.run("entry boundaries infer generic Copy and Drop requirements", [] {
    auto checked = take(check(R"(module sample;
      entry fn Identity<T:Type>(x:T){return x;}
      entry fn Demo(x:bool){return Identity(x);}
    )"));
    require(!definition(checked, "sample::Identity").permissionBounds.empty(),
            "generic Host boundary did not retain inferred usage requirements");
    take(closeEntry(checked, "sample::Demo", {}, EntryKind::Function));
  });
  cases.run("scoped Local callbacks cannot acquire the enclosing Host stage",
            [] {
              refuses(check(R"(module sample;
      fn apply(x:bool,f:fn(bool)->bool)->bool effects(f){return f(x);}
      entry fn E(x:bool){return x;}
      entry fn Demo(x:bool){return apply(x,fn(y)=>E(y));}
    )"),
                      "source.stage");
            });
  cases.run("call depth and closed instance ceilings bound entry traversal",
            [] {
              Limits limits;
              limits.callDepth = 2;
              refuses(check(R"(module sample;
      entry fn A(x:bool){return x;}
      entry fn B(x:bool){return A(x);}
      entry fn C(x:bool){return B(x);}
      entry fn Demo(x:bool){return C(x);}
    )",
                            limits),
                      "source.limit");
              limits = {};
              limits.instances = 1;
              refuses(close("module sample; entry fn E(x:bool){return x;} "
                            "entry fn Demo(x:bool){return E(x);}",
                            "sample::Demo", limits),
                      "source.limit");
            });
  cases.run("entry functions have no generated member invocation spelling", [] {
    refuses(check(R"(module sample;
      entry fn E(x:bool){return x;}
      entry fn Demo(x:bool){return E::run(x);}
    )"),
            "source.name");
  });
  cases.run("old run declarations have no source compatibility branch", [] {
    refuses(check((protocol + "run Old=Work<F>;").str()), "source.syntax");
  });
  cases.run("entry fn is the sole application declaration syntax", [] {
    for (StringRef source :
         {"run Demo(){return ();}", "run fn Demo(){return ();}",
          "pub run Demo(){return ();}", "entry Demo(){return ();}"})
      refuses(check(("module sample;" + source).str()), "source.syntax");
    refuses(check("module sample; interface Bad { entry fn Demo()->(); }"),
            "source.mode");
  });
  cases.run("entry and run remain contextual names", [] {
    take(close(R"(module sample;
      fn run(entry:index)->index{return entry;}
      entry fn Demo(entry:index){return run(entry);}
    )"));
    take(close("module sample; entry fn run(entry:index){return entry;}",
               "sample::run"));
  });
  cases.run("no host fn or workflow source forms are admitted", [] {
    refuses(check("module sample; host fn Demo(){return ();}"),
            "source.syntax");
    refuses(check("module sample; workflow Demo(){return ();}"),
            "source.syntax");
  });
  return cases.result();
}
