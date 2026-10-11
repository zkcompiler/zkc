#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
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
Expected<CheckedProject> checked(StringRef source) {
  auto captured = capture({{"m", source.str(), "construction.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
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
  cases.run("Entry closes the selected factory and every handler", [&] {
    auto project = take(checked((program + R"(
      component Provider:TestTranscript<F>{
        type State:Copy+Drop=(index,index);
        fn initialize()->State{return State((0,0));}
        fn observe(t:State,v:F)->State{return t;}
        fn draw(t:State)->(State,F){return (t,1);}
      }
      proof Demo=Round<F>{prover P;verifier V;public{public};accept ok;
        construction Derived<F,Provider>;}
    )")
                                    .str()));
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
