#include "../lib/Language/ScopedWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef declarations) {
  auto captured =
      capture({{"facade", "module facade;pub use zkc::prelude::{Random};",
                "facade.zkc"},
               {"m",
                "module m;domain F=field(\"koala-bear.ext4-binomial3\");" +
                    declarations.str(),
                "managed.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Body &body(const CheckedProject &project, StringRef name = "Run") {
  auto at = llvm::find_if(project.declarations(),
                          [&](const auto &decl) { return decl.name == name; });
  require(at != project.declarations().end() && at->body, "missing body");
  return const_cast<Body &>(*at->body);
}
uint64_t replay(const CheckedProject &project) {
  std::vector<SourceWorkBudget> observations;
  if (auto error = checkScopedElaboration(project, {}, &observations))
    throw std::runtime_error(toString(std::move(error)));
  require(observations.size() == 1, "missing replay work observation");
  return observations.front().ledger.total;
}
void rejected(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "complete authored region exchange was accepted");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.binding-witness"),
          "unexpected diagnostic: " + message);
}
std::vector<Control *> controls(Body &candidate) {
  std::vector<Control *> result;
  for (auto &op : candidate.operations) {
    if (auto *control = std::get_if<Control>(&op.action)) {
      result.push_back(control);
      for (const auto &region : control->regions) {
        auto nested = controls(const_cast<Body &>(*region));
        result.insert(result.end(), nested.begin(), nested.end());
      }
    }
    if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
      auto nested = controls(const_cast<Body &>(*repeat->region));
      result.insert(result.end(), nested.begin(), nested.end());
    }
  }
  return result;
}
std::string aliases(unsigned count, bool managed, bool used = true,
                    bool control = true) {
  std::string source =
      "protocol Run roles(V)(go:bool@V,coins:facade::Random<F>@V)->(){";
  std::string previous = managed ? "coins" : "go";
  for (unsigned i = 0; i < count; ++i) {
    auto name = "alias" + std::to_string(i);
    source += "let " + name + "=" + previous + ";";
    previous = name;
  }
  if (control)
    source += "if go roles(V) {";
  if (managed && used)
    source += "let unused=" + previous + ".draw();";
  if (control)
    source += "} else {}";
  return source + "return ();}";
}
std::string inventory(unsigned ports, unsigned queries, unsigned aliasCount,
                      unsigned controlCount, bool managedAliases) {
  std::string source = "protocol Run roles(V)(go:bool@V";
  for (unsigned i = 0; i < ports; ++i)
    source += ",coins" + std::to_string(i) + ":facade::Random<F>@V";
  source += ")->(){";
  std::string previous = managedAliases ? "coins0" : "go";
  // Independent aliases isolate inventory size from alias-chain depth.
  for (unsigned i = 0; i < aliasCount; ++i)
    source += "let alias" + std::to_string(i) + "=" + previous + ";";
  for (unsigned i = 0; i < controlCount; ++i)
    source += "if go roles(V) {} else {}";
  for (unsigned i = 0; i < queries; ++i)
    source += "let value" + std::to_string(i) + "=coins" +
              std::to_string(ports - 1) + ".draw();";
  return source + "return ();}";
}
} // namespace
int main() {
  Cases cases;
  const char *arms[] = {
      "if go roles(V) {let a=coins.index<8>();} else {let b=coins.index<9>();}",
      "if go roles(V) {{let a=coins.indices(8,2);}} else {{let "
      "b=coins.indices(8,3);}}",
      "match flag roles(V) {Right()=>{let b=coins.index<9>();},Left()=>{let "
      "a=coins.index<8>();}}",
      "if go roles(V) {let alias=coins;if go roles(V) {let "
      "a=alias.index<8>();} else {let b=alias.index<9>();}} else {if go "
      "roles(V) {let c=coins.index<10>();} else {let d=coins.index<11>();}}",
      "for i in 0..n roles(V) max 2 {let local=coins;if go roles(V) {let "
      "a=local.index<8>();} else {let b=local.index<9>();}}"};
  for (unsigned i = 0; i < std::size(arms); ++i)
    cases.run("complete managed arms " + Twine(i), [&] {
      auto project = take(check("enum Flag{Left(),Right()} protocol Run "
                                "roles(V)(go:bool@V,flag:Flag@V,n:index@V,"
                                "coins:facade::Random<F>@V)->(){" +
                                std::string(arms[i]) + "return ();}"));
      replay(project);
      auto candidates = controls(body(project));
      require(!candidates.empty() && candidates.front()->regions.size() == 2,
              "missing exchangeable arms");
      std::swap(candidates.front()->regions[0], candidates.front()->regions[1]);
      rejected(project);
    });
  cases.run("regions exchanged between sibling repeats", [&] {
    auto project = take(check(R"(
protocol Run roles(V)(n:index@V,coins:facade::Random<F>@V)->(){
 for i in 0..n roles(V) max 2 {let a=coins.index<8>();}
 for j in 0..n roles(V) max 2 {let b=coins.index<9>();}
 return ();
})"));
    replay(project);
    std::vector<ProtocolRepeat *> repeats;
    for (auto &op : body(project).operations)
      if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        repeats.push_back(repeat);
    require(repeats.size() == 2, "missing sibling repeats");
    std::swap(repeats[0]->region, repeats[1]->region);
    rejected(project);
  });
  cases.run("local loop regions exchanged between siblings", [&] {
    auto project = take(check(R"(
fn dormant(n:index,go:bool)->(){
 for i in 0..n {require go;}
 for j in 0..n {require !go;}
 return ();
})"));
    replay(project);
    auto candidates = controls(body(project, "dormant"));
    require(candidates.size() == 2, "missing sibling local loops");
    std::swap(candidates[0]->regions[0], candidates[1]->regions[0]);
    rejected(project);
  });
  cases.run("nested controls preserve local aliases and captures", [&] {
    auto project = take(check(R"(
protocol Run roles(V)(go:bool@V,n:index@V,coins:facade::Random<F>@V)->(){
 let outer=coins;
 for i in 0..n roles(V) max 2 {
  let inner=outer;
  if go roles(V) {
   let local=inner;
   if go roles(V) {let a=local.index<8>();} else {let b=local.index<9>();}
  } else {let c=inner.draw();}
 }
 return ();
})"));
    replay(project);
    auto candidates = controls(body(project));
    require(candidates.size() == 2, "missing captured inner control");
    std::swap(candidates[1]->regions[0], candidates[1]->regions[1]);
    rejected(project);
  });
  for (StringRef mode : {"fn", "math fn"})
    cases.run("ordinary lexical arms " + mode, [&] {
      auto project = take(check(
          (mode + R"( first(x:bool)->bool{return x;}
)" + mode + R"( second(x:bool)->bool{return !x;}
)" + mode +
           R"( dormant(go:bool)->bool{return if go {{first(go)}} else {{second(go)}};})")
              .str()));
      replay(project);
      auto candidates = controls(body(project, "dormant"));
      require(candidates.size() == 1, "missing ordinary control");
      std::swap(candidates[0]->regions[0], candidates[0]->regions[1]);
      rejected(project);
    });
  for (StringRef boolean : {"&&", "||"})
    cases.run("local short circuit arms " + boolean, [&] {
      auto project = take(check(("fn dormant(go:bool)->bool{return go" +
                                 boolean + "{require go;go};}")
                                    .str()));
      replay(project);
      auto candidates = controls(body(project, "dormant"));
      require(candidates.size() == 1, "missing short circuit control");
      std::swap(candidates[0]->regions[0], candidates[0]->regions[1]);
      rejected(project);
    });
  cases.run("callback lexical arms", [&] {
    auto project = take(check(R"(
fn apply(go:bool,callback:fn(bool)->bool effects(stop))->bool effects(stop){return callback(go);}
fn dormant(go:bool)->bool{return apply(go,fn(x)=>{if x {require x;x} else {require !x;!x}});}
)"));
    replay(project);
    auto &bindings = body(project, "dormant").scopedBindings;
    auto at = llvm::find_if(bindings, [](const auto &binding) {
      return bool(binding.computation);
    });
    require(at != bindings.end(), "missing callback");
    auto candidates = controls(const_cast<Body &>(*at->computation->body));
    require(candidates.size() == 1, "missing callback control");
    std::swap(candidates[0]->regions[0], candidates[0]->regions[1]);
    rejected(project);
  });
  cases.run("eager Boolean regions and callback modes remain valid", [&] {
    replay(take(check(R"(
math fn mathematical(go:bool)->bool{return go&&{go||!go};}
math fn math_apply(go:bool,callback:math fn(bool)->bool)->bool{return callback(go);}
fn local_apply(go:bool,callback:fn(bool)->bool effects(stop))->bool effects(stop){return callback(go);}
fn dormant(go:bool)->bool{return math_apply(go,fn(x)=>x&&go)&&local_apply(go,fn(x)=>x||go);}
protocol Run roles(V)(go:bool@V)->(out:bool@V){return go&&{go||!go};}
)")));
  });
  cases.run("oracle bodies and generated predicate regions remain valid", [&] {
    replay(take(check(R"(
type Table=builtin("oracle.table",bool,16);
type O=builtin("oracle",Table);
oracle def Identity(source:O)->O {
 requires true&&true;
 query(position:index) {
  let answer <- oracle.query(source,position);
  return answer&&true;
 }
}
)")));
  });
  cases.run("unused ordinary chain does not consume managed depth",
            [&] { replay(take(check(aliases(65, false)))); });
  for (unsigned count : {64, 65, 256})
    for (bool used : {false, true})
      for (bool control : {false, true})
        cases.run(
            "flat managed aliases " + Twine(count) + "/" + Twine(used) + "/" +
                Twine(control),
            [&] { replay(take(check(aliases(count, true, used, control)))); });
  // Cross differences cancel unrelated linear setup and per-query costs.
  // These are deterministic charged-work checks, not timing benchmarks.
  cases.run("ports and queries have additive replay work", [&] {
    auto work = [&](unsigned ports, unsigned queries) {
      return replay(take(check(inventory(ports, queries, 0, 0, false))));
    };
    auto small = work(1, 1), ports = work(128, 1);
    auto queries = work(1, 128), both = work(128, 128);
    require(both + small <= ports + queries + 2048,
            "unrelated ports multiply per-query replay work");
  });
  for (bool managed : {false, true})
    cases.run("aliases and controls have additive replay work " +
                  Twine(managed),
              [&] {
                auto work = [&](unsigned aliases, unsigned controls) {
                  return replay(
                      take(check(inventory(1, 0, aliases, controls, managed))));
                };
                auto small = work(0, 1), aliases = work(128, 1);
                auto controls = work(0, 128), both = work(128, 128);
                require(both + small <= aliases + controls + 2048,
                        "unrelated aliases multiply per-control replay work");
              });
  return cases.result();
}
