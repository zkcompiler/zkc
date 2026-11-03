#include "../lib/Language/CommonSummary.h"
#include "../lib/Language/State.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Names.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source_detail = zkc::language::detail;
namespace {
Expected<CheckedProject> check(StringRef source, bool layout = false) {
  CaptureOptions options;
  options.format = layout ? "zkc-layout" : "zkc";
  auto captured = capture({{"m", source.str(), "summaries.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
DeclarationId named(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.name == name;
  });
  require(found != project.declarations().end(),
          "missing declaration: " + name);
  return found->id;
}
struct Result {
  std::vector<CommonControlRequirement> rows;
  uint64_t work;
  source_detail::CommonSummaryObservation observation;
};
Result derive(const CheckedProject &project, StringRef name = "Run",
              const Limits &limits = {}) {
  source_detail::Work work{limits};
  source_detail::CommonSummaryObservation observation;
  auto rows = take(source_detail::deriveCommonSummaryRequirements(
      source_detail::DeclarationAccess::get(project), project.assets(), work,
      named(project, name), observation));
  return {std::move(rows), work.used, observation};
}
void exactInputs(ArrayRef<CommonControlRequirement> rows,
                 ArrayRef<unsigned> expected) {
  std::set<unsigned> actual;
  for (const auto &row : rows) {
    require(!row.tagOnly && !row.extentAxis && row.components.size() == 2,
            "unexpected observation facet or arity");
    auto input = row.components.front().input;
    for (const auto &component : row.components)
      require(component.input == input && component.path.empty(),
              "summary changed the actual input/path association");
    actual.insert(input);
  }
  require(rows.size() == expected.size() &&
              actual == std::set<unsigned>(expected.begin(), expected.end()),
          "summary omitted or added an input requirement");
}
void requireLimit(Error error) {
  require(bool(error), "expected common summary limit refusal");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.limit"), message);
}
// Each level uses its predecessor twice. Agreement must traverse the resulting
// shared expression DAG, not expand an expression tree of size 2^depth.
std::string chain(unsigned depth, bool diamond = false) {
  std::string source = "module m;math fn h0(x:bool)->bool{return !x;}";
  for (unsigned i = 1; i <= depth; ++i) {
    auto previous = "h" + std::to_string(i - 1);
    source += "math fn h" + std::to_string(i) + "(x:bool)->bool{";
    if (diamond)
      source +=
          "let a=" + previous + "(x);let b=" + previous + "(x);return a&&b;}";
    else
      source += "let a=" + previous + "(x);return a&&a;}";
  }
  return source + "protocol Run roles(P,V)(flag:bool@(P,V))->(){let guard=h" +
         std::to_string(depth) + "(flag);if guard{()}else{()}return();}";
}
std::string independent(unsigned bodySize, unsigned calls, unsigned roots) {
  std::string source = "module m;math fn helper(x:bool)->bool{";
  for (unsigned i = 0; i < bodySize; ++i)
    source += "let unused" + std::to_string(i) + "=if x{true}else{false};";
  source += "return x;}";
  for (unsigned r = 0; r < roots; ++r) {
    source += "protocol Root" + std::to_string(r) +
              " roles(P,V)(flag:bool@(P,V))->(){";
    for (unsigned k = 0; k < calls; ++k)
      source += "let flag" + std::to_string(k) + "=helper(flag);if flag" +
                std::to_string(k) + "{()}else{()}";
    source += "return();}";
  }
  return source;
}
Result all(const CheckedProject &project, const Limits &limits = {}) {
  source_detail::Work work{limits};
  source_detail::CommonSummaryObservation observation;
  if (auto error = source_detail::checkCommonSummaryRequirements(
          source_detail::DeclarationAccess::get(project), project.assets(),
          work, observation))
    throw std::runtime_error(toString(std::move(error)));
  return {{}, work.used, observation};
}
const std::string finitePrelude = R"(module m;
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn apply(x:bool,body:math fn(bool)->bool)->bool{return body(x);}
)";
} // namespace
int main() {
  Cases cases;
  cases.run("forty-deep agreement shares completed demands", [&] {
    std::vector<uint64_t> work;
    for (unsigned depth : {0u, 20u, 40u}) {
      auto result = derive(take(check(chain(depth))));
      exactInputs(result.rows, {0});
      require(result.observation.instances == depth + 2,
              "a chain body was constructed more than once");
      work.push_back(result.work);
      outs() << "chain " << depth << ": work=" << result.work << '\n';
    }
    require((work[2] - work[1]) * 2 <= (work[1] - work[0]) * 3,
            "common agreement work grows faster than the chain gate");
  });
  cases.run("forty-deep diamond retains shared call products", [&] {
    auto result = derive(take(check(chain(40, true))));
    exactInputs(result.rows, {0});
    require(result.observation.instances == 42 &&
                result.observation.instanceHits >= 40 &&
                result.observation.applicationHits >= 40 &&
                result.observation.applications <= 42,
            "diamond expanded its call tree");
  });
  cases.run("unused helper work is constructed once across roots", [&] {
    std::vector<uint64_t> deltas;
    for (unsigned bodySize : {40u, 400u}) {
      auto small = all(take(check(independent(bodySize, 1, 1))));
      auto large = all(take(check(independent(bodySize, 8, 8))));
      require(small.observation.instances == 2 &&
                  large.observation.instances == 9,
              "helper products were rebuilt for an application");
      require(large.observation.bodyTraversals -
                      small.observation.bodyTraversals ==
                  7 + 2 * (64 - 1),
              "an application re-entered a helper's source regions");
      deltas.push_back(large.work - small.work);
      outs() << "independent body=" << bodySize << ": delta=" << deltas.back()
             << ", bodies=" << large.observation.bodyTraversals << '\n';
    }
    auto difference =
        deltas[0] > deltas[1] ? deltas[0] - deltas[1] : deltas[1] - deltas[0];
    require(difference * 100 <= std::max(deltas[0], deltas[1]),
            "per-application work depends on unused helper body size");
  });
  cases.run("projection does not force an unused helper result field", [&] {
    for (unsigned length : {40u, 400u}) {
      std::string source = "module m;math fn pair(x:bool)->(bool,bool){";
      source += "let value0=x;";
      for (unsigned i = 1; i <= length; ++i)
        source += "let value" + std::to_string(i) + "=!value" +
                  std::to_string(i - 1) + ";";
      source += "return (x,value" + std::to_string(length) + ");}";
      source += R"(protocol Run roles(P,V)(flag:bool@(P,V))->(){
 let a=pair(flag);let b=pair(flag);if a.0{()}else{()}if b.0{()}else{()}return();})";
      auto result = derive(take(check(source)));
      exactInputs(result.rows, {0});
      require(result.observation.expressions < 40,
              "projection evaluated the unused expression chain");
    }
  });
  cases.run("exact recurrence classes and actual role order survive reuse", [&] {
    auto project = take(check(
        R"(protocol Evolve roles(A,B)(count:index @(A,B),base:bool @(A,B),step:bool @(A,B))->bool @(A,B):
    mut state = base
    for i in 0..count roles(A,B) max 4:
        if state:
            ()
        else:
            ()
        state := if state:
            step
        else:
            false
    return state
pub protocol Run roles(P,V)(n:index @(P,V),a:bool @(P,V),b:bool @(P,V),c:bool @(P,V),d:bool @(P,V))->() @(P,V):
    first <- Evolve(n,a,b) @(V,P)
    second <- Evolve(n,c,d) @(P,V)
    return ()
)",
        true));
    auto result = derive(project);
    exactInputs(result.rows, {0, 1, 2, 3, 4});
    require(result.observation.loopNamespaces == 2,
            "repeated recurrence applications reused a namespace");
    for (const auto &row : result.rows) {
      auto input = row.components[0].input;
      require(row.components[0].role == (input < 3 ? 1u : 0u) &&
                  row.components[1].role == (input < 3 ? 0u : 1u),
              "application sorted a protocol role substitution");
    }
  });
  cases.run(
      "zero one and dynamic counts rebind the same recurrence instance", [&] {
        auto project = take(check(
            R"(protocol Evolve roles(A,B)(count:index @(A,B),base:bool @(A,B),step:bool @(A,B))->bool @(A,B):
    mut state = base
    for i in 0..count roles(A,B) max 4:
        if state:
            ()
        else:
            ()
        state := step
    return state
pub protocol Zero roles(P,V)(n:index @(P,V),base:bool @(P,V),step:bool @(P,V))->() @(P,V):
    state <- Evolve(index<0>(),base,step) @(P,V)
    if state:
        ()
    else:
        ()
    return ()
pub protocol One roles(P,V)(n:index @(P,V),base:bool @(P,V),step:bool @(P,V))->() @(P,V):
    state <- Evolve(index<1>(),base,step) @(P,V)
    if state:
        ()
    else:
        ()
    return ()
pub protocol Run roles(P,V)(n:index @(P,V),base:bool @(P,V),step:bool @(P,V))->() @(P,V):
    state <- Evolve(n,base,step) @(P,V)
    if state:
        ()
    else:
        ()
    return ()
)",
            true));
        exactInputs(derive(project, "Zero").rows, {1});
        exactInputs(derive(project, "One").rows, {1, 2});
        exactInputs(derive(project).rows, {0, 1, 2});
        auto shared = all(project);
        require(shared.observation.instances == 4 &&
                    shared.observation.instanceHits >= 3,
                "count observations specialized the recurrence template");
      });
  cases.run("conditional cycle closures never become zero-height proofs", [&] {
    auto project = take(check(R"(pub protocol Run roles(P,V)()->() @(P,V):
    mut x = true
    mut y = true
    for i in 0..index<3>() roles(P,V) max 4:
        if x:
            ()
        else:
            ()
        previous = x
        x := y
        y := previous
    if x:
        ()
    else:
        ()
    return ()
)",
                              true));
    Limits limits;
    limits.expressionDepth = 3;
    require(derive(project, "Run", limits).rows.empty(),
            "a grounded cycle acquired input premises");
    limits.expressionDepth = 2;
    refuses(
        deriveCommonControlRequirements(project, named(project, "Run"), limits),
        "source.limit");
  });
  cases.run("equal-looking helper clocks remain distinct", [&] {
    refuses(
        check(R"(protocol Clock roles(A,B)(count:index @(A,B))->index @(A,B):
    mut last = index<0>()
    for i in 0..count roles(A,B) max 4:
        last := i
    return last
pub protocol Run roles(P,V)(n:index @(P,V))->() @(P,V):
    left <- Clock(n) @(P,V)
    right <- Clock(n) @(P,V)
    both = @(P = left, V = right)
    if both == index<0>():
        ()
    else:
        ()
    return ()
)",
              true),
        "source.common-provenance");
  });
  cases.run("same dependencies do not establish actual-value congruence", [&] {
    refuses(check(R"(module m;
math fn identity(x:bool)->bool{return x;}
math fn inverted(x:bool)->bool{return !x;}
protocol Run roles(P,V)(x:bool@(P,V))->(){
 let a=identity(x);let b=inverted(x);let both=@(P=a,V=b);
 if both{()}else{()}return();})"),
            "source.common-provenance");
  });
  for (bool dormant : {false, true})
    cases.run(
        dormant ? "dormant arm preserves received-control formation"
                : "zero-trip body preserves received-control formation",
        [&] {
          auto region = std::string("let received=send P->V(flag);") +
                        "let both=@(P=flag,V=received);if both{()}else{()}";
          auto source =
              std::string(
                  "module m;protocol Run roles(P,V)(flag:bool@(P,V))->(){") +
              (dormant ? "if false{"
                       : "for _ in 0..index<0>() roles(P,V) max 0{") +
              region + (dormant ? "}else{()}" : "}") + "return();}";
          refuses(check(source), "source.common-provenance");
        });
  cases.run("zero-trip stop remains legal source formation", [&] {
    auto project = take(check(R"(module m;
protocol Run roles(P,V)(flag:bool@(P,V))->(){
 for _ in 0..index<0>() roles(P,V) max 0 {require @P false;}
 if flag{()}else{()}return();})"));
    exactInputs(derive(project).rows, {0});
  });
  cases.run("callback captures remain actual operands", [&] {
    auto project = take(check(finitePrelude + R"(
protocol Run roles(P,V)(x:bool@(P,V),a:bool@(P,V),b:bool@(P,V))->(){
 let left=apply(x,fn(y)=>if y{a}else{false});
 let right=apply(x,fn(y)=>if y{b}else{false});
 if left{()}else{()}if right{()}else{()}return();})"));
    exactInputs(derive(project).rows, {0, 1, 2});
    refuses(check(finitePrelude + R"(
protocol Run roles(P,V)(x:bool@(P,V),a:bool@(P,V))->(){
 let received=send P->V(a);let both=@(P=a,V=received);
 let warm=apply(x,fn(y)=>y);if warm{()}else{()}
 let cold=apply(x,fn(y)=>if y{both}else{false});if cold{()}else{()}return();})"),
            "source.common-provenance");
  });
  for (StringRef difference : {"same", "domain", "callback", "capture"})
    cases.run("finite expression distinguishes " + difference, [&] {
      auto source = finitePrelude + R"(
math fn calc(rows:domain<index>,x:bool,cap:bool,step:math fn(bool)->bool)->bool{
 return fold(rows,x,fn(s,i)=>step(if s{cap}else{false}));}
math fn choose(flag:bool,x:bool,cap:bool,n:index,m:index,other:bool,step:math fn(bool)->bool)->bool{
 let left=calc(range(0,n),x,cap,step);
 let right=calc(range(0,)";
      source += difference == "domain" ? "m" : "n";
      source += "),x,";
      source += difference == "capture" ? "other" : "cap";
      source += ",";
      source += difference == "callback" ? "fn(y)=>!y" : "step";
      source += R"();return if flag{left}else{right};}
protocol Run roles(P,V)(flag:bool@(P,V),x:bool@(P,V),cap:bool@(P,V),n:index@(P,V),m:index@(P,V),other:bool@(P,V))->(){
 let received=send P->V(flag);let selector=@(P=flag,V=received);
 let guard=choose(selector,x,cap,n,m,other,fn(y)=>y);
 if guard{()}else{()}return();})";
      if (difference == "same")
        exactInputs(derive(take(check(source))).rows, {1, 2, 3});
      else
        refuses(check(source), "source.common-provenance");
    });
  cases.run("staged lexical pow2 never normalizes unused keys eagerly", [&] {
    auto project = take(check(R"(module m;
math fn ignore<N:nat>(x:bool)->bool{return x;}
math fn inner<N:nat>(x:bool)->bool{return ignore<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->bool{return inner<pow2(M)>(x);}
protocol Run<M:nat> roles(P,V)(flag:bool@(P,V))->(){
 let guard=outer<M>(flag);if guard{()}else{()}return();})"));
    exactInputs(derive(project).rows, {0});
    Type five(Type::Kind::Natural);
    five.dimension = Natural::constant(5);
    take(closeNativeRun(project, "m::Run", {}, {five}));
    five.dimension = Natural::constant(6);
    refuses(closeNativeRun(project, "m::Run", {}, {five}), "source.natural");
  });
  cases.run("actual implementation declarations distinguish warmed instances",
            [&] {
              refuses(check(R"(module m;
interface Operation{math fn apply(x:bool)->bool;}
module Direct:Operation{math fn apply(x:bool)->bool{return x;}}
module Inverted:Operation{math fn apply(x:bool)->bool{return !x;}}
math fn via<C:Operation>(x:bool)->bool{return C::apply(x);}
protocol Warm roles(P,V)(flag:bool@(P,V))->(){
 let guard=via<Direct>(flag);if guard{()}else{()}return();}
protocol Run roles(P,V)(flag:bool@(P,V))->(){
 let left=via<Direct>(flag);let right=via<Inverted>(flag);
 let guard=@(P=left,V=right);if guard{()}else{()}return();})"),
                      "source.common-provenance");
            });
  cases.run("source natural premises are still required", [&] {
    refuses(check(R"(module m;
math fn head<N:nat>(xs:[bool;N])->bool where () {return xs[1];}
protocol Run<N:nat> roles(P,V)(xs:[bool;N]@(P,V))->(){
 let guard=head<N>(xs);if guard{()}else{()}return();})"),
            "source.bound");
  });
  cases.run("summary formation does not invent a finite item premise", [&] {
    refuses(check(finitePrelude + R"(
math fn wrong(a:domain<index>,b:domain<index>,step:math fn(bool,item:index)->bool where item_from(item,a))->bool{
 return fold(b,false,step);})"),
            "source.scoped-domain");
  });
  cases.run("warm instances retain complete callable height", [&] {
    auto project = take(check(R"(module m;
math fn leaf(x:bool)->bool{return x;}
math fn middle(x:bool)->bool{return leaf(x);}
protocol Warm roles(P,V)(flag:bool@(P,V))->(){let x=leaf(flag);if x{()}else{()}return();}
protocol Run roles(P,V)(flag:bool@(P,V))->(){let x=middle(flag);if x{()}else{()}return();}
)"));
    Limits limits;
    limits.callDepth = 3;
    require(all(project, limits).observation.instanceHits > 0,
            "call boundary did not exercise a completed instance");
    limits.callDepth = 2;
    source_detail::Work work{limits};
    source_detail::CommonSummaryObservation observation;
    requireLimit(source_detail::checkCommonSummaryRequirements(
        source_detail::DeclarationAccess::get(project), project.assets(), work,
        observation));
    require(observation.instanceHits > 0,
            "refusal happened before the warm lookup");
  });
  cases.run("warm regions and expressions respect the narrower current limit",
            [&] {
              auto project = take(check(R"(module m;
math fn helper(x:bool)->bool{let unused=if x{if x{true}else{false}}else{false};return x;}
protocol Warm roles(P,V)(flag:bool@(P,V))->(){let x=helper(flag);if x{()}else{()}return();}
protocol Run roles(P,V)(flag:bool@(P,V))->(){let x=helper(flag);if x{()}else{()}return();}
)"));
              Limits limits;
              limits.expressionDepth = 3;
              require(all(project, limits).observation.instanceHits > 0,
                      "region probe did not warm its helper");
              limits.expressionDepth = 2;
              source_detail::Work work{limits};
              source_detail::CommonSummaryObservation observation;
              requireLimit(source_detail::checkCommonSummaryRequirements(
                  source_detail::DeclarationAccess::get(project),
                  project.assets(), work, observation));
            });
  cases.run("a warm agreement hit retains its expression height", [&] {
    auto project = take(check(R"(module m;
math fn helper(x:bool)->bool{return !x;}
protocol Run roles(P,V)(flag:bool@(P,V))->(){
 let a=helper(flag);let b=helper(flag);let c=helper(flag);
 let guard=a&&(b&&c);if guard{()}else{()}return();})"));
    Limits limits;
    limits.expressionDepth = 3;
    exactInputs(derive(project, "Run", limits).rows, {0});
    limits.expressionDepth = 2;
    source_detail::Work work{limits};
    source_detail::CommonSummaryObservation observation;
    auto result = source_detail::deriveCommonSummaryRequirements(
        source_detail::DeclarationAccess::get(project), project.assets(), work,
        named(project, "Run"), observation);
    refuses(std::move(result), "source.limit");
    require(observation.applicationHits > 0,
            "expression refusal did not exercise a shared application");
  });
  cases.run("lazy projections preserve the current expression depth", [&] {
    auto project = take(check(R"(module m;
math fn helper(x:bool)->(bool,bool){return (x,x);}
protocol Run roles(P,V)(flag:bool@(P,V))->(){
 let a=helper(flag);let b=helper(flag);let c=helper(flag);
 let guard=a.0&&(b.0&&c.0);if guard{()}else{()}return();})"));
    Limits limits;
    limits.expressionDepth = 3;
    exactInputs(derive(project, "Run", limits).rows, {0});
    limits.expressionDepth = 2;
    source_detail::Work work{limits};
    source_detail::CommonSummaryObservation observation;
    refuses(source_detail::deriveCommonSummaryRequirements(
                source_detail::DeclarationAccess::get(project),
                project.assets(), work, named(project, "Run"), observation),
            "source.limit");
    require(observation.applicationHits > 0,
            "projection refusal did not reuse a completed application");
  });
  cases.run("instance and application capacity remain independent of work",
            [&] {
              auto project = take(check(chain(1)));
              Limits limits;
              limits.instances = 3;
              limits.operations = 3;
              exactInputs(derive(project, "Run", limits).rows, {0});
              for (bool instance : {false, true}) {
                auto smaller = limits;
                if (instance)
                  smaller.instances = 2;
                else
                  smaller.operations = 2;
                refuses(deriveCommonControlRequirements(
                            project, named(project, "Run"), smaller),
                        "source.limit");
              }
            });
  cases.run("fresh recurrence capacity is bounded on unused loop results", [&] {
    auto project = take(check(R"(module m;
protocol Run roles(P,V)()->(){
 for _ in 0..index<0>() roles(P,V) max 0 {}
 for _ in 0..index<0>() roles(P,V) max 0 {}
 for _ in 0..index<0>() roles(P,V) max 0 {}return();})"));
    Limits limits;
    limits.operations = 3;
    auto result = derive(project, "Run", limits);
    require(result.observation.loopNamespaces == 3,
            "source loops lost their fresh namespace");
    limits.operations = 2;
    refuses(
        deriveCommonControlRequirements(project, named(project, "Run"), limits),
        "source.limit");
  });
  cases.run(
      "exact cumulative work boundary includes completed cache hits", [&] {
        auto project = take(check(independent(40, 8, 8)));
        auto measured = all(project);
        require(measured.observation.instanceHits > 0 && measured.work > 0,
                "budget probe did not use completed instances");
        for (bool enough : {false, true}) {
          Limits limits;
          uint64_t remaining = measured.work - unsigned(!enough);
          source_detail::Work work{limits};
          work.allowance = &remaining;
          source_detail::CommonSummaryObservation observation;
          auto error = source_detail::checkCommonSummaryRequirements(
              source_detail::DeclarationAccess::get(project), project.assets(),
              work, observation);
          if (enough) {
            require(!error, "measured exact allowance failed");
            require(remaining == 0 && work.used == measured.work,
                    "warm applications escaped cumulative accounting");
          } else
            requireLimit(std::move(error));
        }
      });
  return cases.result();
}
