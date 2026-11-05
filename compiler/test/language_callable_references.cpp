#include "../lib/Language/CallableConstraints.h"
#include "../lib/Language/FiniteContracts.h"
#include "../lib/Language/HelperResults.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Inspection.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "named.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const std::string helpers = R"(
def apply<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return f(x)
def forward<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return apply(x, f)
def identity<T: Type + Copy + Drop>(x: T) -> T:
    return x
local def ordered(x: bool, f: local fn(bool) -> bool effects(stop)) -> bool effects(f):
    result <- f(x)
    return result
local def checked(x: bool) -> bool effects(stop):
    guard x
    return x
)";
const std::string run = R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return forward(x, identity)
)";
void prepares(StringRef source) {
  auto project = take(check(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
  auto entry = take(closeNativeRun(project, "m::Run"));
  if (auto error = checkScopedSpecialization(entry))
    throw std::runtime_error(toString(std::move(error)));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
void refusal(Error error, StringRef code) {
  require(bool(error), "mutation was accepted");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), message);
}
Expected<CheckedProject> ordinary(StringRef source) {
  auto captured = capture({{"m", source.str(), "named.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &declarationNamed(const CheckedProject &project,
                                    StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}
void replayOrdinary(StringRef source) {
  auto project = take(ordinary(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void preparesOrdinary(StringRef source) {
  auto project = take(ordinary(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
  auto entry = take(closeNativeRun(project, "m::Run"));
  if (auto error = checkScopedSpecialization(entry))
    throw std::runtime_error(toString(std::move(error)));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
const std::string projectionPrelude = R"(module m;
domain F=field("bls12-381.fr");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
math fn apply<N:nat>(xs:[Array<F,4>;N],f:math fn([Array<F,4>;N])->bool)->bool{return f(xs);}
math fn unused<N:nat>(xs:[Array<F,4>;N],f:math fn([Array<F,4>;N])->bool)->bool{return true;}
math fn same(xs:Array<F,4>,ys:Array<F,4>)->bool where equal_extent(xs,ys){return true;}
math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return true;}
interface Selection{math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0);}
module Implementation:Selection{math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return true;}}
)";
std::string factorySource(unsigned middle = 2, unsigned last = 4) {
  return R"(module m;
domain F=field("bls12-381.fr");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Array<F,N>=finite("math.collect.field_array");
interface Recipe{domain fn make(lo:index,hi:index,seed:domain<index>)->domain<index>;}
module FromSeed:Recipe{domain fn make(lo:index,hi:index,seed:domain<index>)->domain<index>{return seed;}}
module FromRange:Recipe{domain fn make(lo:index,hi:index,seed:domain<index>)->domain<index>{return range(lo,hi);}}
domain fn wrapper<C:Recipe>(lo:index,hi:index,seed:domain<index>)->domain<index>{return C::make(lo,hi,seed);}
math fn apply<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,f:math fn(A)->B)->B{return f(x);}
math fn identity(x:F)->F{return x;}
math fn selected<A:Recipe,B:Recipe,N:nat>(x:F)->(Array<F,4>,Array<F,)" +
         std::to_string(middle) + ">,Array<F," + std::to_string(last) + R"(>){
 let lo=index<0>();let hi=index<N>();let seed=range(lo,index<4>());
 let first=fixed<index,4>(wrapper<A>(lo,hi,seed),fn(i)=>x);
 let nested=apply(x,identity);
 let second=fixed<index,)" +
         std::to_string(middle) + R"(>(wrapper<B>(lo,hi,seed),fn(i)=>nested);
 let third=fixed<index,)" +
         std::to_string(last) + R"(>(wrapper<A>(lo,hi,seed),fn(i)=>x);
 return (first,second,third);
}
math fn good(x:F)->(Array<F,4>,Array<F,)" +
         std::to_string(middle) + ">,Array<F," + std::to_string(last) +
         ">){return apply(x,selected<FromSeed,FromRange,2>);}\n";
}
void finiteBudgets(StringRef source, StringRef observation,
                   bool lastOccurrence = false) {
  auto project = take(ordinary(source));
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
  const std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
  const auto &root = declarationNamed(project, "m::good");
  namespace detail = zkc::language::detail;
  for (bool warm : {false, true}) {
    uint64_t cost = 0;
    for (unsigned trial = 0; trial < 3; ++trial) {
      Limits limits;
      detail::Work work{limits};
      detail::Semantics types(declarations, {}, work);
      detail::HelperResults results(types, declarations);
      auto run = [&] {
        return detail::checkFiniteContracts(types, declarations, root,
                                            *root.body, results);
      };
      if (warm)
        require(run(), "finite warm setup failed");
      uint64_t remaining = trial ? cost - (trial == 2) : limits.work;
      work.allowance = &remaining;
      const auto before = work.used;
      const bool accepted = run();
      if (trial == 2) {
        require(!accepted && types.diagnostic &&
                    types.diagnostic->code == "source.limit",
                "finite L-1 did not refuse");
        types.diagnostic.reset();
        work.allowance = nullptr;
        require(run(), "limited observation poisoned retry");
      } else {
        require(accepted, "finite exact allowance failed");
        if (!trial)
          cost = work.used - before;
        else
          require(remaining == 0 && work.used - before == cost,
                  "finite exact allowance was not consumed");
      }
    }
    outs() << "finite observation warm=" << warm << " L=" << cost
           << ": L/L-1/retry passed\n";
    // Find the longest charged observation, excluding one-unit structural
    // previsits and final domain-cache lookups at the same source span. Its
    // next allowance must reach later work. Retry uses the same result reader.
    const auto position =
        lastOccurrence ? source.rfind(observation) : source.find(observation);
    require(position != StringRef::npos, "missing observation marker");
    std::optional<uint64_t> last;
    uint64_t length = 0, longest = 0;
    for (uint64_t allowance = 0; allowance < cost; ++allowance) {
      Limits limits;
      detail::Work work{limits};
      detail::Semantics types(declarations, {}, work);
      detail::HelperResults results(types, declarations);
      auto run = [&] {
        return detail::checkFiniteContracts(types, declarations, root,
                                            *root.body, results);
      };
      if (warm)
        require(run(), "observation warm setup failed");
      uint64_t remaining = allowance;
      work.allowance = &remaining;
      require(!run() && types.diagnostic &&
                  types.diagnostic->code == "source.limit",
              "partial allowance escaped the work boundary");
      if (types.diagnostic->primary &&
          types.diagnostic->primary->begin == position) {
        if (++length > longest) {
          longest = length;
          last = allowance;
        }
      } else
        length = 0;
    }
    require(last.has_value(),
            "limited traversal did not reach the selected observation");
    require(longest > 1, "only a structural previsit reached the observation");
    for (bool exact : {false, true}) {
      Limits limits;
      detail::Work work{limits};
      detail::Semantics types(declarations, {}, work);
      detail::HelperResults results(types, declarations);
      auto run = [&] {
        return detail::checkFiniteContracts(types, declarations, root,
                                            *root.body, results);
      };
      if (warm)
        require(run(), "observation boundary warm setup failed");
      uint64_t remaining = *last + exact;
      work.allowance = &remaining;
      const bool accepted = run();
      if (exact) {
        require(accepted || (types.diagnostic &&
                             types.diagnostic->code == "source.limit" &&
                             (!types.diagnostic->primary ||
                              types.diagnostic->primary->begin != position)),
                "exact observation allowance did not reach later work");
      } else {
        require(!accepted && types.diagnostic &&
                    types.diagnostic->code == "source.limit" &&
                    types.diagnostic->primary &&
                    types.diagnostic->primary->begin == position,
                "observation L-1 did not refuse at the selected observation");
        types.diagnostic.reset();
        work.allowance = nullptr;
        require(run(), "failed selected observation poisoned retry");
      }
    }
    outs() << "selected observation warm=" << warm << " L=" << *last + 1
           << " window=" << longest << " at " << observation
           << ": L/L-1/retry passed\n";
  }
}
const std::string extentPrelude = R"(module m;
domain F=field("koala-bear");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
type Vector<E:Field>=builtin("vector",E);
math fn apply(xs:Array<F,4>,ys:Array<F,4>,f:math fn(Array<F,4>,Array<F,4>)->bool)->bool{return f(xs,ys);}
math fn unused(xs:Array<F,4>,ys:Array<F,4>,f:math fn(Array<F,4>,Array<F,4>)->bool)->bool{return true;}
math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys){return true;}
interface Same{math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys);}
module Implementation:Same{math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys){return true;}}
)";
} // namespace
int main() {
  Cases cases;
  for (bool abstract : {false, true})
    for (StringRef selection : {"selected<M>", "selected"})
      for (StringRef consumer : {"apply", "unused"})
        cases.run("symbolic projection " + std::to_string(abstract) +
                      selection.str() + consumer.str(),
                  [&] {
                    replayOrdinary(
                        projectionPrelude + "math fn good<M:nat" +
                        (abstract ? std::string(",C:Selection") : "") +
                        ">(xs:[Array<F,4>;M])->bool where 1<=M{return " +
                        consumer.str() + "(xs," + (abstract ? "C::" : "") +
                        selection.str() + ");}");
                  });
  for (StringRef expression :
       {"selected<M>(xs)", "apply(xs,fn(a)=>selected<M>(a))",
        "apply(xs,fn(a)=>apply(a,selected<M>))"})
    cases.run("symbolic projection direct and literal " + expression.str(),
              [&] {
                replayOrdinary(projectionPrelude + R"(
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return )" +
                               expression.str() + ";}");
              });
  for (bool abstract : {false, true})
    for (StringRef selection : {"selected<M>", "selected"})
      cases.run(
          "symbolic projection requires caller natural bound " +
              std::to_string(abstract) + selection.str(),
          [&] {
            refuses(ordinary(projectionPrelude + "math fn bad<M:nat" +
                             (abstract ? std::string(",C:Selection") : "") +
                             ">(xs:[Array<F,4>;M])->bool where (){return "
                             "apply(xs," +
                             (abstract ? "C::" : "") + selection.str() + ");}"),
                    "source.bound");
          });
  cases.run("closed positive and zero length projection", [] {
    replayOrdinary(projectionPrelude + R"(
math fn good(xs:[Array<F,4>;1])->bool{return apply(xs,selected<1>);}
)");
    refuses(ordinary(projectionPrelude + R"(
math fn bad(xs:[Array<F,4>;0])->bool{return apply(xs,selected<0>);}
)"),
            "source.bound");
  });
  cases.run("raw projection still requires its template natural bound", [] {
    refuses(ordinary(projectionPrelude + R"(
math fn invalid<N:nat>(xs:[Array<F,4>;N])->bool where equal_extent(xs.0,xs.0){return true;}
math fn bad(xs:[Array<F,4>;1])->bool{return apply(xs,invalid<1>);}
)"),
            "source.bound");
  });
  for (bool abstract : {false, true})
    cases.run("nested symbolic array paths " + std::to_string(abstract), [&] {
      replayOrdinary(projectionPrelude + R"(
math fn deep<N:nat,K:nat>(xs:[[Array<F,4>;K];N])->bool where 1<=N,1<=K,equal_extent(xs.0.0,xs.0.0){return true;}
interface Deep{math fn deep<N:nat,K:nat>(xs:[[Array<F,4>;K];N])->bool where 1<=N,1<=K,equal_extent(xs.0.0,xs.0.0);}
math fn accept<A:Type+Copy+Drop>(xs:A,f:math fn(A)->bool)->bool{return f(xs);}
)" + "math fn good<M:nat,L:nat" +
                     (abstract ? std::string(",C:Deep") : "") +
                     ">(xs:[[Array<F,4>;L];M])->bool where 1<=M,1<=L{return "
                     "accept(xs," +
                     (abstract ? "C::" : "") + "deep<M,L>);}");
    });
  cases.run("selected nested literal projects in the helper template", [] {
    replayOrdinary(projectionPrelude + R"(
math fn nested<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{return apply(xs,fn(a)=>same(a[0],a[0]));}
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,nested<M>);}
)");
  });
  cases.run("parent projection follows a nested named selection", [] {
    replayOrdinary(projectionPrelude + R"(
math fn nested<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{let first=apply(xs,selected<N>);return same(xs[0],xs[0]);}
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,nested<M>);}
)");
  });
  cases.run("inherited module naturals and implementation self projections",
            [] {
              replayOrdinary(projectionPrelude + R"(
interface Family<N:nat>{math fn member(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0);}
module Members<N:nat>:Family<N>{
 math fn member(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return apply(xs,fn(a)=>same(a[0],a[0]));}
 pub math fn nested(xs:[Array<F,4>;N])->bool where 1<=N{return apply(xs,member);}
}
math fn abstract_member<M:nat,C:Family<M>>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,C::member);}
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,Members<M>::nested);}
)");
            });
  cases.run("symbolic projection closes and independently prepares", [] {
    preparesOrdinary(projectionPrelude + R"(
math fn good<M:nat,C:Selection>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,C::selected<M>);}
pub protocol Run roles(P)(xs:[Array<F,4>;1]@P)->(result:bool@P){return good<1,Implementation>(xs);}
)");
  });
  cases.run("abstract self field and inherited natural projection close", [] {
    preparesOrdinary(projectionPrelude + R"(
interface Family<N:nat>{type Scalar:Field;math fn member(xs:[Array<Scalar,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0);}
module Members<N:nat>:Family<N>{type Scalar:Field=F;
 math fn member(xs:[Array<Scalar,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return true;}
}
math fn accept<E:Field,N:nat>(xs:[Array<E,4>;N],f:math fn([Array<E,4>;N])->bool)->bool{return f(xs);}
math fn good<M:nat,C:Family<M>>(xs:[Array<C::Scalar,4>;M])->bool where 1<=M{return accept(xs,C::member);}
pub protocol Run roles(P)(xs:[Array<F,4>;1]@P)->(result:bool@P){return good<1,Members<1>>(xs);}
)");
  });
  cases.run("selected projection obeys exact finite work", [] {
    finiteBudgets(projectionPrelude + R"(
math fn nested<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{let first=apply(xs,selected<N>);return same(xs[0],xs[0]);}
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,nested<M>);}
)",
                  "equal_extent(xs.0,xs.0)");
  });
  cases.run(
      "one traversal distinguishes selected factory recipes and reuse", [] {
        auto project = take(ordinary(factorySource()));
        const auto &selected = declarationNamed(project, "m::selected");
        std::vector<const DescriptorBinding *> bindings;
        for (const auto &binding : selected.body->descriptorBindings)
          if (binding.factory &&
              project.declarations()[binding.factory->declaration.index].name ==
                  "wrapper")
            bindings.push_back(&binding);
        require(bindings.size() == 3, "missing wrapper observations");
        for (const auto *binding : bindings)
          require(binding->factory->declaration.index ==
                          bindings.front()->factory->declaration.index &&
                      llvm::equal(binding->operands, bindings.front()->operands,
                                  [](ValueId a, ValueId b) {
                                    return a.index == b.index;
                                  }) &&
                      binding->children == bindings.front()->children &&
                      !binding->children.empty(),
                  "factory controls changed data origins or children");
        require(bindings[0]->arguments == bindings[2]->arguments &&
                    bindings[0]->arguments != bindings[1]->arguments,
                "factory controls do not distinguish static selection");
        if (auto error = checkScopedElaboration(project))
          throw std::runtime_error(toString(std::move(error)));
        finiteBudgets(factorySource(), "wrapper<B>");
      });
  cases.run("parent projection after nested selection obeys exact work", [] {
    finiteBudgets(projectionPrelude + R"(
math fn nested<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{let first=apply(xs,selected<N>);return same(xs[0],xs[0]);}
math fn good<M:nat>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,nested<M>);}
)",
                  "same(xs[0],xs[0])");
  });
  cases.run("reused first selected factory recipe obeys exact work",
            [] { finiteBudgets(factorySource(), "wrapper<A>", true); });
  for (bool middle : {false, true})
    cases.run("selected factory refuses a conflated recipe " +
                  std::to_string(middle),
              [&] {
                refuses(ordinary(factorySource(middle ? 4 : 2, middle ? 4 : 2)),
                        "source.data-bound");
              });
  cases.run("selected factory recipes close through candidate replay", [] {
    preparesOrdinary(factorySource() + R"(
pub protocol Run roles(P)(x:F@P)->(result:(Array<F,4>,Array<F,2>,Array<F,4>)@P){return good(x);}
)");
  });
  cases.run("inferred Math selection forwards and closes actual declaration",
            [] { prepares(helpers + run); });
  cases.run("explicit static reference", [] {
    prepares(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return apply(x, identity<bool>)
)");
  });
  cases.run("distinct named statics do not alias in summaries or closure", [] {
    prepares(helpers + R"(
def tag<N: nat>(x: bool) -> index:
    return index<N>()
pub protocol Run roles(P)(x: bool @P) -> (index, index) @P:
    return (forward(x, tag<2>), forward(x, tag<7>))
)");
  });
  cases.run("direct and named invocations reuse one ordinary declaration", [] {
    auto project = take(check(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> (bool, bool, bool) @P:
    return (identity(x), forward(x, identity), forward(x, identity))
)"));
    auto closed = take(closeNativeRun(project, "m::Run"));
    unsigned count = 0;
    for (const auto &decl : closed.declarations())
      if (decl.name == "identity" && decl.origin) {
        ++count;
        require(decl.origin.has_value() && !decl.scopedOrigin &&
                    !decl.anonymous,
                "named declaration was synthesized as a lambda");
      }
    require(count == 1,
            "named and direct calls duplicated specialization owner");
  });
  cases.run("named Local selection retains stop effects", [] {
    prepares(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    result <- ordered(x, checked)
    return result
)");
  });
  cases.run("member generics retain abstract selection through forwarding", [] {
    prepares(helpers + R"(
interface Identity:
    def run<T: Type + Copy + Drop>(x: T) -> T
module Implementation: Identity:
    def run<T: Type + Copy + Drop>(x: T) -> T:
        return x
def through<C: Identity>(x: bool) -> bool:
    return forward(x, C::run<bool>)
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return through<Implementation>(x)
)");
  });
  cases.run("imports and reexports preserve provider and complete route", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto captured = take(capture(
        {{"provider",
          "pub def same<T: Type + Copy + Drop>(x: T) -> T:\n    return x\n",
          "provider.zkc"},
         {"exports", "pub use provider::{same}\n", "exports.zkc"},
         {"m", "use exports as selected\n" + helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return forward(x, selected::same)
)",
          "named.zkc"}},
        options));
    auto project = take(analyze(captured).checkedProject());
    auto entry = take(closeNativeRun(project, "m::Run"));
    auto original = take(prepareOriginal(entry));
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
  });
  cases.run("nested lambda forwards a named helper without capturing it", [] {
    prepares(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return apply(x, fn(y) => forward(y, identity))
)");
  });
  cases.run("unused callback retains exact selection and formation", [] {
    prepares(helpers + R"(
def unused(x: bool, f: fn(bool) -> bool) -> bool:
    return x
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return unused(x, identity)
)");
  });
  cases.run("empty Local effects do not convert its mode", [] {
    refuses(check(helpers + R"(
local def empty(x: bool) -> bool effects():
    return x
def bad(x: bool) -> bool:
    return apply(x, empty)
)"),
            "source.scoped");
  });
  cases.run("named Local effect ceiling is enforced", [] {
    refuses(check(helpers + R"(
local def clean(x: bool, f: local fn(bool) -> bool effects()) -> bool effects():
    result <- f(x)
    return result
local def bad(x: bool) -> bool effects():
    result <- clean(x, checked)
    return result
)"),
            "source.effect");
  });
  cases.run("helper input and result shape are both constrained", [] {
    refuses(check(helpers + R"(
def wrong(x: (bool, bool)) -> bool:
    return x.0
def bad(x: bool) -> bool:
    return apply(x, wrong)
)"),
            "source.type");
  });
  for (bool math : {false, true})
    cases.run(math ? "Local does not convert to Math"
                   : "Math does not convert to Local",
              [=] {
                refuses(check(helpers + (math ? R"(
def bad(x: bool) -> bool:
    return apply(x, checked)
)"
                                              : R"(
local def bad(x: bool) -> bool:
    result <- ordered(x, identity)
    return result
)")),
                        "source.scoped");
              });
  cases.run("named functions have no runtime value", [] {
    refuses(check(helpers + R"(
def bad(x: bool) -> bool:
    stored = identity
    return x
)"),
            "source.name");
  });
  cases.run("braced source accepts explicit and inferred named statics", [] {
    take(ordinary(R"(module m;
math fn apply(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
math fn identity<T:Type+Copy+Drop>(x:T)->T{return x;}
math fn good(x:bool)->(bool,bool){return (apply(x,identity),apply(x,identity<bool>));}
)"));
  });
  cases.run("lexical data cannot shadow a callable declaration", [] {
    refuses(check(helpers + R"(
def bad(x: bool) -> bool:
    identity = x
    return apply(x, identity)
)"),
            "source.shadow");
  });
  cases.run("View declarations are not Math callbacks", [] {
    refuses(check(helpers + R"(
view def view_identity(x: bool) -> bool:
    return x
def bad(x: bool) -> bool:
    return apply(x, view_identity)
)"),
            "source.scoped");
  });
  cases.run("named data preconditions cannot strengthen an unused callback",
            [] {
              refuses(ordinary(R"(module m;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
math fn unused(xs:Vector<F>,i:index,f:math fn(Vector<F>,index)->bool)->bool{return true;}
math fn restricted(xs:Vector<F>,i:index)->bool where in_bounds(i,xs){return true;}
math fn bad(xs:Vector<F>,i:index)->bool{return unused(xs,i,restricted);}
)"),
                      "source.data-bound");
            });
  cases.run("tautological header guarantees need no callback strengthening",
            [] {
              take(ordinary(R"(module m;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
math fn apply(xs:Vector<F>,f:math fn(Vector<F>)->bool)->bool{return f(xs);}
math fn same(xs:Vector<F>)->bool where equal_extent(xs,xs){return true;}
math fn good(xs:Vector<F>)->bool{return apply(xs,same);}
)"));
            });
  cases.run("abstract named header guarantees are proved independently", [] {
    take(ordinary(R"(module m;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
math fn apply(xs:Vector<F>,f:math fn(Vector<F>)->bool)->bool{return f(xs);}
interface Same { math fn same(xs:Vector<F>)->bool where equal_extent(xs,xs); }
math fn good<C:Same>(xs:Vector<F>)->bool{return apply(xs,C::same);}
)"));
  });
  cases.run("abstract named header cannot strengthen unused callback", [] {
    refuses(ordinary(R"(module m;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
math fn unused(xs:Vector<F>,i:index,f:math fn(Vector<F>,index)->bool)->bool{return true;}
interface Restricted { math fn restricted(xs:Vector<F>,i:index)->bool where in_bounds(i,xs); }
math fn bad<C:Restricted>(xs:Vector<F>,i:index)->bool{return unused(xs,i,C::restricted);}
)"),
            "source.data-bound");
  });
  cases.run("receiving static extents discharge complete named headers", [] {
    take(ordinary(R"(module m;
domain F=field("koala-bear");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
math fn apply(xs:Array<F,4>,ys:Array<F,4>,f:math fn(Array<F,4>,Array<F,4>)->bool)->bool{return f(xs,ys);}
math fn same(xs:Array<F,4>,ys:Array<F,4>)->bool where equal_extent(xs,ys){return true;}
interface Same { math fn same(xs:Array<F,4>,ys:Array<F,4>)->bool where equal_extent(xs,ys); }
math fn good<C:Same>(xs:Array<F,4>,ys:Array<F,4>)->(bool,bool){return (apply(xs,ys,same),apply(xs,ys,C::same));}
)"));
  });
  for (bool abstract : {false, true})
    for (StringRef selection : {"same<4,4>", "same"})
      for (StringRef consumer : {"apply", "unused"})
        cases.run("selected generic extents " + std::to_string(abstract) +
                      selection.str() + consumer.str(),
                  [&] {
                    const std::string selected =
                        (abstract ? "C::" : "") + selection.str();
                    auto source =
                        extentPrelude + "math fn good" +
                        (abstract ? std::string("<C:Same>") : "") +
                        "(xs:Array<F,4>,ys:Array<F,4>)->bool{return " +
                        consumer.str() + "(xs,ys," + selected + ");}\n" +
                        "pub protocol Run "
                        "roles(P)(xs:Array<F,4>@P,ys:Array<F,4>@P)->(result:"
                        "bool@P){return good" +
                        (abstract ? "<Implementation>" : "") + "(xs,ys);}";
                    replayOrdinary(source);
                  });
  for (StringRef call :
       {"same<4,4>(xs,ys)", "apply(xs,ys,fn(a,b)=>same<4,4>(a,b))",
        "apply(xs,ys,fn(a,b)=>unused(a,b,same))"})
    cases.run("selected extent direct and nested controls " + call.str(), [&] {
      replayOrdinary(extentPrelude +
                     "math fn good(xs:Array<F,4>,ys:Array<F,4>)->bool{return " +
                     call.str() + ";}");
    });
  for (StringRef body :
       {"return xs;", "let nested=(xs.0,xs.1);let "
                      "checked=same<N,M>(nested.0,nested.1);return nested;"})
    cases.run("selected tuple body observes substituted generic types " +
                  body.str(),
              [&] {
                replayOrdinary(extentPrelude + R"(
math fn pair<A:Type+Copy+Drop,B:Type+Copy+Drop>(xs:A,ys:B,f:math fn(A,B)->A)->A{return f(xs,ys);}
math fn selected<N:nat,M:nat>(xs:(Array<F,N>,Array<F,M>),ys:bool)->(Array<F,N>,Array<F,M>) where equal_extent(xs.0,xs.1){)" +
                               body.str() + R"(}
math fn good(xs:(Array<F,4>,Array<F,4>))->(Array<F,4>,Array<F,4>){return pair(xs,true,selected<4,4>);}
)");
              });
  for (bool abstract : {false, true})
    for (bool explicitStatics : {false, true})
      for (unsigned trips : {0, 4})
        for (unsigned extent : {4, 5})
          cases.run("selected generic zero-trip formation " +
                        std::to_string(abstract) +
                        std::to_string(explicitStatics) +
                        std::to_string(trips) + std::to_string(extent),
                    [&] {
                      auto source =
                          extentPrelude + R"(
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn restricted<N:nat,M:nat>(state:(Array<F,N>,Array<F,M>),i:index)->(Array<F,N>,Array<F,M>) where equal_extent(state.0,state.1){return state;}
interface Restricted{math fn restricted<N:nat,M:nat>(state:(Array<F,N>,Array<F,M>),i:index)->(Array<F,N>,Array<F,M>) where equal_extent(state.0,state.1);}
)" + "math fn good" + (abstract ? std::string("<C:Restricted>") : "") +
                          "(xs:(Array<F,4>,Array<F," + std::to_string(extent) +
                          ">))->(Array<F,4>,Array<F," + std::to_string(extent) +
                          ">){return fold(range(index<0>(),index<" +
                          std::to_string(trips) + ">()),xs," +
                          (abstract ? "C::" : "") + "restricted" +
                          (explicitStatics
                               ? "<4," + std::to_string(extent) + ">"
                               : "") +
                          ");}";
                      if (extent == 5)
                        refuses(ordinary(source), "source.data-bound");
                      else
                        replayOrdinary(source);
                    });
  for (bool nested : {false, true})
    for (unsigned count : {4, 5})
      cases.run("selected body static cardinality " + std::to_string(nested) +
                    std::to_string(count),
                [&] {
                  auto source =
                      extentPrelude + R"(
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Array<F,N>=finite("math.collect.field_array");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn value(x:F,f:math fn(F)->Array<F,4>)->Array<F,4>{return f(x);}
math fn selected<N:nat>(x:F)->Array<F,4>{return )" +
                      (nested ? std::string("value(x,fn(a)=>") : "") +
                      "fixed(range(index<0>(),index<N>()),fn(i)=>" +
                      (nested ? "a))" : "x)") + ";}" +
                      "math fn good(x:F)->Array<F,4>{return value(x,selected<" +
                      std::to_string(count) + ">);}";
                  if (count == 5)
                    refuses(ordinary(source), "source.data-bound");
                  else
                    replayOrdinary(source);
                });
  for (unsigned count : {4, 5})
    cases.run("inherited module statics and nested exact dispatch " +
                  std::to_string(count),
              [&] {
                auto source = extentPrelude + R"(
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Array<F,N>=finite("math.collect.field_array");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn value(x:F,f:math fn(F)->Array<F,4>)->Array<F,4>{return f(x);}
interface Producer{math fn make(x:F)->Array<F,4>;}
module Maker<N:nat>:Producer{
 math fn make(x:F)->Array<F,4>{return value(x,fn(a)=>fixed(range(index<0>(),index<N>()),fn(i)=>a));}
}
math fn outer<C:Producer>(x:F)->Array<F,4>{return value(x,C::make);}
math fn good(x:F)->Array<F,4>{return value(x,outer<Maker<)" +
                              std::to_string(count) + ">>);}";
                if (count == 5)
                  refuses(ordinary(source), "source.data-bound");
                else
                  replayOrdinary(source);
              });
  for (unsigned count : {4, 5})
    cases.run("selected static factory traversal " + std::to_string(count),
              [&] {
                auto source = extentPrelude + R"(
math fn fixed<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Array<F,N>=finite("math.collect.field_array");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
module Ranges<N:nat>{pub domain fn rows(lo:index,hi:index)->domain<index>{return range(lo,hi);}}
math fn value(x:F,f:math fn(F)->Array<F,4>)->Array<F,4>{return f(x);}
math fn selected<N:nat>(x:F)->Array<F,4>{return fixed(Ranges<N>::rows(index<0>(),index<N>()),fn(i)=>x);}
math fn good(x:F)->Array<F,4>{return value(x,selected<)" +
                              std::to_string(count) + ">);}";
                if (count == 5)
                  refuses(ordinary(source), "source.data-bound");
                else
                  replayOrdinary(source);
              });
  for (StringRef argument : {"Missing", "bool"}) {
    for (bool layout : {false, true}) {
      for (StringRef value : {"x", "f"})
        cases.run("lexical bare statics refuse " + std::to_string(layout) +
                      value.str() + argument.str(),
                  [&] {
                    std::string source;
                    if (layout)
                      source = helpers +
                               "def bad(x: bool, f: fn(bool) -> bool) -> "
                               "bool:\n    return " +
                               (value == "x"
                                    ? "x<" + argument.str() + ">"
                                    : "apply(x, f<" + argument.str() + ">)") +
                               "\n";
                    else
                      source = "module m; math fn apply(x:bool,f:math "
                               "fn(bool)->bool)->bool{return f(x);}" +
                               std::string("math fn bad(x:bool,f:math "
                                           "fn(bool)->bool)->bool{return ") +
                               (value == "x"
                                    ? "x<" + argument.str() + ">"
                                    : "apply(x,f<" + argument.str() + ">)") +
                               ";}";
                    refuses(layout ? check(source) : ordinary(source),
                            "source.static-argument");
                  });
    }
  }
  for (StringRef argument : {"Missing", "bool"}) {
    for (StringRef expression :
         {"alias<ARG>", "alias<ARG>.0", "apply(x,fn(y)=>alias<ARG>.0)"})
      cases.run("lexical alias place and capture statics " + expression.str() +
                    argument.str(),
                [&] {
                  auto expr = expression.str();
                  expr.replace(expr.find("ARG"), 3, argument.str());
                  refuses(check(helpers +
                                "def bad(x: bool) -> bool:\n    alias = (x, "
                                "x)\n    ignored = " +
                                expr + "\n    return x\n"),
                          "source.static-argument");
                });
    cases.run("domain forwarding rejects lexical statics " + argument.str(),
              [&] {
                refuses(ordinary(extentPrelude + R"(
math fn accept_domain(rows:domain<index>)->bool{return true;}
math fn bad(rows:domain<index>)->bool{return accept_domain(rows<)" +
                                 argument.str() + ">);}"),
                        "source.static-argument");
              });
    cases.run("layout domain recipe rejects lexical statics " + argument.str(),
              [&] {
                refuses(check(R"(
type Finite<I:Type+Copy+Drop> = builtin("finite",I)
view def invalid(rows: Finite<index>) -> Finite<index>:
    return rows<)" + argument.str() +
                              ">\n"),
                        "source.static-argument");
              });
    cases.run("braced lexical shadow retains precedence " + argument.str(),
              [&] {
                refuses(ordinary(R"(module m;
math fn identity<T:Type+Copy+Drop>(x:T)->T{return x;}
math fn apply(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
math fn bad(x:bool,identity:math fn(bool)->bool)->bool{return apply(x,identity<)" +
                                 argument.str() + ">);}"),
                        "source.shadow");
              });
  }
  cases.run(
      "common summaries retain actual named bodies across forwarding", [] {
        auto project = take(check(helpers + R"(
def always(x: bool) -> bool:
    return true
pub protocol Run roles(P,V)(x: bool @(P,V),y: bool @(P,V)) -> () @(P,V):
    if forward(x, always):
        ()
    else:
        ()
    if forward(y, identity):
        ()
    else:
        ()
    return ()
)"));
        for (const auto &decl : project.declarations())
          if (decl.name == "Run") {
            const auto rows =
                take(deriveCommonControlRequirements(project, decl.id));
            require(rows.size() == 1 && rows.front().components.size() == 2,
                    "named bodies changed common observation coverage");
            for (const auto &component : rows.front().components)
              require(component.input == 1 && component.path.empty(),
                      "named summary conflated constant and input provenance");
            return;
          }
        require(false, "missing common summary entry");
      });
  cases.run("zero trip finite callback remains checked", [] {
    auto project = take(ordinary(R"(module m;
domain F=field("koala-bear");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn accumulate(state:F,item:index)->F{return state+1;}
math fn work()->F{return fold(range(index<0>(),index<0>()),0,accumulate);}
protocol Run roles(P)()->(result:F@P){return work();}
)"));
    auto closed = take(closeNativeRun(project, "m::Run"));
    auto original = take(prepareOriginal(closed));
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
  });
  cases.run("zero trip cannot hide a named callback precondition", [] {
    refuses(ordinary(R"(module m;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn restricted(state:Vector<F>,i:index)->Vector<F> where in_bounds(i,state){return state;}
math fn bad(xs:Vector<F>)->Vector<F>{return fold(range(index<0>(),index<0>()),xs,restricted);}
)"),
            "source.data-bound");
  });
  for (unsigned mutation = 0; mutation < 15; ++mutation)
    cases.run(
        "independent named selection mutation " + std::to_string(mutation),
        [=] {
          auto project = take(check(helpers + run));
          bool changed = false;
          for (const auto &decl : project.declarations()) {
            if (!decl.body)
              continue;
            auto body = std::make_shared<Body>(*decl.body);
            for (auto &binding : body->scopedBindings) {
              if (!binding.named)
                continue;
              auto named = std::make_shared<SelectedCallable>(*binding.named);
              switch (mutation) {
              case 0:
                named->target.declaration.index = decl.id.index;
                break;
              case 1:
                named->target.reference.path.clear();
                break;
              case 2:
                named->arguments.front() = Type(Type::Kind::Index);
                break;
              case 3:
                named->signature.mode = ScopedSignature::Mode::Local;
                break;
              case 4:
                named->effects.fixed.mayStop = true;
                break;
              case 5:
                binding.source.reset();
                break;
              case 6:
                binding.captures.push_back({0});
                break;
              case 7:
                named->target.authoredReference = 99999;
                break;
              case 8:
                binding.named.reset();
                break;
              case 9:
                named->target.reference.provider.index = decl.id.index;
                break;
              case 10:
                named->signature.result = Type(Type::Kind::Index);
                break;
              case 11:
                named->signature.inputs.clear();
                break;
              case 12:
                named->target.module = Type(Type::Kind::Module, "forged");
                break;
              case 13:
                named->effects.dependencies.emplace(0, Effects{true, false});
                break;
              case 14:
                binding.signature.allowance.mayStop = true;
                break;
              }
              if (mutation != 8)
                binding.named = std::move(named);
              const_cast<Declaration &>(decl).body = body;
              changed = true;
              break;
            }
            if (changed)
              break;
          }
          require(changed, "named selection mutation did not reach a binding");
          refusal(checkScopedElaboration(project), "source.scoped-witness");
        });
  cases.run("named binding cannot borrow a literal source witness", [] {
    auto project = take(check(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> (bool,bool) @P:
    return (forward(x, identity),forward(x, fn(y) => y))
)"));
    for (const auto &decl : project.declarations()) {
      if (!decl.body)
        continue;
      std::optional<unsigned> literal;
      for (const auto &binding : decl.body->scopedBindings)
        if (binding.computation)
          literal = binding.source;
      if (!literal)
        continue;
      auto body = std::make_shared<Body>(*decl.body);
      for (auto &binding : body->scopedBindings)
        if (binding.named) {
          binding.source = literal;
          const_cast<Declaration &>(decl).body = body;
          refusal(checkScopedElaboration(project), "source.scoped-witness");
          return;
        }
    }
    require(false, "mutation did not find named and literal bindings");
  });
  cases.run("selected record copies obey the exact work allowance", [] {
    auto project = take(check(helpers + run));
    const SelectedCallable *selection = nullptr;
    for (const auto &decl : project.declarations())
      if (decl.body)
        for (const auto &binding : decl.body->scopedBindings)
          if (binding.named)
            selection = binding.named.get();
    require(selection != nullptr, "missing named selection");
    namespace detail = zkc::language::detail;
    Limits limits;
    detail::Work measured{limits};
    detail::Semantics types(project.declarations(), {}, measured);
    require(detail::chargeSelectedCallable(types, *selection, {}),
            "cannot measure selected record");
    const auto cost = measured.used;
    require(cost > 1, "selected record did not charge its metadata");
    for (bool shortBudget : {false, true}) {
      uint64_t remaining = cost - shortBudget;
      detail::Work work{limits};
      work.allowance = &remaining;
      detail::Semantics bounded(project.declarations(), {}, work);
      require(detail::chargeSelectedCallable(bounded, *selection, {}) ==
                  !shortBudget,
              "selected record ignored its exact copy allowance");
      if (shortBudget)
        require(bounded.diagnostic &&
                    bounded.diagnostic->code == "source.limit",
                "short copy allowance lost its diagnostic");
      else
        require(remaining == 0, "exact allowance was not consumed");
    }
  });
  cases.run("named edges obey the source call depth limit", [] {
    Limits limits;
    limits.callDepth = 2;
    refuses(check(helpers + run, limits), "source.limit");
    auto project = take(check(helpers + run));
    refuses(closeNativeRun(project, "m::Run", limits), "source.limit");
  });
  cases.run(
      "cold and reused named instances obey exact specialization work", [] {
        auto project = take(check(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> (bool, bool, bool) @P:
    return (identity(x), forward(x, identity), forward(x, identity))
)"));
        namespace detail = zkc::language::detail;
        auto specialize = [&](detail::Work &work) {
          std::vector<Declaration> declarations(project.declarations().begin(),
                                                project.declarations().end());
          Declaration entry;
          entry.id = {uint32_t(declarations.size())};
          entry.kind = Declaration::Kind::Entry;
          for (const auto &decl : declarations)
            if (decl.name == "Run")
              entry.target = decl.id;
          require(entry.target.has_value(), "missing specialization target");
          const auto selected = entry.id;
          declarations.push_back(std::move(entry));
          return detail::specialize(declarations, project.assets(), work,
                                    selected);
        };
        Limits limits;
        detail::Work measured{limits};
        if (auto error = specialize(measured))
          throw std::runtime_error(toString(std::move(error)));
        require(measured.used > 1, "specialization did not charge work");
        for (bool shortBudget : {false, true}) {
          uint64_t remaining = measured.used - shortBudget;
          detail::Work work{limits};
          work.allowance = &remaining;
          auto error = specialize(work);
          if (shortBudget)
            refusal(std::move(error), "source.limit");
          else {
            require(!error, "measured exact specialization allowance failed");
            require(remaining == 0 && work.used == measured.used,
                    "specialization reuse escaped cumulative accounting");
          }
        }
      });
  cases.run("independent closure rejects a forged named declaration origin",
            [] {
              auto project = take(check(helpers + run));
              auto closed = take(closeNativeRun(project, "m::Run"));
              bool changed = false;
              for (const auto &decl : closed.declarations())
                if (decl.name == "identity" && decl.origin) {
                  const_cast<Declaration &>(decl).origin->index = 0;
                  changed = true;
                }
              require(changed, "missing named declaration specialization");
              refusal(checkScopedSpecialization(closed),
                      "source.scoped-specialization");
            });
  return cases.result();
}
