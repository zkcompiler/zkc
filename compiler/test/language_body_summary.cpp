#include "../lib/Language/BodySummary.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
const Type boolean(Type::Kind::Boolean);
ScopedSignature signature(unsigned inputs = 1) {
  return {ScopedSignature::Mode::Math,
          std::vector<Type>(inputs, boolean),
          boolean,
          {}};
}
std::shared_ptr<Body> inputs(unsigned count) {
  auto body = std::make_shared<Body>();
  body->mode = Body::Mode::Math;
  body->inputs = count;
  for (unsigned i = 0; i < count; ++i)
    body->values.push_back({boolean, {i}, {}});
  return body;
}
ValueId operation(Body &body, decltype(Operation::action) action,
                  std::vector<unsigned> dependencies) {
  ValueId result{unsigned(body.values.size())};
  body.values.push_back({boolean, std::move(dependencies), {}});
  body.operations.push_back({std::move(action), {result}, {}, 0});
  return result;
}
std::shared_ptr<Body> identityBody(unsigned count = 1, unsigned result = 0) {
  auto body = inputs(count);
  body->results = {{result}};
  return body;
}
std::shared_ptr<Body> constant(unsigned count = 1) {
  auto body = inputs(count);
  body->results = {operation(
      *body, MathValue{MathematicalIdentity::BooleanConstant, {}, "true"}, {})};
  return body;
}
std::shared_ptr<ScopedComputation> computation(std::shared_ptr<const Body> body,
                                               unsigned arity = 1) {
  auto result = std::make_shared<ScopedComputation>();
  result->lexicalOwner = {0};
  result->expression = 0;
  result->signature = signature(arity);
  for (unsigned i = arity; i < body->inputs; ++i)
    result->captures.push_back({i, {}, body->values[i].type, {}});
  result->body = std::move(body);
  return result;
}
ScopedSummaryBinding binding(const ScopedComputation &selected,
                             std::vector<Dependencies> captures = {}) {
  return {&selected, selected.signature, {}, std::move(captures), {}, {}};
}
std::shared_ptr<Body> invocation(unsigned width = 0) {
  auto body = inputs(2);
  body->parameterizedSummary = true;
  body->scopedBindings.push_back({signature(), 0, {}, {}, {}, {}, {}});
  for (unsigned i = 0; i < width; ++i) {
    auto left = identityBody(), right = identityBody();
    Control control;
    control.kind = Control::Kind::If;
    control.operands = {{0}, {1}};
    control.regions = {left, right};
    operation(*body, std::move(control), {0, 1});
  }
  body->results = {operation(*body, ScopedInvoke{0, {{1}}, 0}, {})};
  return body;
}
BodySummaryApplication apply(BodySummaryCache &cache, Semantics &types,
                             const std::vector<Declaration> &declarations,
                             const Body &body, ArrayRef<Dependencies> arguments,
                             ArrayRef<ScopedSummaryBinding> callbacks = {},
                             ArrayRef<Dependencies> domains = {},
                             unsigned depth = 1) {
  auto result = cache.apply(types, declarations, body, {}, arguments, callbacks,
                            depth, domains);
  if (!result)
    throw std::runtime_error(toString(types.takeError()));
  return std::move(*result);
}
void dependency(const Dependencies &actual, std::vector<unsigned> expected,
                bool parameterized = false) {
  require(actual.inputs == expected && actual.parameterized == parameterized,
          "dependency slots or unresolved parameterization differ");
}
bool contains(ArrayRef<Dependencies> requirements,
              const std::vector<unsigned> &expected) {
  return llvm::any_of(requirements, [&](const Dependencies &value) {
    return value.inputs == expected && !value.parameterized;
  });
}
void refused(Semantics &types, StringRef code) {
  require(types.diagnostic && types.diagnostic->code == code,
          "unexpected body-summary refusal");
  types.diagnostic.reset();
}
std::vector<Declaration> graph(unsigned depth, bool diamond) {
  std::vector<Declaration> declarations(depth + 1);
  for (unsigned i = 0; i <= depth; ++i) {
    auto body = identityBody();
    if (i) {
      auto first =
          operation(*body, HelperCall{{i - 1}, {{0}}, {}, {}, {}}, {0});
      body->results = {first};
      if (diamond)
        body->results = {
            operation(*body, HelperCall{{i - 1}, {{0}}, {}, {}, {}}, {0})};
    }
    auto &declaration = declarations[i];
    declaration.kind = Declaration::Kind::Math;
    declaration.id = {i};
    declaration.name = "helper" + std::to_string(i);
    declaration.qualifiedName = "m::" + declaration.name;
    declaration.body = std::move(body);
  }
  return declarations;
}
uint64_t graphWork(unsigned depth, bool diamond) {
  auto declarations = graph(depth, diamond);
  Limits limits;
  Work work{limits};
  Semantics types(declarations, {}, work);
  BodySummaryCache cache;
  auto result = apply(cache, types, declarations, *declarations.back().body,
                      {{{17}, false}});
  dependency(result.results.front(), {17});
  return work.used;
}
uint64_t callbackGraphWork(unsigned depth, bool diamond) {
  auto declarations = graph(depth, diamond);
  declarations.front().body = invocation();
  for (unsigned i = 1; i <= depth; ++i) {
    auto body = inputs(2);
    body->parameterizedSummary = true;
    body->scopedBindings.push_back({signature(), 0, {}, {}, {}, {}, {}});
    for (unsigned edge = 0; edge < (diamond ? 2u : 1u); ++edge) {
      HelperCall call{{i - 1}, {{0}, {1}}, {}, {}, {}};
      call.scopedArguments = {0};
      body->results = {operation(*body, std::move(call), {})};
    }
    declarations[i].body = std::move(body);
  }
  auto selected = computation(identityBody());
  Limits limits;
  Work work{limits};
  Semantics types(declarations, {}, work);
  BodySummaryCache cache;
  auto result = apply(cache, types, declarations, *declarations.back().body,
                      {{{17}, false}, {{19}, false}}, {binding(*selected)});
  dependency(result.results.front(), {19});
  return work.used;
}
uint64_t repeatedWork(unsigned width, unsigned calls, bool parameterized) {
  const std::vector<Declaration> declarations;
  Limits limits;
  Work work{limits};
  Semantics types(declarations, {}, work);
  BodySummaryCache cache;
  auto body = invocation(width);
  auto selected = computation(identityBody());
  auto callback = binding(*selected);
  if (!parameterized) {
    body->scopedBindings.clear();
    body->operations.pop_back();
    body->values.pop_back();
    body->results = {{1}};
    body->formationRequirements = {{0, 1}};
    body->parameterizedSummary = false;
  }
  for (unsigned i = 0; i < calls; ++i) {
    auto result =
        apply(cache, types, declarations, *body, {{{10}, false}, {{20}, false}},
              parameterized ? ArrayRef<ScopedSummaryBinding>(callback)
                            : ArrayRef<ScopedSummaryBinding>());
    dependency(result.results.front(), {20});
    require(contains(result.formation, {10, 20}),
            "unused independent arms lost their formation demand");
  }
  return work.used;
}
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured = capture({{"m", "module m;" + source.str(), "summary.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "helper chain 40 and shared diamond 30 have linear charged work", [] {
        auto zero = graphWork(0, false), twenty = graphWork(20, false),
             forty = graphWork(40, false);
        require((forty - twenty) * 2 <= (twenty - zero) * 3,
                "helper chain summary construction grows superlinearly");
        auto fifteen = graphWork(15, true), thirty = graphWork(30, true);
        require(thirty <= fifteen * 2,
                "shared diamond expanded into an application tree");
        require(forty < 100000 && thirty < 100000,
                "bounded helper summary work exceeded its regression ceiling");
      });
  cases.run(
      "parameterized callback helper DAGs compose retained instances", [] {
        auto zero = callbackGraphWork(0, false),
             twenty = callbackGraphWork(20, false),
             forty = callbackGraphWork(40, false);
        require((forty - twenty) * 2 <= (twenty - zero) * 3,
                "callback helper chain repeatedly expands completed bodies");
        auto fifteen = callbackGraphWork(15, true),
             thirty = callbackGraphWork(30, true);
        require(
            thirty * 2 <= fifteen * 5 && thirty < 100000,
            "callback diamond expanded rather than reusing its shared child");
      });
  for (bool parameterized : {false, true})
    cases.run(parameterized
                  ? "callback instances have body-independent warm cost"
                  : "completed Math has body-independent warm cost",
              [=] {
                auto small = repeatedWork(40, 8, parameterized) -
                             repeatedWork(40, 1, parameterized);
                auto large = repeatedWork(400, 8, parameterized) -
                             repeatedWork(400, 1, parameterized);
                require(small == large && small > 0,
                        "incremental calls depend on callee body size");
              });
  cases.run("unknown callback is not a cached constant", [] {
    const std::vector<Declaration> declarations;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    BodySummaryCache cache;
    auto body = invocation();
    ScopedSummaryBinding unknown{nullptr, signature(), {}, {}, {}, {}};
    auto symbolic = apply(cache, types, declarations, *body,
                          {{{}, false}, {{}, false}}, {unknown});
    dependency(symbolic.results.front(), {}, true);
    require(symbolic.parameterized, "unknown callback became a constant");
    auto selected = computation(constant());
    auto concrete = apply(cache, types, declarations, *body,
                          {{{10}, false}, {{20}, false}}, {binding(*selected)});
    dependency(concrete.results.front(), {});
    require(!concrete.parameterized,
            "unknown selection leaked into new instance");
  });
  cases.run("capture aliasing and unused intermediate formation rebind", [] {
    const std::vector<Declaration> declarations;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    BodySummaryCache cache;
    auto callbackBody = constant(3);
    operation(*callbackBody,
              MathValue{MathematicalIdentity::BooleanAnd, {{1}, {2}}, {}},
              {1, 2});
    callbackBody->formationRequirements = {{1, 2}};
    auto selected = computation(callbackBody);
    auto body = invocation();
    auto first =
        apply(cache, types, declarations, *body, {{{1}, false}, {{2}, false}},
              {binding(*selected, {{{7}, false}, {{7}, false}})});
    dependency(first.results.front(), {});
    require(contains(first.formation, {7}),
            "aliased captures were not demanded");
    auto second =
        apply(cache, types, declarations, *body, {{{3}, false}, {{4}, false}},
              {binding(*selected, {{{8}, false}, {{9}, false}})});
    dependency(second.results.front(), {});
    require(contains(second.formation, {8, 9}) &&
                !contains(second.formation, {7}),
            "cached formation retained the first capture alias partition");
  });
  cases.run("finite fold rebinds domain, seed and callback capture slots", [] {
    const std::vector<Declaration> declarations;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    BodySummaryCache cache;
    auto body = inputs(1);
    body->parameterizedSummary = true;
    body->domainBindings.push_back(
        {DomainBinding::Kind::Parameter, boolean, {}, {}, 0, 0});
    body->scopedBindings.push_back({signature(2), 0, {}, {}, {}, {}, {}});
    body->results = {operation(
        *body,
        FiniteApplication{FiniteApplication::Kind::Fold, 0, 0, {}, {{0}}}, {})};
    auto step = inputs(3);
    step->results = {operation(
        *step, MathValue{MathematicalIdentity::BooleanAnd, {{1}, {2}}, {}},
        {1, 2})};
    step->formationRequirements = {{1, 2}};
    auto selected = computation(step, 2);
    auto first = apply(cache, types, declarations, *body, {{{10}, false}},
                       {binding(*selected, {{{30}, false}})}, {{{20}, false}});
    dependency(first.results.front(), {10, 20, 30});
    auto second = apply(cache, types, declarations, *body, {{{40}, false}},
                        {binding(*selected, {{{60}, false}})}, {{{50}, true}});
    dependency(second.results.front(), {40, 50, 60}, true);
    require(second.parameterized && !contains(second.formation, {20, 30}),
            "finite context reused an earlier domain judgment");
  });
  cases.run("finite collect retains predicate formation and eager domains", [] {
    const std::vector<Declaration> declarations;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    BodySummaryCache cache;
    auto body = inputs(2);
    body->parameterizedSummary = true;
    body->domainBindings.push_back(
        {DomainBinding::Kind::Range, boolean, {{0}, {1}}, {}, 0, {}});
    body->scopedBindings.push_back({signature(), 0, {}, {}, {}, {}, {}});
    body->scopedBindings.push_back({signature(), 1, {}, {}, {}, {}, {}});
    body->results = {operation(
        *body, FiniteApplication{FiniteApplication::Kind::Collect, 0, 0, 1, {}},
        {})};
    auto item = computation(identityBody());
    auto predicateBody = constant(2);
    operation(*predicateBody,
              MathValue{MathematicalIdentity::BooleanAnd, {{0}, {1}}, {}},
              {0, 1});
    predicateBody->formationRequirements = {{0, 1}};
    auto predicate = computation(predicateBody);
    for (unsigned offset : {0, 100}) {
      auto result = apply(
          cache, types, declarations, *body,
          {{{10 + offset}, false}, {{20 + offset}, false}},
          {binding(*item), binding(*predicate, {{{30 + offset}, false}})});
      dependency(result.results.front(), {10 + offset, 20 + offset});
      require(
          contains(result.formation, {10 + offset, 20 + offset, 30 + offset}),
          "unused predicate intermediate or eager domain operand vanished");
    }
  });
  cases.run("completed scratch callback lifetimes belong to the summary owner",
            [] {
              const std::vector<Declaration> declarations;
              Limits limits;
              Work work{limits};
              Semantics types(declarations, {}, work);
              auto body = invocation();
              std::weak_ptr<const ScopedComputation> retained;
              {
                BodySummaryCache cache;
                {
                  auto selected = computation(identityBody());
                  retained = selected;
                  auto callback = binding(*selected);
                  callback.owner = selected;
                  apply(cache, types, declarations, *body,
                        {{{1}, false}, {{2}, false}}, {callback});
                }
                require(!retained.expired(),
                        "discarded scratch body invalidated a key");
              }
              require(retained.expired(),
                      "callback lifetime escaped its summary owner");
            });
  cases.run(
      "nested callbacks rebind captured data and domains recursively", [] {
        const std::vector<Declaration> declarations;
        Limits limits;
        Work work{limits};
        Semantics types(declarations, {}, work);
        BodySummaryCache cache;
        auto outerBody = inputs(2);
        outerBody->parameterizedSummary = true;
        outerBody->domainBindings.push_back(
            {DomainBinding::Kind::Parameter, boolean, {}, {}, 0, 0});
        outerBody->scopedBindings.push_back(
            {signature(2), 0, {}, {}, {}, {}, {}});
        outerBody->results = {operation(
            *outerBody,
            FiniteApplication{FiniteApplication::Kind::Fold, 0, 0, {}, {{1}}},
            {})};
        auto outer = computation(outerBody);
        outer->scopedCaptures = {0};
        outer->domainCaptures = {0};
        auto stepBody = inputs(3);
        stepBody->results = {operation(
            *stepBody,
            MathValue{MathematicalIdentity::BooleanAnd, {{0}, {2}}, {}},
            {0, 2})};
        stepBody->formationRequirements = {{0, 2}};
        auto step = computation(stepBody, 2);
        auto body = invocation();
        for (unsigned offset : {0, 100}) {
          auto selected = binding(*outer, {{{42 + offset}, false}});
          selected.domains = {{{43 + offset}, false}};
          selected.scoped = {binding(*step, {{{44 + offset}, false}})};
          auto result = apply(cache, types, declarations, *body,
                              {{{10}, false}, {{20}, false}}, {selected});
          dependency(result.results.front(),
                     {42 + offset, 43 + offset, 44 + offset});
          auto reference =
              summarizeBody(types, declarations, *body, {},
                            {{{10}, false}, {{20}, false}}, {selected});
          require(bool(reference), "independent nested traversal refused");
          dependency(reference->results.front(), result.results.front().inputs);
        }
      });
  cases.run("cold and warm work allowances admit exactly L and refuse L-1", [] {
    auto body = invocation(40);
    auto selected = computation(identityBody());
    const std::vector<Declaration> declarations;
    for (bool warm : {false, true}) {
      uint64_t cost = 0;
      for (unsigned trial = 0; trial < 3; ++trial) {
        Limits limits;
        Work work{limits};
        Semantics types(declarations, {}, work);
        BodySummaryCache cache;
        if (warm)
          apply(cache, types, declarations, *body, {{{1}, false}, {{2}, false}},
                {binding(*selected)});
        uint64_t allowance = trial ? cost - (trial == 2) : limits.work;
        uint64_t initial = allowance, before = work.used;
        work.allowance = &allowance;
        auto result =
            cache.apply(types, declarations, *body, {},
                        {{{3}, false}, {{4}, false}}, {binding(*selected)});
        if (!trial) {
          require(bool(result), "initial allowance measurement refused");
          cost = work.used - before;
        } else if (trial == 1)
          require(result && !allowance && work.used - before == cost,
                  "exact measured summary allowance did not suffice");
        else {
          require(!result, "summary ignored L-1 allowance");
          refused(types, "source.limit");
          require(work.used - before == initial - allowance,
                  "failed summary lost admitted work");
        }
      }
    }
  });
  cases.run("failed applications publish no reusable contract", [] {
    const std::vector<Declaration> declarations;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto body = invocation(40);
    auto selected = computation(identityBody());
    uint64_t cold, warm;
    {
      BodySummaryCache cache;
      auto before = work.used;
      apply(cache, types, declarations, *body, {{{1}, false}, {{2}, false}},
            {binding(*selected)});
      cold = work.used - before;
      before = work.used;
      apply(cache, types, declarations, *body, {{{1}, false}, {{2}, false}},
            {binding(*selected)});
      warm = work.used - before;
    }
    BodySummaryCache cache;
    uint64_t allowance = cold - 1;
    work.allowance = &allowance;
    require(!cache.apply(types, declarations, *body, {},
                         {{{1}, false}, {{2}, false}}, {binding(*selected)}),
            "incomplete application accepted");
    refused(types, "source.limit");
    allowance = warm;
    require(!cache.apply(types, declarations, *body, {},
                         {{{3}, false}, {{4}, false}}, {binding(*selected)}),
            "failed application published a warm contract");
    refused(types, "source.limit");
    work.allowance = nullptr;
    auto result = apply(cache, types, declarations, *body,
                        {{{5}, false}, {{6}, false}}, {binding(*selected)});
    dependency(result.results.front(), {6});
  });
  cases.run("warm summaries preserve internal callback call and type bounds",
            [] {
              const std::vector<Declaration> declarations;
              Limits limits;
              Work work{limits};
              Semantics types(declarations, {}, work);
              BodySummaryCache cache;
              auto body = invocation();
              auto internal = identityBody();
              Type nested(Type::Kind::Tuple);
              nested.arguments = {boolean};
              internal->values.push_back({nested, {}, {}});
              auto selected = computation(internal);
              apply(cache, types, declarations, *body,
                    {{{1}, false}, {{2}, false}}, {binding(*selected)});
              limits.callDepth = 2;
              limits.typeDepth = 2;
              limits.typeNodes = 2;
              apply(cache, types, declarations, *body,
                    {{{3}, false}, {{4}, false}}, {binding(*selected)});
              require(!cache.apply(types, declarations, *body, {},
                                   {{{3}, false}, {{4}, false}},
                                   {binding(*selected)}, 2),
                      "warm application bypassed retained callback height");
              refused(types, "source.limit");
              limits.typeDepth = 1;
              require(!cache.apply(types, declarations, *body, {},
                                   {{{3}, false}, {{4}, false}},
                                   {binding(*selected)}),
                      "warm application bypassed internal type depth");
              refused(types, "source.limit");
              limits.typeDepth = 2;
              limits.typeNodes = 1;
              require(!cache.apply(types, declarations, *body, {},
                                   {{{3}, false}, {{4}, false}},
                                   {binding(*selected)}),
                      "warm application bypassed internal type node bound");
              refused(types, "source.limit");
            });
  cases.run("warm unrelated entries cannot hide a recursive source body", [] {
    auto declarations = graph(1, false);
    auto cyclic = inputs(1);
    cyclic->results = {
        operation(*cyclic, HelperCall{{1}, {{0}}, {}, {}, {}}, {0})};
    declarations[1].body = cyclic;
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    BodySummaryCache cache;
    apply(cache, types, declarations, *declarations[0].body, {{{1}, false}});
    require(!cache.apply(types, declarations, *cyclic, {}, {{{2}, false}}, {}),
            "recursive source body accepted through a retained entry");
    refused(types, "source.cycle");
  });
  cases.run(
      "source helper chain 40 and shared diamond 30 fit default limits", [] {
        for (bool diamond : {false, true}) {
          std::string source = "math fn helper0(x:bool)->bool{return x;}";
          unsigned depth = diamond ? 30 : 40;
          for (unsigned i = 1; i <= depth; ++i) {
            auto previous = "helper" + std::to_string(i - 1) + "(x)";
            source += "math fn helper" + std::to_string(i) + "(x:bool)->bool{";
            if (diamond)
              source += "let unused=" + previous + ";";
            source += "return " + previous + ";}";
          }
          take(check(source));
        }
      });
  cases.run("source formation preserves unused work and role placement", [] {
    const std::string helper = R"(
math fn apply_math(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
math fn subject(x:bool,a:bool,b:bool)->bool{
 return apply_math(x,fn(y)=>{let unused=a&&b;true});
})";
    take(check(helper + R"(
protocol Demo roles(P,Q)(x:bool@P,a:bool@Q,b:bool@Q)->(r:bool@Q){
 return subject(x,a,b);
})"));
    refuses(check(helper + R"(
protocol Demo roles(P,Q)(x:bool@P,a:bool@P,b:bool@Q)->(r:bool@P){
 return subject(x,a,b);
})"),
            "source.roles");
  });
  cases.run(
      "recorded implementation and defining callback frames select instances",
      [] {
        const std::string helper = R"(
interface Operation{math fn apply(x:bool)->bool;}
module Direct:Operation{math fn apply(x:bool)->bool{return x;}}
module Constant:Operation{math fn apply(x:bool)->bool{return true;}}
math fn invoke<C:Operation>(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
math fn choose<A:Operation,B:Operation>(x:bool)->bool{
 return invoke<B>(x,fn(y)=>A::apply(y));
})";
        take(check(helper + R"(
protocol Demo roles(P,Q)(a:bool@P,b:bool@Q)->(r:bool@P){
 let warm=choose<Direct,Constant>(a);
 return choose<Constant,Direct>(b);
})"));
        refuses(check(helper + R"(
protocol Demo roles(P,Q)(a:bool@P,b:bool@Q)->(r:bool@P){
 let warm=choose<Constant,Direct>(a);
 return choose<Direct,Constant>(b);
})"),
                "source.roles");
      });
  cases.run("unused staged statics retain lexical normalization stages", [] {
    auto project = take(check(R"(
math fn ignore<N:nat>(x:bool)->bool{return x;}
math fn inner<N:nat>(x:bool)->bool{return ignore<pow2(N)>(x);}
math fn outer<M:nat>(x:bool)->bool{return inner<pow2(M)>(x);}
protocol Demo<M:nat> roles(P)(x:bool@P)->(r:bool@P){return outer<M>(x);}
)"));
    auto argument = [](unsigned value) {
      Type natural(Type::Kind::Natural);
      natural.dimension = Natural::constant(value);
      return natural;
    };
    take(closeNativeRun(project, "m::Demo", {}, {argument(5)}));
    refuses(closeNativeRun(project, "m::Demo", {}, {argument(6)}),
            "source.natural");
  });
  for (bool formation : {false, true})
    cases.run(
        formation ? "independent witness rejects forged formation metadata"
                  : "independent witness rejects forged dependency metadata",
        [=] {
          auto project = take(check(R"(
math fn apply_math(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
math fn subject(x:bool,y:bool)->bool{let unused=x&&y;return apply_math(x,fn(v)=>v);}
protocol Demo roles(P)(x:bool@P,y:bool@P)->(r:bool@P){return subject(x,y);}
entry fn Run(inputs:Demo::Inputs){return Demo::run(inputs);}
)"));
          auto closed = take(closeProtocolDeployment(project, "m::Run"));
          bool changed = false;
          for (const auto &declaration : closed.declarations())
            if (declaration.name == "subject" && declaration.body) {
              auto body = std::make_shared<Body>(*declaration.body);
              if (formation)
                body->formationRequirements.clear();
              else
                body->values[body->results.front().index].components = {1};
              const_cast<Declaration &>(declaration).body = body;
              changed = true;
            }
          require(changed, "missing specialized helper to mutate");
          auto error = checkScopedSpecialization(closed);
          require(bool(error), "forged summary metadata accepted");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.scoped-specialization"),
                  "unexpected summary metadata refusal");
        });
  return cases.result();
}
