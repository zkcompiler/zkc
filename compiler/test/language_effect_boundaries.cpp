#include "../lib/Language/Effects.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
constexpr Span invocationSpan{{0}, 40, 60};
constexpr Span bindingSpan{{0}, 10, 30};
Expected<CheckedProject> check(StringRef source, const Limits &limits = {}) {
  auto captured =
      capture({{"m", "module m;domain Fr=field(\"koala-bear\");" + source.str(),
                "effect-boundaries.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
const Declaration &named(ArrayRef<Declaration> declarations, StringRef name) {
  for (const auto &decl : declarations)
    if (decl.name == name && decl.body)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}
void succeeds(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refuses(Error error, StringRef code) {
  require(bool(error), "expected refusal: " + code);
  auto diagnostic = diagnose(std::move(error));
  require(diagnostic && diagnostic->code == code, "unexpected diagnostic");
}
void diagnosticAt(const Semantics &types, StringRef code, Span span) {
  require(types.diagnostic && types.diagnostic->code == code,
          "wrong effect diagnostic identifier");
  const auto &primary = types.diagnostic->primary;
  require(primary && primary->source.index == span.source.index &&
              primary->begin == span.begin && primary->end == span.end,
          "effect diagnostic lost its source span");
}
ScopedBinding formal() {
  ScopedBinding result{};
  result.signature.mode = ScopedSignature::Mode::Local;
  result.signature.allowance = {true, true};
  result.parameter = 0;
  result.span = bindingSpan;
  return result;
}
ScopedBinding captured(unsigned index) {
  auto result = formal();
  result.parameter.reset();
  auto computation = std::make_shared<ScopedComputation>();
  auto body = std::make_shared<Body>();
  body->mode = Body::Mode::Local;
  body->effects.dependencies.emplace(0, Effects{true, true});
  computation->signature = result.signature;
  computation->body = body;
  result.computation = computation;
  result.scopedCaptures = {index};
  return result;
}
// Copy just the path being mutated so that the closed entry's retained source
// remains intact. Child indices enumerate immediate regions in operation order.
std::shared_ptr<const Body> eraseRegionEffects(const Body &source,
                                               ArrayRef<unsigned> path) {
  auto body = std::make_shared<Body>(source);
  if (path.empty()) {
    require(body->effects.fixed.mayStop, "mutation target is not stopping");
    body->effects = {};
    return body;
  }
  unsigned index = 0;
  for (auto &op : body->operations) {
    if (auto *control = std::get_if<LocalControl>(&op.action)) {
      for (auto &region : control->regions)
        if (index++ == path.front()) {
          region = eraseRegionEffects(*region, path.drop_front());
          return body;
        }
    } else if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
      if (index++ == path.front()) {
        repeat->region = eraseRegionEffects(*repeat->region, path.drop_front());
        return body;
      }
    }
  }
  throw std::runtime_error("missing mutation region");
}
} // namespace
int main() {
  Cases cases;
  cases.run("one call level permits formal invocation and nested regions", [] {
    Limits limits;
    limits.callDepth = 1;
    auto project = take(check(R"(
fn apply(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}
fn branches(go:bool,x:Fr,f:fn(Fr)->Fr)->Fr effects(f){
 return if go {if go {f(x)} else {x}} else {f(x)};
}
)",
                              limits));
    const auto &body = *named(project.declarations(), "branches").body;
    require(body.effects.dependencies ==
                    std::map<unsigned, Effects>{{0, {true, true}}} &&
                body.effects.fixed == Effects{},
            "region composition lost callback identity or precision");
    succeeds(checkScopedElaboration(project, limits));
    limits.expressionDepth = 1;
    refuses(checkScopedElaboration(project, limits), "source.limit");
  });
  cases.run(
      "one call level permits nested protocol regions through closure", [] {
        Limits limits;
        limits.callDepth = 1;
        auto project = take(check(R"(
protocol Demo roles(P)(n:index@P,go:bool@P,x:Fr@P)->(r:Fr@P){
 for _ in 0..n roles(P) max 2 {
   for _ in 0..n roles(P) max 2 {require @P go;}
 }
 return x;
}
run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)",
                                  limits));
        auto closed =
            take(zkc::test::closeProtocolDeployment(project, "m::Run", limits));
        succeeds(checkScopedSpecialization(closed, limits));
        limits.expressionDepth = 1;
        refuses(checkScopedSpecialization(closed, limits), "source.limit");
      });
  cases.run("real helper calls still consume call depth", [] {
    Limits limits;
    limits.callDepth = 1;
    StringRef source = "fn inner(x:Fr)->Fr{return x;}"
                       "fn outer(x:Fr)->Fr{return inner(x);}";
    refuses(check(source, limits), "source.limit");
    limits.callDepth = 2;
    take(check(source, limits));
  });
  for (StringRef kind : {"if", "match", "for"})
    cases.run("region callback capture preserves a later formal: " + kind, [&] {
      std::string statements, flagType = "bool";
      if (kind == "if")
        statements = "return if go {invoke(x,fn(y)=>b(y))} else {x};";
      else if (kind == "match") {
        flagType = "Choice";
        statements = "return match go {Left(v)=>{invoke(v,fn(y)=>b(y))},"
                     "Right(v)=>{v}};";
      } else
        statements = "let mut value=x;for _ in 0..n "
                     "{value=invoke(value,fn(y)=>b(y));}return value;";
      auto source =
          "enum Choice {Left(Fr),Right(Fr)}"
          "fn invoke(x:Fr,f:fn(Fr)->Fr)->Fr effects(f){return f(x);}"
          "fn pick(go:" +
          flagType +
          ",n:index,x:Fr,a:fn(Fr)->Fr,b:fn(Fr)->Fr effects(stop))->Fr "
          "effects(b){" +
          statements + "}protocol Demo roles(P)(go:" + flagType +
          "@P,n:index@P,x:Fr@P)->(r:Fr@P){"
          "return pick(go,n,x,fn(v)=>v,fn(v)=>{require v==1;v});}"
          "run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }";
      auto project = take(check(source));
      const auto &decl = named(project.declarations(), "pick");
      require(decl.body->effects.dependencies ==
                      std::map<unsigned, Effects>{{1, {true, false}}} &&
                  decl.body->effects.fixed == Effects{},
              "region capture changed callback effect identity");
      succeeds(checkScopedElaboration(project));
      auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Run"));
      const auto &closedEffects =
          named(closed.declarations(), "pick").body->effects;
      require(closedEffects.fixed == Effects{true, false} &&
                  closedEffects.dependencies.empty(),
              "region callback effect was lost during specialization");
      succeeds(checkScopedSpecialization(closed));
      auto wrongContract = source;
      wrongContract.replace(wrongContract.find("effects(b)"),
                            StringRef("effects(b)").size(), "effects(a)");
      refuses(check(wrongContract), "source.effect");

      auto body = std::make_shared<Body>(*decl.body);
      bool changed = false;
      for (auto &op : body->operations)
        if (auto *control = std::get_if<LocalControl>(&op.action)) {
          require(!control->regions.empty(), "missing control arm");
          auto region = std::make_shared<Body>(*control->regions.front());
          require(region->scopedBindings.size() >= 2,
                  "missing inherited callback parameters");
          std::swap(region->scopedBindings[0], region->scopedBindings[1]);
          control->regions.front() = std::move(region);
          changed = true;
          break;
        }
      require(changed, "missing control operation");
      const_cast<Declaration &>(decl).body = std::move(body);
      refuses(checkScopedElaboration(project), "source.scoped-witness");
    });
  cases.run("formal lookup needs no extra expression level", [] {
    Limits limits;
    limits.callDepth = limits.expressionDepth = 1;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    Body body{};
    body.mode = Body::Mode::Local;
    body.scopedBindings = {formal()};
    body.operations.push_back({ScopedInvoke{0, {}, 0}, {}, invocationSpan, 0});
    auto effect = inferEffects(types, declarations, body);
    require(effect && effect->dependencies ==
                          std::map<unsigned, Effects>{{0, {true, true}}},
            "formal lookup consumed another expression level");
  });
  for (unsigned depth : {1u, 2u})
    cases.run("capture expression depth " + std::to_string(depth), [&] {
      Limits limits;
      limits.callDepth = 1;
      limits.expressionDepth = depth;
      Work work{limits};
      std::vector<Declaration> declarations;
      Semantics types(declarations, {}, work);
      Body body{};
      body.mode = Body::Mode::Local;
      body.scopedBindings = {formal(), captured(0)};
      auto effect = bindingEffects(types, body, 1);
      if (depth == 1) {
        require(!effect, "capture traversal exceeded expression depth");
        diagnosticAt(types, "source.limit", bindingSpan);
      } else {
        require(effect && effect->dependencies ==
                              std::map<unsigned, Effects>{{0, {true, true}}},
                "capture depth was charged as call depth");
      }
    });
  cases.run("cyclic captures stop at the expression limit", [] {
    Limits limits;
    limits.expressionDepth = 3;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    Body body{};
    body.mode = Body::Mode::Local;
    body.scopedBindings = {captured(0)};
    require(!bindingEffects(types, body, 0), "cyclic capture accepted");
    diagnosticAt(types, "source.limit", bindingSpan);
  });
  for (StringRef malformed :
       {"index", "body", "empty-body", "capture", "dependency"})
    cases.run("malformed callback diagnostic: " + malformed, [&] {
      Limits limits;
      Work work{limits};
      std::vector<Declaration> declarations;
      Semantics types(declarations, {}, work);
      Body body{};
      body.mode = Body::Mode::Local;
      body.operations.push_back(
          {ScopedInvoke{0, {}, 0}, {}, invocationSpan, 0});
      if (malformed == "body") {
        auto binding = formal();
        binding.parameter.reset();
        body.scopedBindings = {binding};
      } else if (malformed == "empty-body") {
        auto binding = captured(0);
        binding.computation = std::make_shared<ScopedComputation>();
        body.scopedBindings = {binding};
      } else if (malformed == "capture") {
        body.scopedBindings = {captured(1)};
      } else if (malformed == "dependency") {
        auto binding = captured(0);
        binding.scopedCaptures.clear();
        body.scopedBindings = {binding};
      }
      require(!inferEffects(types, declarations, body),
              "malformed callback evidence accepted");
      diagnosticAt(types, "source.effect",
                   malformed == "index" ? invocationSpan : bindingSpan);
    });
  cases.run("effect work exhaustion retains the operation span", [] {
    Limits limits;
    limits.work = 0;
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    Body body{};
    body.mode = Body::Mode::Local;
    body.operations.push_back({ScopedInvoke{0, {}, 0}, {}, invocationSpan, 0});
    require(!inferEffects(types, declarations, body), "work limit bypassed");
    diagnosticAt(types, "source.limit", invocationSpan);
  });
  for (bool protocol : {false, true})
    cases.run(protocol ? "missing repeat effect evidence"
                       : "missing control effect evidence",
              [&] {
                Limits limits;
                Work work{limits};
                std::vector<Declaration> declarations;
                Semantics types(declarations, {}, work);
                Body body{};
                body.mode = protocol ? Body::Mode::Protocol : Body::Mode::Local;
                if (protocol) {
                  ProtocolRepeat repeat{};
                  body.operations.push_back({repeat, {}, invocationSpan, 0});
                } else {
                  LocalControl control{};
                  control.regions.push_back(nullptr);
                  body.operations.push_back({control, {}, invocationSpan, 0});
                }
                require(!inferEffects(types, declarations, body),
                        "missing region accepted");
                diagnosticAt(types, "source.effect", invocationSpan);
              });
  cases.run("bottom-up region composition uses linear work", [] {
    constexpr unsigned levels = 24;
    Limits limits;
    limits.work = 8 * (levels + 1);
    Work work{limits};
    std::vector<Declaration> declarations;
    Semantics types(declarations, {}, work);
    auto body = std::make_shared<Body>();
    body->mode = Body::Mode::Local;
    body->stopped = true;
    for (unsigned i = 0; i <= levels; ++i) {
      auto effects = inferEffects(types, declarations, *body);
      require(effects && effects->fixed.mayStop,
              "region effects re-traversed ancestors or lost stopping");
      body->effects = *effects;
      auto parent = std::make_shared<Body>();
      parent->mode = Body::Mode::Local;
      LocalControl control{};
      control.regions = {body};
      parent->operations.push_back({control, {}, invocationSpan, 0});
      body = parent;
    }
  });
  const std::string localRegions = R"(
fn branches(go:bool,x:Fr)->Fr effects(stop){
 require go;
 return if go {require go; if go {require go; x} else {require go; x}}
              else {require go; x};
}
protocol Demo roles(P)(go:bool@P,x:Fr@P)->(r:Fr@P){return branches(go,x);}
run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
  const std::string protocolRegions = R"(
protocol Demo roles(P)(n:index@P,go:bool@P,x:Fr@P)->(r:Fr@P){
 require @P go;
 for _ in 0..n roles(P) max 2 {
   require @P go;
   for _ in 0..n roles(P) max 2 {require @P go;}
 }
 return x;
}
run Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
  for (bool specialized : {false, true})
    for (bool protocol : {false, true}) {
      const std::vector<std::vector<unsigned>> paths =
          protocol
              ? std::vector<std::vector<unsigned>>{{0}, {0, 0}}
              : std::vector<std::vector<unsigned>>{{0}, {1}, {0, 0}, {0, 1}};
      for (unsigned i = 0; i < paths.size(); ++i)
        cases.run(
            std::string(specialized ? "closed" : "open") +
                (protocol ? " repeat" : " control") +
                " independently checks region " + std::to_string(i),
            [&] {
              auto project =
                  take(check(protocol ? protocolRegions : localRegions));
              auto closed =
                  take(zkc::test::closeProtocolDeployment(project, "m::Run"));
              succeeds(checkScopedElaboration(project));
              succeeds(checkScopedSpecialization(closed));
              auto declarations =
                  specialized ? closed.declarations() : project.declarations();
              auto &decl = const_cast<Declaration &>(
                  named(declarations, protocol ? "Demo" : "branches"));
              auto original = decl.body->effects;
              decl.body = eraseRegionEffects(*decl.body, paths[i]);
              require(decl.body->effects == original,
                      "mutation changed parent summary instead of its child");
              refuses(specialized ? checkScopedSpecialization(closed)
                                  : checkScopedElaboration(project),
                      specialized ? "source.scoped-specialization"
                                  : "source.scoped-witness");
            });
    }
  cases.run("registered primitives infer effects and enforce their ceiling",
            [] {
              auto project = take(check(R"(
type Vector<F:Field>=builtin("vector",F);
fn get<F:Field>(xs:Vector<F>,i:index)->F effects(stop)=primitive("vector.get");
math fn plus(a:Fr,b:Fr)->Fr=primitive("field.add");
)"));
              require(named(project.declarations(), "get").body->effects ==
                          EffectSummary{Effects{true, false}},
                      "ordered primitive summary differs");
              require(named(project.declarations(), "plus").body->effects ==
                          EffectSummary{},
                      "mathematical primitive acquired effects");
              succeeds(checkScopedElaboration(project));
              refuses(check(R"(
type Vector<F:Field>=builtin("vector",F);
fn get<F:Field>(xs:Vector<F>,i:index)->F effects()=primitive("vector.get");
)"),
                      "source.effect");
            });
  for (bool filtered : {false, true})
    cases.run(
        filtered ? "filtered finite effects and ceiling"
                 : "finite effects and ceiling",
        [&] {
          auto declaration = [&](StringRef allowance, bool math) {
            std::string mode = math ? "math " : "";
            std::string effect = math ? "" : " effects(stop)";
            std::string predicate =
                filtered ? "accept:" + mode + "fn(item:Fr)->bool" + effect +
                               " where item_from(item,rows),"
                         : "";
            return mode + "fn fold(rows:domain<Fr>,initial:Fr," + predicate +
                   "step:" + mode + "fn(Fr,item:Fr)->Fr" + effect +
                   " where item_from(item,rows))->Fr" + allowance.str() +
                   "=finite(\"" + (math ? "math" : "local") +
                   (filtered ? ".fold_where\");" : ".fold\");");
          };
          for (bool math : {false, true}) {
            auto project =
                take(check(declaration(math ? "" : " effects(stop)", math)));
            require(named(project.declarations(), "fold").body->effects ==
                        EffectSummary{Effects{!math, false}},
                    "finite callback or admission effects differ");
            succeeds(checkScopedElaboration(project));
          }
          refuses(check(declaration(" effects()", false)), "source.effect");
          refuses(check(declaration(" effects(opaque)", false)),
                  "source.effect");
          refuses(check(declaration(" effects(step)", false)), "source.effect");
        });
  return cases.result();
}
