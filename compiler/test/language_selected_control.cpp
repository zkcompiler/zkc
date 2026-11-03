#include "mlir/Parser/Parser.h"
#include "support/ExternalSupply.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/CommonControl.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/CommonControl.h"
#include "zkc/Language/Inspection.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "selected.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.name == name;
  });
  require(found != project.declarations().end(), "missing declaration");
  return *found;
}
ClosedEntry closed(const CheckedProject &project) {
  // Semantic control checks also cover inputs supplied by another protocol,
  // including oracle handles and private record fields.
  return take(closeSubject(project, "m::Run"));
}
/// Publish through the production comparison, which maps every published
/// inventory through the component map and compares it with the actual native
/// analysis; return that analysis for the selected Protocol.
llvm::SmallVector<zkc::CommonControlRequirement>
nativeInventory(const ClosedEntry &entry) {
  auto original = take(prepareOriginal(entry));
  take(readInterface(original.bytes(), original.interfaceJson()));
  // Native rows refer to context-owned types and attributes.
  static auto *context = [] {
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    auto *result = new mlir::MLIRContext(registry);
    result->loadAllAvailableDialects();
    return result;
  }();
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), context);
  require(bool(module), "original did not parse");
  zkc::protocol_ir::MathematicalOp root;
  module->walk([&](zkc::protocol_ir::MathematicalOp function) {
    if (function.getSymName() == entry.protocol().symbol)
      root = function;
  });
  require(bool(root), "original omitted the selected Protocol");
  uint64_t remaining = 8000000;
  zkc::facts::Work work(remaining);
  return take(zkc::deriveCommonControlRequirements(root, work));
}
const Control &control(const Declaration &decl) {
  for (const auto &op : decl.body->operations)
    if (const auto *selected = std::get_if<Control>(&op.action))
      return *selected;
  throw std::runtime_error("missing selected control");
}
} // namespace
int main() {
  Cases cases;
  cases.run("Math branches keep all checked arms and dependencies", [] {
    auto project =
        take(check(R"(def choose(flag: bool, x: bool, y: bool) -> bool:
    return if flag:
        x
    else:
        y
pub protocol Run roles(P)(flag: bool @P, x: bool @P, y: bool @P) -> bool @P:
    result = choose(flag, x, y)
    return result
)"));
    auto &selected = control(named(project, "choose"));
    require(selected.regions.size() == 2 &&
                selected.regions[0]->mode == Body::Mode::Math,
            "Math control mode or arm coverage lost");
    auto entry = closed(project);
    require(take(deriveCommonControlRequirements(entry)).empty(),
            "role-local control needs no agreement");
  });
  cases.run("dormant Math arms are typechecked", [] {
    refuses(check(R"(def value() -> bool:
    return if true:
        false
    else:
        index<1>()
)"),
            "source.type");
  });
  cases.run("Math arms reject ordered Local work", [] {
    refuses(check(R"(local def ordered(x: bool) -> bool:
    return x
pub def value(x: bool) -> bool:
    return if true:
        x
    else:
        y <- ordered(x)
        y
)"),
            "source.mode");
  });
  cases.run("shared header exports actual immutable input requirements", [] {
    auto project = take(check(
        R"(pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @(P,V)) -> bool @(P,V):
    result = if flag roles(P,V):
        x
    else:
        x
    return result
)"));
    auto requirements = take(deriveCommonControlRequirements(closed(project)));
    require(requirements.size() == 1 && !requirements.front().tagOnly,
            "missing exact Boolean admission obligation");
    const auto &components = requirements.front().components;
    require(components.size() == 2 && components[0].input == 0 &&
                components[1].input == 0 && components[0].role == 0 &&
                components[1].role == 1 && components[0].path.empty(),
            "requirement guessed a name, public flag or wrong input");
  });
  cases.run("static shared control has no raw input requirement", [] {
    auto project = take(
        check(R"(pub protocol Run roles(P,V)(x: bool @(P,V)) -> bool @(P,V):
    result = if true:
        x
    else:
        x
    return result
)"));
    require(take(deriveCommonControlRequirements(closed(project))).empty(),
            "static selector acquired an obligation");
  });
  cases.run("role-local control accepts nonuniform selectors", [] {
    auto project = take(check(
        R"(pub protocol Run roles(P,V)(flag: bool @P, x: bool @P) -> bool @P:
    result = if flag roles(P):
        x
    else:
        x
    return result
)"));
    closed(project);
  });
  cases.run("role-local arms cannot hide a send to a peer", [] {
    refuses(
        check(
            R"(pub protocol Run roles(P,V)(flag: bool @P, x: bool @P) -> bool @P:
    if flag roles(P):
        sent <- send x from P to V
    else:
        ()
    return x
)"),
        "source.roles");
  });
  cases.run("Local results do not become shared evidence", [] {
    refuses(check(R"(local def identity(x: bool) -> bool:
    return x
pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @(P,V)) -> bool @(P,V):
    p: bool @P <- identity(flag)
    v: bool @V <- identity(flag)
    both = @(P = p, V = v)
    result = if both:
        x
    else:
        x
    return result
)"),
            "source.common-provenance");
  });
  cases.run("ordinary enum matching retains all payload associations", [] {
    auto project = take(check(R"(enum Choice:
    Some(bool)
    None()
pub protocol Run roles(P,V)(value: Choice @(P,V)) -> bool @(P,V):
    result = match value:
        case Some(item):
            item
        case None():
            false
    return result
)"));
    auto entry = closed(project);
    auto requirements = take(deriveCommonControlRequirements(entry));
    require(requirements.size() == 1 && requirements.front().tagOnly,
            "enum header required payload equality instead of tag equality");
    auto &selected = control(named(project, "Run"));
    require(selected.regions[0]->inputs == 1 &&
                selected.regions[1]->inputs == 0,
            "enum payload port order differs");
  });
  cases.run("nonexhaustive ordinary enum refuses", [] {
    refuses(check(R"(enum Choice:
    Some(bool)
    None()
pub protocol Run roles(P)(value: Choice @P) -> bool @P:
    result = match value:
        case Some(item):
            item
    return result
)"),
            "source.match");
  });
  cases.run("branch assignment joins immutable successors", [] {
    auto project = take(check(
        R"(pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @(P,V)) -> bool @(P,V):
    mut state = x
    if flag:
        state := true
    else:
        state := false
    result = if state:
        x
    else:
        x
    return result
)"));
    require(!take(deriveCommonControlRequirements(closed(project))).empty(),
            "shared input selector lost requirement");
  });
  cases.run("payload selectors require their own exact enum components", [] {
    auto project = take(check(R"(enum Choice:
    Some(bool)
    None()
pub protocol Run roles(P,V)(value: Choice @(P,V)) -> bool @(P,V):
    result = match value:
        case Some(item):
            if item:
                true
            else:
                false
        case None():
            false
    return result
)"));
    auto requirements = take(deriveCommonControlRequirements(closed(project)));
    require(requirements.size() == 2 && requirements[0].tagOnly &&
                !requirements[1].tagOnly,
            "common tag was reused as payload agreement");
    const auto &path = requirements[1].components.front().path;
    require(path.size() == 2 &&
                path[0].kind == CommonControlStep::Kind::Alternative &&
                path[0].index == 0 &&
                path[1].kind == CommonControlStep::Kind::Payload &&
                path[1].index == 0,
            "payload requirement lost exact constructor association");
    // The production comparison maps the published payload through the
    // component map; the actual native analysis observes its variant path.
    auto native = nativeInventory(closed(project));
    require(llvm::any_of(native,
                         [](const auto &requirement) {
                           const auto &component = requirement.components[0];
                           return !requirement.tagOnly &&
                                  component.input == 0 &&
                                  ArrayRef<unsigned>(component.path) ==
                                      ArrayRef<unsigned>({0, 0});
                         }),
            "payload did not map to the exact native variant path");
  });
  cases.run("fixed-role record branches preserve recursive placement", [] {
    auto project = take(check(R"(struct Pair roles(A,B):
    pub left: bool @A
    pub right: bool @B
    empty: () @A
pub protocol Run roles(P,V)(flag: bool @(P,V), pair: Pair roles(P,V)) -> Pair roles(P,V):
    result = if flag:
        pair
    else:
        pair
    return result
)"));
    // A direct Run closes and publishes the private field; the SDK's Entry
    // admission refuses its fresh supply.
    auto direct = take(closeInvocation(
        project,
        {HostInvocation::Kind::Run, named(project, "Run").id, {}, {}}));
    Layouts layouts(direct);
    auto pair = take(layouts.protocolPort(direct.protocol().inputs[1]));
    zkc::test::requireWithheld(zkc::test::withheldSupply(*pair.body, "pair"),
                               {"pair.empty"},
                               "private placed field lost its supply mark");
    auto entry = closed(project);
    const auto &body = *entry.protocol().body;
    require(body.values[body.results.front().index].placement ==
                entry.protocol().inputs[1].placement,
            "branch flattened a role telescope to aggregate availability");
  });
  cases.run(
      "shared helper requirements substitute exact product paths and roles",
      [] {
        auto project = take(check(R"(struct State:
    pub flag: bool
    pub unused: bool
protocol Choose roles(A,B)(state: State @(A,B), x: bool @(A,B)) -> bool @(A,B):
    result = if state.flag:
        x
    else:
        x
    return result
pub protocol Run roles(P,V)(state: State @(P,V), x: bool @(P,V)) -> bool @(P,V):
    result <- Choose(state, x) @(V,P)
    return result
)"));
        auto requirements =
            take(deriveCommonControlRequirements(closed(project)));
        require(requirements.size() == 1 &&
                    requirements[0].components[0].role == 1 &&
                    requirements[0].components[1].role == 0 &&
                    requirements[0].components[0].input == 0 &&
                    requirements[0].components[0].path.size() == 1 &&
                    requirements[0].components[0].path[0].index == 0,
                "helper substitution lost its ordered role telescope or field");
      });
  cases.run("loop requirements retain zero trips and branch successors", [] {
    auto project = take(check(
        R"(pub protocol Run roles(P,V)(count: index @(P,V), flag: bool @(P,V), x: bool @(P,V)) -> bool @(P,V):
    mut state = flag
    for i in 0..count roles(P,V) max 4:
        if state:
            state := true
        else:
            state := false
    result = if state:
        x
    else:
        x
    return result
)"));
    auto requirements = take(deriveCommonControlRequirements(closed(project)));
    require(llvm::any_of(requirements,
                         [](const auto &requirement) {
                           return requirement.components.front().input == 1;
                         }),
            "zero-trip initial selector escaped its requirement");
  });
  cases.run("service aliases preserve one exact enclosing root in every arm",
            [] {
              auto project = take(check(R"(domain F = field("bls12-381.fr")
pub protocol Run roles(P,V)(flag: bool @(P,V), coins: Random<F> @P) -> F @P:
    alias = coins
    result = if flag:
        value <- coins.draw()
        value
    else:
        value <- alias.draw()
        value
    return result
)"));
              const auto &selected = control(named(project, "Run"));
              require(selected.services.size() == 1 &&
                          selected.services.front().index == 0 &&
                          selected.regions[0]->services.size() == 1 &&
                          selected.regions[1]->services.size() == 1,
                      "branch created independent service roots for aliases");
              closed(project);
            });
  cases.run("a dormant arm cannot capture a service outside its roster", [] {
    refuses(check(R"(domain F = field("bls12-381.fr")
pub protocol Run roles(P,V)(flag: bool @(P,V), coins: Random<F> @P) -> ():
    if flag roles(V):
        value <- coins.draw()
    else:
        ()
    return ()
)"),
            "source.roles");
  });
  cases.run("equal result types cannot merge different role placements", [] {
    refuses(
        check(
            R"(pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @P, y: bool @V) -> bool @P:
    result = if flag:
        x
    else:
        y
    return result
)"),
        "source.placement");
  });
  cases.run("linear inputs transfer once through either selected arm", [] {
    auto project = take(check(R"(#[linear]
struct Ticket:
    pub value: bool
local def make() -> Ticket:
    ticket <- Ticket{value = false}
    return ticket
pub protocol Run roles(P)(flag: bool @P) -> Ticket @P:
    ticket <- make()
    result = if flag:
        ticket
    else:
        ticket
    return result
)"));
    closed(project);
  });
  cases.run("generic Math specialization rechecks selected arms", [] {
    auto project = take(
        check(R"(def choose<T: Type+Copy+Drop>(flag: bool, x: T, y: T) -> T:
    if flag:
        x
    else:
        y
pub protocol Run roles(P,V)(flag: bool @(P,V), x: bool @(P,V), y: bool @(P,V)) -> bool @(P,V):
    result = choose<bool>(flag, x, y)
    return result
)"));
    closed(project);
  });
  cases.run("statement-position selected arms retain Entry-only completion",
            [] {
              auto captured = take(capture({{"m", R"(module m;
protocol Run roles(P,V)(flag:bool@P,go:bool@P,x:bool@(P,V))->(result:bool@(P,V)) completes {
 if flag roles(P) { let _ = finish_if @P(go)(result=x); } else {}
 return(result=x);
})",
                                             "completion.zkc"}}));
              auto project = take(analyze(captured).checkedProject());
              closed(project);
            });
  cases.run("Math selected arms retain specialized callback captures", [] {
    auto captured = take(capture({{"m", R"(module m;
domain Fr=field("koala-bear");
math fn choose(x:Fr,body:math fn(Fr)->Fr)->Fr {
 return if true { body(x) } else { x };
}
protocol Run roles(P)(x:Fr@P,shift:Fr@P)->(r:Fr@P) {
 return(r=choose(x,fn(y)=>y+shift));
})",
                                   "scoped-math.zkc"}}));
    auto project = take(analyze(captured).checkedProject());
    closed(project);
  });
  for (StringRef name :
       {"shared", "math", "match", "applications", "resources", "payload",
        "placed-oracles", "multireceiver", "static-selection", "services"})
    cases.run("retained source example: " + name, [&] {
      auto file =
          MemoryBuffer::getFile(std::string(ZKC_SELECTED_CONTROL_FIXTURES) +
                                "/" + name.str() + ".zkc");
      require(bool(file), "missing source example");
      auto project = take(check((*file)->getBuffer()));
      closed(project);
    });
  cases.run("common collection extents remain distinct from contents", [] {
    auto captured = take(capture({{"m", R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
math fn extent(xs:Vector<Fr>)->index { return intrinsic<Fr>("vector.length",xs); }
protocol Run roles(P,V)(xs:Vector<Fr>@(P,V),value:bool@(P,V))->(r:bool@(P,V)) {
 let n=extent(xs); let mut state=value;
 for _ in 0..n roles(P,V) max 4 { state=state; }
 return(r=state);
})",
                                   "extent.zkc"}}));
    auto project = take(analyze(captured).checkedProject());
    auto entry = closed(project);
    auto requirements = take(deriveCommonControlRequirements(entry));
    require(requirements.size() == 1 && requirements[0].extentAxis == 0 &&
                !requirements[0].tagOnly &&
                requirements[0].components[0].input == 0,
            "count provenance was replaced with whole-container equality");
    nativeInventory(entry);
  });
  return cases.result();
}
