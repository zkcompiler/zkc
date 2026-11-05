#include "../lib/Language/Internal.h"
#include "../lib/Language/ScopedWitness.h"
#include "../lib/Language/WrittenSource.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace source_detail = zkc::language::detail;
namespace {
const std::string definitions = R"(
pub type Vector<F:Field>=builtin("vector",F);
pub domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
pub fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
pub fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item, rows))->F effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
)";
const std::string prelude = "module m;" + definitions + R"(
domain Fr=field("koala-bear");
domain Ext=field("koala-bear.ext8-binomial3");
math fn square<F:Field>(x:F)->F{return x*x;}
math fn difference<F:Field>(a:F,b:F)->F{return a-b;}
fn custom<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item, rows))->F effects(stop){return sum(rows,term)+1;}
)";
Expected<CheckedProject> check(StringRef text, const Limits &limits = {}) {
  auto captured = capture({{"m", prelude + text.str(), "reductions.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
// Consumer headers still use the legacy reader until the parent callback
// migration. Join the existing readers at their actual checker seam; do not
// manufacture a CheckedProject or bypass scoped-source replay.
Expected<std::shared_ptr<source_detail::CheckedStorage>>
checkLayout(StringRef source, StringRef extraConsumers = "",
            const Limits &limits = {}, StringRef notationExports = "") {
  const std::string consumers = "module consumers;" + definitions + R"(
pub fn fold_where<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
 keep:fn(item:I)->bool effects(stop) where item_from(item,rows),
 step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold_where");
pub fn sum_where<I:Type+Copy+Drop,F:Field>(rows:domain<I>,keep:fn(item:I)->bool effects(stop) where item_from(item,rows),
 term:fn(item:I)->F effects(stop) where item_from(item,rows))->F effects(stop){return fold_where(rows,0,keep,fn(state,item)=>state+term(item));}
pub math fn total_fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,
 step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
pub math fn total_sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:math fn(item:I)->F where item_from(item,rows))->F{return total_fold(rows,0,fn(state,item)=>state+term(item));}
)" + extraConsumers.str();
  std::vector<SourceBuffer> captured{{"consumers", consumers, "consumers.zkc"},
                                     {"m", source.str(), "layout.zkc"}};
  if (!notationExports.empty())
    captured.push_back({"ops", notationExports.str(), "ops.zkc"});
  auto input = capture(std::move(captured));
  if (!input)
    return input.takeError();
  auto output = std::make_shared<source_detail::CheckedStorage>(
      *input, installedCatalogIdentity());
  auto sources = std::make_shared<std::vector<SourceBuffer>>(
      input->sources().begin(), input->sources().end());
  for (const auto &module : source_detail::installedModules())
    sources->push_back({module, "", "<installation>/catalog/" + module,
                        SourceOrigin::Installation});
  output->sources = sources;
  output->tokens.resize(sources->size());
  output->layoutHeaders.resize(sources->size());
  output->layoutBodies.resize(sources->size());
  source_detail::Work work{limits};
  std::vector<source_detail::SyntaxDeclaration> modules;
  for (unsigned i = 0; i < sources->size(); ++i) {
    const auto &buffer = (*sources)[i];
    if (buffer.origin == SourceOrigin::Installation) {
      auto module = source_detail::readInstalledModule(buffer, {i}, work);
      if (!module)
        return module.takeError();
      modules.push_back(std::move(*module));
    } else if (buffer.module != "consumers") {
      auto module =
          source_detail::parseLayoutHeaders(buffer, {i}, *output, work);
      if (!module)
        return module.takeError();
      modules.push_back(std::move(*module));
    } else {
      if (auto error = source_detail::lex(buffer, {i}, work, output->tokens[i]))
        return error;
      auto module = source_detail::parse(buffer, {i}, output->tokens[i], work);
      if (!module)
        return module.takeError();
      modules.push_back(std::move(*module));
    }
  }
  if (auto error = source_detail::check(std::move(modules), *output, work))
    return error;
  source_detail::Work replay{limits};
  if (auto error = source_detail::checkScopedSources(*output, replay))
    return error;
  return output;
}
const Declaration &
layoutDeclaration(const source_detail::CheckedStorage &project,
                  StringRef name) {
  for (const auto &decl : project.declarations)
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing layout declaration " + name.str());
}
const std::string layoutPrelude = R"(use consumers::{Vector}
domain F = field("koala-bear")
notation ∑ x ∈ D, body = consumers::sum(D, fn(x) => body)
notation ∑ x ∈ D with p, body = consumers::sum_where(D, fn(x) => p, fn(x) => body)
notation ∏ x ∈ D, body = consumers::total_sum<F = F>(D, fn(x) => body)
)";
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &declaration : project.declarations())
    if (declaration.qualifiedName == name)
      return declaration;
  throw std::runtime_error("missing declaration " + name.str());
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
const std::string program = R"(
pub reduction ∑=sum;
pub fn f<F:Field>(xs:Vector<F>,ys:Vector<F>,a:F,b:F)->F{
  let first=sum(zip(xs,ys),fn((x,_))=>b*x+a);
  return first+(∑ (x,y) in zip(xs,ys), {
    operator *=difference;
    let z=x*y;
    square(z)+a
  });
}
protocol Demo roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,a:Fr@P,b:Fr@P)->(r:Fr@P){
  return (r=f(xs,ys,a,b));
}
entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
} // namespace
int main() {
  Cases cases;
  cases.run(
      "layout reductions dispatch each form to its ordinary consumer and "
      "replay",
      [] {
        auto project = take(checkLayout(
            layoutPrelude + R"(local def compute(xs: Vector<F>,a: F) -> F:
    plain <- ∑ x ∈ xs, x * a
    filtered <- ∑ x ∈ xs with x == a, x * a
    total = ∏ x ∈ xs, x * a
    return plain + filtered + total
)"));
        const auto &body = *layoutDeclaration(*project, "m::compute").body;
        require(body.scopedBindings.size() == 4,
                "reduction callback count differs");
        std::vector<std::string> selected;
        for (const auto &operation : body.operations)
          if (operation.binding && operation.binding->notation &&
              operation.binding->notation->position ==
                  NotationDescriptor::Position::Reduction)
            selected.push_back(
                project
                    ->declarations[operation.binding->target.declaration.index]
                    .qualifiedName);
        require(selected == std::vector<std::string>{"consumers::sum",
                                                     "consumers::sum_where",
                                                     "consumers::total_sum"},
                "filtered/plain or Math/Local selection changed");
        unsigned filtered = 0;
        for (const auto &binding : project->notations.bindings)
          filtered += binding.filteredOnly;
        require(filtered == 1, "filtered-only authored binding lost");
        const auto &modules = project->writtenSources->modules;
        auto written = llvm::find_if(
            modules, [](const auto &module) { return module.name == "m"; });
        require(written != modules.end() && written->operators.size() == 3 &&
                    written->operators[0].reductionBinder == "x" &&
                    written->operators[1].filteredOnly &&
                    written->operators[1].holes ==
                        std::vector<std::string>{"D", "p", "body"},
                "written reduction templates lost their binder or authored "
                "hole order");
      });
  cases.run(
      "layout reductions keep independent product order, tuple binders and "
      "captures",
      [] {
        auto project = take(checkLayout(
            layoutPrelude + R"(def first(xs: Vector<F>) -> Vector<F>:
    xs
def second(xs: Vector<F>) -> Vector<F>:
    xs
local def compute(xs: Vector<F>,ys: Vector<F>,a: F) -> F:
    result <- ∑ (x ∈ first(xs)) (y ∈ second(ys)), (x * y + a)
    return result
)"));
        const auto &body = *layoutDeclaration(*project, "m::compute").body;
        require(body.scopedBindings.size() == 1 &&
                    body.scopedBindings.front().captures.size() == 1,
                "product callback or capture count changed");
        require(body.operations.size() >= 3 && body.operations[0].binding &&
                    body.operations[1].binding,
                "domain operands were discarded");
        for (unsigned i = 0; i < 2; ++i)
          require(project->declarations[body.operations[i]
                                            .binding->target.declaration.index]
                          .qualifiedName == (i == 0 ? "m::first" : "m::second"),
                  "domain operands did not evaluate once in written order");
      });
  cases.run(
      "layout filtered-only binding does not create an unfiltered consumer",
      [] {
        const std::string prefix = R"(use consumers::{Vector}
domain F = field("koala-bear")
notation ∑ x ∈ D with p, body = consumers::sum_where(D, fn(x) => p, fn(x) => body)
local def compute(xs: Vector<F>) -> F:
)";
        take(checkLayout(
            prefix +
            "    result <- ∑ x ∈ xs with true, x\n    return result\n"));
        refuses(checkLayout(prefix +
                            "    result <- ∑ x ∈ xs, x\n    return result\n"),
                "source.reduction-target");
      });
  cases.run(
      "layout reduction callback origins are checked at the declaration", [] {
        const std::string consumer = R"(
pub fn bad<I:Type+Copy+Drop,F:Field>(rows:domain<I>,term:fn(item:I)->F effects(stop) where item_from(item,missing))->F effects(stop){return 0;}
)";
        refuses(
            checkLayout(
                "notation ∑ x ∈ D, body = consumers::bad(D, fn(x) => body)\n",
                consumer),
            "source.finite-domain");
      });
  cases.run("layout reduction refuses a Local consumer in Math", [] {
    refuses(checkLayout(layoutPrelude + R"(def compute(xs: Vector<F>) -> F:
    ∑ x ∈ xs, x
)"),
            "source.action");
  });
  cases.run(
      "layout reduction independent replay refuses changed callback mode", [] {
        auto project =
            take(checkLayout(layoutPrelude + R"(def compute(xs: Vector<F>) -> F:
    ∏ x ∈ xs, x
)"));
        auto found = llvm::find_if(project->declarations, [](const auto &decl) {
          return decl.qualifiedName == "m::compute";
        });
        require(found != project->declarations.end() && found->body,
                "missing reduction body");
        auto body = std::make_shared<Body>(*found->body);
        body->scopedBindings.front().signature.mode =
            ScopedSignature::Mode::Local;
        found->body = std::move(body);
        Limits limits;
        source_detail::Work work{limits};
        auto error = source_detail::checkScopedSources(*project, work);
        require(bool(error), "forged callback mode passed independent replay");
        require(StringRef(toString(std::move(error)))
                    .contains("source.scoped-witness"),
                "changed callback mode lost its independent diagnostic");
      });
  cases.run(
      "nested layout Math reductions retain their authored syntax and scopes",
      [] {
        auto project = take(checkLayout(
            layoutPrelude + R"(def compute(xs: Vector<F>, a: F) -> F:
    ∏ x ∈ xs, (∏ y ∈ xs, x * y * a)
)"));
        unsigned count = 0;
        for (const auto &tree : project->layoutBodies) {
          if (!tree)
            continue;
          auto formatted = zkc::syntax::format(*tree);
          require(formatted.complete &&
                      StringRef(formatted.text).contains("∏ x ∈ xs") &&
                      StringRef(formatted.text).contains("∏ y ∈ xs"),
                  "reduction formatting expanded authored binders");
          for (const auto &node : tree->nodes())
            count += node.kind == zkc::syntax::Kind::Reduction;
        }
        require(count == 2,
                "nested authored reduction nodes were replaced by callbacks");
      });
  cases.run(
      "layout bare reduction import selects both independent exported forms",
      [] {
        const std::string exported =
            R"(pub notation ∑ x ∈ D, body = consumers::sum(D, fn(x) => body)
pub notation ∑ x ∈ D with p, body = consumers::sum_where(D, fn(x) => p, fn(x) => body)
)";
        take(checkLayout(R"(use consumers::{Vector}
use ops::{∑}
domain F = field("koala-bear")
local def compute(xs: Vector<F>) -> F:
    plain <- ∑ x ∈ xs, x
    filtered <- ∑ x ∈ xs with true, x
    return plain + filtered
)",
                         "", {}, exported));
      });
  cases.run(
      "layout reduction import consumes an existing legacy export unchanged",
      [] {
        take(checkLayout(R"(use consumers::{Vector, ∑}
domain F = field("koala-bear")
local def compute(xs: Vector<F>) -> F:
    result <- ∑ x ∈ xs with true, x
    return result
)",
                         "pub reduction ∑=sum,sum_where;"));
      });
  cases.run("layout reduction binder cannot escape its callback", [] {
    refuses(
        checkLayout(layoutPrelude + R"(local def compute(xs: Vector<F>) -> F:
    result <- ∑ x ∈ xs, x
    return x
)"),
        "source.name");
  });
  cases.run(
      "layout reduction generated products obey the semantic depth budget", [] {
        Limits limits;
        limits.expressionDepth = 4;
        refuses(checkLayout(layoutPrelude +
                                R"(local def compute(xs: Vector<F>) -> F:
    result <- ∑ (a ∈ xs) (b ∈ xs) (c ∈ xs) (d ∈ xs) (e ∈ xs), a
    return result
)",
                            "", limits),
                "source.limit");
      });
  cases.run("named and symbolic reductions retain ordinary scoped computations",
            [] {
              auto project = take(check(program));
              success(checkScopedElaboration(project));
              auto closed =
                  take(zkc::test::closeProtocolDeployment(project, "m::Run"));
              success(checkScopedSpecialization(closed));
              const auto &function = declaration(project, "m::f");
              require(function.body->scopedBindings.size() == 2,
                      "expected one callback per authored body");
              auto report = take(inspectNotations(project, {true, false}));
              require(take(json::parse(report)).getAsObject() &&
                          report.find("reduction") != std::string::npos,
                      "notation inspection lost reduction descriptors");
              require(report.find("fn((x, y)) =>") != std::string::npos,
                      "binder rendering lost the unary tuple pattern");
              require(take(inspectDeclarations(project)).find("reduction<") ==
                          std::string::npos,
                      "obsolete synthetic declaration leaked");
            });
  for (const auto &body :
       {"sum(xs,fn(x)=>x*x)", "custom(xs,fn(x)=>x)", "sum(xs,fn(_)=>1)",
        "sum(zip(xs,xs),fn((x,_))=>x)", "sum(xs,fn(a)=>{let t=a;t+a})",
        "sum(xs,fn(x)=>({let x=a;x})+x)",
        "sum(xs,fn(x)=>if x==a {x} else {a})"})
    cases.run(body, [&] {
      take(check("fn f(xs:Vector<Fr>,a:Fr)->Fr{return " + std::string(body) +
                 ";}"));
    });
  cases.run("local binding selects an ordinary custom finite consumer", [] {
    auto project =
        take(check("reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{reduction "
                   "∑=custom;return ∑ x in xs,x;}"));
    const auto &op = declaration(project, "m::f").body->operations.back();
    require(op.binding && op.binding->target.declaration.index ==
                              declaration(project, "m::custom").id.index,
            "local reduction binding lost");
  });
  for (unsigned mode = 0; mode != 3; ++mode)
    cases.run("reduction import visibility " + Twine(mode), [&] {
      auto captured = take(capture(
          {{"lib", "module lib;" + definitions + "pub reduction ∑=sum;", {}},
           {"bridge",
            "module bridge;pub use lib::{Vector,sum,reduction ∑};",
            {}},
           {"m",
            std::string("module m;") +
                (mode == 0 ? "use bridge::{Vector,reduction ∑};"
                 : mode == 1
                     ? "use lib as lib;type Vector<F:Field>=lib::Vector<F>;"
                     : "use bridge::{Vector,sum};") +
                "domain Fr=field(\"koala-bear\");fn "
                "f(xs:Vector<Fr>)->Fr{return ∑ x in xs,x;}",
            {}}}));
      auto project = analyze(captured).checkedProject();
      if (mode == 2)
        refuses(std::move(project), "source.notation-visibility");
      else
        take(std::move(project));
    });
  for (const auto &[source, code] :
       std::vector<std::pair<std::string, std::string>>{
           {"reduction ∑=square;", "source.reduction-target"},
           {"fn f(xs:Vector<Fr>)->Fr{return reduce sum[x in xs]{x};}",
            "source.reduction"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{return ∑ (x,x) in "
            "zip(xs,xs),x;}",
            "source.binding"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{let r=∑ x in xs,x;return "
            "x;}",
            "source.name"},
           {"reduction ∑=sum;math fn f(xs:Vector<Fr>)->Fr{return ∑ x in xs,x;}",
            "source.mode"},
           {"reduction ∑=sum;fn f(xs:Vector<Fr>,a:Ext)->Fr{return ∑ x in "
            "xs,a;}",
            "source.type"}})
    cases.run(source, [&, source = source, code = code] {
      refuses(check(source), code);
    });
  cases.run("captures follow first use and preserve ignored zip domains", [] {
    auto project = take(check("reduction ∑=sum;fn "
                              "f(xs:Vector<Fr>,ys:Vector<Fr>,a:Fr,b:Fr)->Fr{"
                              "return ∑ (_,x) in zip(xs,ys),(b*x+a+b);}"));
    const auto &body = *declaration(project, "m::f").body;
    const auto &binding = body.scopedBindings.back();
    require(binding.captures.size() == 2, "unexpected capture count");
    const auto &first = body.operations[0], &second = body.operations[1];
    require(std::get<Projection>(first.action).input.index == 3 &&
                std::get<Projection>(second.action).input.index == 2,
            "capture reads lost first-use order");
    const auto &domain = body.descriptorBindings.back();
    require(domain.children.size() == 2, "ignored row removed from strict zip");
    success(checkScopedElaboration(project));
  });
  cases.run("collections evaluate once in written order before captures", [] {
    auto project = take(check(R"(
reduction ∑=sum;
fn first(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn second(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn f(xs:Vector<Fr>,a:Fr)->Fr{return ∑ ((x,y),z) in zip(zip(second(xs),first(xs)),second(xs)),(x*y*z+a);}
)"));
    const auto &body = *declaration(project, "m::f").body;
    for (unsigned i = 0; i != 3; ++i)
      require(body.operations[i].binding &&
                  body.operations[i].binding->target.declaration.index ==
                      declaration(project, i == 1 ? "m::first" : "m::second")
                          .id.index,
              "collection evaluation changed");
    require(std::holds_alternative<Projection>(body.operations[3].action),
            "capture preceded collections");
    success(checkScopedElaboration(project));
  });
  cases.run(
      "local notation in a binder retains its authored lexical scope", [] {
        auto project = take(check(R"(
reduction ∑=sum;operator prefix(75) ⊖=square;
fn f(xs:Vector<Fr>)->Fr{return ∑ x in xs,{
 operator ⊗=difference;operator infixl(70) ⊗=difference;
 operator prefix(75) ⊖=identity; ⊖x ⊗ x
};}
math fn identity(x:Fr)->Fr{return x;}
)"));
        const auto &body = *declaration(project, "m::f")
                                .body->scopedBindings.back()
                                .computation->body;
        auto prefix = llvm::find_if(body.operations, [](const Operation &op) {
          return op.binding && op.binding->symbol == "⊖";
        });
        require(prefix != body.operations.end() &&
                    prefix->binding->target.declaration.index ==
                        declaration(project, "m::identity").id.index,
                "prefix resolved outside its authored scope");
        success(checkScopedElaboration(project));
      });
  cases.run("budgets include ordinary scoped binder work", [] {
    auto project = take(check(program));
    Limits limits;
    limits.declarations = project.checkedDeclarations() - 1;
    refuses(check(program, limits), "source.limit");
    limits = {};
    limits.operations = project.checkedOperations() - 1;
    refuses(check(program, limits), "source.limit");
    limits = {};
    limits.work = project.checkedWork() - 1;
    refuses(check(program, limits), "source.limit");
  });
  cases.run("many binder sites have stable distinct closure identities", [] {
    std::string source = "reduction ∑=sum;fn f(xs:Vector<Fr>)->Fr{";
    for (unsigned i = 0; i != 64; ++i)
      source += "let r" + std::to_string(i) + "=∑ x in xs,(x+1);";
    source += "return r63;}protocol Demo "
              "roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){return f(xs);}entry fn "
              "Run(inputs: Demo::Inputs) { return Demo::run(inputs); }";
    auto first = take(check(source)), second = take(check(source));
    const auto &bindings = declaration(first, "m::f").body->scopedBindings;
    require(bindings.size() == 64, "binder site lost");
    std::set<unsigned> expressions;
    for (const auto &binding : bindings)
      require(expressions.insert(binding.computation->expression).second,
              "binder identity collided");
    auto closed = take(zkc::test::closeProtocolDeployment(first, "m::Run")),
         other = take(zkc::test::closeProtocolDeployment(second, "m::Run"));
    require(closed.declarations().size() == other.declarations().size(),
            "unstable specialization count");
    for (unsigned i = 0; i != closed.declarations().size(); ++i)
      require(closed.declarations()[i].symbol == other.declarations()[i].symbol,
              "unstable closed identity");
    auto report = take(inspectNotations(first, {true, false}));
    require(report == take(inspectNotations(first, {true, false})) &&
                report.find("not-emitted") == std::string::npos,
            "inspection lost a scoped occurrence");
  });
  for (const auto &mutation : {"capture", "capture-order", "body-operand",
                               "binding-target", "missing-binding"})
    cases.run(Twine("independent binder witness rejects ") + mutation, [&] {
      auto project = take(check(program));
      auto &body = const_cast<Body &>(*declaration(project, "m::f").body);
      auto &binding = body.scopedBindings.front();
      StringRef change = mutation;
      if (change == "capture")
        binding.captures[0] = binding.captures[1];
      else if (change == "capture-order")
        std::swap(binding.captures[0], binding.captures[1]);
      else if (change == "body-operand") {
        auto &nested = const_cast<Body &>(*binding.computation->body);
        bool changed = false;
        for (auto &op : nested.operations)
          if (auto *call = std::get_if<LocalPrimitive>(&op.action)) {
            if (call->operands.size() == 2) {
              call->operands[0] = call->operands[1];
              changed = true;
              break;
            }
          }
        require(changed, "missing callback operand mutation target");
      } else {
        auto found = llvm::find_if(body.operations, [](const Operation &op) {
          return op.binding && op.binding->scopedSource;
        });
        require(found != body.operations.end(), "missing scoped call");
        if (change == "binding-target")
          found->binding->target.declaration =
              declaration(project, "m::custom").id;
        else
          found->binding.reset();
      }
      auto error = checkScopedElaboration(project);
      require(bool(error), "corrupt binder evidence accepted");
      consumeError(std::move(error));
    });
  return cases.result();
}
