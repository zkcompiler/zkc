#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Registry.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture(
      {{"sample", ("module sample;" + source).str(), "computation.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Body &body(const CheckedProject &project, StringRef name = "Run") {
  auto at = llvm::find_if(project.declarations(),
                          [&](const auto &decl) { return decl.name == name; });
  require(at != project.declarations().end() && at->body,
          "missing source body");
  return const_cast<Body &>(*at->body);
}
void replay(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void rejects(const CheckedProject &project, StringRef expected = {}) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "rewritten authored computation passed replay");
  auto message = toString(std::move(error));
  require(expected.empty() || StringRef(message).contains(expected), message);
  require(StringRef(message).contains("source.scoped-witness") ||
              StringRef(message).contains("source.binding-witness"),
          message);
}
using Producer = std::pair<Body *, Operation *>;
void producers(Body &checked, std::vector<Producer> &found,
               function_ref<bool(const Operation &)> select) {
  for (auto &op : checked.operations) {
    if (select(op))
      found.emplace_back(&checked, &op);
    if (auto *control = std::get_if<Control>(&op.action))
      for (const auto &arm : control->regions)
        producers(const_cast<Body &>(*arm), found, select);
  }
  for (const auto &binding : checked.scopedBindings)
    if (binding.computation)
      producers(const_cast<Body &>(*binding.computation->body), found, select);
}
CheckedOriginal original(StringRef source) {
  auto project = take(check(source));
  replay(project);
  auto closed = take(closeProtocolDeployment(project, "sample::Demo"));
  if (auto error = checkScopedSpecialization(closed))
    throw std::runtime_error(toString(std::move(error)));
  return take(prepareOriginal(closed));
}
constexpr StringLiteral entry =
    "entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}";
constexpr StringLiteral helpers = R"(
domain F=field("koala-bear");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn expensive(n:index,x:F)->bool{return fold(range(0,n),x,fn(s,i)=>s+x)==x;}
math fn apply(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
)";
constexpr StringLiteral selected = R"(
protocol Run roles(P,V)(a:bool@P,b:bool@P)->(r:bool@P){return a&&b;}
)";
} // namespace
int main() {
  Cases cases;
  for (StringRef mode : {"math fn", "fn"})
    cases.run("enum formation and selected match in " + mode, [&] {
      auto source = ("enum Choice{Empty(),Value(bool)} " + mode +
                     R"( choose(a:bool)->bool{
        let empty=Choice::Empty();
        let value=Choice::Value(a);
        return match value{Empty()=>{false},Value(x)=>{match empty{Empty()=>{x},Value(y)=>{y}}}};
      }
      protocol Run roles(P)(a:bool@P)->(r:bool@P){return choose(a);}
      )" + entry)
                        .str();
      auto input = original(source);
      require(input.bytes().contains("data.branch") || mode == "fn",
              "Math enum match was not selected");
      for (bool simplify : {false, true})
        take(compileEntry(input, {simplify, false}));
    });
  for (StringRef roles : {"P", "(P,V)"})
    cases.run("pointwise enum payload availability " + roles, [&] {
      auto input = original(
          ("enum Choice{Empty(),Value(bool)} "
           "math fn unwrap(x:Choice)->bool{return match "
           "x{Empty()=>{false},Value(v)=>{v}};}"
           "protocol Run roles(P,V)(a:bool@" +
           roles + ")->(r:bool@" + roles +
           "){let value=Choice::Value(a);return unwrap(value);}" + entry)
              .str());
      for (bool simplify : {false, true})
        take(compileEntry(input, {simplify, false}));
    });
  for (StringRef formula : {"a&&b", "a||b", "a&&(b||a)",
                            "a||apply(b,fn(x)=>x&&a)", "a&&{let x=b;x||a}"})
    cases.run("private pointwise selected Boolean " + formula, [&] {
      auto input = original(
          (helpers +
           "protocol Run roles(P,V)(a:bool@P,b:bool@P)->(r:bool@P){return " +
           formula + ";}" + entry)
              .str());
      require(input.bytes().contains("data.branch"), "missing Math selection");
      require(!input.bytes().contains("protocol.branch"),
              "pointwise Boolean became shared Protocol control");
      for (bool simplify : {false, true})
        take(compileEntry(input, {simplify, false}));
    });
  cases.run("enum payload availability combines every written operand", [&] {
    auto input = original((StringRef(R"(
      enum E{Pair(bool,bool),Empty()}
      math fn both(x:E)->bool{return match x{Pair(a,b)=>{a&&b},Empty()=>{false}};}
      protocol Run roles(P,V)(a:bool@P,b:bool@(P,V))->(r:bool@P){
        return both(E::Pair(a,b));
      }
    )") + entry)
                              .str());
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  cases.run("sealed enum construction retains its owning authority", [&] {
    auto input = original((StringRef(R"(
      module Hidden{
        #[sealed] pub enum E{Empty(),Value(bool)}
        pub math fn work(a:bool)->bool{
          return match E::Value(a){Empty()=>{false},Value(v)=>{v}};
        }
      }
      protocol Run roles(P)(a:bool@P)->(r:bool@P){return Hidden::work(a);}
    )") + entry)
                              .str());
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  for (StringRef mode : {"math fn", "protocol"})
    for (StringRef formula : {"false&&expensive(n,x)", "true||expensive(n,x)",
                              "true&&expensive(n,x)", "false||expensive(n,x)"})
      cases.run(
          "finite RHS remains inside selected " + mode + " " + formula, [&] {
            std::string source = helpers.str();
            if (mode == "math fn")
              source += "math fn choose(n:index,x:F)->bool{return " +
                        formula.str() + ";}";
            source +=
                "protocol Run roles(P,V)(n:index@P,x:F@P)->(r:bool@P){return " +
                (mode == "math fn" ? std::string("choose(n,x)")
                                   : formula.str()) +
                ";}" + entry.str();
            auto input = original(source);
            auto branch = input.bytes().find("data.branch");
            require(branch != StringRef::npos,
                    "missing selected finite branch");
            // The finite call/consumer must occur after the branch starts,
            // within its selected region, never as an eager capture of the RHS
            // result.
            auto finite = input.bytes().find("data.finite_fold", branch);
            auto call = input.bytes().find("func.call", branch);
            require(finite != StringRef::npos || call != StringRef::npos,
                    "selected arm lost its finite computation");
            for (bool simplify : {false, true})
              take(compileEntry(input, {simplify, false}));
          });
  cases.run("projection captures snapshot current mutable data", [&] {
    auto input = original((StringRef(R"(
      struct Pair{pub left:bool,pub right:bool}
      protocol Run roles(P,V)(a:bool@P,b:bool@P)->(r:bool@P){
        let mut pair=Pair{left:a,right:b};
        let first=pair.left&&pair.right;
        pair=Pair{left:b,right:a};
        return first||pair.left;
      }
    )") + entry)
                              .str());
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  cases.run(
      "selected body captures retained domains and mathematical callbacks",
      [&] {
        auto input = original((helpers + R"(
      protocol Run roles(P,V)(go:bool@P,n:index@P,x:F@P)->(r:bool@P){
        let rows=range(0,n);
        return go&&{let value=fold(rows,x,fn(s,i)=>s+x);value==x};
      }
    )" + entry)
                                  .str());
        for (bool simplify : {false, true})
          take(compileEntry(input, {simplify, false}));
      });
  cases.run("selected callbacks preserve complete domain item origins", [&] {
    auto input = original((helpers + R"(
      type Vector=builtin("vector",F);
      domain fn indices(xs:Vector)->domain<index>=domain("indices");
      math fn at(xs:Vector,i:index)->F where in_bounds(i,xs){return intrinsic<Vector>("container.at",xs,i);}
      protocol Run roles(P)(go:bool@P,xs:Vector@P,x:F@P)->(r:bool@P){
        let rows=indices(xs);
        return go&&fold(rows,true,fn(acc,item)=>{let value=at(xs,item);acc&&(value==x)});
      }
    )" + entry)
                              .str());
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  cases.run("selected Boolean callbacks transport native index bounds", [&] {
    auto project = take(check((helpers + R"(
      type Vector=builtin("vector",F);
      domain fn indices(xs:Vector)->domain<index>=domain("indices");
      math fn at(xs:Vector,i:index)->F where in_bounds(i,xs){return intrinsic<Vector>("container.at",xs,i);}
      protocol Run roles(P)(go:bool@P,xs:Vector@P,x:F@P)->(r:bool@P){
        let rows=indices(xs);
        return go&&fold(rows,true,fn(acc,item)=>acc&&(at(xs,item)==x));
      }
    )" + entry)
                                  .str()));
    replay(project);
    auto closed = take(closeProtocolDeployment(project, "sample::Demo"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
    auto input = take(prepareOriginal(closed));
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  cases.run("selected retained domain identities cannot be crossed", [&] {
    auto project = take(check((helpers + R"(
      protocol Run roles(P)(go:bool@P,n:index@P,m:index@P,x:F@P)->(r:bool@P){
        let rows=range(0,n);let others=range(0,m);
        return go&&{let left=fold(rows,x,fn(s,i)=>s+x);
                    let right=fold(others,x,fn(s,i)=>s+x);left==right};
      }
    )")
                                  .str()));
    replay(project);
    auto &binding = body(project).scopedBindings.front();
    require(binding.descriptorCaptures.size() == 2, "lost domain captures");
    std::swap(binding.descriptorCaptures[0], binding.descriptorCaptures[1]);
    rejects(project);
  });
  cases.run(
      "selected computation retains exact work and call-depth limits", [&] {
        auto captured = take(
            capture({{"sample", ("module sample;" + selected).str(), {}}}));
        auto project = take(analyze(captured).checkedProject());
        Limits limits;
        limits.work = project.checkedWork();
        take(analyze(captured, limits).checkedProject());
        --limits.work;
        refuses(analyze(captured, limits).checkedProject(), "source.limit");
        limits = Limits{};
        limits.callDepth = 1;
        refuses(analyze(captured, limits).checkedProject(), "source.limit");
      });
  cases.run("Oracle Boolean selection explicitly refuses", [&] {
    refuses(check(R"(
      type Table=builtin("oracle.table",bool,16);
      type O=builtin("oracle",Table);
      oracle def Identity(source:O)->O {query(position:index){
        let answer <- oracle.query(source,position);return answer&&true;
      }}
    )"),
            "source.mode");
  });
  cases.run("unrestricted imported enum keeps nominal identity", [&] {
    auto input = original((StringRef(R"(
      module Values{pub enum Choice<T:Type>{Empty(),Value(T)}}
      use Values::{Choice};
      math fn work(x:bool)->bool{return match Choice::Value<bool>(x){Empty()=>{false},Value(v)=>{v}};}
      protocol Run roles(P)(x:bool@P)->(r:bool@P){return work(x);}
    )") + entry)
                              .str());
    for (bool simplify : {false, true})
      take(compileEntry(input, {simplify, false}));
  });
  for (StringRef mode : {"fn", "math fn", "protocol"})
    cases.run("enum kind and alternative replacement in " + mode, [&] {
      auto project =
          take(check(("enum E{First(bool),Second(bool)} " + mode +
                      (mode == "protocol" ? " Run roles(P)(a:bool@P)->(r:E@P)"
                                          : " Run(a:bool)->E") +
                      "{return E::First(a);}")
                         .str()));
      replay(project);
      auto &checked = body(project);
      auto at = llvm::find_if(checked.operations, [](const auto &op) {
        return std::holds_alternative<Construct>(op.action);
      });
      require(at != checked.operations.end(), "missing enum formation");
      auto replacement = std::get<Construct>(at->action);
      replacement.kind = Construct::Kind::Aggregate;
      replacement.alternative = "Second";
      at->action = std::move(replacement);
      rejects(project);
    });
  for (StringRef mode : {"fn", "math fn", "protocol"})
    for (StringRef formula : {"true&&false", "false||true"})
      for (unsigned mutation = 0; mutation < 5; ++mutation)
        cases.run(
            "selected producer replacement in " + mode + " " + formula + " " +
                Twine(mutation),
            [&] {
              auto project = take(
                  check((mode +
                         (mode == "protocol" ? " Run roles(P)()->(r:bool@P)"
                                             : " Run()->bool") +
                         "{return " + formula + ";}")
                            .str()));
              replay(project);
              auto *checked = &body(project);
              if (mode == "protocol") {
                const auto &binding = checked->scopedBindings.front();
                require(binding.captures.empty(),
                        "constant selection must be captureless");
                checked = &const_cast<Body &>(*binding.computation->body);
              }
              auto at = llvm::find_if(checked->operations, [](const auto &op) {
                return std::holds_alternative<Control>(op.action);
              });
              require(at != checked->operations.end(),
                      "missing selected control");
              auto expression = *at->expression;
              auto selector = std::get<Control>(at->action).operands.front();
              if (mutation == 1)
                at->action = Projection{selector, {}};
              else if (mutation == 2)
                checked->expressionValues[expression] = selector;
              else if (mutation == 3)
                checked->expressionValues.erase(expression);
              else {
                at->action =
                    MathValue{zkc::MathematicalIdentity::BooleanConstant,
                              {},
                              formula == "true&&false" ? "true" : "false"};
                if (mutation == 4) {
                  at->expression.reset();
                  checked->expressionValues.erase(expression);
                }
              }
              rejects(project);
            });
  for (StringRef mode : {"fn", "math fn", "protocol"})
    for (unsigned mutation = 0; mutation < 3; ++mutation)
      cases.run(
          "empty enum producer replacement in " + mode + " " + Twine(mutation),
          [&] {
            auto project = take(
                check(("enum E{Empty(),Other()} " + mode +
                       (mode == "protocol" ? " Run roles(P)(a:E@P)->(r:E@P)"
                                           : " Run(a:E)->E") +
                       "{return E::Empty();}")
                          .str()));
            replay(project);
            auto &checked = body(project);
            auto at = llvm::find_if(checked.operations, [](const auto &op) {
              return std::holds_alternative<Construct>(op.action);
            });
            require(at != checked.operations.end(),
                    "missing empty enum constructor");
            auto expression = *at->expression;
            if (mutation == 0)
              at->action = Projection{ValueId{0}, {}};
            if (mutation == 1)
              checked.expressionValues[expression] = ValueId{0};
            if (mutation == 2) {
              at->action = Projection{ValueId{0}, {}};
              at->expression.reset();
              checked.expressionValues.erase(expression);
            }
            rejects(project);
          });
  for (StringRef source :
       {"fn Run()->bool{return true&&{false||true};}",
        "math fn Run()->bool{return true&&{false||true};}",
        "protocol Run roles(P)()->(r:bool@P){return true&&{false||true};}",
        "math fn apply(f:math fn()->bool)->bool{return f();} math fn "
        "Run()->bool{return apply(fn()=>true&&false);}",
        "math fn apply(f:math fn()->bool)->bool{return f();} protocol Run "
        "roles(P)()->(r:bool@P){return true||apply(fn()=>true&&false);}"})
    cases.run("nested selected producer replacement " + source, [&] {
      auto project = take(check(source));
      replay(project);
      std::vector<Producer> found;
      producers(body(project), found, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(!found.empty(), "missing nested selected producer");
      found.back().second->action =
          MathValue{zkc::MathematicalIdentity::BooleanConstant, {}, "true"};
      rejects(project);
    });
  for (StringRef mode : {"math fn", "protocol"})
    cases.run("dormant scoped enum producer replacement in " + mode, [&] {
      auto project =
          take(check(("enum E{First(bool),Second(bool)} " + mode +
                      (mode == "protocol" ? " Run roles(P)()->(r:bool@P)"
                                          : " Run()->bool") +
                      "{return false&&{let unused=E::First(true);true};}")
                         .str()));
      replay(project);
      std::vector<Producer> found;
      producers(body(project), found, [](const auto &op) {
        return std::holds_alternative<Construct>(op.action);
      });
      require(found.size() == 1, "missing dormant enum producer");
      auto &construct = std::get<Construct>(found.front().second->action);
      construct.kind = Construct::Kind::Aggregate;
      construct.alternative = "Second";
      rejects(project);
    });
  for (StringRef mode : {"fn", "math fn", "protocol"})
    cases.run(
        "Boolean literal replaced by same-typed projection in " + mode, [&] {
          auto project = take(
              check((mode +
                     (mode == "protocol" ? " Run roles(P)(a:bool@P)->(r:bool@P)"
                                         : " Run(a:bool)->bool") +
                     "{return true;}")
                        .str()));
          replay(project);
          auto &checked = body(project);
          require(checked.operations.size() == 1, "missing literal producer");
          checked.operations.front().action = Projection{ValueId{0}, {}};
          rejects(project);
        });
  for (StringRef operation : {"&&", "||"})
    for (StringRef context :
         {"plain", "state", "nested", "dormant", "callback", "callback-state"})
      for (bool identity : {false, true})
        cases.run(
            "Local selected yield " + operation + " " + context + " " +
                Twine(identity),
            [&] {
              const bool conjunction = operation == "&&";
              const bool state =
                  context == "state" || context == "callback-state";
              auto wrong = conjunction ? "true" : "false";
              auto tail = conjunction ? "false" : "true";
              std::string formula =
                  std::string(conjunction ? "true" : "false") +
                  operation.str() + "{" +
                  (state ? "left=true;right=false;" : "") +
                  "let unused=" + wrong + ";" + tail + "}";
              if (context == "nested" || context == "dormant")
                formula =
                    std::string(context == "nested" ? "true&&{" : "false&&{") +
                    formula + "}";
              std::string local =
                  "{" +
                  std::string(state ? "let mut left=false;let mut right=true;"
                                    : "") +
                  formula + "}";
              auto project =
                  take(check(context.starts_with("callback")
                                 ? "fn apply(f:fn()->bool)->bool{return f();} "
                                   "fn Run()->bool{return apply(fn()=>" +
                                       local + ");}"
                                 : "fn Run()->bool{return " + local + ";}"));
              replay(project);
              std::vector<Producer> found;
              producers(body(project), found, [](const auto &op) {
                return std::holds_alternative<Control>(op.action);
              });
              require(!found.empty(), "missing Local selected control");
              auto &control = std::get<Control>(found.back().second->action);
              auto &arm =
                  const_cast<Body &>(*control.regions[conjunction ? 0 : 1]);
              std::optional<ValueId> replacement;
              std::vector<Operation *> definitions(arm.values.size());
              for (auto &op : arm.operations) {
                for (auto result : op.results)
                  definitions[result.index] = &op;
                if (auto *constant = std::get_if<LocalPrimitive>(&op.action);
                    constant && constant->contract == "bool.constant" &&
                    constant->parameters == std::vector<std::string>{wrong})
                  replacement = op.results.front();
              }
              require(replacement.has_value(),
                      "missing opposite authored literal");
              ValueId *yield = &arm.results.front();
              if (state) {
                auto *pack =
                    std::get_if<Construct>(&definitions[yield->index]->action);
                require(pack && pack->kind == Construct::Kind::Aggregate &&
                            pack->operands.size() == 3,
                        "missing Boolean and two-state result pack");
                yield = &pack->operands.front();
              }
              if (identity) {
                auto *projection =
                    std::get_if<Projection>(&definitions[yield->index]->action);
                require(projection && projection->path.empty(),
                        "missing result identity projection");
                yield = &projection->input;
              }
              *yield = *replacement;
              rejects(project);
            });
  for (bool state : {false, true})
    for (bool cycle : {false, true})
      cases.run(
          "Local yield identity chain " + Twine(state) + " " + Twine(cycle),
          [&] {
            auto project = take(check(
                "fn Run(a:bool)->bool{" +
                std::string(state ? "let mut state=false;" : "") +
                "return a&&{" + (state ? "state=true;" : "") + "false};}"));
            replay(project);
            std::vector<Producer> found;
            producers(body(project), found, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found.size() == 1, "missing selected control");
            auto &control = std::get<Control>(found.front().second->action);
            for (const auto &region : control.regions) {
              auto &arm = const_cast<Body &>(*region);
              for (unsigned i = 0; i < 3; ++i) {
                auto result = arm.results.front();
                auto value = arm.values[result.index];
                ValueId next{uint32_t(arm.values.size())};
                Operation identity{Projection{cycle ? next : result, {}},
                                   {next},
                                   found.front().second->span,
                                   found.front().second->statement};
                arm.values.push_back(std::move(value));
                arm.operations.push_back(std::move(identity));
                arm.results.front() = next;
              }
            }
            if (cycle)
              rejects(project);
            else
              replay(project);
          });
  for (StringRef operation : {"&&", "||"})
    cases.run("Local selected stopped RHS " + operation, [&] {
      auto project = take(check(
          ("fn Run(a:bool)->bool{return a" + operation + "{stop \"abort\";};}")
              .str()));
      replay(project);
    });
  for (StringRef mode : {"fn", "math fn"})
    cases.run("selected arm stop cannot hide a yield in " + mode, [&] {
      auto project =
          take(check((mode + " Run()->bool{return true&&false;}").str()));
      replay(project);
      std::vector<Producer> found;
      producers(body(project), found, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found.size() == 1, "missing selected control");
      auto &arm = const_cast<Body &>(
          *std::get<Control>(found.front().second->action).regions.front());
      arm.stopped = true;
      arm.stopReason = "abort";
      if (mode == "math fn")
        arm.results.clear();
      rejects(project);
    });
  for (StringRef operation : {"&&", "||"})
    for (unsigned selectedArm : {0u, 1u})
      cases.run(
          "invented Local arm stop " + operation + " " + Twine(selectedArm),
          [&] {
            auto project = take(check(
                ("fn Run(a:bool,b:bool)->bool{return a" + operation + "b;}")
                    .str()));
            replay(project);
            std::vector<Producer> found;
            producers(body(project), found, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found.size() == 1, "missing selected control");
            auto &arm = const_cast<Body &>(
                *std::get<Control>(found.front().second->action)
                     .regions[selectedArm]);
            arm.stopped = true;
            arm.stopReason = "invented";
            arm.results.clear();
            arm.effects.fixed.mayStop = true;
            body(project).effects.fixed.mayStop = true;
            rejects(project);
          });
  for (StringRef formula : {R"(a&&{if b{stop "abort";}else{stop "reject";}})",
                            R"(a||{if b{stop "abort";}else{stop "reject";}})",
                            R"(a&&{for i in 0..2{stop "abort";}false})"})
    cases.run("authored nested exit " + formula, [&] {
      auto project = take(check(
          ("fn Run(a:bool,b:bool)->bool{return " + formula + ";}").str()));
      replay(project);
    });
  for (StringRef operation : {"&&", "||"})
    cases.run("selected stop reason is source bound " + operation, [&] {
      auto project = take(check(
          ("fn Run(a:bool)->bool{return a" + operation + R"({stop "abort";};})")
              .str()));
      replay(project);
      std::vector<Producer> found;
      producers(body(project), found, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      bool changed = false;
      for (auto &[owner, op] : found)
        for (const auto &region : std::get<Control>(op->action).regions)
          if (region->stopped) {
            const_cast<Body &>(*region).stopReason = "reject";
            changed = true;
          }
      require(changed, "missing authored stop");
      rejects(project);
    });
  for (bool stopped : {false, true})
    cases.run("Local callback exit is source bound " + Twine(stopped), [&] {
      auto source = std::string("fn apply(f:fn()->bool)->bool{return f();} fn "
                                "Run()->bool{return apply(fn()=>{") +
                    (stopped ? "stop \"abort\";" : "true") + "});}";
      auto project = take(check(source));
      replay(project);
      auto &bindings = body(project).scopedBindings;
      require(bindings.size() == 1 && bindings.front().computation,
              "missing Local callback");
      auto &callback = const_cast<Body &>(*bindings.front().computation->body);
      callback.stopped = true;
      callback.stopReason = "reject";
      callback.results.clear();
      callback.effects.fixed.mayStop = true;
      body(project).effects.fixed.mayStop = true;
      rejects(project);
    });
  for (StringRef context : {"If", "Match", "For", "callback", "deferred",
                            "root", "block", "dormant", "zero-trip"})
    for (StringRef mutation : {"invented stop", "removed stop", "reason"})
      cases.run("authored index exit " + context + " " + mutation, [&] {
        const bool stopped = mutation != "invented stop";
        const bool loop = context == "For" || context == "zero-trip";
        std::string leaf = stopped ? "let _:index=7;stop \"abort\";" : "7";
        std::string source;
        if (context == "If" || context == "dormant")
          source = "fn Run(go:bool)->index{return if " +
                   std::string(context == "dormant" ? "false" : "go") + "{" +
                   leaf + "}else{2};}";
        else if (context == "Match")
          source = "enum Choice{First(),Second()} fn Run(go:Choice)->index{"
                   "return match go{Second()=>{2},First()=>{" +
                   leaf + "}};}";
        else if (loop)
          source = "fn Run(n:index)->index{for _ in 0.." +
                   std::string(context == "zero-trip" ? "0" : "n") + "{" +
                   (stopped ? "let _:()=();" + leaf : "let _:index=7;") +
                   "}return n;}";
        else if (context == "callback" || context == "deferred")
          source = "fn apply(f:fn()->index)->index{return " +
                   std::string(context == "deferred" ? "2" : "f()") +
                   ";}fn Run()->index{return apply(fn()=>{" + leaf + "});}";
        else if (context == "block")
          source = "fn Run()->index{return {{" + leaf + "}};}";
        else
          source = "fn Run()->index{" + (stopped ? leaf : "return 7;") + "}";
        auto project = take(check(source));
        replay(project);
        auto &root = body(project);
        Body *target = &root;
        if (context == "callback" || context == "deferred") {
          require(root.scopedBindings.size() == 1 &&
                      root.scopedBindings.front().computation,
                  "missing callback exit");
          target = const_cast<Body *>(
              root.scopedBindings.front().computation->body.get());
        } else if (context != "root" && context != "block") {
          std::vector<Producer> found;
          producers(root, found, [](const auto &op) {
            return std::holds_alternative<Control>(op.action);
          });
          require(found.size() == 1, "missing index control exit");
          target = const_cast<Body *>(
              std::get<Control>(found.front().second->action).regions[0].get());
        }
        require(target->stopped == stopped, "wrong authored exit fixture");
        if (mutation == "removed stop") {
          auto value = llvm::find_if(target->values, [&](const auto &value) {
            return value.type.kind ==
                   (loop ? Type::Kind::Unit : Type::Kind::Index);
          });
          require(value != target->values.end(), "missing continuing value");
          target->stopped = false;
          target->stopReason.clear();
          target->results = {ValueId{uint32_t(value - target->values.begin())}};
          target->effects.fixed.mayStop = false;
          root.effects.fixed.mayStop = false;
        } else {
          target->stopped = true;
          target->stopReason = "reject";
          target->results.clear();
          target->effects.fixed.mayStop = true;
          if (context != "deferred")
            root.effects.fixed.mayStop = true;
        }
        rejects(project);
      });
  cases.run("authored explicit stop cannot retain a result", [&] {
    auto project =
        take(check("fn Run()->index{let _:index=7;stop \"abort\";}"));
    replay(project);
    auto &root = body(project);
    require(!root.values.empty() &&
                root.values.front().type.kind == Type::Kind::Index,
            "missing pre-stop value");
    root.results = {ValueId{0}};
    rejects(project);
  });
  for (
      StringRef selection :
      {R"(if go{stop "reject";}else{stop "abort";})",
       R"(match choice{Second()=>{stop "abort";},First()=>{stop "reject";}})",
       R"(if go{if go{stop "reject";}else{stop "abort";}}else{stop "refused";})"})
    for (bool removeStop : {false, true})
      cases.run(
          "all-stopped parent exit " + selection + " " + Twine(removeStop),
          [&] {
            auto project =
                take(check(("enum Choice{First(),Second()} fn "
                            "Run(go:bool,choice:Choice)->index{return " +
                            selection + ";}")
                               .str()));
            replay(project);
            auto &root = body(project);
            require(root.stopped && root.stopReason == "reject",
                    "producer did not use native first arm reason");
            // No path reaches this parent terminator. In particular the
            // reordered Match must not require its first written reason.
            root.stopReason = "exhausted";
            replay(project);
            if (removeStop) {
              root.stopped = false;
            } else {
              std::vector<Producer> found;
              producers(root, found, [](const auto &op) {
                return std::holds_alternative<Control>(op.action);
              });
              bool changed = false;
              for (auto &[owner, op] : found)
                for (const auto &arm : std::get<Control>(op->action).regions)
                  if (arm->operations.empty()) {
                    const_cast<Body &>(*arm).stopReason = "incomplete";
                    changed = true;
                  }
              require(changed, "missing reachable leaf stop");
            }
            rejects(project);
          });
  for (StringRef selection :
       {R"(if go{stop "reject";}else{stop "abort";})",
        R"(match choice{Second()=>{stop "abort";},First()=>{stop "reject";}})"})
    cases.run("erase stop-establishing control " + selection, [&] {
      auto project = take(check(("enum Choice{First(),Second()} fn "
                                 "Run(go:bool,choice:Choice)->index{return " +
                                 selection + ";}")
                                    .str()));
      replay(project);
      auto &root = body(project);
      require(root.stopped && root.results.empty(), "missing all-stop fixture");
      root.stopReason = "refused";
      replay(project);
      root.operations.clear();
      root.values.resize(root.inputs);
      rejects(project);
    });
  cases.run("erase an unused authored data binding", [&] {
    auto project = take(check("fn Run(source:index,other:index)->index{"
                              "let unused=source;return other;}"));
    replay(project);
    auto &root = body(project);
    require(root.operations.size() == 1, "missing unused binding fixture");
    root.operations.clear();
    root.values.resize(root.inputs);
    rejects(project);
  });
  for (bool call : {false, true})
    for (unsigned aliases : {1u, 2u})
      for (bool hint : {false, true})
        cases.run(
            "coordinated ordinary alias call=" + Twine(call) +
                " aliases=" + Twine(aliases) + " hint=" + Twine(hint),
            [&] {
              std::string source = "fn Keep(x:index)->index{return x;}"
                                   "fn Run(source:index,other:index)->index{";
              for (unsigned i = 0; i < aliases; ++i)
                source += "let alias" + std::to_string(i) + "=" +
                          (i ? "alias" + std::to_string(i - 1) : "source") +
                          ";";
              auto name = "alias" + std::to_string(aliases - 1);
              source += "return " + (call ? "Keep(" + name + ")" : name) + ";}";
              auto project = take(check(source));
              replay(project);
              auto &root = body(project);
              if (!hint) {
                for (auto &op : root.operations)
                  if (std::holds_alternative<Projection>(op.action))
                    op.expression.reset();
                replay(project);
              }
              unsigned changed = 0;
              for (auto &op : root.operations) {
                if (changed == aliases)
                  break;
                auto *projection = std::get_if<Projection>(&op.action);
                if (!projection || !projection->path.empty())
                  continue;
                if (!changed)
                  projection->input = ValueId{1};
                auto span = op.span;
                // check() prepends the module declaration to this source.
                auto useName = "alias" + std::to_string(changed);
                span.begin =
                    StringRef("module sample;").size() + source.rfind(useName);
                span.end = span.begin + useName.size();
                op.span = span;
                root.values[op.results.front().index].span = span;
                if (!hint)
                  op.expression.reset();
                ++changed;
              }
              require(changed == aliases, "missing ordinary aliases");
              rejects(project);
            });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool alias : {false, true})
      cases.run(
          "ordinary control selector source edge " + mode +
              (alias ? " alias" : " direct"),
          [&] {
            const bool protocol = mode == "protocol";
            std::string source = mode.str() + " Run";
            source += protocol
                          ? " roles(P)(go:bool@P,other:bool@P)->(r:bool@P){"
                          : "(go:bool,other:bool)->bool{";
            source +=
                alias ? "let selected=go;return if selected{true}else{false};}"
                      : "return if go{true}else{false};}";
            auto project = take(check(source));
            replay(project);
            auto &root = body(project);
            auto found = llvm::find_if(root.operations, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found != root.operations.end(), "missing selected control");
            std::get<Control>(found->action).operands.front() = ValueId{1};
            rejects(project, "source.binding-witness: control header value "
                             "differs from source");
          });
  for (unsigned bound : {0u, 1u})
    cases.run("local loop bound source edge " + Twine(bound), [&] {
      auto project =
          take(check("fn Run(lo:index,hi:index)->index{for _ in lo..hi{"
                     "let _:index=7;}return hi;}"));
      replay(project);
      auto &root = body(project);
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing loop control");
      auto &control = std::get<Control>(found->action);
      control.operands[bound] = control.operands[1 - bound];
      rejects(
          project,
          "source.binding-witness: control header value differs from source");
    });
  cases.run("protocol loop count source edge", [&] {
    auto project = take(
        check("protocol Run roles(P)(n:index@P,other:index@P)->(r:index@P){"
              "for _ in 0..n roles(P) max 8{}return n;}"));
    replay(project);
    auto &root = body(project);
    auto found = llvm::find_if(root.operations, [](const auto &op) {
      return std::holds_alternative<ProtocolRepeat>(op.action);
    });
    require(found != root.operations.end(), "missing protocol repeat");
    std::get<ProtocolRepeat>(found->action).count = ValueId{1};
    rejects(project,
            "source.binding-witness: repeat count differs from source");
  });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool inferred : {false, true})
      for (bool omit : {false, true}) {
        if (mode == "protocol" && inferred)
          continue;
        cases.run(
            "root source tail " + mode + " inferred=" + Twine(inferred) +
                " omit=" + Twine(omit),
            [&] {
              auto source =
                  mode.str() + " Run" +
                  (mode == "protocol"
                       ? " roles(P)(go:bool@P,other:bool@P)->(r:bool@P)"
                       : "(go:bool,other:bool)" +
                             std::string(inferred ? "" : "->bool")) +
                  "{return if go{true}else{false};}";
              auto project = take(check(source));
              replay(project);
              auto &root = body(project);
              auto found = llvm::find_if(root.operations, [](const auto &op) {
                return std::holds_alternative<Control>(op.action);
              });
              require(found != root.operations.end(), "missing root control");
              if (omit)
                root.expressionValues.erase(*found->expression);
              root.results.front() = ValueId{1};
              rejects(project);
            });
      }
  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (StringRef context : {"root", "arm", "closure", "block", "unused"})
      cases.run("required source result map " + mode + " " + context, [&] {
        const bool protocol = mode == "protocol";
        std::string source;
        if (context == "closure")
          source = "math fn apply(f:math fn()->bool)->bool{return f();}";
        source += mode.str() + " Run" +
                  (protocol ? " roles(P)(go:bool@P)->(r:bool@P)"
                            : "(go:bool)->bool") +
                  "{";
        if (context == "closure")
          source += "return apply(fn()=>if go{true}else{false});}";
        else if (context == "block")
          source += "return {if go{true}else{false}};}";
        else if (context == "unused")
          source += "let _=if go{true}else{false};return go;}";
        else
          source += "return if go{true}else{false};}";
        auto project = take(check(source));
        replay(project);
        std::vector<Producer> found;
        producers(body(project), found, [](const auto &op) {
          return std::holds_alternative<Control>(op.action);
        });
        require(found.size() == 1, "missing control result map fixture");
        auto &[container, op] = found.front();
        if (context == "arm") {
          auto &arm = const_cast<Body &>(
              *std::get<Control>(op->action).regions.front());
          arm.expressionValues.clear();
        } else
          container->expressionValues.erase(*op->expression);
        rejects(project);
      });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool tuple : {false, true})
      cases.run(
          "ordinary arm tail redirection " + mode + " tuple=" + Twine(tuple),
          [&] {
            const bool protocol = mode == "protocol";
            std::string type = tuple ? "(bool,bool)" : "bool";
            auto source = mode.str() + " Run" +
                          (protocol ? " roles(P)(go:bool@P,x:" + type +
                                          "@P)->(r:" + type + "@P)"
                                    : "(go:bool,x:" + type + ")->" + type) +
                          "{return if go{let wrong=x;" +
                          (tuple ? "(true,false)" : "true") + "}else{x};}";
            auto project = take(check(source));
            replay(project);
            auto &root = body(project);
            auto found = llvm::find_if(root.operations, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found != root.operations.end(), "missing arm fixture");
            auto &arm = const_cast<Body &>(
                *std::get<Control>(found->action).regions.front());
            require(arm.inputs, "missing equally typed capture");
            arm.results.front() = ValueId{0};
            rejects(project);
          });
  for (bool protocol : {false, true})
    for (StringRef mutation : {"initial", "successor", "capture"})
      cases.run(
          "loop mutable source edges protocol=" + Twine(protocol) + " " +
              mutation,
          [&] {
            auto source = protocol
                              ? "protocol Run "
                                "roles(P)(n:index@P,a:bool@P,b:bool@P)->(r:"
                                "bool@P){let mut s=a;for _ in 0..n roles(P) "
                                "max 8{let _=b;s=true;}return s;}"
                              : "fn Run(n:index,a:bool,b:bool)->bool{let mut "
                                "s=a;for _ in 0..n{let _=b;s=true;}return s;}";
            auto project = take(check(source));
            replay(project);
            auto &root = body(project);
            auto found = llvm::find_if(root.operations, [&](const auto &op) {
              return protocol
                         ? std::holds_alternative<ProtocolRepeat>(op.action)
                         : std::holds_alternative<Control>(op.action);
            });
            require(found != root.operations.end(), "missing state loop");
            if (protocol) {
              auto &loop = std::get<ProtocolRepeat>(found->action);
              require(loop.carried.size() == 1 && loop.captures.size() == 1,
                      "wrong repeat state fixture");
              if (mutation == "initial")
                loop.carried.front() = ValueId{2};
              else if (mutation == "capture")
                loop.captures.front() = ValueId{1};
              else
                const_cast<Body &>(*loop.region).results.front() = ValueId{1};
            } else {
              auto &loop = std::get<Control>(found->action);
              require(loop.carried == 1 && loop.operands.size() == 4,
                      "wrong local state fixture");
              if (mutation == "initial")
                loop.operands[2] = ValueId{2};
              else if (mutation == "capture")
                loop.operands[3] = ValueId{1};
              else
                const_cast<Body &>(*loop.regions.front()).results.front() =
                    ValueId{1};
            }
            rejects(project);
          });
  for (bool protocol : {false, true})
    for (bool packed : {false, true})
      cases.run(
          "joined mutable latest generation protocol=" + Twine(protocol) +
              " packed=" + Twine(packed),
          [&] {
            std::string source =
                protocol
                    ? "protocol Run roles(P)(go:bool@P,a:bool@P)->(r:bool@P){"
                    : "fn Run(go:bool,a:bool)->bool{";
            source += "let mut s=a;let result=if go{s=true;" +
                      std::string(packed ? "false" : "()") + "}else{s=false;" +
                      (packed ? "true" : "()") + "};return s;}";
            auto project = take(check(source));
            replay(project);
            auto &root = body(project);
            auto found = llvm::find_if(root.operations, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(found != root.operations.end(), "missing joined state");
            auto &arm = const_cast<Body &>(
                *std::get<Control>(found->action).regions.front());
            require(arm.inputs, "missing initial state input");
            if (!packed)
              arm.results.front() = ValueId{0};
            else {
              auto pack = llvm::find_if(arm.operations, [&](const auto &op) {
                return !op.results.empty() &&
                       op.results.front().index == arm.results.front().index;
              });
              require(pack != arm.operations.end(), "missing state pack");
              auto *aggregate = std::get_if<Construct>(&pack->action);
              require(aggregate && aggregate->operands.size() == 2,
                      "wrong joined pack");
              aggregate->operands.back() = ValueId{0};
            }
            rejects(project);
          });
  cases.run("retained protocol repeat maximum", [&] {
    auto project =
        take(check("protocol Run<N:nat> roles(P)(n:index@P)->(r:index@P){for _ "
                   "in 0..n roles(P) max N{}return n;}"));
    replay(project);
    auto &root = body(project);
    auto found = llvm::find_if(root.operations, [](const auto &op) {
      return std::holds_alternative<ProtocolRepeat>(op.action);
    });
    require(found != root.operations.end(), "missing symbolic maximum");
    std::get<ProtocolRepeat>(found->action).maximum = Natural::constant(7);
    rejects(project);
  });
  cases.run("named protocol return edges and authored order", [&] {
    auto project = take(check("protocol Run "
                              "roles(P)(a:bool@P,b:bool@P)->(left:bool@P,right:"
                              "bool@P){return(right={b},left={a});}"));
    replay(project);
    auto &root = body(project);
    require(root.results.size() == 2, "missing named returns");
    std::swap(root.results[0], root.results[1]);
    rejects(project);
  });
  for (StringRef source :
       {"fn Run(go:bool,a:bool)->bool{let mut s=a;let _=if "
        "go{s=true;()}else{()};return s;}",
        "fn Run(go:bool)->bool{return if go{stop \"abort\";}else{{true}};}",
        "fn Run(n:index,a:bool)->bool{let mut s=a;for _ in 0..n{s=true;}return "
        "s;}",
        "fn Run()->(){for _ in 0..0{stop \"abort\";}return ();}",
        "math fn Run(go:bool)->(bool,bool){return if "
        "go{{(true,false)}}else{(false,true)};}",
        "math fn Run(go:bool)->(){return if go{()}else{()};}",
        "protocol Run roles(P)(n:index@P,a:bool@P)->(r:bool@P){let mut s=a;for "
        "_ in 0..n roles(P) max 8{s=true;}return s;}"})
    cases.run("distinct source control/yield paths " + source,
              [&] { replay(take(check(source))); });

  for (StringRef mode : {"math fn", "fn", "protocol"})
    for (bool closure : {false, true})
      cases.run(
          "equally typed captured source edges " + mode +
              " closure=" + Twine(closure),
          [&] {
            const bool protocol = mode == "protocol";
            std::string source =
                closure ? "math fn apply(f:math fn()->bool)->bool{return f();}"
                        : "";
            source +=
                mode.str() + " Run" +
                (protocol ? " roles(P)(go:bool@P,a:bool@P,b:bool@P)->(r:bool@P)"
                          : "(go:bool,a:bool,b:bool)->bool") +
                "{return " + (closure ? "apply(fn()=>" : "") +
                "if go{a}else{b}" + (closure ? ")" : "") + ";}";
            auto project = take(check(source));
            replay(project);
            auto &root = body(project);
            if (closure) {
              auto found =
                  llvm::find_if(root.scopedBindings, [](const auto &binding) {
                    return bool(binding.computation);
                  });
              require(found != root.scopedBindings.end() &&
                          found->captures.size() == 3,
                      "missing closure captures");
              found->captures[1] = found->captures[2];
            } else {
              auto found = llvm::find_if(root.operations, [](const auto &op) {
                return std::holds_alternative<Control>(op.action);
              });
              require(found != root.operations.end(),
                      "missing capture control");
              auto &control = std::get<Control>(found->action);
              require(control.operands.size() == 3,
                      "missing distinct captures");
              control.operands[1] = control.operands[2];
            }
            rejects(project);
          });
  cases.run("zero-trip input of an all-stopped mutable loop", [&] {
    auto project =
        take(check("fn Run(n:index,a:bool,b:bool)->bool{let mut s=a;for _ in "
                   "0..n{s=true;stop \"abort\";}return b;}"));
    replay(project);
    auto &root = body(project);
    auto found = llvm::find_if(root.operations, [](const auto &op) {
      return std::holds_alternative<Control>(op.action);
    });
    require(found != root.operations.end(), "missing stopped loop");
    std::get<Control>(found->action).operands[2] = ValueId{2};
    rejects(project, "source.binding-witness: loop initial state differs from "
                     "source binding");
  });
  for (StringRef mode : {"math fn", "fn", "protocol"})
    cases.run("native-order Match source tail " + mode, [&] {
      const bool protocol = mode == "protocol";
      auto source = "enum Choice{First(),Second()} " + mode.str() + " Run" +
                    (protocol ? " roles(P)(x:Choice@P)->(r:bool@P)"
                              : "(x:Choice)->bool") +
                    "{return match x{Second()=>{let "
                    "unused=true;false},First()=>{true}};}";
      auto project = take(check(source));
      replay(project);
      auto &root = body(project);
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing Match");
      auto &control = std::get<Control>(found->action);
      require(control.alternatives ==
                  std::vector<std::string>{"First", "Second"},
              "source arm order replaced native order");
      auto &second = const_cast<Body &>(*control.regions[1]);
      auto literal = llvm::find_if(second.operations, [](const auto &op) {
        if (const auto *local = std::get_if<LocalPrimitive>(&op.action))
          return local->parameters == std::vector<std::string>{"true"};
        if (const auto *math = std::get_if<MathValue>(&op.action))
          return math->literal == "true";
        return false;
      });
      require(literal != second.operations.end(), "missing unused Match value");
      second.results.front() = literal->results.front();
      rejects(project,
              "source.binding-witness: control yield differs from source tail");
    });
  cases.run("joined mutable state with one stopped arm", [&] {
    replay(take(check("fn Run(go:bool,a:bool)->bool{let mut s=a;let _=if "
                      "go{stop \"abort\";}else{s=true;()};return s;}")));
  });

  for (StringRef kind : {"for", "if", "closure"})
    cases.run("stale mutable capture generation " + kind, [&] {
      std::string source =
          kind == "closure"
              ? "math fn apply(f:math fn()->bool)->bool{return f();}"
              : "";
      source += "fn Run(go:bool,n:index)->bool{let mut s=false;s=true;";
      if (kind == "for")
        source += "for _ in 0..n{s=false;}return s;}";
      else if (kind == "if")
        source += "return if go{s}else{s};}";
      else
        source += "return apply(fn()=>s);}";
      auto project = take(check(source));
      replay(project);
      auto &root = body(project);
      std::vector<ValueId> versions;
      for (const auto &op : root.operations)
        if (const auto *projection = std::get_if<Projection>(&op.action);
            projection && projection->path.empty())
          versions.push_back(op.results.front());
      require(versions.size() >= 2, "missing mutable generations");
      if (kind == "closure") {
        auto found =
            llvm::find_if(root.scopedBindings, [](const auto &binding) {
              return bool(binding.computation);
            });
        require(found != root.scopedBindings.end() &&
                    found->captures.size() == 1,
                "missing snapshot closure");
        found->captures.front() = versions.front();
      } else {
        auto found = llvm::find_if(root.operations, [](const auto &op) {
          return std::holds_alternative<Control>(op.action);
        });
        require(found != root.operations.end(), "missing generation control");
        auto &control = std::get<Control>(found->action);
        control.operands[kind == "for" ? 2 : 1] = versions.front();
      }
      rejects(project);
    });
  for (StringRef source :
       {"fn Run(n:index)->(){let mut s=();for _ in 0..n{s=();}return s;}",
        "fn Run(go:bool)->(){let mut s=();let _=if go{s=();()}else{()};return "
        "s;}",
        "fn apply(f:fn()->bool,ignored:bool)->bool{return f();} fn "
        "Run()->bool{let mut s=false;return apply(fn()=>s,{s=true;true});}"})
    cases.run("Unit carry and retained capture snapshot " + source,
              [&] { replay(take(check(source))); });

  for (bool protocol : {false, true})
    cases.run(
        "loop Unit result cannot select mutable state " + Twine(protocol), [&] {
          auto source =
              protocol
                  ? "protocol Run roles(P)(n:index@P,a:bool@P)->(r:bool@P){let "
                    "mut s=a;for _ in 0..n roles(P) max 8{s=true;}return a;}"
                  : "fn Run(n:index,a:bool)->bool{let mut s=a;for _ in "
                    "0..n{s=true;stop \"abort\";}return a;}";
          auto project = take(check(source));
          replay(project);
          auto &root = body(project);
          auto found = llvm::find_if(root.operations, [&](const auto &op) {
            return protocol ? std::holds_alternative<ProtocolRepeat>(op.action)
                            : std::holds_alternative<Control>(op.action);
          });
          require(found != root.operations.end() && !found->results.empty(),
                  "missing loop state result");
          root.expressionValues[*found->expression] = found->results.front();
          rejects(project, protocol ? "source.binding-witness: repeat unit "
                                      "value differs from source"
                                    : "source.binding-witness: loop unit value "
                                      "differs from source");
        });
  for (bool protocol : {false, true})
    cases.run("omitted whole mutable join " + Twine(protocol), [&] {
      auto source =
          protocol
              ? "protocol Run roles(P)(go:bool@P,a:bool@P)->(r:bool@P){let mut "
                "s=a;let _=if go{s=true;()}else{()};return s;}"
              : "fn Run(go:bool,a:bool)->bool{let mut s=a;let _=if "
                "go{s=true;()}else{()};return s;}";
      auto project = take(check(source));
      replay(project);
      auto &root = body(project);
      auto initial = llvm::find_if(root.operations, [](const auto &op) {
        auto *p = std::get_if<Projection>(&op.action);
        return p && p->path.empty();
      });
      require(initial != root.operations.end(),
              "missing initial mutable binding");
      auto old = initial->results.front();
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing omitted state fixture");
      auto result = found->results.front();
      root.values[result.index].type = Type(Type::Kind::Unit);
      for (auto &region : std::get<Control>(found->action).regions) {
        auto &arm = const_cast<Body &>(*region);
        auto empty = llvm::find_if(arm.operations, [](const auto &op) {
          auto *pack = std::get_if<Construct>(&op.action);
          return pack && pack->kind == Construct::Kind::Aggregate &&
                 pack->operands.empty();
        });
        require(empty != arm.operations.end(), "missing arm Unit value");
        arm.results.front() = empty->results.front();
      }
      for (auto &[id, value] : root.expressionValues)
        if (value.index == result.index)
          value = old;
      root.results.front() = old;
      rejects(project, "source.binding-witness: lexical value origin differs");
    });
  for (bool protocol : {false, true})
    cases.run(
        "old explicit result cannot become current state " + Twine(protocol),
        [&] {
          auto source =
              protocol
                  ? "protocol Run roles(P)(go:bool@P,a:bool@P)->(r:bool@P){let "
                    "mut s=a;let _=if go{let old=s;s=true;old}else{let "
                    "old=s;s=false;old};return s;}"
                  : "fn Run(go:bool,a:bool)->bool{let mut s=a;let _=if go{let "
                    "old=s;s=true;old}else{let old=s;s=false;old};return s;}";
          auto project = take(check(source));
          replay(project);
          auto &root = body(project);
          auto found = llvm::find_if(root.operations, [](const auto &op) {
            return std::holds_alternative<Control>(op.action);
          });
          require(found != root.operations.end(),
                  "missing packed state fixture");
          auto explicitResult = root.expressionValues.at(*found->expression);
          auto current = root.results.front();
          for (auto &[id, value] : root.expressionValues)
            if (value.index == current.index)
              value = explicitResult;
          root.results.front() = explicitResult;
          rejects(project,
                  "source.binding-witness: lexical value origin differs");
        });
  for (StringRef source : {"fn Run(go:bool,a:bool)->bool{let mut s=a;let _=if "
                           "go{s=true;stop \"abort\";}else{()};return s;}",
                           "fn Run(go:bool)->bool{let mut s=false;let _=if "
                           "{s=true;go}{()}else{()};return s;}",
                           "fn Run(n:index)->bool{let mut s=false;for _ in "
                           "{s=true;0}..n{}return s;}",
                           "fn Run(n:index)->bool{let mut s=false;for _ in "
                           "0..{s=true;n}{}return s;}",
                           "fn Run(n:index,a:bool)->bool{let mut s=a;for _ in "
                           "0..n{let _=s;s={stop \"abort\";};}return s;}",
                           "fn Run<T:Type+Drop>(go:bool,a:T,b:T)->T{let mut "
                           "s=a;return if go{s=b;s}else{let _=b;s};}"})
    cases.run("source state boundary and header flow " + source,
              [&] { replay(take(check(source))); });

  for (StringRef mutation : {"missing", "duplicate", "misplaced"})
    cases.run("whole region control coverage " + mutation, [&] {
      auto project = take(check(R"(
        fn Run(go:bool,value:index)->index{
          let _:index=if go{if go{value}else{value}}else{value};return value;
        }
      )"));
      replay(project);
      auto &root = body(project);
      auto found = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Control>(op.action);
      });
      require(found != root.operations.end(), "missing ordinary control");
      if (mutation == "missing")
        root.operations.erase(found);
      else if (mutation == "duplicate") {
        auto copy = *found;
        copy.results.clear();
        root.operations.push_back(std::move(copy));
      } else {
        const auto &arm = *std::get<Control>(found->action).regions.front();
        auto nested = llvm::find_if(arm.operations, [](const auto &op) {
          return std::holds_alternative<Control>(op.action);
        });
        require(nested != arm.operations.end(), "missing nested control");
        *found = *nested;
      }
      auto error = checkScopedElaboration(project);
      require(bool(error), "whole control coverage mutation passed");
      auto diagnostic = toString(std::move(error));
      require(StringRef(diagnostic).contains("source.binding-witness") &&
                  StringRef(diagnostic)
                      .contains("control occurrence coverage differs"),
              diagnostic);
    });
  for (StringRef mutation :
       {"operation span", "value span", "duplicate", "misplaced"})
    cases.run("whole region binding coverage " + mutation, [&] {
      auto project = take(check(R"(
        fn Run(go:bool,value:index)->index{
          let unused=value;return if go{value}else{value};
        }
      )"));
      replay(project);
      auto &root = body(project);
      auto alias = llvm::find_if(root.operations, [](const auto &op) {
        return std::holds_alternative<Projection>(op.action);
      });
      require(alias != root.operations.end() && alias->results.size() == 1,
              "missing unused alias");
      auto value = alias->results.front();
      if (mutation == "operation span")
        ++alias->span.begin;
      else if (mutation == "value span")
        ++root.values[value.index].span.begin;
      else if (mutation == "duplicate") {
        auto copy = *alias;
        copy.results = {ValueId{uint32_t(root.values.size())}};
        root.values.push_back(root.values[value.index]);
        root.operations.push_back(std::move(copy));
      } else {
        auto control = llvm::find_if(root.operations, [](const auto &op) {
          return std::holds_alternative<Control>(op.action);
        });
        require(control != root.operations.end(), "missing alias region");
        auto &arm = const_cast<Body &>(
            *std::get<Control>(control->action).regions.front());
        auto copy = *alias;
        copy.expression.reset();
        std::get<Projection>(copy.action).input = ValueId{0};
        copy.results = {ValueId{uint32_t(arm.values.size())}};
        arm.values.push_back(root.values[value.index]);
        arm.operations.push_back(std::move(copy));
        root.operations.erase(alias);
      }
      auto error = checkScopedElaboration(project);
      require(bool(error), "binding coverage mutation passed");
      auto diagnostic = toString(std::move(error));
      require(StringRef(diagnostic).contains("source.binding-witness") &&
                  StringRef(diagnostic)
                      .contains("binding occurrence coverage differs"),
              diagnostic);
    });
  for (StringRef action :
       {"let unused:index=", "let mut unused:index=0;unused="})
    cases.run("stopping initializer creates no binding " + action, [&] {
      auto project =
          take(check(("fn Run(go:bool)->index{" + action +
                      "if go{stop \"reject\";}else{stop \"abort\";};}")
                         .str()));
      replay(project);
    });
  cases.run("source exits share work and preserve exact bounded replay", [&] {
    auto measure = [&](unsigned count) {
      std::string source = "module sample;fn Run(go:bool)->index{";
      for (unsigned i = 0; i < count; ++i)
        source += "let _:index={if go{1}else{2}};";
      source += "return {if go{stop \"abort\";}else{3}};}";
      auto captured = take(capture({{"sample", source, "exits.zkc"}}));
      auto project = take(analyze(captured).checkedProject());
      std::vector<SourceWorkBudget> observations;
      if (auto error = checkScopedElaboration(project, {}, &observations))
        throw std::runtime_error(toString(std::move(error)));
      require(observations.size() == 1 &&
                  observations.front().ledger.total ==
                      observations.front().ledger.used(
                          SourceWorkPhase::ScopedElaboration),
              "source exit work escaped the shared replay budget");
      Limits limits;
      limits.work =
          std::max(project.checkedWork(), observations.front().ledger.total);
      if (auto error = checkScopedElaboration(project, limits))
        throw std::runtime_error(toString(std::move(error)));
      --limits.work;
      auto error = checkScopedElaboration(project, limits);
      require(
          bool(error) &&
              StringRef(toString(std::move(error))).contains("source.limit"),
          "source exits exceeded the observed replay allowance");
      limits.work = project.checkedWork();
      take(analyze(captured, limits).checkedProject());
      --limits.work;
      refuses(analyze(captured, limits).checkedProject(), "source.limit");
      outs() << count << " exit regions: analysis " << project.checkedWork()
             << ", replay " << observations.front().ledger.total << '\n';
      return observations.front().ledger.total;
    };
    auto small = measure(64), large = measure(128);
    require(large > small && large < 3 * small,
            "source exits repeated work for sibling regions");
  });
  for (StringRef mode : {"fn", "math fn", "protocol"})
    for (bool clearHint : {false, true})
      for (StringRef context : {"standalone", "nested", "dormant", "callback"})
        cases.run(
            "missing Boolean literal mapping in " + mode + " " + context + " " +
                Twine(clearHint),
            [&] {
              std::string formula = "true";
              if (context == "nested")
                formula = "true&&{let _=true;false||true}";
              if (context == "dormant")
                formula = "false&&{let _=true;true}";
              if (context == "callback")
                formula = "apply(fn()=>{let _=true;false})";
              auto source =
                  std::string(context != "callback" ? ""
                              : mode == "fn"
                                  ? "fn apply(f:fn()->bool)->bool{return f();}"
                                  : "math fn apply(f:math "
                                    "fn()->bool)->bool{return f();}") +
                  mode.str() +
                  (mode == "protocol" ? " Run roles(P)()->(r:bool@P)"
                                      : " Run()->bool") +
                  "{return " + formula + ";}";
              auto project = take(check(source));
              replay(project);
              std::vector<Producer> found;
              producers(body(project), found, [](const auto &op) {
                if (const auto *constant =
                        std::get_if<LocalPrimitive>(&op.action))
                  return constant->contract == "bool.constant";
                if (const auto *constant = std::get_if<MathValue>(&op.action))
                  return constant->identity ==
                         zkc::MathematicalIdentity::BooleanConstant;
                return false;
              });
              require(!found.empty(), "missing Boolean literal");
              auto target = found.begin();
              if (context != "standalone") {
                auto begin = StringRef("module sample;").size() +
                             source.find("let _=") + StringRef("let _=").size();
                target = llvm::find_if(found, [&](const auto &candidate) {
                  return candidate.second->span.begin == begin;
                });
              }
              require(target != found.end(),
                      "missing ignored authored literal");
              auto [checked, op] = *target;
              require(op->expression.has_value(),
                      "literal has no occurrence hint");
              require(checked->expressionValues.erase(*op->expression) == 1,
                      "literal has no source mapping");
              if (auto *constant = std::get_if<LocalPrimitive>(&op->action))
                constant->parameters.front() =
                    constant->parameters.front() == "true" ? "false" : "true";
              else {
                auto &math = std::get<MathValue>(op->action);
                math.literal = math.literal == "true" ? "false" : "true";
              }
              if (clearHint)
                op->expression.reset();
              rejects(project);
            });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("enum source formation mutation " + Twine(mutation), [&] {
      auto project = take(check(R"(
        enum E{First(bool),Second(bool)} enum Other{First(bool),Second(bool)}
        math fn Run(a:bool,b:bool)->E{return E::First(a);}
      )"));
      replay(project);
      auto &checked = body(project);
      auto at = llvm::find_if(checked.operations, [](const auto &op) {
        return std::holds_alternative<Construct>(op.action);
      });
      require(at != checked.operations.end(), "missing enum formation");
      auto &construct = std::get<Construct>(at->action);
      if (mutation == 0)
        construct.alternative = "Second";
      if (mutation == 1)
        construct.operands.front() = ValueId{1};
      if (mutation == 2)
        checked.values[at->results.front().index].type.domain = "sample::Other";
      rejects(project);
    });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run("crossed authored Boolean scope " + Twine(mutation), [&] {
      auto project = take(check(R"(
        protocol Run roles(P)(a:bool@P,b:bool@P)->(r:bool@P){
          let first=a&&b;let second=b&&a;return first||second;
        }
      )"));
      replay(project);
      auto &checked = body(project);
      std::vector<Operation *> invokes;
      for (auto &op : checked.operations)
        if (std::holds_alternative<ScopedInvoke>(op.action))
          invokes.push_back(&op);
      require(invokes.size() == 3, "selection was duplicated or merged");
      auto &first = std::get<ScopedInvoke>(invokes[0]->action);
      auto &second = std::get<ScopedInvoke>(invokes[1]->action);
      if (mutation == 0)
        std::swap(first.source, second.source);
      if (mutation == 1)
        std::swap(first.binding, second.binding);
      if (mutation == 2)
        std::swap(invokes[0]->expression, invokes[1]->expression);
      if (mutation == 3)
        std::swap(checked.scopedBindings[first.binding].computation,
                  checked.scopedBindings[second.binding].computation);
      rejects(project);
    });
  cases.run("enum static instantiations cannot be crossed", [&] {
    auto project = take(check(R"(
      enum E<N:nat>{Empty(),Other()}
      math fn Run()->bool{let first=E::Empty<1>();let second=E::Empty<2>();return true;}
    )"));
    replay(project);
    auto &checked = body(project);
    std::vector<ValueId> variants;
    for (const auto &op : checked.operations)
      if (const auto *construct = std::get_if<Construct>(&op.action);
          construct && construct->kind == Construct::Kind::Variant)
        variants.push_back(op.results.front());
    require(variants.size() == 2, "missing generic enum instantiations");
    checked.values[variants[0].index].type =
        checked.values[variants[1].index].type;
    rejects(project);
  });
  cases.run(
      "native enum alternative mutation preserves typing and refuses "
      "comparison",
      [&] {
        auto input = original((StringRef(R"(
      enum E{First(bool),Second(bool)}
      math fn work(x:bool)->bool{return match E::First(x){First(a)=>{a},Second(b)=>{!b}};}
      protocol Run roles(P)(x:bool@P)->(r:bool@P){return work(x);}
    )") + entry)
                                  .str());
        mlir::DialectRegistry registry;
        zkc::registerDialects(registry);
        mlir::MLIRContext context(registry);
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
        require(bool(module), "cannot parse native enum original");
        bool changed = false;
        module->walk([&](mlir::Operation *op) {
          if (!changed && op->getName().getStringRef() == "data.make") {
            auto label = op->getAttrOfType<mlir::StringAttr>("alternative");
            require(bool(label), "enum alternative missing");
            op->setAttr("alternative",
                        mlir::StringAttr::get(&context,
                                              label.getValue() == "case00000000"
                                                  ? "case00000001"
                                                  : "case00000000"));
            changed = true;
          }
        });
        require(changed && succeeded(mlir::verify(*module)),
                "mutation must remain typed");
        refuses(compareOriginal(input.entry(), *module),
                "source.correspondence");
      });
  cases.run("native pointwise Boolean arms cannot be crossed", [&] {
    auto input = original((selected + entry).str());
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    mlir::MLIRContext context(registry);
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(input.bytes(), &context);
    require(bool(module), "cannot parse native selected Boolean");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (!changed && op->getName().getStringRef() == "data.branch") {
        require(op->getNumRegions() == 2, "missing native arms");
        mlir::Region temporary;
        temporary.takeBody(op->getRegion(0));
        op->getRegion(0).takeBody(op->getRegion(1));
        op->getRegion(1).takeBody(temporary);
        changed = true;
      }
    });
    require(changed && succeeded(mlir::verify(*module)),
            "crossed native arms must remain typed");
    refuses(compareOriginal(input.entry(), *module), "source.correspondence");
  });
  const std::pair<StringRef, StringRef> negatives[] = {
      {R"(enum E{A(bool),B()} protocol Run roles(P,V)(x:bool@P)->(r:E@V){return E::A(x);})",
       "source.roles"},
      {R"(enum E{A(bool),B()} protocol Run roles(P,V)(x:bool@P,y:bool@V)->(r:E@P){return E::A(x&&y);})",
       "source.roles"},
      {R"(enum E{A(bool,bool),B()} protocol Run roles(P,V)(x:bool@P,y:bool@V)->(r:E@P){return E::A(x,y);})",
       "source.roles"},
      {R"(#[linear] struct Token{} enum E{A(),B(Token)} math fn bad()->E{return E::A();})",
       "source.mode"},
      {R"(domain F=field("koala-bear");type Polynomial=builtin("polynomial",F);enum E{A(),B(Polynomial)} math fn bad()->E{return E::A();})",
       "source.mode"},
      {R"(domain F=field("koala-bear");type Polynomial=builtin("polynomial",F);enum E{A(),B(Polynomial)} protocol Run roles(P)()->(r:E@P){return E::A();})",
       "source.mode"},
      {R"(type T=builtin("oracle.table",bool,16);type O=builtin("oracle",T);enum E{A(),B(O)})",
       "source.oracle-aggregate"},
      {R"(type T=builtin("oracle.table",bool,16);type O=builtin("oracle",T);enum E{A()} oracle def Identity(source:O)->O{query(position:index){let answer<-oracle.query(source,position);let unused=E::A();return answer;}})",
       "source.mode"},
      {R"(#[linear] enum E{A(),B()} math fn bad()->E{return E::A();})",
       "source.mode"},
      {R"(module Hidden{#[sealed] pub enum E{A(),B()}} math fn bad()->Hidden::E{return Hidden::E::A();})",
       "source.private"},
      {R"(enum E{A(bool),B()} math fn bad()->E{return E::A(index<0>());})",
       "source.type"},
      {R"(enum E{A(bool),B()} math fn bad()->E{return E::A();})",
       "source.call"},
      {R"(fn local(x:bool)->bool effects(){return x;} protocol Run roles(P)(a:bool@P)->(r:bool@P){return false&&local(a);})",
       "source.mode"},
      {R"(protocol Run roles(P)(a:bool@P)->(r:bool@P){return true||{require a;a};})",
       "source.mode"},
      {R"(protocol Run roles(P)(a:bool@P)->(r:bool@P){return true||{let mut b=a;b};})",
       "source.mode"},
      {R"(math fn bad(a:bool)->bool{return true||{let b=index<0>();b};})",
       "source.type"},
      {R"(math fn bad(a:bool)->bool{return false&&unknown(a);})",
       "source.name"},
      {R"(math fn bad(a:bool)->bool{return index<0>()&&a;})", "source.type"},
      {R"(math fn helper<N:nat>(x:bool)->bool where 1<=N{return x;} protocol Run roles(P)(a:bool@P)->(r:bool@P){return false&&helper<0>(a);})",
       "source.bound"},
      {R"(#[linear] struct Token{} enum E<T:Type+Copy>{A(),B(T)} math fn bad()->bool{let ignored=E::A<Token>();return true;})",
       "source.permission"},
      {R"(interface I{type State:Type+Copy+Drop;} module C:I{type State:Type+Copy+Drop=bool;math fn bad(x:bool)->State{return State(x);}})",
       "source.call"},
  };
  for (const auto &[source, diagnostic] : negatives)
    cases.run("refuse " + source, [source = source, diagnostic = diagnostic] {
      refuses(check(source), diagnostic);
    });
  for (bool protocol : {false, true})
    for (unsigned mutation = 0; mutation < 5; ++mutation)
      cases.run(
          "authored Boolean mutation " + Twine(protocol) + ":" +
              Twine(mutation),
          [&] {
            auto project = take(check(
                protocol
                    ? StringRef(selected)
                    : StringRef(
                          "math fn Run(a:bool,b:bool)->bool{return a&&b;}")));
            replay(project);
            auto &outer = body(project);
            auto *nested = &outer;
            if (protocol)
              nested = &const_cast<Body &>(
                  *outer.scopedBindings.front().computation->body);
            auto at = llvm::find_if(nested->operations, [](const auto &op) {
              return std::holds_alternative<Control>(op.action);
            });
            require(at != nested->operations.end(), "missing selected control");
            auto &control = std::get<Control>(at->action);
            if (mutation == 0)
              std::swap(control.regions[0], control.regions[1]);
            if (mutation == 1)
              control.operands.front() = control.operands.back();
            if (mutation == 2) {
              auto &arm = const_cast<Body &>(*control.regions.front());
              auto replacement = *control.regions.back();
              require(!replacement.operations.empty(), "missing literal arm");
              auto operation = replacement.operations.front();
              operation.results = {ValueId{uint32_t(arm.values.size())}};
              arm.values.push_back(
                  replacement.values[replacement.results.front().index]);
              arm.operations.push_back(operation);
              arm.results.front() = operation.results.front();
            }
            if (mutation == 3) {
              if (protocol)
                std::swap(outer.scopedBindings.front().captures[0],
                          outer.scopedBindings.front().captures[1]);
              else
                control.regions[0] = control.regions[1];
            }
            if (mutation == 4) {
              if (protocol) {
                for (auto &op : outer.operations)
                  if (auto *invoke = std::get_if<ScopedInvoke>(&op.action))
                    invoke->operands.push_back({0});
              } else
                at->expression.reset();
            }
            rejects(project);
          });
  return cases.result();
}
