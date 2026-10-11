#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
fn get<F:Field>(xs:Vector<F>,i:index)->F=primitive("vector.get");
math fn apply_math<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:scoped math fn(A)->B)->B{return body(x);}
math fn forward_math<A:Type+Copy+Drop,B:Type+Copy+Drop>(x:A,body:scoped math fn(A)->B)->B{return apply_math(x,body);}
fn apply<A:Type,B:Type>(x:A,body:scoped fn(A)->B !{stop})->B !{stop}{return body(x);}
fn forward<A:Type,B:Type>(x:A,body:scoped fn(A)->B !{stop})->B !{stop}{return apply(x,body);}
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "scoped.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
void succeeds(StringRef source) {
  auto project = take(check(source));
  if (!project.entries().empty()) {
    auto closed = take(closeEntry(project, "m::Run"));
    for (const auto &decl : closed.declarations())
      if (decl.body) {
        require(decl.scopedInputs.empty(), "scoped signature survived closure");
        require(decl.body->scopedBindings.empty(),
                "scoped bindings survived closure");
        for (const auto &op : decl.body->operations)
          require(!std::holds_alternative<ScopedInvoke>(op.action),
                  "scoped invocation survived closure");
      }
  }
}
} // namespace
int main() {
  Cases cases;
  cases.run("generic Local apply and forwarding", [] {
    succeeds(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return(r=forward(x,fun y=>y+a));}
run Run=Demo;)");
  });
  cases.run("existing reduction inside scoped callback", [] {
    succeeds(R"(
fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");
fn example(xs:Vector<Fr>,a:Fr)->Fr {
 return apply(a,fun y=>reduce sum [x in xs] {x+a+y});
}
protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P)->(r:Fr@P){return example(xs,a);}
run Run=Demo;)");
  });
  cases.run(
      "scoped specialization retains joint authored and captured aliases", [] {
        auto project = take(check(R"(
fn twice(x:Fr,y:Fr,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{return body(x)+y;}
fn dispatcher(x:Fr,y:Fr,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{
 return twice(x,x,body)+twice(x,y,body);
}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return dispatcher(x,y,fun v=>v+y);}
run Run=Demo;
)"));
        auto closed = take(closeEntry(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
        unsigned variants = 0;
        for (const auto &declaration : closed.declarations())
          if (declaration.body && declaration.name == "twice") {
            ++variants;
            const auto &layout = declaration.closureLayout;
            if (layout.inputs == std::vector<unsigned>({0, 0}))
              require(layout.captures == std::vector<unsigned>{2} &&
                          declaration.inputs.size() == 3,
                      "independent captured value was merged with an authored "
                      "input");
            else
              require(layout.inputs == std::vector<unsigned>({0, 1}) &&
                          layout.captures == std::vector<unsigned>{1} &&
                          declaration.inputs.size() == 2,
                      "equal captured and authored places received different "
                      "ports");
          }
        require(variants == 2,
                "distinct alias partitions shared a specialization");
        bool changed = false;
        for (const auto &declaration : closed.declarations())
          if (declaration.body && declaration.name == "twice" &&
              declaration.inputs.size() == 3) {
            auto &layout = const_cast<Declaration &>(declaration).closureLayout;
            layout.captures.front() = 0;
            changed = true;
            break;
          }
        require(changed, "missing distinct-capture specialization");
        auto error = checkScopedSpecialization(closed);
        require(bool(error), "forged capture alias was accepted");
        consumeError(std::move(error));
      });
  cases.run("long sequential let aliases close without expression recursion",
            [] {
              std::string program = "fn chain(x:Fr)->Fr !{stop}{let a0=x;";
              for (unsigned i = 1; i <= 150; ++i)
                program += "let a" + std::to_string(i) + "=a" +
                           std::to_string(i - 1) + ";";
              program += "return apply(a150,fun y=>y+a150);}";
              program += "protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return "
                         "chain(x);}run Run=Demo;";
              auto closed = take(closeEntry(take(check(program)), "m::Run"));
              if (auto error = checkScopedSpecialization(closed))
                throw std::runtime_error(toString(std::move(error)));
            });
  cases.run("many scoped calls share one body origin table", [] {
    std::string program =
        "fn wide(x:Fr,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{";
    for (unsigned i = 0; i < 1200; ++i)
      program += "let a" + std::to_string(i) + "=apply(x,body);";
    program +=
        "return x;}protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return "
        "wide(x,fun y=>y+a);}run Run=Demo;";
    auto closed = take(closeEntry(take(check(program)), "m::Run"));
    if (auto error = checkScopedSpecialization(closed))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("protocol edge rejects coordinated forged input aliases", [] {
    auto closed = take(closeEntry(take(check(R"(
protocol Inner roles(P)(a:Fr@P,b:Fr@P)->(r:Fr@P){return a-b;}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){let r=Inner(x,y);return r;}run Run=Demo;
)")),
                                  "m::Run"));
    bool changed = false;
    for (const auto &declaration : closed.declarations())
      if (declaration.body && declaration.name == "Inner") {
        auto &selected = const_cast<Declaration &>(declaration);
        selected.closureLayout.inputs = {0, 0};
        auto body = std::make_shared<Body>(*selected.body);
        selected.body = body;
        for (auto &op : body->operations)
          if (auto *math = std::get_if<MathValue>(&op.action))
            for (auto &operand : math->operands)
              if (operand.index == 1) {
                operand.index = 0;
                changed = true;
              }
      }
    require(changed, "protocol mutation did not reach the second operand");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "forged specialization accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong specialization refusal");
  });
  cases.run("truncated hidden input body is rejected before reading ports", [] {
    auto closed = take(closeEntry(take(check(R"(
fn twice(x:Fr,y:Fr,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{return body(x)+y;}
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return twice(x,x,fun y=>y+a);}run Run=Demo;
)")),
                                  "m::Run"));
    bool changed = false;
    for (const auto &declaration : closed.declarations())
      if (declaration.body && declaration.name == "twice") {
        require(declaration.inputs.size() == 3, "missing hidden input");
        auto body = std::make_shared<Body>(*declaration.body);
        const_cast<Declaration &>(declaration).body = body;
        body->values.resize(2);
        changed = true;
      }
    require(changed, "missing candidate body");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "forged specialization accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong specialization refusal");
  });
  cases.run("reduction expression evidence keeps the helper value space", [] {
    auto project = take(check(R"(
fn sum<F:Field>(xs:Vector<F>)->F=primitive("vector.sum");
fn g(xs:Vector<Fr>,a:Fr,body:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{let r=reduce sum [x in xs]{x+a};return body(r);}
protocol Demo roles(P)(xs:Vector<Fr>@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return g(xs,a,fun y=>y+b);}run Run=Demo;
)"));
    const ReductionBinding *evidence = nullptr;
    for (const auto &declaration : project.declarations())
      if (declaration.name == "g" && declaration.body)
        for (const auto &op : declaration.body->operations)
          if (op.reduction)
            evidence = &*op.reduction;
    require(evidence != nullptr, "missing source reduction evidence");
    auto closed = take(closeEntry(project, "m::Run"));
    bool checked = false;
    for (const auto &declaration : closed.declarations())
      if (declaration.name == "g" && declaration.body) {
        require(declaration.inputs.size() == 3,
                "helper did not gain a capture port");
        for (const auto &op : declaration.body->operations)
          if (op.reduction) {
            require(op.reduction->expressions.size() ==
                        evidence->expressions.size(),
                    "reduction expression coverage changed");
            for (const auto &entry : evidence->expressions) {
              auto expression = entry.first;
              auto value = entry.second;
              auto found = llvm::find_if(
                  op.reduction->expressions,
                  [&](const auto &entry) { return entry.first == expression; });
              require(found != op.reduction->expressions.end() &&
                          found->second.index == value.index,
                      "enclosing capture layout rewrote a nested helper value");
            }
            checked = true;
          }
      }
    require(checked, "missing closed reduction evidence");
  });
  cases.run("generic Math apply and forwarding", [] {
    succeeds(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return(r=forward_math(x,fun y=>y+a));}
run Run=Demo;)");
  });
  cases.run("component nested scoped capture and record projections", [] {
    succeeds(R"(
interface Transform<F:Field>{fn adjust(x:F)->F !{};fn run(x:F,body:scoped fn(F)->F !{stop})->F !{stop};}
component Increment<F:Field>:Transform<F>{
 fn adjust(x:F)->F !{}{return x+1;}
 fn run(x:F,body:scoped fn(F)->F !{stop})->F !{stop}{return forward(x,fun y=>body(adjust(y)));}
}
fn through<F:Field,C:Transform<F>>(x:F,body:scoped fn(F)->F !{stop})->F !{stop}{return C::run(x,body);}
struct Parameters<F:Field>{pub shift:F,pub table:Vector<F>}
protocol Demo roles(P,V)(x:Fr@(P,V),parameters:Parameters<Fr>@P,position:index@P)->(r:Fr@P){
 let result=through<Fr,Increment<Fr>>(x,fun y=>forward(y,fun z=>get(parameters.table,position)+z+parameters.shift));
 return(r=result);
}
run Run=Demo;)");
  });
  cases.run("Local callback has short circuit inside protocol", [] {
    succeeds(R"(
fn fail(x:bool)->bool !{stop}{require x;return x;}
protocol Demo roles(P)(x:bool@P)->(r:bool@P){return(r=apply(x,fun y=>false && fail(y)));}
run Run=Demo;)");
  });
  cases.run("multiple inputs and tuple destructuring", [] {
    succeeds(R"(
fn two(x:Fr,y:Fr,body:scoped fn(Fr,Fr)->Fr !{})->Fr !{}{return body(x,y);}
fn pair(x:(Fr,Fr),body:scoped fn((Fr,Fr))->Fr !{})->Fr !{}{return body(x);}
fn example(x:Fr,y:Fr)->Fr{return two(x,y,fun a b=>a+b)+pair((x,y),fun (a,b)=>a-b);}
protocol Demo roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return(r=example(x,y));}run Run=Demo;)");
  });
  cases.run("affine explicit parameters and mutable callback state", [] {
    succeeds(R"(
struct Token:Drop {}
fn carry(x:Token,n:index)->Token{return forward(x,fun y=>{let mut state=y;for _ in 0..n {let old=state;consume old;state=Token{};}state});}
fn work(n:index)->bool{let value=carry(Token{},n);consume value;return true;}
protocol Demo roles(P)(n:index@P)->(r:bool@P){return work(n);}run Run=Demo;
)");
  });
  cases.run("Math Boolean callback inside protocol formula", [] {
    succeeds(R"(
protocol Demo roles(P,V)(x:bool@(P,V))->(r:bool@(P,V)){return true && apply_math(x,fun y=>y || false);}run Run=Demo;
)");
  });
  cases.run("unused contextual callback and all-stopping callback", [] {
    succeeds(R"(
fn ignore<A:Type+Drop,B:Type+Copy+Drop>(x:A,body:scoped fn(A)->B !{stop},fallback:B)->B !{}{return fallback;}
fn work(x:Fr)->Fr{return ignore(x,fun _=>{stop "reject";},x);}
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return work(x);}run Run=Demo;
)");
  });

  cases.run("abstract Math callback captures survive wrapper summaries", [] {
    const std::string helpers = R"(
interface MathOps<F:Field>{math fn run(x:F,body:scoped math fn(F)->F)->F;}
component Impl<F:Field>:MathOps<F>{math fn run(x:F,body:scoped math fn(F)->F)->F{return body(x);}}
math fn g<F:Field,C:MathOps<F>>(x:F,y:F)->F{return C::run(x,fun t=>t+y);}
math fn h(x:Fr,y:Fr)->Fr{return g<Fr,Impl<Fr>>(x,y);}
)";
    for (const auto &call : {"h(x,y)", "g<Fr,Impl<Fr>>(x,y)"})
      refuses(check(helpers +
                    "protocol Demo "
                    "roles(P,V)(x:Fr@(P,V),y:Fr@P)->(r:Fr@(P,V)){return(r=" +
                    call + ");}run Run=Demo;"),
              "source.roles");
    succeeds(helpers + "protocol Demo "
                       "roles(P,V)(x:Fr@(P,V),y:Fr@P)->(r:Fr@P){return(r=h(x,y)"
                       ");}run Run=Demo;");
  });
  cases.run("callback after whole reassignment does not capture moved input",
            [] {
              succeeds(R"(
struct Token:Drop {}
struct Holder {pub v:Fr,pub t:Token}
fn f(x:Fr,c:bool,h:Holder)->Fr{
 let mut s=h;let old=s;
 return if c {s=Holder{v:x,t:Token{}};apply(x,fun y=>y+s.v)}
 else {s=Holder{v:x,t:Token{}};x};
}
fn run(x:Fr,c:bool)->Fr{return f(x,c,Holder{v:x,t:Token{}});}
protocol Demo roles(P)(x:Fr@P,c:bool@P)->(r:Fr@P){return run(x,c);}run Run=Demo;
)");
            });
  cases.run("always-stopping argument excludes unreachable callback capture",
            [] {
              refuses(check(R"(
fn g(a:Fr,b:Fr)->Fr{return a;}
fn f(x:Fr,a:Fr)->Fr{return apply(x,fun y=>g({stop "reject";},a));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P)->(r:Fr@P){return f(x,a);}run Run=Demo;
)"),
                      "source.unreachable");
            });

  cases.run("formation summaries are sets across wide helper reuse", [] {
    std::string source = "math fn wide(x:Fr)->Fr{";
    for (unsigned i = 0; i < 256; ++i)
      source += "let a" + std::to_string(i) + "=x+x;";
    source += "return x;} math fn middle(x:Fr)->Fr{return wide(x);} math fn "
              "caller(x:Fr)->Fr{";
    for (unsigned i = 0; i < 256; ++i)
      source += "let a" + std::to_string(i) + "=middle(x);";
    source += "return x;}";
    auto captured = take(capture({{"m", prelude + source, "wide.zkc"}}));
    auto project = take(analyze(captured).checkedProject());
    for (const auto &decl : project.declarations())
      if (decl.name == "wide" || decl.name == "middle" || decl.name == "caller")
        require(decl.body->formationRequirements.size() == 1,
                "duplicate formation requirements accumulated");
    Limits limits;
    limits.work = project.checkedWork() - 1;
    refuses(analyze(captured, limits).checkedProject(), "source.limit");
    limits.work = project.checkedWork();
    take(analyze(captured, limits).checkedProject());
  });

  const std::vector<std::pair<std::string, std::string>> refusals = {
      {"fn f(x:Fr,b:scoped fn(Fr)->Fr)->Fr{return x;}", "source.effect"},
      {"fn f(x:Fr,b:scoped math fn(Fr)->Fr !{stop})->Fr{return x;}",
       "source.effect"},
      {"fn f(x:Fr)->Fr{return apply_math(x,fun y=>get(([],),0));}",
       "source.type"},
      {"fn f(x:Fr,b:scoped fn(Fr)->Fr !{})->Fr{return b;}", "source.scoped"},
      {"fn f(x:Fr)->Fr{let b=fun y=>y;return x;}", "source.scoped"},
      {"fn f(x:Fr)->Fr{let mut a=x;return apply(x,fun y=>{a=y;y});}",
       "source.scoped-capture"},
      {"fn unused<A:Type>(x:A,b:scoped fn(A)->A !{})->A{return b(true);}",
       "source.type"},
      {"math fn f(x:Fr,b:scoped fn(Fr)->Fr !{})->Fr{return b(x);}",
       "source.mode"},
      {"fn stop_value(x:Fr)->Fr !{stop}{stop \"reject\";} fn "
       "f(x:Fr)->Fr{return apply_math(x,fun y=>stop_value(y));}",
       "source.mode"},
      {"fn clean(x:Fr,b:scoped fn(Fr)->Fr !{})->Fr !{}{return b(x);} fn "
       "stop_value(x:Fr)->Fr !{stop}{stop \"reject\";} fn f(x:Fr)->Fr{return "
       "clean(x,fun y=>stop_value(y));}",
       "source.effect"},
      {"fn f(x:Fr,b:scoped fn(Fr)->Fr !{})->Fr{return apply_math(x,b);}",
       "source.scoped"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@(P,V),a:Fr@P,b:Fr@V)->(r:Fr@P){return(r=apply(x,fun "
       "y=>y+a+b));}run Run=Demo;",
       "source.roles"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@(P,V))->(r:Fr@(P,V)){return(r=apply(x,fun y=>y));}run "
       "Run=Demo;",
       "source.roles"},
      {"fn identity(x:Fr)->Fr{return x;} protocol Demo "
       "roles(P,V)(x:Fr@(P,V))->(r:Fr@P){return(r=apply_math(identity(x),fun "
       "_=>0));}run Run=Demo;",
       "source.owner"},
      {"protocol Demo "
       "roles(P,V)(x:Fr@P,a:Fr@P,b:Fr@V)->(r:Fr@P){return(r=apply_math(x,fun "
       "_=>{let dead=a+b;0}));}run Run=Demo;",
       "source.roles"},
      {"fn f(x:Fr)->Fr{return apply(x,fun (a,b)=>a+b);}", "source.type"},
      {"fn f(x:Fr)->Fr{return apply(x,fun a b=>a+b);}", "source.scoped"},
      {"fn f(x:Fr)->Fr{return apply(x,fun y=>f(y));}", "source.cycle"},
      {"struct Token:Drop {} fn f(x:Fr,t:Token)->Fr{return apply(x,fun "
       "y=>{consume t;y});}",
       "source.scoped-capture"},
      {"struct Token:Copy {} fn f(x:Fr,t:Token)->Fr{return apply(x,fun "
       "y=>{consume t;y});}",
       "source.scoped-capture"},
      {"struct Token:Drop {} fn f(t:Token)->(Token,Token){return apply(t,fun "
       "y=>(y,y));}",
       "source.move"},
      {"protocol Demo roles(P)(x:Fr@P,coins:Random<Fr>@P)->(r:Fr@P){return "
       "apply(x,fun y=>y+coins.draw());}run Run=Demo;",
       "source.scoped-capture"},
      {"interface I{fn f(x:Fr,b:scoped fn(Fr)->Fr !{})->Fr !{};}component "
       "C:I{fn f(x:Fr,b:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{return b(x);}}",
       "source.conformance"},
      {"fn unused<A:Type+Copy+Drop>(x:A)->A{return apply_math(x,fun y=>{let "
       "bad:bool=y;y});}",
       "source.type"},
  };
  for (unsigned i = 0; i < refusals.size(); ++i)
    cases.run("scoped refusal " + std::to_string(i),
              [&] { refuses(check(refusals[i].first), refusals[i].second); });
  cases.run("scoped expansion respects closed instance and depth bounds", [] {
    auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P)->(r:Fr@P){return forward(x,fun y=>forward(y,fun z=>z+x));}run Run=Demo;
)"));
    Limits limits;
    limits.instances = 2;
    refuses(closeEntry(project, "m::Run", limits), "source.limit");
    limits = Limits{};
    limits.callDepth = 2;
    refuses(closeEntry(project, "m::Run", limits), "source.limit");
    limits = Limits{};
    limits.work = 1;
    auto error = checkScopedElaboration(project, limits);
    require(bool(error), "capture witness ignored lowered work bound");
    require(toString(std::move(error)).find("source.limit") !=
                std::string::npos,
            "wrong witness budget refusal");
  });
  cases.run("declaration inspection separates scoped and runtime inputs", [] {
    auto project = take(check("pub fn export_body(x:Fr,body:scoped fn(Fr)->Fr "
                              "!{stop})->Fr !{stop}{return body(x);}"));
    auto json = take(inspectDeclarations(project));
    require(StringRef(json).contains("\"scoped_inputs\"") &&
                StringRef(json).contains("\"scoped\"") &&
                StringRef(json).contains("\"stop\""),
            "scoped inspection contract missing");
  });
  cases.run("forwarded scoped selection mutation is rejected", [] {
    auto project = take(check(R"(
fn chain(x:Fr,first:scoped fn(Fr)->Fr !{stop},second:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{return second(first(x));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return chain(x,fun y=>y+a,fun y=>y*b);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool changed = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.name == "chain") {
        auto &candidate = const_cast<Declaration &>(decl);
        std::swap(candidate.scopedArguments[0], candidate.scopedArguments[1]);
        changed = true;
      }
    require(changed, "missing selected chain");
    auto error = checkScopedSpecialization(closed);
    require(bool(error), "swapped static callback targets accepted");
    require(toString(std::move(error)).find("source.scoped-specialization") !=
                std::string::npos,
            "wrong static target refusal");
  });
  const std::string captured = R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return(r=forward(x,fun y=>{let dead=a+b;y+a-b}));}
run Run=Demo;)";
  for (bool specialized : {false, true})
    for (unsigned mutation = 0; mutation < 4; ++mutation)
      cases.run(
          std::string(specialized ? "specialized" : "authored") +
              " scoped call mapping mutation " + std::to_string(mutation),
          [&] {
            auto project = take(check(R"(
fn chain(x:Fr,first:scoped fn(Fr)->Fr !{stop},second:scoped fn(Fr)->Fr !{stop})->Fr !{stop}{return second(first(x));}
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return chain(second=fun y=>y*b,x=x,first=fun y=>y+a);}run Run=Demo;
)"));
            auto closed = take(closeEntry(project, "m::Run"));
            auto declarations =
                specialized ? closed.declarations() : project.declarations();
            bool changed = false;
            for (const auto &decl : declarations)
              if (decl.name == "Demo" && decl.body) {
                auto body = std::make_shared<Body>(*decl.body);
                const_cast<Declaration &>(decl).body = body;
                for (auto &operation : body->operations)
                  if (operation.binding && operation.binding->scopedSource) {
                    auto &binding = *operation.binding;
                    if (mutation == 0)
                      binding.scopedSource.reset();
                    if (mutation == 1)
                      std::swap(binding.argumentOrder[0],
                                binding.argumentOrder[1]);
                    if (mutation == 2)
                      std::swap(binding.scopedArguments[0],
                                binding.scopedArguments[1]);
                    if (mutation == 3) {
                      std::swap(binding.scopedArguments[0],
                                binding.scopedArguments[1]);
                      if (!specialized) {
                        auto &call = std::get<HelperCall>(operation.action);
                        std::swap(call.scopedArguments[0],
                                  call.scopedArguments[1]);
                      }
                      // Specialization has erased static arguments;
                      // preserved source evidence must still agree.
                    }
                    changed = true;
                    break;
                  }
              }
            require(changed, "missing scoped call mapping evidence");
            auto error = specialized ? checkScopedSpecialization(closed)
                                     : checkScopedElaboration(project);
            require(bool(error), "corrupted scoped call mapping accepted");
            require(toString(std::move(error))
                            .find(specialized ? "source.scoped-specialization"
                                              : "source.scoped-witness") !=
                        std::string::npos,
                    "wrong scoped call mapping refusal");
          });
  cases.run("authored witness checks capture operands inside callback", [&] {
    auto project = take(check(captured));
    for (const auto &decl : project.declarations()) {
      if (decl.name != "Demo")
        continue;
      auto body = std::make_shared<Body>(*decl.body);
      const_cast<Declaration &>(decl).body = body;
      auto &binding = body->scopedBindings.front();
      auto computation =
          std::make_shared<ScopedComputation>(*binding.computation);
      auto nested = std::make_shared<Body>(*computation->body);
      binding.computation = computation;
      computation->body = nested;
      auto swap = [](ValueId &v) {
        if (v.index == 1)
          v.index = 2;
        else if (v.index == 2)
          v.index = 1;
      };
      for (auto &op : nested->operations) {
        std::visit(
            [&](auto &action) {
              using T = std::decay_t<decltype(action)>;
              if constexpr (std::is_same_v<T, MathValue> ||
                            std::is_same_v<T, HelperCall> ||
                            std::is_same_v<T, LocalPrimitive>)
                for (auto &v : action.operands)
                  swap(v);
            },
            op.action);
        if (op.binding)
          for (auto &v : op.binding->operands)
            swap(v);
      }
    }
    auto error = checkScopedElaboration(project);
    require(bool(error), "callback capture use mutation accepted");
    require(toString(std::move(error)).find("source.scoped-witness") !=
                std::string::npos,
            "wrong capture use refusal");
  });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run(
        "capture occurrence correspondence mutation " +
            std::to_string(mutation),
        [&, mutation] {
          auto project = take(check(R"(
protocol Demo roles(P)(x:Fr@P,a:Fr@P,b:Fr@P)->(r:Fr@P){return forward(x,fun y=>{let t=a;y+t-b});}run Run=Demo;
)"));
          bool changed = false;
          for (const auto &decl : project.declarations())
            if (decl.name == "Demo") {
              auto outer = std::make_shared<Body>(*decl.body);
              const_cast<Declaration &>(decl).body = outer;
              auto &binding = outer->scopedBindings.front();
              auto computation =
                  std::make_shared<ScopedComputation>(*binding.computation);
              auto body = std::make_shared<Body>(*computation->body);
              binding.computation = computation;
              computation->body = body;
              if (mutation < 2) {
                for (auto it = body->expressionValues.begin();
                     it != body->expressionValues.end(); ++it)
                  if (it->second.index == 1) {
                    if (mutation == 0)
                      it->second.index = 2;
                    else
                      body->expressionValues.erase(it);
                    changed = true;
                    break;
                  }
              } else {
                for (auto &op : body->operations)
                  if (auto *projection = std::get_if<Projection>(&op.action))
                    if (projection->input.index == 1) {
                      projection->input.index = 2;
                      if (mutation == 3)
                        for (auto &[id, value] : body->expressionValues)
                          if (value.index == 1)
                            value.index = 2;
                      changed = true;
                      break;
                    }
              }
            }
          require(changed, "mutation did not reach a capture read");
          auto error = checkScopedElaboration(project);
          require(bool(error), "corrupted capture occurrence accepted");
          require(toString(std::move(error)).find("source.scoped-witness") !=
                      std::string::npos,
                  "wrong occurrence refusal");
        });
  for (unsigned mutation = 0; mutation < 7; ++mutation)
    cases.run("capture witness mutation " + std::to_string(mutation), [&] {
      auto project = take(check(captured));
      Declaration *declaration = nullptr;
      for (const auto &decl : project.declarations())
        if (decl.name == "Demo")
          declaration = &const_cast<Declaration &>(decl);
      auto body = std::make_shared<Body>(*declaration->body);
      declaration->body = body;
      auto &binding = body->scopedBindings.front();
      auto computation =
          std::make_shared<ScopedComputation>(*binding.computation);
      binding.computation = computation;
      if (mutation == 0)
        std::swap(binding.captures[0], binding.captures[1]);
      if (mutation == 1)
        std::swap(computation->captures[0].binding,
                  computation->captures[1].binding);
      if (mutation == 2)
        computation->captures[0].path.push_back(0);
      if (mutation == 3)
        computation->signature.allowance.mayStop = false;
      if (mutation == 4)
        binding.source.reset();
      if (mutation == 5)
        body->scopedBindings.push_back(binding);
      if (mutation == 6)
        body->scopedBindings.clear();
      auto error = checkScopedElaboration(project);
      require(bool(error), "corrupted capture witness accepted");
      require(toString(std::move(error)).find("source.scoped-witness") !=
                  std::string::npos,
              "wrong capture refusal");
    });
  for (unsigned mutation = 0; mutation < 7; ++mutation)
    cases.run(
        "specialization mapping mutation " + std::to_string(mutation), [&] {
          auto project = take(check(captured));
          auto closed = take(closeEntry(project, "m::Run"));
          Declaration *selected = nullptr;
          for (const auto &decl : closed.declarations())
            if (decl.body &&
                (mutation == 0 || mutation == 5
                     ? decl.kind == Declaration::Kind::Protocol
                 : mutation == 1 ? decl.name == "forward"
                                 : decl.scopedOrigin.has_value())) {
              selected = &const_cast<Declaration &>(decl);
              break;
            }
          require(selected != nullptr, "missing candidate");
          auto body = std::make_shared<Body>(*selected->body);
          selected->body = body;
          if (mutation == 0 || mutation == 1) {
            for (auto &op : body->operations)
              if (auto *call = std::get_if<HelperCall>(&op.action)) {
                if (call->operands.size() >= 3) {
                  std::swap(call->operands[1], call->operands[2]);
                  break;
                }
              }
          }
          if (mutation == 2)
            body->operations.erase(body->operations.begin());
          if (mutation == 3)
            selected->scopedOrigin->second += 1;
          if (mutation == 4)
            selected->inputs.back().type = Type{};
          if (mutation == 5)
            for (auto &op : body->operations)
              if (auto *call = std::get_if<HelperCall>(&op.action))
                call->owner = 99;
          if (mutation == 6)
            body->operations.push_back(body->operations.front());
          auto error = checkScopedSpecialization(closed);
          require(bool(error), "corrupted specialization accepted");
          require(
              toString(std::move(error)).find("source.scoped-specialization") !=
                  std::string::npos,
              "wrong specialization refusal");
        });
  return cases.result();
}
