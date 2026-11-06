#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/DeclarationIndex.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Names.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(std::vector<SourceBuffer> sources,
                               StringRef format = "zkc-layout") {
  CaptureOptions options;
  options.format = format.str();
  auto captured = capture(std::move(sources), options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<CheckedProject> check(StringRef code,
                               StringRef format = "zkc-layout") {
  return check({{"m", code.str(), "methods.zkc"}}, format);
}
const Declaration &named(ArrayRef<Declaration> declarations, StringRef name) {
  auto found = llvm::find_if(declarations, [&](const auto &decl) {
    return decl.qualifiedName == name;
  });
  require(found != declarations.end(), "missing declaration: " + name);
  return *found;
}
const char *home = R"(pub struct Box<T: Type + Copy + Drop>:
    pub payload: T
type Receiver<T: Type + Copy + Drop> = Box<T>
pub def merge<T: Type + Copy + Drop>(self: Receiver<T>, other: T) -> T:
    other
pub def choose<T: Type + Copy + Drop>(self: Box<T>, left: T, right: T) -> T:
    left
def hidden(self: Box<bool>) -> bool:
    self.payload
pub local def ordered(self: Box<bool>) -> bool effects(stop):
    guard self.payload
    return self.payload
)";
const char *logical = R"(module m;
domain F=field("bls12-381.fr");
type O=builtin("oracle",builtin("oracle.table",F,16));
#[logical] struct State{pub word:O}
)";
} // namespace
int main() {
  Cases cases;
  cases.run("qualified method and notation retain canonical alias binding", [] {
    auto project = take(check(
        {{"home", home, "home.zkc"},
         {"facade", R"(pub type Alias<T: Type + Copy + Drop> = home::Box<T>
)",
          "facade.zkc"},
         {"m", R"(use facade::{Alias}
notation infixl(60) self ⊙ other = home::merge(self,other)
pub protocol Demo roles(P)(item: Alias<bool> @P) -> bool @P:
    qualified = home::merge<T = bool>(item, other = true)
    method = item.merge<T = bool>(other = true)
    notation = item ⊙ true
    named = item.choose(right = false, left = true)
    return qualified and method and notation and named
)",
          "main.zkc"}}));
    const auto &body = *named(project.declarations(), "m::Demo").body;
    const auto target = named(project.declarations(), "home::merge").id.index;
    unsigned calls = 0;
    for (const auto &op : body.operations)
      if (const auto *call = std::get_if<HelperCall>(&op.action);
          call && call->callee.index == target) {
        ++calls;
        require(op.binding && op.binding->target.declaration.index == target &&
                    op.binding->arguments == std::vector<Type>{Type{}} &&
                    call->operands.size() == 2 && call->operands[0].index == 0,
                "invocation route changed target, statics or receiver binding");
      }
    require(calls == 3,
            "qualified, method and notation did not share a target");
    auto written = take(inspectWrittenSource(project));
    require(StringRef(written).contains("expr.method_call"),
            "method spelling disappeared from written source");
    auto entry = take(closeNativeRun(project, "m::Demo"));
    auto original = take(prepareOriginal(entry));
    take(compileEntry(original));
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto bytes = take(emitOriginal(entry, context));
    auto candidate = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(candidate), "method original did not parse");
    take(compareOriginal(entry, *candidate));
    bool changed = false;
    candidate->walk([&](mlir::Operation *op) {
      if (changed || op->getName().getStringRef() != "func.call" ||
          op->getNumOperands() != 2 ||
          op->getOperand(0).getType() != op->getOperand(1).getType() ||
          op->getOperand(0) == op->getOperand(1))
        return;
      auto receiver = op->getOperand(0);
      op->setOperand(0, op->getOperand(1));
      op->setOperand(1, receiver);
      changed = true;
    });
    require(changed, "no comparable receiver/argument operands");
    refuses(compareOriginal(entry, *candidate), "source.correspondence");
  });
  for (bool imported : {false, true})
    cases.run(
        imported ? "foreign imports cannot add or replace methods"
                 : "home methods need no callable import",
        [&] {
          const std::string imports = imported ? "use foreign as extra\n" : "";
          auto project = take(check(
              {{"home", home, "home.zkc"},
               {"foreign",
                R"(pub def merge(self: home::Box<bool>, other: bool) -> bool:
    self.payload
pub def extension(self: home::Box<bool>) -> bool:
    self.payload
)",
                "foreign.zkc"},
               {"m", imports + R"(use home::{Box}
pub protocol Demo roles(P)(item: Box<bool> @P) -> bool @P:
    return item.merge(true)
)",
                "main.zkc"}}));
          const auto &body = *named(project.declarations(), "m::Demo").body;
          auto call = llvm::find_if(body.operations, [](const auto &op) {
            return std::holds_alternative<HelperCall>(op.action);
          });
          require(call != body.operations.end() &&
                      std::get<HelperCall>(call->action).callee.index ==
                          named(project.declarations(), "home::merge").id.index,
                  "import changed selected home");
          refuses(check({{"home", home, "home.zkc"},
                         {"foreign",
                          R"(pub def extension(self: home::Box<bool>) -> bool:
    self.payload
)",
                          "foreign.zkc"},
                         {"m", imports + R"(use home::{Box}
pub protocol Demo roles(P)(item: Box<bool> @P) -> bool @P:
    return item.extension()
)",
                          "main.zkc"}}),
                  "source.method");
        });
  cases.run("private home methods refuse outside their authority", [] {
    refuses(
        check(
            {{"home", home, "home.zkc"},
             {"m",
              R"(pub protocol Demo roles(P)(item: home::Box<bool> @P) -> bool @P:
    return item.hidden()
)",
              "main.zkc"}}),
        "source.private");
  });
  for (bool reverse : {false, true})
    cases.run("reexported foreign functions do not extend the type home", [&] {
      std::vector<SourceBuffer> sources{
          {"home", R"(pub struct Box:
    pub payload: bool
pub use foreign::{extension}
)",
           "home.zkc"},
          {"foreign", R"(pub def extension(self: home::Box) -> bool:
    self.payload
)",
           "foreign.zkc"},
          {"m", R"(pub protocol Demo roles(P)(item: home::Box @P) -> bool @P:
    return item.extension()
)",
           "main.zkc"}};
      if (reverse)
        std::reverse(sources.begin(), sources.end());
      refuses(check(std::move(sources)), "source.method");
    });
  cases.run("private home methods remain available inside their authority", [] {
    auto project = take(check(std::string(home) + R"(
pub protocol Demo roles(P)(item: Box<bool> @P) -> bool @P:
    return item.hidden()
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run(
      "layout protocol method derives roles without equal role names", [] {
        auto project = take(check(R"(struct Box:
    pub payload: bool
protocol relay roles(A)(self: Box @A) -> Box @A:
    return self
pub protocol Demo roles(P)(item: Box @P) -> Box @P:
    result <- item.relay()
    return result
)"));
        const auto &body = *named(project.declarations(), "m::Demo").body;
        auto call = llvm::find_if(body.operations, [](const auto &op) {
          return std::holds_alternative<ProtocolApplication>(op.action);
        });
        require(
            call != body.operations.end() &&
                std::get<ProtocolApplication>(call->action).roles ==
                    std::vector<unsigned>{0},
            "method used role spelling instead of exact receiver placement");
        take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
      });
  cases.run("distributed method retains the nominal telescope permutation", [] {
    auto project = take(check(R"(struct Pair roles(A, B):
    pub first: index @A
    pub second: index @B
type Reversed roles(A, B) = Pair roles(B, A)
protocol observe roles(Y, X)(self: Reversed roles(Y, X)) -> index @X:
    return self.first
pub protocol Demo roles(P, V)() -> index @P:
    item = Pair roles(P, V) {first: 7, second: 9}
    result <- item.observe()
    return result
)"));
    const auto &body = *named(project.declarations(), "m::Demo").body;
    auto call = llvm::find_if(body.operations, [](const auto &op) {
      return std::holds_alternative<ProtocolApplication>(op.action);
    });
    require(call != body.operations.end() &&
                std::get<ProtocolApplication>(call->action).roles ==
                    std::vector<unsigned>({1, 0}),
            "nominal receiver map was replaced by its availability union");
    auto entry = take(closeNativeRun(project, "m::Demo"));
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto bytes = take(emitOriginal(entry, context));
    auto candidate = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(candidate), "distributed method original did not parse");
    take(compareOriginal(entry, *candidate));
  });
  cases.run("empty nominal receiver preserves roles with no native leaves", [] {
    auto project = take(check(R"(struct Empty roles(A, B):
protocol observe roles(Y, X)(self: Empty roles(X, Y)) -> bool @Y:
    return true
pub protocol Demo roles(P, V)() -> bool @V:
    item = Empty roles(P, V) {}
    result <- item.observe()
    return result
)"));
    const auto &body = *named(project.declarations(), "m::Demo").body;
    auto call = llvm::find_if(body.operations, [](const auto &op) {
      return std::holds_alternative<ProtocolApplication>(op.action);
    });
    require(call != body.operations.end() &&
                std::get<ProtocolApplication>(call->action).roles ==
                    std::vector<unsigned>({1, 0}),
            "empty receiver lost its nominal role correspondence");
  });
  cases.run("receiver cannot invent an uncovered protocol role", [] {
    refuses(check(R"(struct Empty roles(A, B):
protocol observe roles(X, Y, Z)(self: Empty roles(X, Y)) -> bool @Z:
    return true
pub protocol Demo roles(P, V, Q)() -> bool @Q:
    item = Empty roles(P, V) {}
    result <- item.observe()
    return result
)"),
            "source.roles");
  });
  for (bool privateField : {false, true})
    cases.run(
        privateField ? "private fields cannot fall through to methods"
                     : "public fields cannot fall through to methods",
        [&] {
          const std::string field =
              privateField ? "    merge: bool\n" : "    pub merge: bool\n";
          refuses(
              check(
                  {{"home",
                    "pub struct Box:\n" + field +
                        R"(pub def merge(self: Box) -> bool:
    true
)",
                    "home.zkc"},
                   {"m",
                    R"(pub protocol Demo roles(P)(item: home::Box @P) -> bool @P:
    return item.merge()
)",
                    "main.zkc"}}),
              privateField ? "source.private" : "source.method");
        });
  for (StringRef expression :
       {"item.choose(self = item, left = true)",
        "item.choose(left = true, left = false)",
        "item.choose(unknown = true, right = false)",
        "item.choose(right = true, false)", "item.choose(true)"})
    cases.run("method uses normal named binding refusal: " + expression, [&] {
      refuses(check({{"home", home, "home.zkc"},
                     {"m",
                      ("pub protocol Demo roles(P)(item: home::Box<bool> @P) "
                       "-> bool @P:\n    return " +
                       expression + "\n")
                          .str(),
                      "main.zkc"}}),
              "source.call");
    });
  for (bool ordered : {false, true})
    cases.run(
        ordered ? "ordered method requires an action binding"
                : "pure method refuses an action binding",
        [&] {
          const auto expression =
              ordered ? "item.ordered()" : "item.merge(true)";
          refuses(check({{"home", home, "home.zkc"},
                         {"m",
                          std::string(
                              "pub protocol Demo roles(P)(item: "
                              "home::Box<bool> @P) -> bool @P:\n    result ") +
                              (ordered ? "= " : "<- ") + expression +
                              "\n    return result\n",
                          "main.zkc"}}),
                  "source.action");
        });
  cases.run("ordered method retains effects and native body comparison", [] {
    auto project = take(check(
        {{"home", home, "home.zkc"},
         {"m",
          R"(pub protocol Demo roles(P)(item: home::Box<bool> @P) -> bool @P:
    result <- item.ordered()
    return result
)",
          "main.zkc"}}));
    require(
        named(project.declarations(), "m::Demo").body->effects.fixed.mayStop,
        "resolved method effects disappeared");
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("method effects obey the selected callable ceiling", [] {
    refuses(
        check({{"home", home, "home.zkc"},
               {"m", R"(local def run(item: home::Box<bool>) -> bool effects():
    value <- item.ordered()
    return value
)",
                "main.zkc"}}),
        "source.effect");
  });
  cases.run("method result annotations infer otherwise absent statics", [] {
    auto project = take(check(R"(struct Box:
    pub payload: bool
def empty<T: Type + Copy + Drop>(self: Box) -> [T, 0]:
    []
pub protocol Demo roles(P)(item: Box @P) -> [bool, 0] @P:
    value: [bool, 0] = item.empty()
    return value
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("notation receivers use ordinary structural inference", [] {
    auto project = take(check(R"(struct Box:
    pub payload: bool
def same(self: Box) -> Box:
    self
def merge(self: Box, other: bool) -> bool:
    other
notation ⟦item⟧ = same(item)
pub protocol Demo roles(P)(item: Box @P) -> bool @P:
    return ⟦item⟧.merge(true)
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("method assignments retain expected static inference", [] {
    auto project = take(check(R"(struct Box:
    pub payload: bool
def empty<T: Type + Copy + Drop>(self: Box) -> [T, 0]:
    []
pub protocol Demo roles(P)(item: Box @P) -> [bool, 0] @P:
    mut value: [bool, 0] = []
    value := item.empty()
    return value
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("method eligibility does not select among duplicate names", [] {
    refuses(check(R"(struct Box:
    pub payload: bool
struct Other:
    pub payload: bool
def merge(self: Box) -> bool:
    true
def merge(self: Other) -> bool:
    false
)"),
            "source.duplicate");
  });
  for (StringRef invocation : {"item.relay()", "relay(item)"})
    cases.run("unbound ordered invocation requires an action: " + invocation,
              [&] {
                refuses(check((R"(struct Box:
    pub payload: bool
protocol relay roles(P)(self: Box @P) -> Box @P:
    return self
pub protocol Demo roles(P)(item: Box @P) -> Box @P:
    )" + invocation + "\n    return item\n")
                                  .str()),
                        "source.action");
              });
  cases.run("receiver and named operands evaluate once in authored order", [] {
    auto project = take(check(R"(module m;
struct Box{pub payload:bool}
fn receiver(x:Box)->Box effects(stop){require x.payload;return x;}
fn markLeft(x:bool)->bool effects(stop){require x;return x;}
fn markRight(x:bool)->bool effects(stop){require x;return x;}
fn choose(self:Box,left:bool,right:bool)->bool effects(){return left;}
fn run(x:Box,a:bool,b:bool)->bool effects(stop){
  return receiver(x).choose(right=markRight(b),left=markLeft(a));
}
protocol Demo roles(P)(x:Box@P,a:bool@P,b:bool@P)->(r:bool@P){return run(x,a,b);}
)",
                              "zkc"));
    const auto &body = *named(project.declarations(), "m::run").body;
    std::vector<std::string> order;
    std::vector<ValueId> values;
    const HelperCall *selected = nullptr;
    for (const auto &op : body.operations)
      if (const auto *call = std::get_if<HelperCall>(&op.action)) {
        order.push_back(project.declarations()[call->callee.index].name);
        if (order.back() == "choose")
          selected = call;
        else
          values.push_back(op.results.front());
      }
    require(order == std::vector<std::string>(
                         {"receiver", "markRight", "markLeft", "choose"}),
            "receiver duplicated or operand evaluation order changed");
    require(selected && selected->operands[0].index == values[0].index &&
                selected->operands[1].index == values[2].index &&
                selected->operands[2].index == values[1].index,
            "named operands were not bound in formal order");
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("protocol receiver and named operands retain authored order", [] {
    auto project = take(check(R"(module m;
struct Box{pub payload:bool}
fn receiver(x:Box)->Box effects(stop){require x.payload;return x;}
fn markLeft(x:bool)->bool effects(stop){require x;return x;}
fn markRight(x:bool)->bool effects(stop){require x;return x;}
protocol choose roles(A)(self:Box@A,left:bool@A,right:bool@A)->(r:bool@A){return left;}
protocol Demo roles(P)(x:Box@P,a:bool@P,b:bool@P)->(r:bool@P){
  let result=receiver(x).choose(right=markRight(b),left=markLeft(a));return result;
}
)",
                              "zkc"));
    const auto &body = *named(project.declarations(), "m::Demo").body;
    std::vector<std::string> order;
    std::vector<ValueId> values;
    const ProtocolApplication *selected = nullptr;
    for (const auto &op : body.operations) {
      if (const auto *call = std::get_if<HelperCall>(&op.action)) {
        order.push_back(project.declarations()[call->callee.index].name);
        values.push_back(op.results.front());
      } else if (const auto *call =
                     std::get_if<ProtocolApplication>(&op.action)) {
        order.push_back(project.declarations()[call->callee.index].name);
        selected = call;
      }
    }
    require(order == std::vector<std::string>(
                         {"receiver", "markRight", "markLeft", "choose"}),
            "protocol receiver duplicated or authored operands reordered");
    require(selected && selected->operands[0].index == values[0].index &&
                selected->operands[1].index == values[2].index &&
                selected->operands[2].index == values[1].index,
            "protocol method operands lost formal binding order");
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("well-formed native receiver relocation loses correspondence", [] {
    auto project = take(check(R"(struct Box:
    pub payload: bool
protocol observe roles(A)(self: Box @A) -> bool @A:
    return self.payload
pub protocol Demo roles(P, V)() -> bool @P:
    item: Box @P = Box{payload = true}
    ignored <- item.observe()
    return true
)"));
    auto entry = take(closeNativeRun(project, "m::Demo"));
    mlir::DialectRegistry registry;
    zkc::registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto bytes = take(emitOriginal(entry, context));
    auto candidate = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(candidate), "method role fixture did not parse");
    take(compareOriginal(entry, *candidate));
    unsigned changed = 0;
    candidate->walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() != "protocol.apply")
        return;
      auto *restriction = op->getOperand(0).getDefiningOp();
      require(restriction && restriction->getName().getStringRef() ==
                                 "protocol.restrict_roles",
              "expected an explicitly placed receiver");
      op->setOperand(0, restriction->getOperand(0));
      op->setAttr(
          "roles",
          mlir::ArrayAttr::get(
              &context, {mlir::StringAttr::get(&context, nativeRoleName(1))}));
      ++changed;
    });
    require(changed == 1, "expected one protocol method application");
    // The unrestrained constant admits both placements. Removing the explicit
    // receiver restriction and relocating the unused call remains well formed;
    // stage formation alone cannot detect this changed source action.
    refuses(compareOriginal(entry, *candidate), "source.correspondence");
  });
  for (bool swapReceiver : {false, true})
    cases.run(
        swapReceiver ? "scoped method refuses a same-typed receiver swap"
                     : "scoped method refuses changed authored mapping",
        [&] {
          auto project = take(check(R"(module m;
struct Box{pub payload:bool}
math fn apply(self:Box,other:Box,body:math fn(bool)->bool)->bool{return body(self.payload);}
math fn run(x:Box,other:Box)->bool{return x.apply(other,fn(y)=>y);}
protocol Demo roles(P)(x:Box@P,y:Box@P)->(r:bool@P){return run(x,y);}
)",
                                    "zkc"));
          if (auto error = checkScopedElaboration(project))
            throw std::runtime_error(toString(std::move(error)));
          take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
          auto body = std::make_shared<Body>(
              *named(project.declarations(), "m::run").body);
          bool changed = false;
          for (auto &op : body->operations)
            if (op.binding && op.binding->scopedSource) {
              if (swapReceiver) {
                auto &call = std::get<HelperCall>(op.action);
                std::swap(call.operands[0], call.operands[1]);
                op.binding->operands = call.operands;
              } else
                std::swap(op.binding->argumentOrder[0],
                          op.binding->argumentOrder[1]);
              changed = true;
            }
          require(changed, "missing method scoped witness");
          const_cast<Declaration &>(named(project.declarations(), "m::run"))
              .body = body;
          auto error = checkScopedElaboration(project);
          require(bool(error) && namesIdentifier(toString(std::move(error)),
                                                 "source.scoped-witness"),
                  "independent scoped check accepted a changed method binding");
        });
  cases.run("protocol method derives remapped roles from exact receiver", [] {
    auto project = take(check(std::string(logical) + R"(
protocol forward roles(B,A)(self:State@A->B)->(out:State@A->B){return self;}
protocol Demo roles(P,V)(x:State@P->V)->(out:State@P->V){
  let a=forward roles(V,P)(x);let b=a.forward();return b;
}
)",
                              "zkc"));
    const auto &body = *named(project.declarations(), "m::Demo").body;
    unsigned calls = 0;
    for (const auto &op : body.operations)
      if (const auto *call = std::get_if<ProtocolApplication>(&op.action)) {
        require(call->roles == std::vector<unsigned>({1, 0}),
                "method invented role substitution");
        ++calls;
      }
    require(calls == 2, "qualified and method applications differed");
    take(prepareOriginal(take(closeSubject(project, "m::Demo"))));
  });
  for (StringRef fixture : {"ambiguous", "missing", "incorrect"})
    cases.run("protocol method refuses " + fixture + " receiver mapping", [&] {
      std::string source = logical;
      if (fixture == "ambiguous")
        source +=
            R"(protocol forward roles(A,B,C)(self:State@A->(B,C))->(out:State@A->(B,C)){return self;}
protocol Demo roles(P,V,W)(x:State@P->(V,W))->(out:State@P->(V,W)){let y=x.forward();return y;})";
      else if (fixture == "missing")
        source +=
            R"(protocol forward roles(A,B,C)(self:State@A->B)->(out:State@A->B){return self;}
protocol Demo roles(P,V,W)(x:State@P->V)->(out:State@P->V){let y=x.forward();return y;})";
      else
        source +=
            R"(protocol forward roles(A,B)(self:State@A->B,other:State@B->A)->(out:State@A->B){return self;}
protocol Demo roles(P,V)(x:State@P->V,other:State@P->V)->(out:State@P->V){let y=x.forward(other);return y;})";
      refuses(check(source, "zkc"),
              fixture == "incorrect" ? "source.oracle-role" : "source.roles");
    });
  cases.run(
      "catalog builtin home retains aliases and refuses foreign extensions",
      [] {
        auto project = take(check(
            {{"zkc::vector", R"(module zkc::vector;
domain F=field("bls12-381.fr");
pub type Vector=builtin("vector",F);
pub fn length(values:Vector)->index{return index<0>();}
pub fn wrong(first:bool,values:Vector)->bool{return first;}
)",
              "vector.zkc"},
             {"foreign",
              R"(module foreign;pub fn extra(values:zkc::vector::Vector)->bool{return true;})",
              "foreign.zkc"},
             {"m",
              R"(module m;use foreign as extra;type Alias=zkc::vector::Vector;
fn run(values:Alias)->index{return values.length();}
)",
              "main.zkc"}},
            "zkc"));
        const auto &run = named(project.declarations(), "m::run");
        auto home = project.declarationIndex().home(run.inputs.front().type);
        require(home &&
                    home->index ==
                        named(project.declarations(), "zkc::vector").id.index,
                "builtin alias lost its catalog constructor home");
        const auto &body = *run.body;
        auto call = llvm::find_if(body.operations, [](const auto &op) {
          return std::holds_alternative<HelperCall>(op.action);
        });
        require(call != body.operations.end() && call->binding &&
                    call->binding->target.declaration.index ==
                        named(project.declarations(), "zkc::vector::length")
                            .id.index,
                "builtin method did not select its canonical home");
        for (StringRef method : {"extra()", "wrong(true)"})
          refuses(
              check(
                  {{"zkc::vector",
                    R"(module zkc::vector;domain F=field("bls12-381.fr");pub type Vector=builtin("vector",F);pub fn wrong(first:bool,values:Vector)->bool{return first;})",
                    "vector.zkc"},
                   {"foreign",
                    R"(module foreign;pub fn extra(values:zkc::vector::Vector)->bool{return true;})",
                    "foreign.zkc"},
                   {"m",
                    "module m;use foreign::{extra};fn "
                    "run(values:zkc::vector::Vector)->bool{return values." +
                        method.str() + ";}",
                    "main.zkc"}},
                  "zkc"),
              "source.method");
      });
  cases.run(
      "direct logical constructors use catalog homes without type-name "
      "authority",
      [] {
        auto project = take(check(
            {{"zkc::oracles",
              R"(module zkc::oracles;domain F=field("bls12-381.fr");type O=builtin("oracle",builtin("oracle.table",F,4));pub protocol forward roles(H,R)(word:O@H->R)->(out:O@H->R){return word;})",
              "oracles.zkc"},
             {"m",
              R"(module m;domain F=field("bls12-381.fr");type O=builtin("oracle",builtin("oracle.table",F,4));#[logical] struct Wrapper{pub word:O}protocol Read roles(P,V)(word:O@P->V)->(out:O@P->V){let next@(P,V)=word.forward();return next;})",
              "main.zkc"}},
            "zkc"));
        const auto &read = named(project.declarations(), "m::Read");
        auto home = project.declarationIndex().home(read.inputs.front().type);
        require(home &&
                    home->index ==
                        named(project.declarations(), "zkc::oracles").id.index,
                "direct Oracle failed catalog home lookup");
        Type spoof(Type::Kind::Record, "oracle");
        require(!project.declarationIndex().home(spoof),
                "type-name text acquired a builtin home");
      });
  cases.run(
      "catalog-listed builtin forwarding requires a public canonical export",
      [] {
        const std::string primitives = R"(module zkc::primitives::vector;
pub type Vector<F:Field>=builtin("vector",F);
pub fn length<F:Field>(values:Vector<F>)->index=primitive("vector.length");
)";
        for (bool exposed : {false, true}) {
          auto result =
              check({{"zkc::primitives::vector", primitives, "primitive.zkc"},
                     {"zkc::vector",
                      "module zkc::vector;pub use "
                      "zkc::primitives::vector::{Vector};" +
                          std::string(exposed ? "pub " : "") +
                          "use zkc::primitives::vector::{length};",
                      "vector.zkc"},
                     {"m", R"(module m;domain F=field("bls12-381.fr");
fn read(values:zkc::vector::Vector<F>)->index{return values.length();}
protocol Run roles(P)(values:zkc::vector::Vector<F>@P)->(out:index@P){let n@P=read(values);return n;}
)",
                      "main.zkc"}},
                    "zkc");
          if (!exposed) {
            refuses(std::move(result), "source.method");
            continue;
          }
          auto project = take(std::move(result));
          const auto &read = named(project.declarations(), "m::read");
          auto call = llvm::find_if(read.body->operations, [](const auto &op) {
            return op.binding.has_value();
          });
          require(call != read.body->operations.end() &&
                      call->binding->target.declaration.index ==
                          named(project.declarations(),
                                "zkc::primitives::vector::length")
                              .id.index,
                  "builtin forwarding selected an unrelated declaration");
          require(call->binding->target.reference.provider.index ==
                      named(project.declarations(), "zkc::vector").id.index,
                  "builtin forwarding lost its selected home provider");
          take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
        }
      });
  return cases.result();
}
