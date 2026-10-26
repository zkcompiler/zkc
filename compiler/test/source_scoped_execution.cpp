#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Language.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
struct Sample {
  const char *name, *source;
};
const Sample samples[] = {
    {"ordinary and mathematical helpers", R"(
math fn square(x:Fr)->Fr{return x*x;}
fn add(x:Fr,y:Fr)->Fr{return square(x)+y;}
fn wrapper(x:Fr,y:Fr)->Fr{return add(x,y);}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return wrapper(x,y);}
)"},
    {"require and returning branches", R"(
fn work(x:Fr,y:Fr,go:bool)->Fr{require go;return if go{x+y}else{x-y};}
protocol Run roles(P)(x:Fr@P,y:Fr@P,go:bool@P)->(r:Fr@P){return work(x,y,go);}
)"},
    {"nested loops retain invariant captures", R"(
fn work(x:Fr,n:index)->Fr{let mut y=x;for _ in 0..n{for _ in 0..n{y=y+x;}}return y;}
protocol Run roles(P)(x:Fr@P,n:index@P)->(r:Fr@P){return work(x,n);}
)"},
    {"zero-state loop", R"(
fn work(n:index)->(){for _ in 0..n{}return ();}
protocol Run roles(P)(n:index@P)->(){work(n);return ();}
)"},
    {"variant construction and match", R"(
enum Choice{Some(Fr),None()}
fn work(x:Fr,go:bool)->Fr{let v=if go{Choice::Some(x)}else{Choice::None()};return match v{Some(y)=>{y},None()=>{x}};}
protocol Run roles(P)(x:Fr@P,go:bool@P)->(r:Fr@P){return work(x,go);}
)"},
    {"stopped branch", R"(
fn work(x:Fr,go:bool)->Fr{return if go{x}else{stop "reject";};}
protocol Run roles(P)(x:Fr@P,go:bool@P)->(r:Fr@P){return work(x,go);}
)"},
    {"packed sequence product", R"(
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
fn empty<T:Type+Copy+Drop>()->Sequence<T>=primitive("sequence.empty");
fn append<T:Type+Copy+Drop>(xs:Sequence<T>,x:T)->Sequence<T>=primitive("sequence.append");
fn get<T:Type+Copy+Drop>(xs:Sequence<T>,i:index)->T=primitive("sequence.at");
fn work(x:Fr,y:Fr)->Fr{let xs=append(empty(),(x,y));let pair=get(xs,0);return pair.0+pair.1;}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return work(x,y);}
)"},
    {"filtered ordered fold with stopping callback", R"(
type Vector<F:Field>=builtin("vector",F);
domain fn vector<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn filtered<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item,rows),step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold_where");
fn work(xs:Vector<Fr>,seed:Fr,enabled:bool)->Fr{return filtered(vector(xs),seed,fn(item)=>enabled,fn(state,item)=>if enabled{state+item}else{stop "reject";});}
protocol Run roles(P)(xs:Vector<Fr>@P,seed:Fr@P,enabled:bool@P)->(r:Fr@P){return work(xs,seed,enabled);}
)"},
    {"ordered collection of products", R"(
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
struct Row {pub a:Fr,pub b:Fr}
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<I>,body:fn(item:I)->B effects(stop) where item_from(item,rows))->Sequence<B> effects(stop)=finite("local.collect.sequence");
fn work(xs:Sequence<Row>)->Sequence<Row>{return collect(elements(xs),fn(item)=>item);}
protocol Run roles(P)(xs:Sequence<Row>@P)->(r:Sequence<Row>@P){return work(xs);}
)"},
    {"zero-state finite fold", R"(
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
fn work(xs:Sequence<()>)->(){return fold(elements(xs),(),fn(state,item)=>state);}
protocol Run roles(P)(xs:Sequence<()>@P)->(){work(xs);return ();}
)"},
    {"mapped vectors and scalar captures reuse definitions", R"(
type Vector<F:Field>=builtin("vector",F);
math fn affine(x:Fr,y:Fr,r:Fr)->Fr{return x+y*r;}
fn work(xs:Vector<Fr>,ys:Vector<Fr>,r:Fr)->Vector<Fr>{let first=map affine(each xs,each ys,r);return map affine(each first,each xs,r);}
protocol Run roles(P)(xs:Vector<Fr>@P,ys:Vector<Fr>@P,r:Fr@P)->(v:Vector<Fr>@P){return work(xs,ys,r);}
)"},
    {"finite fold preserves an affine callback state", R"(
#[affine] struct State {}
fn create()->State{return State{};}
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
fn work(xs:Vector<Fr>,seed:State)->State{return fold(elements(xs),seed,fn(state,item)=>state);}
protocol Run roles(P)(xs:Vector<Fr>@P)->(r:State@P){let seed @P=create();return work(xs,seed);}
)"},
    {"affine fold joins returning and stopping callback branches", R"(
#[affine] struct State {}
fn create()->State{return State{};}
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
fn work(xs:Vector<Fr>,seed:State,enabled:bool)->State{return fold(elements(xs),seed,fn(state,item)=>if enabled{state}else{stop "reject";});}
protocol Run roles(P)(xs:Vector<Fr>@P,enabled:bool@P)->(r:State@P){let seed @P=create();return work(xs,seed,enabled);}
)"},
    {"protocol repeat retains the scoped helper state root", R"(
#[affine] struct State {}
fn create()->State{return State{};}
fn step(state:State)->State{return state;}
protocol Run roles(P)(n:index@P)->(r:State@P){
  let mut state @P=create();
  for _ in 0..n roles(P) max 4 {state=step(state);}
  return state;
}
)"},
    {"protocol repeat sees nested helper control", R"(
#[affine] struct State {}
fn create()->State{return State{};}
fn step(state:State,n:index,go:bool)->State{
  let mut current=state;
  for _ in 0..n {current=if go{current}else{stop "reject";};}
  return current;
}
protocol Run roles(P)(n:index@P,go:bool@P)->(r:State@P){
  let mut state @P=create();
  for _ in 0..n roles(P) max 4 {state=step(state,n,go);}
  return state;
}
)"}};
struct Fixture {
  CheckedProject checked;
  ClosedEntry entry;
  std::string text;
  OwningOpRef<ModuleOp> module;
  Fixture(MLIRContext &context, const Sample &sample)
      : checked(take(
            analyze(
                take(capture(
                    {{"sample",
                      std::string(
                          "module sample;domain Fr=field(\"koala-bear\");\n") +
                          sample.source,
                      "scoped-source.zkc"}})))
                .checkedProject())),
        entry(take(closeNativeRun(checked, "sample::Run"))),
        text(take(emitOriginal(entry, context))),
        module(parseSourceString<ModuleOp>(text, &context)) {
    require(module && succeeded(verify(*module)),
            "source emission failed admission");
    take(compareOriginal(entry, *module));
    module->walk([&](mlir::Operation *op) {
      auto name = op->getName().getStringRef();
      require(!name.starts_with("local.") && name != "algebra.map_realize",
              "source retained a replaced execution owner");
    });
  }
};
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (const auto &sample : samples) {
    cases.run(sample.name, [&] { Fixture fixture(context, sample); });
    cases.run((llvm::Twine("project ") + sample.name).str(), [&] {
      Fixture fixture(context, sample);
      auto candidate = OwningOpRef<ModuleOp>(
          cast<ModuleOp>(fixture.module->getOperation()->clone()));
      PassManager manager(&context);
      manager.addPass(protocol::createProjectProtocolPass());
      require(succeeded(manager.run(*candidate)),
              "scoped source projection failed");
      require(succeeded(mathematical::verifyProjectionPreserved(*fixture.module,
                                                                *candidate)),
              "scoped source projection correspondence failed");
      require(succeeded(mathematical::verifyAuthoredLocalsPreserved(
                  &fixture.module->getBody()->front(),
                  &candidate->getBody()->front())),
              "projection changed the authored closure");
    });
  }
  auto projected = [&](Fixture &fixture) {
    auto candidate = OwningOpRef<ModuleOp>(
        cast<ModuleOp>(fixture.module->getOperation()->clone()));
    PassManager manager(&context);
    manager.addPass(protocol::createProjectProtocolPass());
    require(succeeded(manager.run(*candidate)), "projection fixture failed");
    return candidate;
  };
  cases.run("projection refuses a changed scoped helper body", [&] {
    Fixture fixture(context, samples[0]);
    auto candidate = projected(fixture);
    bool changed = false;
    candidate->walk([&](exec::ReturnOp returned) {
      auto function = returned->getParentOfType<func::FuncOp>();
      if (!changed && function.getNumArguments() == 3 &&
          returned.getValues().size() == 1) {
        returned->setOperand(0, function.getArgument(1));
        changed = true;
      }
    });
    require(changed && succeeded(verify(*candidate)),
            "body mutation must remain admitted");
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(failed(mathematical::verifyProjectionPreserved(*fixture.module,
                                                           *candidate)),
            "projection ignored its actual scoped helper body");
  });
  for (bool scoped : {true, false})
    cases.run(scoped ? "projection retains dormant scoped helpers"
                     : "projection retains dormant mathematical helpers",
              [&] {
                Fixture fixture(context, samples[0]);
                auto &owner = fixture.module->getBody()->front();
                func::FuncOp original;
                for (auto function :
                     owner.getRegion(0).front().getOps<func::FuncOp>())
                  if (protocol::isScopedExecutionFunction(function) == scoped &&
                      !function->hasAttr("runtime.region")) {
                    original = function;
                    break;
                  }
                require(bool(original), "missing dormant helper template");
                auto extra = cast<func::FuncOp>(original->clone());
                extra.setSymName("dormant");
                owner.getRegion(0).front().push_back(extra);
                require(succeeded(verify(*fixture.module)),
                        "dormant helper fixture is invalid");
                auto candidate = projected(fixture);
                auto &target = candidate->getBody()->front();
                SymbolTable::lookupSymbolIn(&target, "dormant")->erase();
                require(succeeded(verify(*candidate)),
                        "dormant deletion must remain admitted");
                ScopedDiagnosticHandler silence(&context,
                                                [](mlir::Diagnostic &) {});
                require(failed(mathematical::verifyProjectionPreserved(
                            *fixture.module, *candidate)),
                        "projection silently dropped a dormant definition");
              });
  cases.run("participant invocation cannot change its role", [&] {
    Fixture fixture(context, samples[0]);
    auto candidate = projected(fixture);
    candidate->walk(
        [&](protocol_ir::LocalCallOp call) { call.setRole("different"); });
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(failed(verify(*candidate)),
            "participant invocation accepted a foreign role");
  });
  auto mutation = [&](llvm::StringRef name, unsigned sample, auto edit) {
    cases.run(name, [&] {
      Fixture fixture(context, samples[sample]);
      edit(*fixture.module);
      require(succeeded(verify(*fixture.module)),
              "correspondence mutation must remain admitted");
      refuses(compareOriginal(fixture.entry, *fixture.module),
              "source.correspondence");
    });
  };
  mutation("same-typed primitive operand substitution", 0,
           [&](ModuleOp module) {
             bool changed = false;
             module.walk([&](exec::ApplyOp op) {
               if (!changed && op.getInputs().size() == 2) {
                 op->setOperand(2, op.getInputs().front());
                 changed = true;
               }
             });
             require(changed, "missing primitive operands");
           });
  mutation("helper occurrence substitution", 0, [&](ModuleOp module) {
    bool changed = false;
    module.walk([&](func::CallOp op) {
      if (op->hasAttr("runtime.site")) {
        op->setAttr("runtime.site", StringAttr::get(&context, "different"));
        changed = true;
      }
    });
    require(changed, "missing ordinary helper call");
  });
  mutation("conditional arm permutation", 1, [&](ModuleOp module) {
    SmallVector<func::CallOp> calls;
    module.walk([&](func::CallOp op) {
      if (!op->hasAttr("runtime.site") && op.getNumOperands() == 1)
        calls.push_back(op);
    });
    require(calls.size() == 2 &&
                calls[0].getResultTypes() == calls[1].getResultTypes(),
            "missing matching conditional arms");
    auto first = calls[0].getCalleeAttr();
    calls[0].setCalleeAttr(calls[1].getCalleeAttr());
    calls[1].setCalleeAttr(first);
  });
  mutation("changed rejection reason", 5, [&](ModuleOp module) {
    bool changed = false;
    module.walk([&](exec::RejectOp op) {
      op->setAttr("reason", StringAttr::get(&context, "abort"));
      changed = true;
    });
    require(changed, "missing rejection");
  });
  mutation("changed uncharged return payload", 0, [&](ModuleOp module) {
    bool changed = false;
    module.walk([&](exec::ReturnOp op) {
      auto function = op->getParentOfType<func::FuncOp>();
      if (!changed && op.getValues().size() == 1 &&
          function.getNumArguments() > 1 &&
          function.getArgument(1).getType() ==
              op.getValues().front().getType()) {
        op->setOperand(0, function.getArgument(1));
        changed = true;
      }
    });
    require(changed, "missing helper result");
  });
  mutation("mapped callback capture substitution", 10, [&](ModuleOp module) {
    bool changed = false;
    module.walk([&](exec::ComputeOp op) {
      auto function = op->getParentOfType<func::FuncOp>();
      if (function.getSymName().starts_with("zkl_map_") &&
          op.getInputs().size() == 3) {
        op->setOperand(3, op.getInputs().front());
        changed = true;
      }
    });
    require(changed, "missing mapped callback");
  });
  mutation("unrelated dormant ordinary helper", 0, [&](ModuleOp module) {
    func::FuncOp original;
    module.walk([&](func::FuncOp function) {
      if (!original && function->hasAttr("runtime.origin"))
        original = function;
    });
    require(bool(original), "missing ordinary helper");
    auto extra = cast<func::FuncOp>(original->clone());
    extra.setSymName("unrelated");
    original->getBlock()->push_back(extra);
  });
  for (unsigned sample : {7U, 8U, 9U, 10U})
    cases.run(std::string("unresolved finite extraction refuses: ") +
                  samples[sample].name,
              [&] {
                Fixture fixture(context, samples[sample]);
                auto &owner = fixture.module->getBody()->front();
                refuses(protocol::readSourceExecutionDefinitions(&owner),
                        "execution-cfg");
              });
  for (unsigned sample : {2U, 7U, 8U, 9U, 10U})
    cases.run(
        std::string("exact comparison allowance: ") + samples[sample].name,
        [&] {
          Fixture fixture(context, samples[sample]);
          auto report = take(compareOriginal(fixture.entry, *fixture.module));
          Limits exact;
          exact.operations = report.operations;
          take(compareOriginal(fixture.entry, *fixture.module, exact));
          for (uint64_t limit = 1; limit < exact.operations; ++limit) {
            Limits smaller = exact;
            smaller.operations = limit;
            refuses(compareOriginal(fixture.entry, *fixture.module, smaller),
                    "source.limit");
          }
        });
  return cases.result();
}
