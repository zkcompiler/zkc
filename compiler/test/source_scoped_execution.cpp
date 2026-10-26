#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Algorithms.h"
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
)"},
    {"alias captures after ordinary helper substitution", R"(
fn identity(x:Fr)->Fr{return x;}
fn work(x:Fr,n:index)->Fr{let y=identity(x);let mut acc=x;for _ in 0..n{acc=acc+x+y;}return acc;}
protocol Run roles(P)(x:Fr@P,n:index@P)->(r:Fr@P){return work(x,n);}
)"},
    {"stopping ordinary helper truncates its caller", R"(
fn fail(x:Fr)->Fr{stop "reject";}
fn work(x:Fr)->Fr{let y=fail(x);return x+y;}
protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return work(x);}
)"},
    {"participant mathematical demand", R"(
math fn square(x:Fr)->Fr{return x*x;}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return square(x)+y;}
)"},
    {"participant direct and computed guards", R"(
protocol Run roles(P)(x:Fr@P,y:Fr@P,go:bool@P)->(r:Fr@P){require @P go;require @P x==y;return x+y;}
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
    cases.run((llvm::Twine("expand ") + sample.name).str(), [&] {
      Fixture fixture(context, sample);
      auto expanded = protocol::expandScopedHelpers(*fixture.module);
      require(bool(expanded), "scoped helper expansion failed");
      require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                  *fixture.module, *expanded)),
              "scoped helper correspondence failed");
      expanded->walk([&](func::CallOp call) {
        require(!call->hasAttr("runtime.site"),
                "ordinary scoped helper call survived expansion");
      });
    });
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
    cases.run((llvm::Twine("prepare ") + sample.name).str(), [&] {
      Fixture fixture(context, sample);
      auto candidate = OwningOpRef<ModuleOp>(
          cast<ModuleOp>(fixture.module->getOperation()->clone()));
      PassManager manager(&context);
      manager.addPass(protocol::createProjectProtocolPass());
      require(succeeded(manager.run(*candidate)),
              "preparation projection failed");
      auto expanded = protocol::expandScopedHelpers(*candidate);
      require(bool(expanded), "preparation helper expansion failed");
      PassManager lowering(&context);
      lowering.addPass(protocol::createLowerMathPass());
      require(succeeded(lowering.run(*candidate)),
              "scoped mathematical preparation failed");
      require(succeeded(mathematical::verifyProjectionPreserved(*expanded,
                                                                *candidate)),
              "scoped preparation correspondence failed");
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
  auto expandedMutation = [&](StringRef name, auto edit, unsigned sample = 0) {
    cases.run(name, [&] {
      Fixture fixture(context, samples[sample]);
      auto candidate = protocol::expandScopedHelpers(*fixture.module);
      require(bool(candidate), "expansion mutation fixture failed");
      edit(*candidate);
      require(succeeded(verify(*candidate)),
              "expansion mutation must remain admitted");
      ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
      require(failed(protocol::verifyScopedHelperExpansionPreserved(
                  *fixture.module, *candidate)),
              "independent expansion check accepted a changed computation");
    });
  };
  auto preparedMutation = [&](StringRef name, unsigned sample, auto edit,
                              bool formed = true) {
    cases.run(name, [&] {
      Fixture fixture(context, samples[sample]);
      auto projectedSource = projected(fixture);
      auto original = protocol::expandScopedHelpers(*projectedSource);
      require(bool(original), "preparation source fixture failed");
      auto candidate =
          OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
      PassManager lowering(&context);
      lowering.addPass(protocol::createLowerMathPass());
      require(succeeded(lowering.run(*candidate)),
              "preparation fixture failed");
      edit(*candidate);
      ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
      if (formed) {
        require(succeeded(verify(*candidate)),
                "preparation mutation lost admission");
        require(failed(mathematical::verifyProjectionPreserved(*original,
                                                               *candidate)),
                "preparation changed semantics without detection");
      } else {
        require(failed(verify(*candidate)),
                "malformed calculation was admitted");
      }
    });
  };
  preparedMutation("prepared mathematical invocation swaps actual captures", 17,
                   [&](ModuleOp module) {
                     bool changed = false;
                     module.walk([&](protocol_ir::LocalCallOp call) {
                       if (!changed && call.getNumOperands() == 2) {
                         auto first = call->getOperand(0);
                         call->setOperand(0, call->getOperand(1));
                         call->setOperand(1, first);
                         changed = true;
                       }
                     });
                     require(changed, "missing generated calculation");
                   });
  preparedMutation(
      "prepared calculation changes its actual equation", 17,
      [&](ModuleOp module) {
        bool changed = false;
        module.walk([&](mlir::Operation *op) {
          auto unit = op->getParentOfType<ModuleOp>();
          if (!changed && unit && unit->hasAttr("exec.computation") &&
              op->getName().getStringRef() == "algebra.field_add") {
            op->setOperand(1, op->getOperand(0));
            changed = true;
          }
        });
        require(changed, "missing retained equation");
      });
  preparedMutation("preparation retains original mathematical definitions", 17,
                   [&](ModuleOp module) {
                     auto &owner = module.getBody()->front();
                     for (auto function :
                          owner.getRegion(0).front().getOps<func::FuncOp>())
                       if (!protocol::isScopedExecutionFunction(function)) {
                         function.erase();
                         return;
                       }
                     require(false, "missing original mathematical helper");
                   });
  preparedMutation(
      "prepared guard cannot reverse its branch outcomes", 18,
      [&](ModuleOp module) {
        SmallVector<func::CallOp> calls;
        module.walk([&](func::CallOp call) {
          if (!call->hasAttr("runtime.site"))
            calls.push_back(call);
        });
        require(calls.size() >= 2, "missing generated guard branches");
        auto first = calls[0].getCalleeAttr();
        calls[0].setCalleeAttr(calls[1].getCalleeAttr());
        calls[1].setCalleeAttr(first);
      },
      false);
  expandedMutation("expanded primitive uses a different operand",
                   [&](ModuleOp module) {
                     bool changed = false;
                     module.walk([&](exec::ApplyOp op) {
                       if (!changed && op.getInputs().size() == 2) {
                         op->setOperand(2, op.getInputs().front());
                         changed = true;
                       }
                     });
                     require(changed, "missing expanded primitive");
                   });
  expandedMutation("expanded occurrence loses its invocation path",
                   [&](ModuleOp module) {
                     bool changed = false;
                     module.walk([&](exec::ComputeOp op) {
                       if (!changed) {
                         op.setSite("different");
                         changed = true;
                       }
                     });
                     require(changed, "missing expanded computation");
                   });
  expandedMutation("expanded return selects an earlier value",
                   [&](ModuleOp module) {
                     bool changed = false;
                     module.walk([&](exec::ReturnOp op) {
                       auto function = op->getParentOfType<func::FuncOp>();
                       if (!changed && function.getNumArguments() == 3 &&
                           op.getValues().size() == 1) {
                         op->setOperand(0, function.getArgument(1));
                         changed = true;
                       }
                     });
                     require(changed, "missing expanded return");
                   });
  expandedMutation(
      "expanded loop yields a stale carried value",
      [&](ModuleOp module) {
        bool changed = false;
        module.walk([&](exec::CompleteOp op) {
          auto function = op->getParentOfType<func::FuncOp>();
          if (!changed && function.getNumArguments() >= 3 &&
              op.getValues().size() == 1 &&
              function.getArgument(2).getType() ==
                  op.getValues().front().getType() &&
              op.getValues().front() != function.getArgument(2)) {
            op->setOperand(1, function.getArgument(2));
            changed = true;
          }
        });
        require(changed, "missing expanded loop yield");
      },
      2);
  cases.run("unexpanded calls cannot claim scoped substitution", [&] {
    Fixture fixture(context, samples[0]);
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(failed(protocol::verifyScopedHelperExpansionPreserved(
                *fixture.module, *fixture.module)),
            "ordinary calls survived independent expansion checking");
  });
  cases.run("checked occurrence paths retain nested helper provenance", [&] {
    Fixture fixture(context, samples[0]);
    std::vector<protocol::AlgorithmOrigin> origins;
    auto candidate = protocol::expandScopedHelpers(*fixture.module, &origins);
    require(bool(candidate), "provenance fixture failed");
    bool nested = false;
    for (const auto &origin : origins) {
      require(!origin.function.empty() && !origin.definition.empty() &&
                  !origin.originalSite.empty(),
              "incomplete occurrence provenance");
      nested |= !origin.path.empty();
      uint64_t bytes = 16 * 1024 * 1024;
      require(take(protocol::algorithmSite(origin.path, origin.originalSite,
                                           bytes)) == origin.site,
              "occurrence path does not identify the actual expanded site");
    }
    require(nested, "ordinary helper path was dropped");
  });
  cases.run("outlined preconditions follow aliased capture positions", [&] {
    Fixture fixture(context, {"finite capture premises", R"(
type Vector<F:Field>=builtin("vector",F);
fn identity(xs:Vector<Fr>)->Vector<Fr>{return xs;}
fn work(xs:Vector<Fr>,go:bool)->(Vector<Fr>,Vector<Fr>){
  let ys=identity(xs);return if go{(xs,ys)}else{(ys,xs)};
}
protocol Run roles(P)(xs:Vector<Fr>@P,go:bool@P)->(a:Vector<Fr>@P,b:Vector<Fr>@P){let pair @P=work(xs,go);return (a=pair.0,b=pair.1);}
)"});
    unsigned regions = 0;
    fixture.module->walk([&](func::FuncOp function) {
      if (!function->hasAttr("runtime.region"))
        return;
      require(function.getNumArguments() == 3,
              "expected two distinct vector captures");
      function->setAttr("data.preconditions",
                        ArrayAttr::get(&context, {data::EqualExtentAttr::get(
                                                     &context, 2, 0, 2, 0)}));
      ++regions;
    });
    require(regions == 2, "missing finite premise regions");
    auto candidate = protocol::expandScopedHelpers(*fixture.module);
    require(bool(candidate), "capture premise transport failed");
    candidate->walk([&](func::FuncOp function) {
      if (!function->hasAttr("runtime.region"))
        return;
      auto conditions =
          function->getAttrOfType<ArrayAttr>("data.preconditions");
      require(function.getNumArguments() == 2 && conditions &&
                  conditions.size() == 1 &&
                  conditions[0] ==
                      data::EqualExtentAttr::get(&context, 1, 0, 1, 0),
              "finite premise did not follow the actual capture argument");
      function->removeAttr("data.preconditions");
    });
    require(succeeded(verify(*candidate)),
            "premise deletion must remain admitted");
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(failed(protocol::verifyScopedHelperExpansionPreserved(
                *fixture.module, *candidate)),
            "expansion checker ignored the outlined static contract");
  });
  cases.run("expansion capacity failure preserves the source", [&] {
    std::string text = "fn f0(x:Fr)->Fr{return x;}\n";
    for (unsigned i = 1; i <= 17; ++i) {
      auto prior = "f" + std::to_string(i - 1);
      text += "fn f" + std::to_string(i) + "(x:Fr)->Fr{let y=" + prior +
              "(x);return " + prior + "(y);}\n";
    }
    text += "protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return f17(x);}";
    Fixture fixture(context, {"bounded expansion", text.c_str()});
    auto original = OwningOpRef<ModuleOp>(
        cast<ModuleOp>(fixture.module->getOperation()->clone()));
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(!protocol::expandScopedHelpers(*fixture.module),
            "unbounded helper substitution was accepted");
    require(OperationEquivalence::isEquivalentTo(
                original->getOperation(), fixture.module->getOperation(),
                OperationEquivalence::IgnoreLocations),
            "failed expansion mutated its source");
  });
  cases.run("outlined expansion capacity refuses without publication", [&] {
    std::string text = "fn f0(x:Fr)->Fr{return if true{x}else{x};}\n";
    for (unsigned i = 1; i <= 12; ++i) {
      auto prior = "f" + std::to_string(i - 1);
      text += "fn f" + std::to_string(i) + "(x:Fr)->Fr{let y=" + prior +
              "(x);return " + prior + "(y);}\n";
    }
    text += "protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return f12(x);}";
    Fixture fixture(context, {"bounded outlined expansion", text.c_str()});
    std::vector<protocol::AlgorithmOrigin> origins{
        {"unchanged", {}, {}, {}, {}}};
    ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
    require(!protocol::expandScopedHelpers(*fixture.module, &origins),
            "unbounded outlined expansion was accepted");
    require(origins.size() == 1 && origins.front().function == "unchanged",
            "failed expansion published partial occurrence paths");
    take(compareOriginal(fixture.entry, *fixture.module));
  });
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
