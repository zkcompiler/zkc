#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/PreparedProtocol.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "../lib/Transforms/ScopedFinite.h"
#include "../lib/Transforms/ScopedPreparation.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/ScopedFixture.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Language.h"
#include "zkc/Translation/Protocol.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
struct Sample {
  const char *name, *source;
  const char *field = "koala-bear";
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
)"},
    {"scoped diagonal producer with two reached consumers", R"(
type Vector<F:Field>=builtin("vector",F);
fn mul<F:Field>(a:Vector<F>,b:Vector<F>)->Vector<F>=primitive("vector.mul");
fn dot<F:Field>(a:Vector<F>,b:Vector<F>)->F=primitive("vector.dot");
fn work(w:Vector<Fr>,f:Vector<Fr>,v:Vector<Fr>)->Fr{let mapped=mul(f,v);let a=dot(w,mapped);let b=dot(w,mapped);return a+b;}
protocol Run roles(P)(w:Vector<Fr>@P,f:Vector<Fr>@P,v:Vector<Fr>@P)->(v:Fr@P){return work(w,f,v);}
)",
     "bls12-381.fr"},
    {"conditional mathematical helper retains its premise", R"(
type Vector<F:Field>=builtin("vector",F);
type Array<F:Field,N:nat>=builtin("field_array",F,N);
math fn at(xs:Array<Fr,2>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Array<Fr,2>>("container.at",xs,i);}
math fn pick(xs:Array<Fr,2>,i:index)->Fr{return at(xs,0);}
fn work(xs:Vector<Fr>,i:index)->Fr{let packed=kernel<Fr,2>("field_array.from_vector",xs);return pick(packed,0);}
protocol Run roles(P)(xs:Vector<Fr>@P,i:index@P)->(r:Fr@P){return work(xs,i);}
)",
     "bls12-381.fr"},
    {"nested finite callbacks retain distinct numerical occurrences", R"(
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
fn work(xs:Vector<Fr>,seed:Fr)->Fr{return fold(elements(xs),seed,fn(state,item)=>fold(elements(xs),state,fn(acc,value)=>acc+value+item));}
protocol Run roles(P)(xs:Vector<Fr>@P,seed:Fr@P)->(r:Fr@P){return work(xs,seed);}
)"},
    {"finite predicate can stop before the state callback", R"(
type Vector<F:Field>=builtin("vector",F);
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item,rows),step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold_where");
fn work(xs:Vector<Fr>,seed:Fr,enabled:bool)->Fr{return fold(elements(xs),seed,fn(item)=>if enabled{true}else{stop "reject";},fn(state,item)=>state+item);}
protocol Run roles(P)(xs:Vector<Fr>@P,seed:Fr@P,enabled:bool@P)->(r:Fr@P){return work(xs,seed,enabled);}
 )"},
    {"finite callbacks retain total bounded computations", R"(
type Vector<F:Field>=builtin("vector",F);
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
math fn at(xs:Vector<Fr>,i:index)->Fr where in_bounds(i,xs){return intrinsic<Vector<Fr>>("container.at",xs,i);}
fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn sum(xs:Vector<Fr>)->Fr{return total(indices(xs),0,fn(state,i)=>state+at(xs,i));}
domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
fn work(xs:Vector<Fr>,seed:Fr)->Fr{return fold(elements(xs),seed,fn(state,item)=>state+sum(xs));}
protocol Run roles(P)(xs:Vector<Fr>@P,seed:Fr@P)->(r:Fr@P){return work(xs,seed);}
)"},
    {"protocol forwarding has no numerical helper", R"(
protocol Run roles(P,V)(x:Fr@(P,V))->(r:Fr@(P,V)){return x;}
)"},
    {"mathematical invocations retain branch captures", R"(
math fn twice(x:Fr)->Fr{return x+x;}
fn work(x:Fr,y:Fr,go:bool)->Fr{return if go{twice(x)}else{twice(y)};}
protocol Run roles(P)(x:Fr@P,y:Fr@P,go:bool@P)->(r:Fr@P){return work(x,y,go);}
)"},
    {"mathematical invocations retain nested iteration captures", R"(
math fn twice(x:Fr)->Fr{return x+x;}
fn work(x:Fr,n:index)->Fr{let mut y=x;for _ in 0..n{for _ in 0..n{y=twice(y);}}return y;}
protocol Run roles(P)(x:Fr@P,n:index@P)->(r:Fr@P){return work(x,n);}
)"},
};
struct Fixture {
  CheckedProject checked;
  ClosedEntry entry;
  std::string text;
  OwningOpRef<ModuleOp> module;
  Fixture(MLIRContext &context, const Sample &sample)
      : checked(take(
            analyze(
                take(capture({{"sample",
                               std::string("module sample;domain Fr=field(\"") +
                                   sample.field + "\");\n" + sample.source,
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
  cases.run("map mismatch precedes admission of a later unused row", [&] {
    const Sample sample{"ordered map rows", R"(
type Vector<F:Field>=builtin("vector",F);
math fn difference(a:Fr,b:Fr,unused:Fr)->Fr{return a-b;}
fn work(a:Vector<Fr>,b:Vector<Fr>,unused:Vector<Fr>)->Vector<Fr>{
 return map difference(each a,each b,each unused);
}
protocol Run roles(P)(a:Vector<Fr>@P,b:Vector<Fr>@P,unused:Vector<Fr>@P)
 ->(r:Vector<Fr>@P){return work(a,b,unused);}
)"};
    Fixture fixture(context, sample);
    mlir::Operation *domain = nullptr;
    fixture.module->walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "data.domain")
        domain = op;
    });
    require(domain, "missing map domain");
    SmallVector<mlir::Operation *> constructors;
    for (auto &op : domain->getRegion(0).front().without_terminator())
      constructors.push_back(&op);
    require(constructors.size() == 5 &&
                constructors[2]->getName().getStringRef() ==
                    "data.domain_zip" &&
                constructors[3]->getName().getStringRef() ==
                    "data.domain_elements" &&
                constructors[4]->getName().getStringRef() == "data.domain_zip",
            "row equality is delayed past a later row admission");
    // This remains well-formed SSA but changes the first reached failure.
    constructors[3]->moveBefore(constructors[2]);
    require(succeeded(verify(*fixture.module)),
            "admission-order mutation is not well formed");
    refuses(compareOriginal(fixture.entry, *fixture.module),
            "source.correspondence");
  });
  cases.run("role-free preparation refuses protocol obligations", [&] {
    Fixture fixture(context, samples[0]);
    auto preparation = mathematical::PreparedProtocol::prepare(*fixture.module);
    require(bool(preparation), "protocol preparation refused");
    std::string diagnostic;
    ScopedDiagnosticHandler capture(&context, [&](mlir::Diagnostic &value) {
      llvm::raw_string_ostream output(diagnostic);
      value.print(output);
      return success();
    });
    require(!std::move(*preparation).execute() &&
                StringRef(diagnostic).contains("numerical-execution-profile"),
            "numerical preparation discarded protocol obligations");
    take(compareOriginal(fixture.entry, *fixture.module));
  });
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
      {
        target::PhysicalPlanOptions physicalOptions;
        physicalOptions.releaseStorage = true;
        physicalOptions.linearContractions = true;
        protocol::Assignments requests;
        candidate->walk([&](runtime::BindingOp binding) {
          if (binding.getContract() == "poly.fold")
            requests.emplace_back(binding.getSymName().str(),
                                  "arkworks-msb/poly.fold");
        });
        auto plan = take(target::proposePhysical(*candidate,
                                                 target::installedCandidates(),
                                                 requests, physicalOptions));
        auto selected = take(plan.cloneSelectedSubject(*candidate));
        auto ports = take(target::ExecutionPorts::read(*selected));
        auto checked = take(target::validatePhysical(*candidate, plan));
        auto physical =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*candidate)->clone()));
        auto physicalPlan = take(
            target::proposePhysical(*physical, target::installedCandidates(),
                                    requests, physicalOptions));
        auto physicalChecked =
            take(target::validatePhysical(*physical, physicalPlan));
        if (auto error =
                protocol::materializePhysical(*physical, physicalChecked))
          throw std::runtime_error(llvm::toString(std::move(error)));
        if (auto error = protocol::verifyPhysicalMaterialization(
                *candidate, *physical, checked))
          throw std::runtime_error(llvm::toString(std::move(error)));
        auto artifact = take(protocol::exportProgram(*physical));
        std::string bytes;
        llvm::raw_string_ostream(bytes) << program::encode(artifact);
        take(protocol::verifyProgramArtifact(*physical, bytes));
        auto storageInput =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*physical)->clone()));
        SmallVector<mlir::Operation *> existingReleases;
        storageInput->walk([&](runtime::ReleaseBindingsOp release) {
          existingReleases.push_back(release);
        });
        for (auto *release : existingReleases)
          release->erase();
        auto storageBefore =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*storageInput)->clone()));
        require(succeeded(protocol::releaseLocalStorage(*storageInput)) &&
                    succeeded(protocol::verifyStoragePreserved(*storageBefore,
                                                               *storageInput)),
                "standalone scoped storage producer or reader failed");
        if (sample.name == StringRef("require and returning branches")) {
          bool changed = false;
          physical->walk([&](exec::ApplyOp apply) {
            if (!changed && apply.getInputs().size() == 2 &&
                apply.getInputs()[0].getType() ==
                    apply.getInputs()[1].getType() &&
                apply.getInputs()[0] != apply.getInputs()[1]) {
              auto first = apply.getInputs()[0];
              apply->setOperand(1, apply.getInputs()[1]);
              apply->setOperand(2, first);
              changed = true;
            }
          });
          require(changed && succeeded(verify(*physical)),
                  "same-typed payload mutation was not admitted");
          auto error = protocol::verifyPhysicalMaterialization(
              *candidate, *physical, checked);
          require(
              bool(error),
              "physical checker accepted changed actual payload association");
          llvm::consumeError(std::move(error));
        }
        if (sample.name ==
            StringRef("scoped diagonal producer with two reached consumers"))
          require(plan.contractions.size() == 1 &&
                      plan.contractions[0].consumers.size() == 2 &&
                      checked.stats().eligibleProducers == 1 &&
                      checked.stats().eligiblePairs == 2 &&
                      checked.stats().selectedPairs == 2,
                  "scoped contraction lost actual payload consumers");
        bool payloadArgument = false;
        for (auto *op : ports.operations()) {
          const auto &node = ports.get(op);
          for (auto [index, value] : llvm::enumerate(node.outputs)) {
            auto definition = ports.definition(value);
            require(definition.owner == op && definition.port == index &&
                        !definition.argument,
                    "payload lost its actual semantic producer");
            payloadArgument |= isa<BlockArgument>(value);
          }
          for (auto [index, value] : llvm::enumerate(node.inputs)) {
            const auto operandIndex = index;
            require(llvm::any_of(ports.uses(value),
                                 [&](auto use) {
                                   return use.operation == op &&
                                          use.operand == operandIndex;
                                 }),
                    "actual payload use disappeared");
          }
          if (auto function = dyn_cast<func::FuncOp>(op))
            require(!ports.contains(function.getArgument(0)),
                    "scope was treated as a represented data value");
        }
        require(
            payloadArgument ||
                sample.name ==
                    StringRef(
                        "stopping ordinary helper truncates its caller") ||
                sample.name ==
                    StringRef("protocol forwarding has no numerical helper"),
            "fixture did not exercise a CFG payload definition");
      }
    });
  }
  for (bool loop : {false, true})
    cases.run(
        loop ? "scoped iteration converts only reached state uses"
             : "scoped branch converts only reached captured uses",
        [&] {
          OpBuilder builder(&context);
          auto location = builder.getUnknownLoc();
          auto module = OwningOpRef<ModuleOp>(ModuleOp::create(location));
          builder.setInsertionPointToStart(module->getBody());
          auto root = protocol_ir::ProtocolModuleOp::create(
              builder, location, protocol_ir::Profile::Exec);
          root.getBody().push_back(new Block);
          builder.setInsertionPointToStart(&root.getBody().front());
          runtime::BindingOp::create(builder, location, "fold", "poly.fold",
                                     builder.getStrArrayAttr({"bls12-381.fr"}),
                                     "arkworks-msb/poly.fold",
                                     builder.getArrayAttr({}));
          auto table =
              parseType("!poly.multilinear<\"bls12-381.fr\">", &context);
          auto field = parseType("!algebra.field<\"bls12-381.fr\">", &context);
          auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
          auto makeFunction = [&](StringRef name, TypeRange ports,
                                  bool region) {
            builder.setInsertionPointToEnd(&root.getBody().front());
            SmallVector<mlir::Type> arguments{
                runtime::ScopeType::get(&context)};
            llvm::append_range(arguments, ports);
            auto result = exec::OutcomeType::get(&context, {table});
            auto function = func::FuncOp::create(
                builder, location, name,
                builder.getFunctionType(arguments, result));
            function->setAttr("no_inline", builder.getUnitAttr());
            if (region) {
              function.setPrivate();
              function->setAttr("runtime.region", builder.getUnitAttr());
            } else {
              function->setAttr(
                  "runtime.origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
            }
            function.addEntryBlock();
            return function;
          };
          SmallVector<mlir::Type> ports{table, field};
          if (loop) {
            ports.push_back(index);
            ports.push_back(index);
          } else {
            ports.push_back(builder.getI1Type());
          }
          auto work = makeFunction("work", ports, false);
          auto branch = makeFunction("body",
                                     loop ? TypeRange{index, table, field}
                                          : TypeRange{table, field},
                                     true);
          builder.setInsertionPointToEnd(&branch.front());
          exec::ScopedExecutionBuilder inner(builder, branch);
          unsigned start = loop ? 2 : 1;
          auto folded = inner.invoke(
              "exec.apply", TypeRange{table},
              inner.scoped(
                  {branch.getArgument(start), branch.getArgument(start + 1)}),
              {builder.getNamedAttr("binding",
                                    FlatSymbolRefAttr::get(&context, "fold")),
               builder.getNamedAttr("parameters", builder.getArrayAttr({})),
               builder.getNamedAttr("site", builder.getStringAttr("fold"))});
          inner.complete(folded);
          func::FuncOp alternative;
          if (!loop) {
            alternative =
                makeFunction("otherwise", TypeRange{table, field}, true);
            builder.setInsertionPointToEnd(&alternative.front());
            exec::ScopedExecutionBuilder(builder, alternative)
                .complete(alternative.getArgument(1));
          }
          builder.setInsertionPointToEnd(&work.front());
          exec::ScopedExecutionBuilder outer(builder, work);
          SmallVector<mlir::Value> result;
          if (loop)
            result = outer.loop(work.getArgument(3), work.getArgument(4),
                                work.getArgument(1), work.getArgument(2),
                                TypeRange{table}, false, "loop",
                                [&](unsigned) { return branch; });
          else
            result = outer.conditional(
                work.getArgument(3), {work.getArgument(1), work.getArgument(2)},
                TypeRange{table}, "choose",
                [&](unsigned arm) { return arm ? alternative : branch; });
          outer.returned(result);
          require(succeeded(verify(*module)),
                  "execution table fixture failed admission");
          auto flow = take(target::ExecutionPorts::read(*module));
          target::PhysicalPlanOptions options;
          options.releaseStorage = true;
          auto plan = take(target::proposePhysical(
              *module, target::installedCandidates(), {}, options));
          auto checked = take(target::validatePhysical(*module, plan));
          unsigned conversions = 0;
          for (auto [position, op] : llvm::enumerate(flow.operations())) {
            const auto &choice = plan.operations[position];
            if (isa<exec::TestOp, exec::RangeOp>(op)) {
              require(choice.conversions.empty(),
                      "capture conversion moved before control entry");
              auto changed = plan;
              auto *entry = flow.get(op).bodies[0];
              auto producer = flow.body(entry).instructions.front();
              unsigned producerIndex = llvm::find(flow.operations(), producer) -
                                       flow.operations().begin();
              changed.operations[position].inputs[loop ? 2 : 1] =
                  plan.operations[producerIndex].inputs[0];
              refuses(target::validatePhysical(*module, changed),
                      "binding-operation-signature");
            }
            for (const auto &conversion : choice.conversions) {
              (void)conversion;
              require(op->getParentOfType<func::FuncOp>()->hasAttr(
                          "runtime.region"),
                      "body-only conversion escaped its reached region");
              ++conversions;
            }
          }
          require(conversions >= 2,
                  "fixture did not require reached-use conversions");
          if (auto error = protocol::materializePhysical(*module, checked))
            throw std::runtime_error(llvm::toString(std::move(error)));
          auto program = take(protocol::exportProgram(*module));
          std::string bytes;
          llvm::raw_string_ostream(bytes) << program::encode(program);
          take(protocol::verifyProgramArtifact(*module, bytes));
        });
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
  for (StringRef mutation : {"formula", "site", "origin", "binding contract"})
    cases.run(
        "numerical correspondence refuses actual scoped " + mutation, [&] {
          Fixture fixture(context, samples[0]);
          auto source = projected(fixture);
          PassManager lowering(&context);
          lowering.addPass(protocol::createLowerMathPass());
          require(succeeded(lowering.run(*source)),
                  "numerical source preparation failed");
          auto candidate = computation::proposeComputationRealization(*source);
          require(bool(candidate) &&
                      succeeded(computation::verifyComputationRealization(
                          *source, *candidate)),
                  "scoped numerical positive control failed");
          bool changed = false;
          candidate->walk([&](exec::ApplyOp op) {
            if (changed || op.getInputs().size() != 2 ||
                op.getInputs()[0].getType() != op.getInputs()[1].getType())
              return;
            if (mutation == "formula") {
              auto function = op->getParentOfType<func::FuncOp>();
              mlir::Value alternative;
              for (mlir::Value argument : function.getArguments().drop_front())
                if (argument.getType() == op.getInputs()[0].getType() &&
                    argument != op.getInputs()[0])
                  alternative = argument;
              if (!alternative)
                return;
              op->setOperand(1, alternative);
            } else if (mutation == "site")
              op.setSite("changed_numerical_occurrence");
            else if (mutation == "origin") {
              auto function = op->getParentOfType<func::FuncOp>();
              function->setAttr(
                  "runtime.origin",
                  ArrayAttr::get(&context,
                                 {StringAttr::get(&context, "changed_origin"),
                                  ArrayAttr::get(&context, {})}));
            } else {
              // Replacing one selected arithmetic instruction with another
              // legal binding preserves the scoped ABI while changing its
              // meaning.
              auto binding = dyn_cast<runtime::BindingOp>(
                  SymbolTable::lookupNearestSymbolFrom(op,
                                                       op.getBindingAttr()));
              if (!binding || binding.getContract() != "field.mul")
                return;
              binding.setContract("field.add");
            }
            changed = true;
          });
          require(changed && succeeded(verify(*candidate)),
                  "numerical mutation must remain admitted");
          ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
          require(failed(computation::verifyComputationRealization(*source,
                                                                   *candidate)),
                  "changed scoped numerical candidate accepted");
        });
  auto finiteSource = [&] {
    Fixture fixture(context, samples[7]);
    auto source = projected(fixture);
    PassManager lowering(&context);
    lowering.addPass(protocol::createLowerMathPass());
    require(succeeded(lowering.run(*source)),
            "finite source preparation failed");
    return source;
  };
  for (StringRef quota : {"copy", "sites", "expressions", "reader"})
    cases.run("finite preparation refuses exhausted " + quota, [&] {
      auto source = finiteSource();
      mathematical::RealizationWork work;
      uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
      if (quota == "copy")
        copy = 0;
      if (quota == "sites")
        bytes = 0;
      if (quota == "expressions")
        work.finiteExpressions = 0;
      if (quota == "reader")
        work.requiredFiniteChecking = 0;
      std::optional<CapacityCause> capacity;
      std::string before;
      llvm::raw_string_ostream saved(before);
      source->print(saved);
      ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
      auto candidate =
          protocol::prepareScopedFinite(*source, work, copy, bytes, capacity);
      require(!candidate, "required finite exhaustion published a candidate");
      std::string after;
      llvm::raw_string_ostream current(after);
      source->print(current);
      require(before == after && succeeded(verify(*source)),
              "failed preparation mutated its source");
    });
  cases.run(
      "finite construction exhaustion is bounded at internal boundaries", [&] {
        auto source = finiteSource();
        mathematical::RealizationWork measured;
        uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
        std::optional<CapacityCause> capacity;
        auto complete = protocol::prepareScopedFinite(*source, measured, copy,
                                                      bytes, capacity);
        require(bool(complete), "finite quota measurement refused");
        uint64_t required = 1000000 - copy;
        ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
        for (uint64_t allowance : {required / 4, required / 2, required - 1}) {
          mathematical::RealizationWork work;
          uint64_t available = allowance, sites = 16 * 1024 * 1024;
          capacity.reset();
          auto partial = protocol::prepareScopedFinite(*source, work, available,
                                                       sites, capacity);
          require(!partial && capacity && available <= allowance,
                  "internal finite exhaustion lost required capacity or "
                  "published partial work");
        }
        mathematical::RealizationWork exact;
        bytes = 16 * 1024 * 1024;
        copy = required;
        capacity.reset();
        auto result = protocol::prepareScopedFinite(*source, exact, copy, bytes,
                                                    capacity);
        require(bool(result) && copy == 0,
                "exact finite construction allowance changed semantics");
      });
  for (StringRef mutation : {"domain site", "callback site", "callback operand",
                             "bound", "region premise"})
    cases.run("finite preparation rejects changed " + mutation, [&] {
      auto source = finiteSource();
      mathematical::RealizationWork work;
      uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
      std::optional<CapacityCause> capacity;
      auto candidate =
          protocol::prepareScopedFinite(*source, work, copy, bytes, capacity);
      require(bool(candidate), "finite preparation positive control failed");
      bool changed = false;
      candidate->walk([&](mlir::Operation *op) {
        if (changed)
          return;
        if (auto function = dyn_cast<func::FuncOp>(op);
            function && mutation == "region premise" &&
            function.getSymName().starts_with("_finite_region_")) {
          function->setAttr("data.preconditions", ArrayAttr::get(&context, {}));
          changed = true;
          return;
        }
        auto site = op->getAttrOfType<StringAttr>("site");
        if (mutation == "domain site" && isa<exec::ApplyOp>(op) && site &&
            site.getValue().contains("_finite_")) {
          op->setAttr("site",
                      StringAttr::get(&context, "changed_domain_occurrence"));
          changed = true;
        } else if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
          auto binding = dyn_cast_or_null<runtime::BindingOp>(
              SymbolTable::lookupNearestSymbolFrom(apply,
                                                   apply.getBindingAttr()));
          auto function = apply->getParentOfType<func::FuncOp>();
          if (!binding || binding.getContract() != "field.add" ||
              !function->hasAttr("runtime.region"))
            return;
          if (mutation == "callback site") {
            apply.setSite("changed_callback_occurrence");
            changed = true;
          } else if (mutation == "callback operand" &&
                     apply.getInputs().size() == 2 &&
                     apply.getInputs()[0] != apply.getInputs()[1]) {
            apply->setOperand(1, apply.getInputs()[1]);
            changed = true;
          }
        } else if (auto loop = dyn_cast<exec::RangeOp>(op);
                   loop && mutation == "bound") {
          loop->setOperand(2, loop.getLower());
          changed = true;
        }
      });
      require(changed && succeeded(verify(*candidate)),
              "finite mutation was not admitted");
      ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
      require(failed(protocol::verifyScopedFinitePreparation(*source,
                                                             *candidate, work)),
              "finite correspondence accepted an actual mutation");
    });
  for (unsigned sample : {8u, 9u, 11u})
    for (bool stops : {false, true})
      cases.run(
          std::string(stops ? "stopping scoped finite callback: "
                            : "returning scoped finite callback: ") +
              samples[sample].name,
          [&] {
            Fixture fixture(context, samples[sample]);
            fixture.module = protocol::expandScopedHelpers(*fixture.module);
            require(bool(fixture.module), "finite callback expansion refused");
            auto sourceOwner = cast<protocol_ir::ProtocolModuleOp>(
                fixture.module->getBody()->front());
            mlir::Operation *request = nullptr;
            fixture.module->walk([&](mlir::Operation *op) {
              if (isa<exec::FoldOp, exec::CollectOp>(op))
                request = op;
            });
            require(request != nullptr, "missing ordered finite source");
            finite::Computation computation;
            require(succeeded(finite::describe(request, computation)),
                    "finite source ABI refused");
            // Independently author a small callback against the admitted finite
            // ABI. These tests isolate domain/control lowering from aggregate
            // preparation.
            auto callback = cast<func::FuncOp>(computation.helper);
            auto payload = cast<exec::OutcomeType>(callback.getResultTypes()[0])
                               .getPayload();
            callback.getBody().dropAllReferences();
            callback.getBody().getBlocks().clear();
            callback.addEntryBlock();
            OpBuilder callbackBuilder(&callback.front(),
                                      callback.front().end());
            exec::ScopedExecutionBuilder callbackControl(callbackBuilder,
                                                         callback);
            if (stops)
              callbackControl.reject("reject", "callback_stop");
            else {
              auto values = callback.getArguments().slice(1, payload.size());
              require(llvm::equal(ValueRange(values).getTypes(), payload),
                      "identity callback ports differ");
              callbackControl.returned(values);
            }
            bool erased;
            do {
              erased = false;
              for (auto function : llvm::make_early_inc_range(
                       sourceOwner.getBody().front().getOps<func::FuncOp>()))
                if (function->hasAttr("runtime.region") &&
                    SymbolTable::symbolKnownUseEmpty(function, sourceOwner)) {
                  function.erase();
                  erased = true;
                }
            } while (erased);
            require(succeeded(verify(*fixture.module)),
                    "authored finite source refused");
            auto closure =
                take(protocol::readSourceExecutionClosure(sourceOwner));
            auto location = fixture.module->getLoc();
            OwningOpRef<ModuleOp> candidate(ModuleOp::create(location));
            OpBuilder builder(candidate->getBody(),
                              candidate->getBody()->end());
            auto owner = protocol_ir::ProtocolModuleOp::create(
                builder, location, protocol_ir::Profile::Exec);
            owner.getBody().emplaceBlock();
            builder.setInsertionPointToEnd(&owner.getBody().front());
            SmallVector<mlir::Type> types{runtime::ScopeType::get(&context)};
            llvm::append_range(types, computation.signature.getInputs());
            auto function = func::FuncOp::create(
                builder, location, "finite",
                builder.getFunctionType(
                    types,
                    {exec::OutcomeType::get(
                        &context, SmallVector<mlir::Type>(
                                      computation.signature.getResults()))}));
            function.setPrivate();
            function.setNoInline(true);
            function->setAttr(
                "runtime.origin",
                builder.getArrayAttr({builder.getStringAttr("finite"),
                                      builder.getArrayAttr({})}));
            function.addEntryBlock();
            builder.setInsertionPointToEnd(&function.front());
            exec::ScopedExecutionBuilder control(builder, function);
            auto emit = [&](func::FuncOp helper, ValueRange inputs,
                            StringRef callSite,
                            exec::ScopedExecutionBuilder &scope)
                -> FailureOr<finite::ScopedCallbackResult> {
              require(helper == callback, "unexpected callback identity");
              if (stops) {
                scope.reject("reject", callSite.str() + "_stop");
                return finite::ScopedCallbackResult{{}, true};
              }
              return finite::ScopedCallbackResult{
                  SmallVector<mlir::Value>(inputs.take_front(payload.size())),
                  false};
            };
            mathematical::RealizationWork work;
            MathematicalSelectionPolicy policy;
            policy.finiteBulk = false;
            auto results = finite::realizeScopedExpression(
                request, function.getArguments().drop_front(), builder, control,
                emit, work, policy);
            require(succeeded(results), "scoped finite emission failed");
            control.returned(*results);
            require(succeeded(verify(*candidate)),
                    "scoped finite candidate failed admission");
            auto actual = take(mathematical::ScopedCandidate::read(owner));
            mathematical::CandidatePorts ports(actual.get());
            auto read = [&](func::FuncOp helper, ValueRange inputs, StringRef,
                            mlir::Operation *&at)
                -> FailureOr<finite::ScopedCallbackResult> {
              const auto &body = closure.bodies.at(helper.getSymName().str());
              if (body.size() != 1)
                return failure();
              if (auto reject =
                      dyn_cast<exec::RejectOp>(body.front().operation)) {
                auto stopped = dyn_cast_or_null<exec::RejectOp>(at);
                if (!stopped || stopped.getReason() != reject.getReason())
                  return failure();
                at = ports.next(at);
                return finite::ScopedCallbackResult{{}, true};
              }
              if (!isa<exec::ReturnOp>(body.front().operation))
                return failure();
              SmallVector<mlir::Value> returned;
              for (auto operand : body.front().inputs) {
                auto position = llvm::find(helper.getArguments(), operand);
                if (position == helper.getArguments().end() ||
                    position == helper.getArguments().begin())
                  return failure();
                returned.push_back(
                    inputs[position - helper.getArguments().begin() - 1]);
              }
              return finite::ScopedCallbackResult{returned, false};
            };
            finite::VerificationLimits limits;
            limits.candidate = actual.get();
            limits.callback = read;
            finite::VerificationResult outcome{
                finite::VerificationStatus::Mismatch, {}};
            auto *cursor = ports.first(&function.front());
            auto pure = [](mlir::Operation *, ValueRange, mlir::Operation *&)
                -> FailureOr<SmallVector<mlir::Value>> { return failure(); };
            auto checked = finite::verifyExpression(
                request, function.getArguments().drop_front(), cursor, pure,
                sourceOwner, limits, outcome, policy);
            require(succeeded(checked) && *checked == *results && cursor &&
                        isa<exec::ReturnOp>(cursor),
                    "independent finite traversal differs");
            bool mutated = false;
            if (stops)
              candidate->walk([&](exec::RejectOp reject) {
                reject->setAttr("reason", builder.getStringAttr("abort"));
                mutated = true;
              });
            else
              candidate->walk([&](exec::RangeOp range) {
                if (!mutated && range.getLower() != range.getUpper()) {
                  range->setOperand(2, range.getLower());
                  mutated = true;
                }
              });
            require(mutated && succeeded(verify(*candidate)),
                    "finite mutation must remain ordinarily admitted");
            actual = take(mathematical::ScopedCandidate::read(owner));
            ports = mathematical::CandidatePorts(actual.get());
            limits.candidate = actual.get();
            cursor = ports.first(&function.front());
            require(failed(finite::verifyExpression(
                        request, function.getArguments().drop_front(), cursor,
                        pure, sourceOwner, limits, outcome, policy)),
                    "finite reader accepted a changed bound or stop reason");
          });
  for (bool discharged : {true, false})
    cases.run(
        discharged
            ? "scoped conditional mathematical entry is selectable"
            : "scoped mathematical use must discharge the actual entry premise",
        [&] {
          Fixture fixture(context, samples[20]);
          func::FuncOp conditional;
          fixture.module->walk([&](func::FuncOp function) {
            if (auto premises =
                    function->getAttrOfType<ArrayAttr>("data.preconditions");
                premises && !premises.empty())
              conditional = function;
          });
          require(bool(conditional), "missing conditional entry");
          bool changed = false;
          fixture.module->walk([&](exec::ComputeOp op) {
            auto function = op->getParentOfType<func::FuncOp>();
            if (!changed && function.getNumArguments() == 3 &&
                op.getInputs().size() == 2 &&
                function.getArgument(2).getType() ==
                    op.getInputs()[1].getType()) {
              op->setAttr("callee", FlatSymbolRefAttr::get(
                                        &context, conditional.getSymName()));
              if (!discharged)
                op->setOperand(2, function.getArgument(2));
              changed = true;
            }
          });
          require(changed, "missing conditional invocation");
          if (discharged) {
            require(succeeded(verify(*fixture.module)),
                    "actual static entry premise was lost");
            auto source = projected(fixture);
            PassManager lowering(&context);
            lowering.addPass(protocol::createLowerMathPass());
            require(succeeded(lowering.run(*source)),
                    "conditional computation preparation refused");
            auto candidate =
                computation::proposeComputationRealization(*source);
            require(
                candidate &&
                    succeeded(computation::verifyComputationRealization(
                        *source, *candidate)),
                "conditional computation selection or correspondence refused");
            return;
          }
          ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
          require(failed(verify(*fixture.module)),
                  "undischarged actual premise accepted");
        });
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
  cases.run("origin encoding refuses insufficient positive allowance", [&] {
    uint64_t bytes = 1;
    auto encoded = protocol::algorithmSite({{"call", "helper"}}, "leaf", bytes);
    require(!encoded && bytes == 1,
            "failed origin encoding changed its caller's allowance");
    require(namesIdentifier(llvm::toString(encoded.takeError()),
                            "algorithm-origin-limit"),
            "origin refusal lost its diagnostic identity");
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
    for (unsigned i = 1; i <= 17; ++i) {
      auto prior = "f" + std::to_string(i - 1);
      text += "fn f" + std::to_string(i) + "(x:Fr)->Fr{let y=" + prior +
              "(x);return " + prior + "(y);}\n";
    }
    text += "protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return f17(x);}";
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
  cases.run(
      "all unchanged scoped roots share independent checking allowances", [&] {
        Fixture fixture(context, {"call-free checking", R"(
fn work(x:Fr)->Fr{return x+x;}
protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return work(x);}
)"});
        auto source = projected(fixture);
        auto owner =
            cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front());
        func::FuncOp original;
        for (auto function : owner.getBody().front().getOps<func::FuncOp>())
          if (protocol::isScopedExecutionFunction(function)) {
            original = function;
            break;
          }
        require(bool(original), "missing call-free scoped root");
        OpBuilder builder(&context);
        for (unsigned i = 0; i < 48; ++i) {
          auto clone = original.clone();
          auto name = "unused_" + std::to_string(i);
          clone.setSymName(name);
          clone->setAttr("runtime.origin",
                         builder.getArrayAttr({builder.getStringAttr(name),
                                               builder.getArrayAttr({})}));
          owner.getBody().front().push_back(clone);
        }
        require(succeeded(verify(*source)),
                "unchanged-root source must be admitted");
        mathematical::RealizationWork construction;
        uint64_t constructionCopy = 1000000,
                 constructionSites = 16 * 1024 * 1024;
        std::optional<CapacityCause> constructionCapacity;
        auto candidate = protocol::prepareScopedFinite(
            *source, construction, constructionCopy, constructionSites,
            constructionCapacity);
        require(bool(candidate), "call-free expansion refused");
        mathematical::RealizationWork measured;
        const auto ceiling = measured.numericalContextChecking;
        require(succeeded(protocol::verifyScopedFinitePreparation(
                    *source, *candidate, measured)),
                "call-free checking refused");
        auto required = ceiling - measured.numericalContextChecking;
        require(required > 1, "dormant root inspection was not charged");
        ScopedDiagnosticHandler silence(&context, [](mlir::Diagnostic &) {});
        for (bool sufficient : {false, true}) {
          mathematical::RealizationWork work;
          work.numericalContextChecking = required - unsigned(!sufficient);
          auto checked = protocol::verifyScopedFinitePreparation(
              *source, *candidate, work);
          require(succeeded(checked) == sufficient,
                  "shared checking did not respect the exact whole-inventory "
                  "allowance");
          if (sufficient)
            require(work.numericalContextChecking == 0,
                    "exact allowance was not consumed");
        }
        auto frozen = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
        mathematical::RealizationWork work;
        work.numericalContextChecking = required - 1;
        uint64_t copy = 1000000, sites = 16 * 1024 * 1024;
        std::optional<CapacityCause> capacity;
        auto refused =
            protocol::prepareScopedFinite(*source, work, copy, sites, capacity);
        require(
            !refused && OperationEquivalence::isEquivalentTo(
                            source->getOperation(), frozen->getOperation(),
                            OperationEquivalence::IgnoreLocations),
            "independent checking exhaustion published or mutated a candidate");
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
  for (bool bindingInventory : {false, true})
    cases.run(
        bindingInventory
            ? "scoped expansion retains 4096 bindings independently"
            : "scoped expansion retains 4096 definitions independently",
        [&] {
          auto text = scopedFixture(R"(
"runtime.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
)",
                                    "%x:i1", "%x", "i1", "i1",
                                    scopedReturn("%x", "i1"), 1);
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "inventory fixture");
          auto owner =
              cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
          auto work = SymbolTable(owner).lookup<func::FuncOp>("Work");
          mlir::Operation *prototype = bindingInventory
                                           ? SymbolTable(owner).lookup("and")
                                           : work.getOperation();
          OpBuilder builder(&context);
          builder.setInsertionPoint(prototype);
          auto add = [&](StringRef name) {
            auto *copy = builder.clone(*prototype);
            copy->setAttr("sym_name", builder.getStringAttr(name));
            if (!bindingInventory)
              copy->setAttr("runtime.origin",
                            builder.getArrayAttr({builder.getStringAttr(name),
                                                  builder.getArrayAttr({})}));
            return copy;
          };
          for (unsigned i = 1; i < 4096; ++i)
            add("unused_" + std::to_string(i));
          auto expanded = protocol::expandScopedHelpers(*module);
          require(bool(expanded), "independent expansion inventory refused");
          require(succeeded(protocol::verifyScopedHelperExpansionPreserved(
                      *module, *expanded)),
                  "inventory expansion correspondence refused");
          auto actual = take(protocol::readSourceExecutionClosure(
              cast<protocol_ir::ProtocolModuleOp>(
                  expanded->getBody()->front())));
          require(actual.definitions.bindings.size() ==
                          (bindingInventory ? 4096 : 1) &&
                      actual.definitions.functions.size() ==
                          (bindingInventory ? 1 : 4096),
                  "expansion truncated an inventory");
          add("overflow");
          refuses(protocol::readSourceExecutionClosure(owner),
                  "execution-source-closure");
          ScopedDiagnosticHandler silence(
              &context, [](mlir::Diagnostic &) { return success(); });
          require(!protocol::expandScopedHelpers(*module),
                  "overflow source was expanded");
        });
  cases.run("outlined source bodies do not consume callable inventory", [&] {
    Fixture fixture(context, {"outlined inventory", R"(
fn work(x:bool)->bool{return if x{x}else{x};}
protocol Run roles(P)(x:bool@P)->(r:bool@P){return work(x);}
)"});
    auto owner =
        cast<protocol_ir::ProtocolModuleOp>(fixture.module->getBody()->front());
    func::FuncOp prototype;
    unsigned roots = 0;
    for (auto function : owner.getBody().front().getOps<func::FuncOp>()) {
      if (function->hasAttr("runtime.region"))
        continue;
      prototype = function;
      ++roots;
    }
    require(prototype && roots > 0, "missing source root");
    unsigned outlines = 0;
    for (auto function : owner.getBody().front().getOps<func::FuncOp>())
      outlines += function->hasAttr("runtime.region");
    require(outlines >= 2, "inventory control must contain outlined branches");
    OpBuilder builder(&context);
    builder.setInsertionPoint(prototype);
    for (unsigned i = roots; i < 4096; ++i) {
      auto *copy = builder.clone(*prototype);
      auto name = builder.getStringAttr("extra_" + std::to_string(i));
      copy->setAttr("sym_name", name);
      copy->setAttr("runtime.origin",
                    builder.getArrayAttr({name, builder.getArrayAttr({})}));
    }
    auto expanded = protocol::expandScopedHelpers(*fixture.module);
    require(bool(expanded), "control outlines consumed callable inventory");
    auto actual = take(protocol::readSourceExecutionClosure(
        cast<protocol_ir::ProtocolModuleOp>(expanded->getBody()->front())));
    require(actual.definitions.functions.size() == 4096,
            "outlined expansion changed callable inventory");
  });
  return cases.result();
}
