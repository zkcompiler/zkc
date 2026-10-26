#include "../lib/Translation/Language/EmissionBudget.h"
#include "../lib/Translation/Language/Finite.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include <limits>

using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
using Values = llvm::SmallVector<mlir::Value>;
using Types = llvm::SmallVector<mlir::Type>;
const std::string prelude = R"(module m;
domain Fr=field("koala-bear");
type Vector<F:Field>=builtin("vector",F);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
struct Row {pub a:Fr,pub b:Fr}
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
domain fn vector<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold");
fn filtered<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item,rows),step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S effects(stop)=finite("local.fold_where");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<I>,body:fn(item:I)->B effects(stop) where item_from(item,rows))->Sequence<B> effects(stop)=finite("local.collect.sequence");
)";
struct Sample {
  const char *name, *source;
};
const Sample samples[] = {{"scalar captures and predicate", R"(
fn work(xs:Vector<Fr>,seed:Fr,shift:Fr,enabled:bool)->Fr{return filtered(vector(xs),seed,fn(item)=>enabled,fn(state,item)=>shift);}
protocol Demo roles(P)(xs:Vector<Fr>@P,seed:Fr@P,shift:Fr@P,enabled:bool@P)->(r:Fr@P){return work(xs,seed,shift,enabled);}
)"},
                          {"source array of products", R"(
fn work(xs:[Row;2],seed:Row)->Row{return fold(array(xs),seed,fn(state,item)=>state);}
protocol Demo roles(P)(xs:[Row;2]@P,seed:Row@P)->(r:Row@P){return work(xs,seed);}
)"},
                          {"sequence of products", R"(
fn work(xs:Sequence<Row>)->Sequence<Row>{return collect(elements(xs),fn(item)=>item);}
protocol Demo roles(P)(xs:Sequence<Row>@P)->(r:Sequence<Row>@P){return work(xs);}
)"},
                          {"zero-state fold", R"(
fn work(xs:Sequence<()>,seed:())->(){return fold(elements(xs),seed,fn(state,item)=>state);}
protocol Demo roles(P)(xs:Sequence<()>@P,seed:()@P)->(r:()@P){return work(xs,seed);}
)"},
                          {"sequence of Unit", R"(
fn work(xs:Sequence<()>)->Sequence<()>{return collect(elements(xs),fn(item)=>item);}
protocol Demo roles(P)(xs:Sequence<()>@P)->(r:Sequence<()>@P){return work(xs);}
)"}};
class Fixture {
public:
  MLIRContext &context;
  CheckedProject checked;
  ClosedEntry project;
  Layouts layouts;
  const Body *source = nullptr;
  const FiniteComputation *finite = nullptr;
  const language::Type *resultType = nullptr;
  OwningOpRef<ModuleOp> module;
  func::FuncOp caller;
  std::vector<Values> values;
  uint64_t inserted = 0;
  uint64_t comparedOperations = 0;
  Types types(const language::Type &type) {
    Types result;
    auto layout = take(layouts.get(type));
    for (const auto &leaf : layout->leaves) {
      require(leaf.data(), "fixture needs native data");
      result.push_back(protocol::decodeBoundType(
          &context, take(protocol::parseBoundType(*leaf.data(), false))));
    }
    return result;
  }
  Fixture(MLIRContext &context, const Sample &sample)
      : context(context),
        checked(take(analyze(take(capture({{"m", prelude + sample.source,
                                            "finite-execution.zkc"}})))
                         .checkedProject())),
        project(take(closeNativeRun(checked, "m::Demo"))), layouts(project) {
    for (const auto &decl : project.declarations())
      if (decl.body && llvm::any_of(decl.body->operations, [](const auto &op) {
            return std::holds_alternative<FiniteComputation>(op.action);
          }))
        source = &*decl.body;
    require(source && source->operations.size() == 1,
            "expected direct finite source");
    const auto &operation = source->operations.front();
    finite = std::get_if<FiniteComputation>(&operation.action);
    require(finite && operation.results.size() == 1,
            "expected finite occurrence");
    resultType = &source->values[operation.results.front().index].type;
    EmissionBudget budget(std::numeric_limits<uint64_t>::max());
    OpBuilder builder(&context, &budget);
    auto loc = builder.getUnknownLoc();
    module = ModuleOp::create(loc);
    builder.setInsertionPointToEnd(module->getBody());
    // These declarations expose only the source helpers' actual ports. This
    // test covers finite adapters; ordinary helper-body correspondence belongs
    // to the enclosing source checker and is not established by this fixture.
    for (const FiniteCallback *callback :
         {&finite->body, finite->predicate ? &*finite->predicate : nullptr}) {
      if (!callback)
        continue;
      const auto &decl = project.declarations()[callback->helper.index];
      Types inputs{runtime::ScopeType::get(&context)}, outputs;
      for (const auto &input : decl.inputs)
        llvm::append_range(inputs, types(input.type));
      for (const auto &output : decl.outputs)
        llvm::append_range(outputs, types(output.type));
      auto function = func::FuncOp::create(
          builder, loc, decl.symbol,
          builder.getFunctionType(inputs,
                                  exec::OutcomeType::get(&context, outputs)));
      function.setPrivate();
    }
    Types inputs{runtime::ScopeType::get(&context)};
    for (unsigned i = 0; i < source->inputs; ++i)
      llvm::append_range(inputs, types(source->values[i].type));
    caller = func::FuncOp::create(
        builder, loc, "caller",
        builder.getFunctionType(
            inputs, exec::OutcomeType::get(&context, types(*resultType))));
    caller.setPrivate();
    caller->setAttr("no_inline", builder.getUnitAttr());
    caller.addEntryBlock();
    values.resize(source->values.size());
    unsigned offset = 1;
    for (unsigned i = 0; i < source->inputs; ++i) {
      auto width = types(source->values[i].type).size();
      values[i] = Values(caller.getArguments().slice(offset, width));
      offset += width;
    }
    builder.setInsertionPointToEnd(&caller.front());
    exec::ScopedExecutionBuilder control(builder, caller);
    uint64_t remaining = Limits{}.work;
    auto result =
        take(emitFinite(project, *source, *finite, *resultType, values, builder,
                        loc, *module->getBody(), layouts, "finite",
                        "source_finite", budget, remaining, &control));
    control.returned(result);
    inserted = budget.count();
    require(succeeded(verify(*module)),
            "scoped source adapter formation failed");
    module->walk([&](func::FuncOp function) {
      if (!function.isExternal())
        require(succeeded(runtime::verifyScopeOwnership(function)),
                "adapter scope ownership failed");
    });
  }
  llvm::Expected<Values> compare(const Limits &limits = {},
                                 const Body *body = nullptr) {
    std::map<std::string, mlir::Operation *> definitions;
    for (auto &op : *module->getBody())
      if (auto name = SymbolTable::getSymbolName(&op))
        definitions.emplace(name.getValue().str(), &op);
    std::set<mlir::Operation *> used;
    auto &block = caller.front();
    auto position = block.begin();
    unsigned cursorWork = 1000000;
    exec::ControlCursor control(caller, cursorWork);
    require(control.enter(&block), "caller CFG entry failed");
    uint64_t operations = 0, remaining = limits.work;
    auto result = compareFinite(
        project, body ? *body : *source, *finite, *resultType, values, block,
        position, definitions, used, layouts, "finite", "source_finite", limits,
        operations, remaining, &control);
    if (!result)
      return result.takeError();
    auto returned = dyn_cast_or_null<exec::ReturnOp>(control.take());
    auto ret = dyn_cast_or_null<func::ReturnOp>(control.take());
    require(returned && returned.getValues() == ValueRange(*result) && ret &&
                ret.getOperands() == ValueRange{returned.getOutcome()} &&
                control.complete(),
            "comparison did not reach the actual source return");
    require(operations > 0 && operations < inserted,
            "CFG accounting escaped source budget");
    comparedOperations = operations;
    return result;
  }
  mlir::Operation *find(llvm::StringRef name, llvm::StringRef within = {}) {
    mlir::Operation *result = nullptr;
    module->walk([&](mlir::Operation *op) {
      auto parent = op->getParentOfType<func::FuncOp>();
      if (!result && op->getName().getStringRef() == name &&
          (within.empty() || (parent && parent.getSymName() == within)))
        result = op;
    });
    require(result, "mutation target missing");
    return result;
  }
};
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  for (const auto &sample : samples)
    cases.run(sample.name, [&] {
      Fixture fixture(context, sample);
      take(fixture.compare());
    });
  for (unsigned mutation = 0; mutation < 9; ++mutation)
    cases.run(
        "independent scoped finite mutation " + std::to_string(mutation), [&] {
          Fixture fixture(context, samples[mutation < 4 ? 0 : 2]);
          OpBuilder builder(&context);
          if (mutation == 0) {
            auto *call = fixture.find("func.call", "finite_body");
            // A same-typed fold state must not replace the captured shift.
            call->setOperand(call->getNumOperands() - 1, call->getOperand(1));
          } else if (mutation == 1)
            fixture.find("exec.fold")
                ->setAttr("site", builder.getStringAttr("elsewhere"));
          else if (mutation == 2)
            fixture.find("func.call", "finite_predicate")
                ->setAttr("runtime.site", builder.getStringAttr("other"));
          else if (mutation == 3) {
            auto *op = fixture.find("exec.returned", "finite_body");
            builder.setInsertionPoint(op);
            mlir::OperationState replacement(op->getLoc(), "exec.complete");
            replacement.addTypes(op->getResultTypes());
            Values operands{op->getParentOfType<func::FuncOp>().getArgument(0)};
            llvm::append_range(operands, op->getOperands());
            replacement.addOperands(operands);
            auto *charged = builder.create(replacement);
            op->getResult(0).replaceAllUsesWith(charged->getResult(0));
            op->erase();
          } else if (mutation == 4) {
            auto *op = fixture.find("exec.variant");
            auto first = op->getOperand(1);
            op->setOperand(1, op->getOperand(2));
            op->setOperand(2, first);
          } else if (mutation == 5)
            fixture.find("exec.complete")
                ->setOperand(1, fixture.find("exec.complete")->getOperand(2));
          else if (mutation == 6) {
            auto function =
                fixture.find("exec.complete")->getParentOfType<func::FuncOp>();
            function->removeAttr("runtime.region");
          } else if (mutation == 7) {
            auto *op = fixture.find("exec.dispatch", "finite_body");
            op->setSuccessor(op->getSuccessor(0), 1);
          } else {
            auto function = fixture.find("exec.returned", "finite_body")
                                ->getParentOfType<func::FuncOp>();
            auto *block = new Block;
            function.getBody().push_back(block);
            builder.setInsertionPointToEnd(block);
            auto stop =
                exec::StopOp::create(builder, function.getLoc(), "extra");
            auto failed = exec::FailureOp::create(builder, function.getLoc(),
                                                  function.getResultTypes()[0],
                                                  stop.getStop());
            func::ReturnOp::create(builder, function.getLoc(),
                                   failed.getOutcome());
          }
          refuses(fixture.compare(), "source.correspondence");
        });
  for (bool work : {false, true})
    cases.run(work ? "scoped finite work limit"
                   : "scoped finite operation limit",
              [&] {
                Fixture fixture(context, samples[2]);
                Limits limits;
                if (work)
                  limits.work = 1;
                else
                  limits.operations = 1;
                refuses(fixture.compare(limits), "source.limit");
              });
  for (const auto &sample : samples)
    cases.run(std::string("exact CFG comparison budget: ") + sample.name, [&] {
      Fixture fixture(context, sample);
      take(fixture.compare());
      auto required = fixture.comparedOperations;
      Limits limits;
      limits.operations = required;
      take(fixture.compare(limits));
      for (uint64_t cap = 0; cap < required; ++cap) {
        limits.operations = cap;
        refuses(fixture.compare(limits), "source.limit");
      }
    });
  cases.run("scoped producer refuses a mathematical source body", [&] {
    Fixture fixture(context, samples[0]);
    Body mathematical = *fixture.source;
    mathematical.mode = Body::Mode::Math;
    EmissionBudget budget(1000);
    OpBuilder builder(&context, &budget);
    exec::ScopedExecutionBuilder control(builder, fixture.caller);
    uint64_t remaining = Limits{}.work;
    refuses(emitFinite(fixture.project, mathematical, *fixture.finite,
                       *fixture.resultType, fixture.values, builder,
                       builder.getUnknownLoc(), *fixture.module->getBody(),
                       fixture.layouts, "invalid", "invalid", budget, remaining,
                       &control),
            "source.emission");
    require(budget.count() == 0, "mode refusal inserted operations");
  });
  cases.run("scoped comparator refuses a mathematical source body", [&] {
    Fixture fixture(context, samples[0]);
    Body mathematical = *fixture.source;
    mathematical.mode = Body::Mode::Math;
    refuses(fixture.compare({}, &mathematical), "source.correspondence");
  });
  return cases.result();
}
