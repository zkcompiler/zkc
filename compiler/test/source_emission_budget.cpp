#include "../lib/Translation/Language/EmissionBudget.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
uint64_t operations(mlir::Operation *root) {
  uint64_t count = 0;
  root->walk([&](mlir::Operation *) { ++count; });
  return count - 1; // The outer Module is constructed outside the builder.
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto sourceBudget = [&](llvm::StringRef source) {
    auto project =
        take(analyze(take(capture({{"sample", source.str(), "budget.zkc"}})))
                 .checkedProject());
    auto entry = take(closeNativeRun(project, "sample::Run"));
    auto text = take(emitOriginal(entry, context));
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(module && succeeded(zkc::admitStage(*module)),
            "invalid original fixture");
    const auto count = operations(*module);
    require(count > 1, "empty source fixture");
    Limits exact;
    exact.operations = count;
    auto limited = take(emitOriginal(entry, context, exact));
    require(limited == text, "exact budget changed source emission");
    Limits shortByOne = exact;
    --shortByOne.operations;
    refuses(emitOriginal(entry, context, shortByOne), "source.limit");
    Limits zero = exact;
    zero.operations = 0;
    refuses(emitOriginal(entry, context, zero), "source.limit");
  };
  cases.run("exact source insertion budget includes ordinary helper bodies",
            [&] {
              sourceBudget(R"(module sample;
domain Fr=field("koala-bear");
fn sum(x:Fr,y:Fr)->Fr{return x+y;}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return sum(x,y);}
)");
            });
  for (bool mathematical : {false, true})
    cases.run(mathematical ? "total finite adapters share the source budget"
                           : "ordered finite adapters share the source budget",
              [&] {
                std::string mode = mathematical ? "math " : "";
                std::string effects = mathematical ? "" : " effects(stop)";
                sourceBudget(std::string(R"(module sample;
domain Fr=field("koala-bear");
struct Row {pub a:Fr,pub b:Fr}
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
)") + mode +
                             "fn "
                             "fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:"
                             "domain<I>,initial:S,step:" +
                             mode + "fn(S,item:I)->S" + effects +
                             " where item_from(item, rows))->S" + effects +
                             "=finite(\"" +
                             (mathematical ? "math.fold" : "local.fold") +
                             R"(");
protocol Run roles(P)(xs:[Row;3]@P,shift:Fr@P)->(r:Fr@P){return fold(array(xs),0,fn(state,row)=>state+row.a+row.b+shift);}
)");
              });
  cases.run("packed sequence callback operations share the source budget", [&] {
    sourceBudget(R"(module sample;
domain Fr=field("koala-bear");
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
struct Row {pub value:Fr,pub enabled:bool}
domain fn elements<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<I>,body:fn(item:I)->B effects(stop) where item_from(item, rows))->Sequence<B> effects(stop)=finite("local.collect.sequence");
protocol Run roles(P)(xs:Sequence<Row>@P)->(r:Sequence<Row>@P){return collect(elements(xs),fn(row)=>row);}
)");
  });
  for (uint64_t limit : {uint64_t(0), uint64_t(100)})
    cases.run(
        "delegated CFG insertions debit shared budget " + std::to_string(limit),
        [&] {
          EmissionBudget budget(limit);
          OpBuilder builder(&context, &budget);
          auto location = builder.getUnknownLoc();
          OwningOpRef<ModuleOp> module(ModuleOp::create(location));
          builder.setInsertionPointToEnd(module->getBody());
          auto scope = runtime::ScopeType::get(&context);
          auto outcome =
              exec::OutcomeType::get(&context, {builder.getI1Type()});
          auto function =
              func::FuncOp::create(builder, location, "body",
                                   builder.getFunctionType(scope, outcome));
          function.addEntryBlock();
          builder.setInsertionPointToEnd(&function.front());
          exec::ScopedExecutionBuilder control(builder, function);
          auto value = control.invoke(
              "exec.boolean", builder.getI1Type(), control.getScope(),
              {builder.getNamedAttr("site", builder.getStringAttr("literal")),
               builder.getNamedAttr("value", builder.getBoolAttr(true))});
          control.complete(value);
          require(succeeded(verify(*module)), "formed delegated body refused");
          require(budget.count() == operations(*module) && budget.count() > 2 &&
                      budget.allows() == (limit != 0),
                  "delegated operations escaped the shared count");
        });
  return cases.result();
}
