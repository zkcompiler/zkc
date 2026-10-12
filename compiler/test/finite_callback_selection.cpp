#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/MathematicalTrace.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::mathematical;
namespace {
constexpr llvm::StringLiteral sourceText = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @multiply(%a:!F,%b:!F)->!F {
   %r = algebra.field_multiply %a,%b : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @wrapped(%a:!F,%b:!F)->!F {
   %r = func.call @multiply(%a,%b) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @step(%s:!F,%x:!F,%xs:!V)->!F {
   %r = func.call @wrapped(%s,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%seed:!F)->!F {
   %r = "algebra.finite_fold"(%xs,%seed) {domain=@items,step=@step} : (!V,!F)->!F
   func.return %r : !F
 }
 local.realize @realized = @total : (!V,!F)->!F
 local.func @work(%xs:!V,%seed:!F)->!F attributes {logical_origin=["work",[]]} {
   %r = local.apply @realized(%xs,%seed) {site="realized"} : (!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = "protocol.local_call"(%xs,%seed) {callee=@work,role="P",site="work"} : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr llvm::StringLiteral indexedSourceText = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @update(%state:!F,%x:!F,%y:!F)->!F {
   %p = algebra.field_multiply %x,%y : (!F,!F)->!F
   %r = algebra.field_add %state,%p : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @step(%state:!F,%i:ui64,%xs:!V,%ys:!V)->!F attributes {data.preconditions=[#data.index_bound<1,2,0>,#data.index_bound<1,3,0>]} {
   %x = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   %y = "data.bounded_at"(%ys,%i) : (!V,ui64)->!F
   %r = func.call @update(%state,%x,%y) : (!F,!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%seed:!F,%ys:!V)->!F attributes {data.preconditions=[#data.equal_extent<0,0,2,0>]} {
   %r = "algebra.finite_fold"(%xs,%seed,%ys) {domain=@items,step=@step} : (!V,!F,!V)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = func.call @total(%xs,%seed,%xs) : (!V,!F,!V)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> parse(MLIRContext &context) {
  auto result = parseSourceString<ModuleOp>(sourceText, &context);
  require(bool(result) && succeeded(verify(*result)), "source refused");
  return result;
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(Operation *a, Operation *b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
Operation *fold(ModuleOp source) {
  return &SymbolTable(unit(source))
              .lookup<func::FuncOp>("total")
              .front()
              .front();
}
local::FuncOp selected(ModuleOp candidate) {
  return SymbolTable(unit(candidate)).lookup<local::FuncOp>("selected");
}
bool hasLoop(local::FuncOp function) {
  bool found = false;
  function.walk([&](local::LocalForOp) { found = true; });
  return found;
}
OwningOpRef<ModuleOp> emit(ModuleOp source, RealizationWork &work,
                           bool optimize = true,
                           RealizationTrace *trace = nullptr) {
  auto candidate = copy(source);
  auto total = SymbolTable(unit(*candidate)).lookup<func::FuncOp>("total");
  OpBuilder builder(source.getContext());
  builder.setInsertionPointToEnd(&unit(*candidate).getBody().front());
  auto function = local::FuncOp::create(builder, total.getLoc(), "selected",
                                        total.getFunctionType());
  function->setAttr("logical_origin",
                    builder.getArrayAttr({builder.getStringAttr("selected"),
                                          builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(function.addEntryBlock());
  // Start at the outlined calculation boundary, before finite emission and
  // primitive lowering. The complete reader compares against this original
  // occurrence; all reusable source helpers stay intact.
  IRMapping mapping;
  mapping.map(total.getArguments(), function.getArguments());
  auto *occurrence = builder.clone(*fold(*candidate), mapping);
  occurrence->setAttr("site", builder.getStringAttr("selection"));
  local::ReturnOp::create(builder, total.getLoc(), occurrence->getResults());
  // This service owns both intermediate finite sites and primitive bindings.
  // Pass the same work object through it so optional and required accounting
  // assertions cover the checked candidate, including any ordered fallback.
  require(succeeded(lowerCalculations(unit(*candidate), {function},
                                      {optimize, false}, &work, trace)),
          "checked callback lowering failed");
  require(succeeded(verify(*candidate)), "candidate refused");
  for (auto helper : unit(source).getBody().front().getOps<func::FuncOp>())
    require(
        same(helper, SymbolTable(unit(*candidate)).lookup(helper.getSymName())),
        "source helper changed");
  return candidate;
}
bool compare(ModuleOp source, ModuleOp candidate) {
  auto function = selected(candidate);
  auto *cursor = &function.getBody().front().front();
  // Bulk correspondence must interpret the original func.call closure itself.
  auto noOrderedReader = [](Operation *, ValueRange,
                            Operation *&) -> FailureOr<SmallVector<Value>> {
    return failure();
  };
  auto result = finite::verifyExpression(fold(source), function.getArguments(),
                                         cursor, noOrderedReader, unit(source));
  return succeeded(result) && cursor == &function.getBody().front().back() &&
         result->size() == 1 && (*result)[0] == cursor->getOperand(0);
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool equality : {false, true})
    cases.run(
        equality ? "called callback retains its indexed extent premise"
                 : "called callback does not import caller-only extents",
        [&] {
          auto source =
              parseSourceString<ModuleOp>(indexedSourceText, &context);
          require(bool(source), "indexed fixture refused");
          auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
          if (equality) {
            auto premises =
                step->getAttrOfType<ArrayAttr>("data.preconditions");
            SmallVector<Attribute> attributes(premises.begin(), premises.end());
            attributes.push_back(
                data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
            step->setAttr("data.preconditions",
                          ArrayAttr::get(&context, attributes));
          }
          require(succeeded(verify(*source)), "indexed source refused");
          RealizationWork work;
          RealizationTrace trace;
          auto candidate = emit(*source, work, true, &trace);
          bool observed = false;
          for (const auto &event : trace.events)
            if (auto *decision = std::get_if<SelectionDecision>(&event.payload);
                decision && decision->family == DecisionFamily::Finite) {
              observed = true;
              require(decision->querySubject.declaration == "selected" &&
                          decision->querySubject.site == "selection" &&
                          decision->querySubject.position.empty(),
                      "normalized query reported a synthetic source position");
            }
          require(observed, "missing normalized callback observation");
          bool dot = false;
          selected(*candidate).walk([&](Operation *op) {
            dot |= op->getName().getStringRef() == "algebra.exec.vector_dot";
          });
          require(dot == equality && hasLoop(selected(*candidate)) != equality,
                  "normalization changed the scope of extent evidence");
          if (equality)
            require(compare(*source, *candidate),
                    "original callback reader refused the indexed dot");
        });
  cases.run("called indexed reads retain their own premise scope", [&] {
    auto source = parseSourceString<ModuleOp>(indexedSourceText, &context);
    require(bool(source), "indexed fixture refused");
    auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
    OpBuilder builder(step);
    auto accessed = cast<func::FuncOp>(builder.clone(*step));
    accessed.setSymName("accessed");
    auto premises = step->getAttrOfType<ArrayAttr>("data.preconditions");
    SmallVector<Attribute> attributes(premises.begin(), premises.end());
    attributes.push_back(data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
    step->setAttr("data.preconditions", ArrayAttr::get(&context, attributes));
    step.getBody().getBlocks().clear();
    builder.setInsertionPointToEnd(step.addEntryBlock());
    auto call = func::CallOp::create(builder, step.getLoc(), accessed,
                                     step.getArguments());
    func::ReturnOp::create(builder, step.getLoc(), call.getResults());
    require(succeeded(verify(*source)), "indexed wrapper source refused");
    RealizationWork work;
    auto candidate = emit(*source, work);
    require(hasLoop(selected(*candidate)),
            "selection imported caller-only premises into an indexed callee");
  });
  cases.run("nested reusable calls select without required reserves", [&] {
    auto source = parse(context), original = copy(*source);
    RealizationWork work;
    work.helperOperations = work.helperSlots = work.polynomial = 0;
    auto candidate = emit(*source, work);
    require(!hasLoop(selected(*candidate)) && compare(*source, *candidate),
            "wrapped product did not select or compare against original");
    require(work.matching.structural < 100000 && !work.helperOperations &&
                !work.helperSlots && !work.polynomial &&
                same(*source, *original),
            "selection spent required reserves or changed original");
    auto *result = selected(*candidate)
                       .getBody()
                       .front()
                       .back()
                       .getOperand(0)
                       .getDefiningOp();
    require(result && result->getNumOperands() == 2, "missing seed combiner");
    result->setOperand(0, result->getOperand(1));
    require(succeeded(verify(*candidate)) && !compare(*source, *candidate),
            "wrong seed escaped original callback comparison");
  });
  for (uint64_t capacity :
       {uint64_t(0), uint64_t(1), uint64_t(2), uint64_t(10)})
    cases.run("quiet normalization capacity " + llvm::Twine(capacity), [&] {
      auto source = parse(context);
      RealizationWork work;
      work.matching.structural = capacity;
      unsigned diagnostics = 0;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &) {
        ++diagnostics;
        return success();
      });
      auto candidate = emit(*source, work);
      require(hasLoop(selected(*candidate)) && !diagnostics,
              "optional decline diagnosed or failed to retain ordered path");
      require(work.matching.structural <= capacity &&
                  work.helperOperations < 100000,
              "fallback lost cumulative or mandatory accounting");
    });
  cases.run("disabled selection spends no optional normalization work", [&] {
    auto source = parse(context);
    RealizationWork work;
    auto candidate = emit(*source, work, false);
    require(hasLoop(selected(*candidate)) && work.matching.structural == 100000,
            "disabled policy normalized its callback");
  });
  cases.run("shared callback allowance is not replenished", [&] {
    auto source = parse(context);
    RealizationWork measured;
    auto first = emit(*source, measured);
    require(!hasLoop(selected(*first)), "measurement did not select");
    RealizationWork work;
    work.matching.structural = 100000 - measured.matching.structural;
    auto exact = emit(*source, work);
    require(!hasLoop(selected(*exact)) && !work.matching.structural,
            "exact shared allowance did not select");
    auto next = emit(*source, work);
    require(hasLoop(selected(*next)) && !work.matching.structural,
            "next occurrence replenished normalization work");
  });
  cases.run("comparison retry retains spent normalization work", [&] {
    auto source = parse(context), ordered = copy(*source);
    RealizationWork work, orderedWork;
    require(
        succeeded(expandMathRealizations(*source, {}, &work, {100000, 1})) &&
            succeeded(expandMathRealizations(*ordered, {false, false},
                                             &orderedWork)) &&
            same(*source, *ordered),
        "comparison capacity did not retry the original ordered callback");
    require(work.matching.structural < orderedWork.matching.structural &&
                work.helperOperations == orderedWork.helperOperations &&
                work.helperSlots == orderedWork.helperSlots &&
                work.polynomial == orderedWork.polynomial,
            "retry refilled optional work or consumed ordered reserves");
  });
  cases.run("unused nested finite callback keeps its ordered admission", [&] {
    auto source = parse(context);
    auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
    OpBuilder builder(step);
    auto inner = cast<func::FuncOp>(builder.clone(*step));
    inner.setSymName("inner");
    builder.setInsertionPointToStart(&step.front());
    IRMapping mapping;
    auto *originalFold = fold(*source);
    mapping.map(originalFold->getOperand(0), step.getArgument(2));
    mapping.map(originalFold->getOperand(1), step.getArgument(0));
    auto *unused = builder.clone(*originalFold, mapping);
    unused->setAttr("step", FlatSymbolRefAttr::get(&context, "inner"));
    require(succeeded(verify(*source)), "nested source refused");
    RealizationWork work;
    auto candidate = emit(*source, work);
    bool retained = false;
    selected(*candidate).walk([&](Operation *op) {
      retained |=
          op->getName().getStringRef() == "algebra.exec.vector_product" &&
          bool(op->getParentOfType<local::LocalForOp>());
    });
    require(retained, "selection erased the unused conditional inner fold");
  });
  return cases.result();
}
