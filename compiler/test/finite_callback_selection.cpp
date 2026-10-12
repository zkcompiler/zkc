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
  cases.run(
      "called indexed reads retain the original callback premise scope", [&] {
        auto source = parseSourceString<ModuleOp>(indexedSourceText, &context);
        require(bool(source), "indexed fixture refused");
        auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
        OpBuilder builder(step);
        auto accessed = cast<func::FuncOp>(builder.clone(*step));
        accessed.setSymName("accessed");
        auto premises = step->getAttrOfType<ArrayAttr>("data.preconditions");
        SmallVector<Attribute> attributes(premises.begin(), premises.end());
        attributes.push_back(data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
        step->setAttr("data.preconditions",
                      ArrayAttr::get(&context, attributes));
        step.getBody().getBlocks().clear();
        builder.setInsertionPointToEnd(step.addEntryBlock());
        auto call = func::CallOp::create(builder, step.getLoc(), accessed,
                                         step.getArguments());
        func::ReturnOp::create(builder, step.getLoc(), call.getResults());
        require(succeeded(verify(*source)), "indexed wrapper source refused");
        RealizationWork work;
        auto candidate = emit(*source, work);
        require(!hasLoop(selected(*candidate)) && compare(*source, *candidate),
                "indexed callee lost the original callback extent premise");
      });
  for (bool equality : {false, true})
    for (bool repeated : {false, true})
      cases.run(
          std::string("nested access argument identity ") +
              (equality ? "with extent " : "without extent ") +
              (repeated ? "repeated" : "distinct"),
          [&] {
            std::string text(indexedSourceText);
            auto start = text.find("   %x = \"data.bounded_at\"");
            auto end = text.find("   func.return %r : !F", start);
            require(start != std::string::npos && end != std::string::npos,
                    "missing indexed body");
            text.replace(
                start, end - start,
                "   %y, %ys2 = func.call @load(%ys,%i) : (!V,ui64)->(!F,!V)\n"
                "   %x, %xs2 = func.call @load(" +
                    std::string(repeated ? "%ys2" : "%xs") +
                    ",%i) : (!V,ui64)->(!F,!V)\n"
                    "   %r = func.call @update(%state,%x,%y) : "
                    "(!F,!F,!F)->!F\n");
            text.insert(text.find(" func.func private @step"), R"mlir(
 func.func private @leaf(%i:ui64,%xs:!V)->(!V,!F) attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %x = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   func.return %xs,%x : !V,!F
 }
 func.func private @load(%xs:!V,%i:ui64)->(!F,!V) attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
   %v,%x = func.call @leaf(%i,%xs) : (ui64,!V)->(!V,!F)
   func.return %x,%v : !F,!V
 }
)mlir");
            auto source = parseSourceString<ModuleOp>(text, &context);
            require(bool(source), "nested indexed source refused");
            auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
            if (equality) {
              auto premises =
                  step->getAttrOfType<ArrayAttr>("data.preconditions");
              SmallVector<Attribute> attributes(premises.begin(),
                                                premises.end());
              attributes.push_back(
                  data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
              step->setAttr("data.preconditions",
                            ArrayAttr::get(&context, attributes));
            }
            require(succeeded(verify(*source)),
                    "nested indexed formation failed");
            RealizationWork work;
            auto candidate = emit(*source, work);
            require(hasLoop(selected(*candidate)) != equality,
                    "nested selection confused bound and extent premises");
            if (!equality)
              return;
            require(compare(*source, *candidate),
                    "reader lost root facts when the leaf omitted the domain "
                    "anchor");
            auto withoutEquality = copy(*source);
            auto unqualifiedStep = SymbolTable(unit(*withoutEquality))
                                       .lookup<func::FuncOp>("step");
            SmallVector<Attribute> bounds;
            for (Attribute premise : unqualifiedStep->getAttrOfType<ArrayAttr>(
                     "data.preconditions"))
              if (!isa<data::EqualExtentAttr>(premise))
                bounds.push_back(premise);
            unqualifiedStep->setAttr("data.preconditions",
                                     ArrayAttr::get(&context, bounds));
            require(succeeded(verify(*withoutEquality)) &&
                        !compare(*withoutEquality, *candidate),
                    "reader imported a missing callback premise from the outer "
                    "caller");
            Operation *dot = nullptr;
            selected(*candidate).walk([&](Operation *op) {
              if (op->getName().getStringRef() == "algebra.exec.vector_dot")
                dot = op;
            });
            require(dot, "nested access did not select dot");
            // Same shape never permits replacing one captured container's
            // values.
            dot->setOperand(0,
                            selected(*candidate).getArgument(repeated ? 0 : 2));
            dot->setOperand(1,
                            selected(*candidate).getArgument(repeated ? 0 : 2));
            require(
                succeeded(verify(*candidate)) && !compare(*source, *candidate),
                "reader equated distinct containers or lost repeated actuals");
          });
  for (bool aliased : {false, true})
    cases.run(
        aliased ? "aliased formals and returned index"
                : "distinct formals and returned index",
        [&] {
          std::string text(indexedSourceText);
          auto start = text.find("   %x = \"data.bounded_at\"");
          auto end = text.find("   %r = func.call @update", start);
          text.replace(
              start, end - start,
              "   %right,%j,%left = func.call @positions(%xs," +
                  std::string(aliased ? "%xs" : "%ys") +
                  ",%i) : (!V,!V,ui64)->(!V,ui64,!V)\n"
                  "   %x = \"data.bounded_at\"(%left,%j) : (!V,ui64)->!F\n"
                  "   %y = \"data.bounded_at\"(%right,%j) : (!V,ui64)->!F\n");
          text.insert(text.find(" func.func private @step"), R"mlir(
 func.func private @positions(%left:!V,%right:!V,%i:ui64)->(!V,ui64,!V) {
   func.return %right,%i,%left : !V,ui64,!V
 }
)mlir");
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source), "alias source refused");
          auto step = SymbolTable(unit(*source)).lookup<func::FuncOp>("step");
          auto premises = step->getAttrOfType<ArrayAttr>("data.preconditions");
          SmallVector<Attribute> attributes(premises.begin(), premises.end());
          attributes.push_back(
              data::EqualExtentAttr::get(&context, 2, 0, 3, 0));
          step->setAttr("data.preconditions",
                        ArrayAttr::get(&context, attributes));
          require(succeeded(verify(*source)), "returned index lost formation");
          RealizationWork work;
          auto candidate = emit(*source, work);
          require(!hasLoop(selected(*candidate)) &&
                      compare(*source, *candidate),
                  "same-typed actuals or returned index lost their identities");
          Operation *dot = nullptr;
          selected(*candidate).walk([&](Operation *op) {
            if (op->getName().getStringRef() == "algebra.exec.vector_dot")
              dot = op;
          });
          require(dot, "missing alias contraction");
          dot->setOperand(0, selected(*candidate).getArgument(aliased ? 2 : 0));
          dot->setOperand(1, selected(*candidate).getArgument(aliased ? 2 : 0));
          require(succeeded(verify(*candidate)) &&
                      !compare(*source, *candidate),
                  "alias mapping accepted a changed container");
        });
  for (bool row : {false, true})
    cases.run(
        row ? "nested selected matrix row" : "nested selected matrix column",
        [&] {
          std::string text = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!M = !algebra.field_matrix<"koala-bear">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @cell(%m:!M,%r:ui64,%c:ui64)->!F attributes {data.preconditions=[#data.index_bound<1,0,0>,#data.index_bound<2,0,1>]} {
   %x = "data.bounded_matrix_at"(%m,%r,%c) : (!M,ui64,ui64)->!F
   func.return %x : !F
 }
 func.func private @step(%s:!F,%i:ui64,%xs:!V,%m:!M,%selected:ui64)->!F attributes {data.preconditions=[#data.index_bound<1,2,0>,#data.index_bound<1,3,VARYING>,#data.index_bound<4,3,FIXED>,#data.equal_extent<2,0,3,VARYING>]} {
   %x = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   %y = func.call @cell(%m,ROW,COLUMN) : (!M,ui64,ui64)->!F
   %p = algebra.field_multiply %x,%y : (!F,!F)->!F
   %r = algebra.field_add %s,%p : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%seed:!F,%m:!M,%selected:ui64)->!F attributes {data.preconditions=[#data.equal_extent<0,0,2,VARYING>,#data.index_bound<3,2,FIXED>]} {
   %r = "algebra.finite_fold"(%xs,%seed,%m,%selected) {domain=@items,step=@step} : (!V,!F,!M,ui64)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ "protocol.return"() : ()->() }) {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
          auto replace = [&](StringRef from, StringRef to) {
            size_t offset = 0;
            while ((offset = text.find(from.str(), offset)) !=
                   std::string::npos) {
              text.replace(offset, from.size(), to.str());
              offset += to.size();
            }
          };
          replace("VARYING", row ? "1" : "0");
          replace("FIXED", row ? "0" : "1");
          replace("ROW", row ? "%selected" : "%i");
          replace("COLUMN", row ? "%i" : "%selected");
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) && succeeded(verify(*source)),
                  "matrix helper fixture refused");
          RealizationWork work;
          auto candidate = emit(*source, work);
          require(
              !hasLoop(selected(*candidate)) && compare(*source, *candidate),
              "nested matrix access lost its axis or fixed selector premise");
          Operation *dot = nullptr, *length = nullptr;
          selected(*candidate).walk([&](Operation *op) {
            if (op->getName().getStringRef() ==
                (row ? "algebra.exec.matrix_row_dot"
                     : "algebra.exec.matrix_column_dot"))
              dot = op;
            if (op->getName().getStringRef() == "algebra.exec.vector_length")
              length = op;
          });
          require(dot && length,
                  "matrix contraction or domain admission missing");
          dot->setOperand(2, length->getResult(0));
          require(succeeded(verify(*candidate)) &&
                      !compare(*source, *candidate),
                  "reader accepted a different fixed selector");
        });
  cases.run("unused callee algebra retains the checked ordered body", [&] {
    std::string text(indexedSourceText);
    auto replace = [&](std::string from, std::string to) {
      size_t at = 0;
      while ((at = text.find(from, at)) != std::string::npos) {
        text.replace(at, from.size(), to);
        at += to.size();
      }
    };
    replace("!V = !algebra.field_vector<\"koala-bear\">",
            "!V = !algebra.field_vector<\"koala-bear\">\n!G = "
            "!algebra.group<\"bn254.g1\">");
    replace("%ys:!V)->!F", "%ys:!V,%g:!G)->!F");
    replace("#data.index_bound<1,3,0>]",
            "#data.index_bound<1,3,0>,#data.equal_extent<2,0,3,0>]");
    replace("   %x = \"data.bounded_at\"",
            "   %unused = func.call @nonfield(%g) : (!G)->!G\n   %x = "
            "\"data.bounded_at\"");
    text.insert(
        text.find(" func.func private @step"),
        "func.func private @nonfield(%g:!G)->!G {\n %r=algebra.group_add %g,%g "
        ": (!G,!G)->!G\nfunc.return %r : !G\n}\n");
    replace("(%xs,%seed,%ys)", "(%xs,%seed,%ys,%g)");
    replace("(!V,!F,!V)->!F", "(!V,!F,!V,!G)->!F");
    auto begin = text.find(" \"protocol.func\"");
    auto end = text.find("}) {profile=", begin);
    text.replace(begin, end - begin,
                 "\"protocol.func\"() ({ \"protocol.return\"() : ()->() }) "
                 "{sym_name=\"main\",function_type=()->(),roles=[\"P\"],input_"
                 "roles=[],output_roles=[]} : ()->()\n");
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source) && succeeded(verify(*source)), "bad fixture");
    RealizationWork work;
    RealizationTrace trace;
    auto candidate = emit(*source, work, true, &trace);
    require(hasLoop(selected(*candidate)),
            "mixed-algebra work entered field-only comparison");
    bool observed = false;
    for (const auto &event : trace.events)
      if (auto *decision = std::get_if<SelectionDecision>(&event.payload);
          decision && decision->family == DecisionFamily::Finite)
        observed |= decision->outcome.reason ==
                    OptimizationReason::ImplementationRestriction;
    require(observed, "mixed-algebra restriction lost its explanation");
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
