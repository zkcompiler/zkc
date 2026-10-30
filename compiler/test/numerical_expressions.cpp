#include "../lib/Transforms/LaneRealization.h"
#include "../lib/Transforms/MathematicalComparison.h"
#include "../lib/Transforms/MathematicalRecipes.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "../lib/Transforms/ScopedPreparation.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationRecipes.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> copy(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
std::string replaceText(std::string text, StringRef from, StringRef to) {
  size_t at = text.find(from.str());
  require(at != std::string::npos, "missing replacement " + from);
  text.replace(at, from.size(), to.str());
  return text;
}
std::string fieldText(std::string text, StringRef field,
                      StringRef original = "koala-bear") {
  size_t at = 0;
  while ((at = text.find(original.str(), at)) != std::string::npos) {
    text.replace(at, original.size(), field.str());
    at += field.size();
  }
  auto literalWidth = [](StringRef domain) -> unsigned {
    if (domain == "bls12-381.fr")
      return 255;
    if (domain == "bn254.fr")
      return 254;
    if (domain == "ristretto255.scalar")
      return 253;
    if (domain.starts_with("koala-bear"))
      return 31;
    if (domain == "gf2-64.pentanomial-4-3-1")
      return 64;
    require(domain == "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
            "missing fixture field presentation");
    return 192;
  };
  auto oldWidth = " : ui" + std::to_string(literalWidth(original)) + ">";
  auto newWidth = " : ui" + std::to_string(literalWidth(field)) + ">";
  at = 0;
  while ((at = text.find(oldWidth, at)) != std::string::npos) {
    text.replace(at, oldWidth.size(), newWidth);
    at += newWidth.size();
  }
  return text;
}
OwningOpRef<ModuleOp> prepareMap(
    ModuleOp source,
    NumericalExpressionMode mode = NumericalExpressionMode::PreferNative) {
  MathematicalSelectionPolicy policy;
  policy.numericalExpressions = mode;
  return sf::prepare(source, policy);
}
LogicalResult compareMap(ModuleOp source, ModuleOp candidate) {
  return sf::compare(source, candidate);
}
Operation *operation(ModuleOp module, StringRef contract) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto declaration =
        reference ? SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                        op, reference)
                  : runtime::BindingOp{};
    if (declaration && declaration.getContract() == contract)
      result = op;
  });
  return result;
}
Value payload(Operation *operation) {
  auto dispatch = dyn_cast_or_null<exec::DispatchOp>(operation->getNextNode());
  require(dispatch && dispatch.getReturned()->getNumArguments() == 1,
          "missing actual outcome payload");
  return dispatch.getReturned()->getArgument(0);
}
void omit(Operation *operation, Value replacement) {
  auto dispatch = cast<exec::DispatchOp>(operation->getNextNode());
  auto *continuation = dispatch.getReturned();
  auto *before = operation->getBlock();
  dispatch.erase();
  operation->erase();
  IRRewriter rewriter(replacement.getContext());
  rewriter.mergeBlocks(continuation, before, {replacement});
}
runtime::BindingOp binding(Operation *op) {
  require(op != nullptr, "missing numerical call");
  auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
  require(bool(reference), "missing numerical binding reference");
  return cast<runtime::BindingOp>(
      SymbolTable::lookupNearestSymbolFrom(op, reference));
}
std::string expression(Operation *op) {
  return take(algebra::encodeRingExpression(cast<algebra::RingExpressionAttr>(
      op->getAttrOfType<ArrayAttr>("parameters")[0])));
}
void expression(Operation *op, StringRef body) {
  OpBuilder builder(op);
  op->setAttr("parameters",
              builder.getArrayAttr({take(algebra::importRingExpression(
                  op->getContext(), take(ring::readExpressionText(body))))}));
}
void mutateBody(Operation *op, llvm::function_ref<void(json::Array &)> edit) {
  auto value = take(ring::readExpressionText(expression(op))).encode();
  edit(*value.getAsArray());
  expression(op, printJson(value));
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  auto source = parseSourceString<ModuleOp>(text, &context);
  require(bool(source) && succeeded(verify(*source)),
          "numerical source refused");
  return source;
}
constexpr StringLiteral foldText = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%s:!F,%x:!F,%xs:!V,%a:!F)->!F {
   %sq = algebra.field_multiply %x,%x : (!F,!F)->!F
   %t = algebra.field_add %sq,%a : (!F,!F)->!F
   %r = algebra.field_add %s,%t : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%seed:!F,%a:!F)->!F {
   %r = "algebra.finite_fold"(%xs,%seed,%a) {domain=@items,step=@step} : (!V,!F,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
// Executable callbacks carry explicit pins, including unused reached work.
// The mathematical source above has no physical binding choices.
constexpr StringLiteral scopedFoldText = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : ()->()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["koala-bear"],implementation="",function_type=(!runtime.scope, !algebra.field<"koala-bear">, !algebra.field<"koala-bear">) -> !exec.outcome<(!algebra.field<"koala-bear">)>} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%s:!F,%x:!F,%xs:!V,%a:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["step",[]]} {
   %square = "exec.apply"(%scope,%x,%x) {binding=@mul,parameters=[],site="square"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%square)[^square,^failed] : (!exec.outcome<(!F)>)->()
 ^square(%sq:!F):
   %term = "exec.apply"(%scope,%sq,%a) {binding=@add,parameters=[],site="term"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%term)[^term,^failed] : (!exec.outcome<(!F)>)->()
 ^term(%t:!F):
   %combined = "exec.apply"(%scope,%s,%t) {binding=@add,parameters=[],site="combine"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%combined)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%r:!F):
   %result = "exec.returned"(%r) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 func.func @work(%scope:!runtime.scope,%xs:!V,%seed:!F,%a:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.fold"(%scope,%xs,%seed,%a) {domain=@items,step=@step,site="realized"} : (!runtime.scope,!V,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%r)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F,%a:!F):
   %r = "protocol.local_call"(%xs,%seed,%a) {callee=@work,role="P",site="work"} : (!V,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
OwningOpRef<ModuleOp> emitFold(ModuleOp source,
                               MathematicalSelectionPolicy policy = {},
                               RealizationWork *available = nullptr) {
  auto numerical = computationRecipeSource(unit(source), "total", "selected");
  RealizationWork standalone;
  auto result = realizeComputationEntry(*numerical, "numerical", policy,
                                        available ? *available : standalone);
  require(bool(result), "numerical fold realization failed");
  require(succeeded(computation::verifyRecipeOutput(*result)),
          "invalid native output");
  return result;
}
bool compareFold(ModuleOp source, ModuleOp candidate) {
  auto numerical = computationRecipeSource(unit(source), "total", "selected");
  return succeeded(
      computation::verifyEntryRecipes(*numerical, candidate, "numerical"));
}
bool hasLoop(ModuleOp module) {
  bool result = false;
  module.walk([&](exec::RangeOp) { result = true; });
  return result;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "expected map fixture path");
  auto bytes = MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "cannot read map fixture");
  const std::string mapText =
      fieldText((*bytes)->getBuffer().str(), "koala-bear", "bls12-381.fr");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool native : {false, true})
    cases.run(
        native ? "native preparation enters the standard tensor profile"
               : "vector preparation stays outside the tensor profile",
        [&] {
          MLIRContext lazy(registry, MLIRContext::Threading::DISABLED);
          auto source = parse(lazy, mapText);
          require(!lazy.getLoadedDialect("tensor") &&
                      !lazy.getLoadedDialect("linalg"),
                  "source fixture already loaded the implementation dialects");
          auto candidate =
              prepareMap(*source, native ? NumericalExpressionMode::PreferNative
                                         : NumericalExpressionMode::VectorOnly);
          require(
              bool(lazy.getLoadedDialect("tensor")) == native &&
                  bool(lazy.getLoadedDialect("linalg")) == native,
              "production preparation bypassed its selected implementation");
          require(bool(operation(*candidate, "numerical.map")) == native &&
                      succeeded(compareMap(*source, *candidate)),
                  "selected execution failed independent comparison");
        });
  cases.run("structured work capacity declines before native emission", [&] {
    auto text = replaceText(mapText, "%sq = func.call @square(%a) : (!F)->!F",
                            "%sq = algebra.field_multiply %a,%a : (!F,!F)->!F");
    auto source = parse(context, text);
    auto candidate = prepareMap(*source);
    auto helper = SymbolTable(unit(*source)).lookup<func::FuncOp>("formula");
    auto mapped = SymbolTable(unit(*candidate)).lookup<func::FuncOp>("work");
    llvm::DenseMap<Value, LaneInput> inputs;
    for (auto [i, argument] : enumerate(helper.getArguments()))
      inputs[argument] = {mapped.getArgument(i + 1), i < 3};
    auto admitted = take(admitLaneFormula(helper.front(), inputs,
                                          mapped.getArgument(1).getType(),
                                          nullptr, mathematicalRecipes()));
    require(bool(admitted.formula), "formula admission failed");
    uint64_t remaining = 0;
    unsigned emitted = 0;
    auto result = take(emitNumericalLanes(
        *admitted.formula, mapped.getArgument(1).getType(),
        payload(operation(*candidate, "vector.length")), LaneResultMode::Map,
        [&](const protocol::BindingApplication &, ValueRange, Type,
            ArrayRef<Attribute>) {
          ++emitted;
          return Value();
        },
        &remaining));
    require(result.status == LaneRealizationStatus::Capacity &&
                result.reason == "mathematical-structured-work" && !emitted &&
                !remaining,
            "structured work limit permitted incomplete emission");
  });
  for (StringRef field :
       {"bls12-381.fr", "bn254.fr", "ristretto255.scalar", "koala-bear",
        "koala-bear.ext4-binomial3", "koala-bear.ext8-binomial3",
        "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1"}) {
    cases.run("actual numerical map " + field, [&] {
      auto source = parse(context, fieldText(mapText, field));
      auto candidate = prepareMap(*source);
      auto *call = operation(*candidate, "numerical.map");
      require(
          call && cast<exec::ApplyOp>(call).getInputs().size() == 5 &&
              binding(call).getArguments()[1] ==
                  DenseBoolArrayAttr::get(&context, {true, true, true, false}),
          "map did not retain every input slot");
      take(protocol::readNumericalExpression(expression(call), field, 4));
      require(!operation(*candidate, "vector.mul") &&
                  !operation(*candidate, "vector.fill"),
              "native map allocated a vector arithmetic intermediate");
      require(succeeded(compareMap(*source, *candidate)),
              "actual map expression failed independent comparison");
      auto vector = prepareMap(*source, NumericalExpressionMode::VectorOnly);
      require(!operation(*vector, "numerical.map") &&
                  operation(*vector, "vector.mul") &&
                  succeeded(compareMap(*source, *vector)),
              "explicit vector alternative was lost");
    });
    for (bool product : {false, true})
      for (bool reassociated : {false, true})
        cases.run(
            Twine(product ? "mapped product " : "mapped sum ") + field +
                (reassociated ? " associative spine" : " direct combiner"),
            [&] {
              auto text = fieldText(foldText.str(), field);
              if (product)
                text = replaceText(text, "%r = algebra.field_add %s,%t",
                                   "%r = algebra.field_multiply %s,%t");
              if (reassociated) {
                StringRef combiner =
                    product ? "algebra.field_multiply" : "algebra.field_add";
                text = replaceText(
                    text, "%r = " + combiner.str() + " %s,%t : (!F,!F)->!F",
                    "%prefix = " + combiner.str() +
                        " %s,%sq : (!F,!F)->!F\n"
                        "   %r = " +
                        combiner.str() + " %prefix,%x : (!F,!F)->!F");
              }
              auto source = parse(context, text);
              auto candidate = emitFold(*source);
              StringRef contract =
                  product ? "numerical.product" : "numerical.sum";
              auto *call = operation(*candidate, contract);
              require(call && !hasLoop(*candidate) &&
                          !operation(*candidate, "vector.sum") &&
                          !operation(*candidate, "vector.product") &&
                          compareFold(*source, *candidate),
                      "mapped expression did not use the identity-based native "
                      "aggregate");
              auto *seed =
                  operation(*candidate, product ? "field.mul" : "field.add");
              require(
                  seed && is_contained(seed->getOperands(), payload(call)),
                  "source seed was not combined outside the numerical call");
              MathematicalSelectionPolicy vectorPolicy;
              vectorPolicy.numericalExpressions =
                  NumericalExpressionMode::VectorOnly;
              auto vector = emitFold(*source, vectorPolicy);
              require(!operation(*vector, contract) &&
                          operation(*vector, product ? "vector.product"
                                                     : "vector.sum") &&
                          compareFold(*source, *vector),
                      "mapped aggregate vector alternative was lost");
              auto wrong = copy(*candidate);
              auto *changed = operation(*wrong, contract);
              // Mutating sum to product (or vice versa) preserves ports, but
              // must fail mathematical comparison of the actual result mode.
              auto declaration = binding(changed);
              declaration->setAttr(
                  "contract",
                  StringAttr::get(&context, product ? "numerical.sum"
                                                    : "numerical.product"));
              require(succeeded(computation::verifyRecipeOutput(*wrong)) &&
                          !compareFold(*source, *wrong),
                      "wrong aggregate mode survived independent comparison");
            });
  }
  for (bool product : {false, true})
    for (StringRef mutation : {"replace seed", "omit seed", "seed in term",
                               "omit sibling", "repeat sibling"})
      cases.run(
          Twine(product ? "native product " : "native sum ") + mutation, [&] {
            std::string combine =
                product ? "algebra.field_multiply" : "algebra.field_add";
            auto text = replaceText(
                foldText.str(), "%r = algebra.field_add %s,%t : (!F,!F)->!F",
                "%prefix = " + combine +
                    " %s,%sq : (!F,!F)->!F\n"
                    "   %middle = " +
                    combine +
                    " %prefix,%x : (!F,!F)->!F\n"
                    "   %r = " +
                    combine + " %middle,%x : (!F,!F)->!F");
            auto source = parse(context, text);
            auto candidate = emitFold(*source);
            StringRef contract =
                product ? "numerical.product" : "numerical.sum";
            auto *call = operation(*candidate, contract);
            require(call && compareFold(*source, *candidate),
                    "associative native control was not selected");
            auto wrong = copy(*candidate);
            call = operation(*wrong, contract);
            auto *seed = operation(*wrong, product ? "field.mul" : "field.add");
            require(seed, "missing external seed combiner");
            auto entry = cast<func::FuncOp>(call->getParentOp());
            if (mutation == "replace seed") {
              for (unsigned i = 1; i < seed->getNumOperands(); ++i)
                if (seed->getOperand(i) != payload(call))
                  seed->setOperand(i, entry.getArgument(3));
            } else if (mutation == "omit seed") {
              omit(seed, payload(call));
            } else if (mutation == "seed in term") {
              require(call->getOperand(call->getNumOperands() - 1) ==
                          entry.getArgument(3),
                      "missing scalar capture slot");
              call->setOperand(call->getNumOperands() - 1,
                               entry.getArgument(2));
              // The source's scalar capture is unused in this spine.
              // Make that slot contribute, duplicating the external seed.
              mutateBody(call, [](json::Array &root) {
                auto &nodes = *root[2].getAsArray();
                auto &outputs = *root[3].getAsArray();
                auto output = *outputs[0].getAsUINT64();
                auto kind =
                    (*nodes[output].getAsArray())[0].getAsString()->str();
                nodes.push_back(json::Array{"input", 1});
                auto slot = nodes.size() - 1;
                nodes.push_back(json::Array{kind, output, slot});
                outputs[0] = nodes.size() - 1;
              });
            } else
              mutateBody(call, [&](json::Array &root) {
                auto &nodes = *root[2].getAsArray();
                auto &outputs = *root[3].getAsArray();
                auto output = *outputs[0].getAsUINT64();
                auto &last = *nodes[output].getAsArray();
                if (mutation == "omit sibling") {
                  require(output + 1 == nodes.size(),
                          "unexpected output order");
                  outputs[0] = *last[1].getAsUINT64();
                  // Remove the obsolete final combiner so ordinary Ring
                  // reachability admission still succeeds for this wrong term.
                  nodes.pop_back();
                } else {
                  auto kind = last[0].getAsString()->str();
                  auto sibling = *last[2].getAsUINT64();
                  nodes.push_back(json::Array{kind, output, sibling});
                  outputs[0] = nodes.size() - 1;
                }
              });
            require(succeeded(computation::verifyRecipeOutput(*wrong)),
                    "semantic mutation failed ordinary admission");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            require(!compareFold(*source, *wrong),
                    "seed or sibling mutation survived native comparison");
          });
  cases.run("native comparison exact allowance and mismatch distinction", [&] {
    auto source = parse(context, mapText);
    auto candidate = prepareMap(*source);
    require(succeeded(compareMap(*source, *candidate)),
            "native comparison control failed");
    auto helper = SymbolTable(unit(*source)).lookup<func::FuncOp>("formula");
    auto *call = operation(*candidate, "numerical.map");
    auto function = call->getParentOfType<func::FuncOp>();
    auto *end = sc::returned(function).getOperation();
    SymbolTable symbols(unit(*candidate));
    auto check = [&](uint64_t &remaining, ComparisonCapacity &capacity,
                     std::optional<CapacityCause> &debit, bool accepted) {
      auto view = take(ScopedCandidate::read(
          unit(*candidate), ScopedCandidate::Requests::Retained));
      Operation *cursor = call;
      llvm::DenseSet<Operation *> bindings;
      auto result = compareLaneFormula(
          helper.front(), {true, true, true, false},
          function.getArguments().drop_front(),
          cast<exec::ApplyOp>(call).getInputs()[0], cursor, symbols, bindings,
          remaining, end, &capacity, &debit,
          sc::returned(function).getOperand(0), view.get());
      require(succeeded(result) == accepted,
              "unexpected direct native comparison outcome");
      require(accepted ? cursor == end : cursor == call && bindings.empty(),
              "failed comparison published cursor or bindings");
    };
    uint64_t remaining = 1000000;
    ComparisonCapacity capacity = ComparisonCapacity::Work;
    std::optional<CapacityCause> debit;
    check(remaining, capacity, debit, true);
    auto cost = 1000000 - remaining;
    require(cost > 1 && cost < 1000000 &&
                capacity == ComparisonCapacity::None && !debit,
            "native comparison work was not measured");
    remaining = cost;
    check(remaining, capacity, debit, true);
    require(!remaining && capacity == ComparisonCapacity::None && !debit,
            "exact native allowance was treated as exhaustion");
    remaining = cost - 1;
    check(remaining, capacity, debit, false);
    require(!remaining && capacity == ComparisonCapacity::Work && debit &&
                debit->owner == WorkOwner::OptionalComparison,
            "one-short native comparison lost its capacity outcome");
    mutateBody(call, [](json::Array &root) {
      auto &last = *root[2].getAsArray()->back().getAsArray();
      last[0] = "mul";
    });
    require(succeeded(verify(*candidate)),
            "body mismatch failed ordinary candidate admission");
    remaining = 1000000;
    check(remaining, capacity, debit, false);
    require(capacity == ComparisonCapacity::None && !debit && remaining,
            "actual mismatch was classified as optional capacity");
    remaining = 1000000 - remaining;
    check(remaining, capacity, debit, false);
    require(!remaining && capacity == ComparisonCapacity::None && !debit,
            "mismatch spending the final unit was treated as capacity");
  });
  cases.run("native readback follows actual helper argument substitution", [&] {
    auto source = parse(context, mapText);
    auto candidate = prepareMap(*source);
    auto *call = operation(*candidate, "numerical.map");
    mutateBody(call, [](json::Array &root) {
      bool changed = false;
      for (auto &row : *root[2].getAsArray()) {
        auto &node = *row.getAsArray();
        if (node[0].getAsString() == "input" && node[1].getAsUINT64() == 0) {
          node[1] = 1;
          changed = true;
        }
      }
      require(changed, "missing helper argument in the emitted body");
    });
    require(succeeded(verify(*candidate)),
            "helper substitution mutation failed ordinary admission");
    ScopedDiagnosticHandler quiet(&context,
                                  [](Diagnostic &) { return success(); });
    require(failed(compareMap(*source, *candidate)),
            "wrong square helper argument survived native readback");
  });
  for (StringRef mutation :
       {"body", "field", "arity", "output", "wiring", "unused-wiring", "rows",
        "string-carrier", "size", "guard", "pin"})
    cases.run("independent map mutation " + mutation, [&] {
      auto source = parse(context, mapText);
      auto candidate = prepareMap(*source);
      auto *call = operation(*candidate, "numerical.map");
      if (mutation == "body")
        mutateBody(call, [](json::Array &root) {
          auto &nodes = *root[2].getAsArray();
          auto &last = *nodes.back().getAsArray();
          last[0] = last[0].getAsString() == "add" ? "mul" : "add";
        });
      else if (mutation == "field")
        mutateBody(call, [](json::Array &root) {
          (*root[1].getAsArray())[2] =
              "bn254.fr"; // An unused slot still matters.
        });
      else if (mutation == "arity")
        mutateBody(call, [](json::Array &root) {
          root[1].getAsArray()->push_back("koala-bear");
        });
      else if (mutation == "output")
        mutateBody(call, [](json::Array &root) {
          root[3].getAsArray()->push_back(0);
        });
      else if (mutation == "wiring") {
        auto left = call->getOperand(2);
        call->setOperand(2, call->getOperand(3));
        call->setOperand(3, left);
      } else if (mutation == "unused-wiring") {
        auto declaration = binding(call);
        declaration->setAttr(
            "arguments",
            ArrayAttr::get(&context, {StringAttr::get(&context, "koala-bear"),
                                      StringAttr::get(&context, "1100")}));
      } else if (mutation == "string-carrier")
        call->setAttr("parameters",
                      Builder(&context).getStrArrayAttr({expression(call)}));
      else if (mutation == "pin")
        binding(call)->setAttr(
            "implementation",
            StringAttr::get(&context, "plonky3/numerical.map"));
      else if (mutation == "size") {
        auto graph = cast<algebra::RingExpressionAttr>(
            call->getAttrOfType<ArrayAttr>("parameters")[0]);
        SmallVector<algebra::RingNodeAttr> nodes;
        for (unsigned i = 0; i < 256; ++i)
          nodes.push_back(algebra::RingNodeAttr::get(
              &context, algebra::RingNodeKind::Input,
              DenseI32ArrayAttr::get(&context, {0}), {}, {}));
        SmallVector<int32_t> layer;
        for (unsigned i = 0; i < nodes.size(); ++i)
          layer.push_back(i);
        while (layer.size() > 1) {
          SmallVector<int32_t> next;
          for (unsigned i = 0; i < layer.size(); i += 2) {
            next.push_back(nodes.size());
            nodes.push_back(algebra::RingNodeAttr::get(
                &context, algebra::RingNodeKind::Add,
                DenseI32ArrayAttr::get(&context, {layer[i], layer[i + 1]}), {},
                {}));
          }
          layer = std::move(next);
        }
        auto oversized = algebra::RingExpressionAttr::get(
            &context, graph.getInputs(), nodes,
            DenseI32ArrayAttr::get(&context, layer));
        require(take(algebra::ringExpressionByteSize(oversized)) > 4096,
                "size mutation does not exceed the numerical profile");
        call->setAttr("parameters",
                      Builder(&context).getArrayAttr({oversized}));
      } else if (mutation == "guard") {
        auto *guard = operation(*candidate, "control.require");
        require(guard != nullptr, "missing unused-input shape guard");
        sc::omit(guard);
      } else {
        auto helper = call->getParentOfType<func::FuncOp>();
        auto stop = cast<exec::DispatchOp>(call->getNextNode()).getStopped();
        auto rows = cast<exec::ApplyOp>(call).getInputs()[0];
        OpBuilder builder(&context);
        builder.setInsertionPointToStart(&unit(*candidate).getBody().front());
        runtime::BindingOp::create(builder, call->getLoc(), "wrong_extent",
                                   "index.constant",
                                   builder.getStrArrayAttr({}), "");
        IRRewriter rewriter(&context);
        auto *before = call->getBlock();
        auto *tail = rewriter.splitBlock(before, call->getIterator());
        builder.setInsertionPointToEnd(before);
        exec::ScopedExecutionBuilder control(builder, helper);
        auto wrong = control.invoke(
            "exec.apply", rows.getType(), control.scoped({}),
            {builder.getNamedAttr(
                 "binding", FlatSymbolRefAttr::get(&context, "wrong_extent")),
             builder.getNamedAttr("parameters",
                                  builder.getArrayAttr({builder.getIntegerAttr(
                                      builder.getIntegerType(64, false), 1)})),
             builder.getNamedAttr("site",
                                  builder.getStringAttr("wrong_extent"))},
            stop);
        rewriter.mergeBlocks(tail, builder.getInsertionBlock());
        call->setOperand(1, wrong[0]);
      }
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      bool semantic = mutation == "body" || mutation == "wiring" ||
                      mutation == "rows" || mutation == "guard" ||
                      mutation == "pin";
      require(succeeded(verify(*candidate)) == semantic,
              "mutation no longer exercises its intended admission boundary");
      require(failed(compareMap(*source, *candidate)),
              "mutated native expression passed the independent reader");
    });
  cases.run(
      "body capacity declines before native emission and retains vectors", [&] {
        auto text = mapText;
        std::string chain;
        std::string previous = "%a";
        for (unsigned i = 0; i < 400; ++i) {
          auto next = "%chain" + std::to_string(i);
          chain += "   " + next + " = algebra.field_add " + previous +
                   ",%a : (!F,!F)->!F\n";
          previous = next;
        }
        text = replaceText(text, "   func.return %p : !F",
                           chain + "   func.return " + previous + " : !F");
        text = replaceText(text, "%sq = func.call @square(%a) : (!F)->!F",
                           "%sq = algebra.field_multiply %a,%a : (!F,!F)->!F");
        auto source = parse(context, text);
        auto candidate = prepareMap(*source);
        require(
            !operation(*candidate, "numerical.map") &&
                operation(*candidate, "vector.add") &&
                succeeded(compareMap(*source, *candidate)),
            "oversized optional native body lost the checked vector fallback");
        auto helper =
            SymbolTable(unit(*source)).lookup<func::FuncOp>("formula");
        auto mapped =
            SymbolTable(unit(*candidate)).lookup<func::FuncOp>("work");
        llvm::DenseMap<Value, LaneInput> inputs;
        for (auto [i, argument] : enumerate(helper.getArguments()))
          inputs[argument] = {mapped.getArgument(i + 1), i < 3};
        auto admitted = take(admitLaneFormula(helper.front(), inputs,
                                              mapped.getArgument(1).getType(),
                                              nullptr, mathematicalRecipes()));
        require(
            bool(admitted.formula) &&
                printJson(admitted.formula->expression.encode()).size() >
                    protocol::NumericalLimits::bodyBytes,
            "body-capacity control did not exceed the numerical byte limit");
        unsigned emitted = 0;
        auto result = take(emitNumericalLanes(
            *admitted.formula, mapped.getArgument(1).getType(),
            payload(operation(*candidate, "vector.length")),
            LaneResultMode::Map,
            [&](const protocol::BindingApplication &, ValueRange, Type,
                ArrayRef<Attribute>) {
              ++emitted;
              return Value();
            }));
        require(result.status == LaneRealizationStatus::Capacity &&
                    result.reason == "numerical-body-limit" && !emitted,
                "oversized numerical body invoked the emission callback");
      });
  for (StringRef field :
       {"gf2-64.pentanomial-4-3-1", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
    cases.run(
        "binary bit-pattern constants retain ordered execution " + field, [&] {
          auto text = fieldText(foldText.str(), field);
          text = replaceText(
              text, "%t = algebra.field_add %sq,%a : (!F,!F)->!F",
              "%bits = \"algebra.constant\"() "
              "{value=#algebra.literal<!F, 2 : ui" +
                  std::to_string(field.contains("ext3") ? 192 : 64) +
                  ">} : ()->!F\n"
                  "   %t = algebra.field_add %sq,%bits : (!F,!F)->!F");
          auto source = parse(context, text);
          auto candidate = emitFold(*source);
          auto *literal = operation(*candidate, "field.constant");
          require(hasLoop(*candidate) && literal &&
                      cast<algebra::FieldLiteralAttr>(
                          literal->getAttrOfType<ArrayAttr>("parameters")[0])
                              .getValue()
                              .getValue() == 2 &&
                      !operation(*candidate, "numerical.sum") &&
                      compareFold(*source, *candidate),
                  "valid bit-pattern constant lost its ordered finite path");
          auto body =
              take(ring::Expression::create(
                       {}, {ring::Node::literal(field.str(), "1")}, {0}))
                  .encode();
          auto &literalNode =
              *(*body.getAsArray())[2].getAsArray()->front().getAsArray();
          literalNode[2] = "0x2";
          refuses(protocol::readNumericalExpression(printJson(body), field, 0),
                  "ring-literal");
        });
  cases.run(
      "port capacity emits nothing and original domain policy survives", [&] {
        auto source = parse(context, foldText);
        auto vector = algebra::FieldVectorType::get(&context, "koala-bear");
        auto total = SymbolTable(unit(*source)).lookup<func::FuncOp>("total");
        auto slots = std::vector<ring::Input>(1024, {"koala-bear"});
        auto body = take(ring::Expression::create(std::move(slots),
                                                  {ring::Node::slot(0)}, {0}));
        LaneFormula formula{std::move(body),
                            nullptr,
                            llvm::DenseMap<Value, LaneInput>(),
                            llvm::DenseMap<Value, uint32_t>(),
                            {},
                            {},
                            {},
                            MathematicalIdentity::FieldAdd};
        formula.slots.assign(1024, LaneInput{total.getArgument(2), false});
        unsigned emitted = 0;
        auto result =
            take(emitNumericalLanes(formula, vector, {}, LaneResultMode::Map,
                                    [&](const protocol::BindingApplication &,
                                        ValueRange, Type, ArrayRef<Attribute>) {
                                      ++emitted;
                                      return Value();
                                    }));
        require(result.status == LaneRealizationStatus::Capacity && !emitted,
                "port capacity emitted an incomplete native call");
        MathematicalSelectionPolicy policy;
        policy.finiteBulk = false;
        auto ordered = emitFold(*source, policy);
        require(hasLoop(*ordered) && !operation(*ordered, "numerical.sum"),
                "native choice erased disabled finite policy");
        RealizationWork bounded;
        bounded.lanes = 0;
        require(hasLoop(*emitFold(*source, {}, &bounded)),
                "optional lane budget lost ordered fallback");
      });
  cases.run(
      "specialized direct reductions and contractions remain preferred", [&] {
        for (bool product : {false, true}) {
          auto text =
              replaceText(foldText.str(), "%r = algebra.field_add %s,%t",
                          product ? "%r = algebra.field_multiply %s,%x"
                                  : "%r = algebra.field_add %s,%x");
          auto source = parse(context, text);
          auto candidate = emitFold(*source);
          require(operation(*candidate,
                            product ? "vector.product" : "vector.sum") &&
                      !operation(*candidate, product ? "numerical.product"
                                                     : "numerical.sum") &&
                      compareFold(*source, *candidate),
                  "native expression displaced a direct reduction");
        }
        auto text = replaceText(foldText.str(), "%r = algebra.field_add %s,%t",
                                "%r = algebra.field_add %s,%sq");
        auto source = parse(context, text);
        auto candidate = emitFold(*source);
        require(operation(*candidate, "vector.dot") &&
                    !operation(*candidate, "numerical.sum") &&
                    compareFold(*source, *candidate),
                "native expression displaced a dot contraction");
      });
  for (unsigned pin = 0; pin != 3; ++pin)
    cases.run("source implementation restriction " + Twine(pin), [&] {
      auto text = scopedFoldText.str();
      if (pin == 1)
        text =
            replaceText(text,
                        "sym_name=\"mul\",contract=\"field.mul\",arguments=["
                        "\"koala-bear\"],implementation=\"\"",
                        "sym_name=\"mul\",contract=\"field.mul\",arguments=["
                        "\"koala-bear\"],implementation=\"plonky3/field.mul\"");
      if (pin == 2) {
        text =
            replaceText(text, " \"runtime.binding\"()",
                        " \"runtime.binding\"() "
                        "{sym_name=\"dead\",contract=\"field.add\",arguments=["
                        "\"koala-bear\"],implementation=\"plonky3/"
                        "field.add\",function_type=(!runtime.scope,!F,!F)->!"
                        "exec.outcome<(!F)>} "
                        ": ()->()\n \"runtime.binding\"()");
        text = replaceText(text, "   %result = \"exec.returned\"(%r)",
                           "   %dead = \"exec.apply\"(%scope,%x,%x) "
                           "{binding=@dead,parameters=[],site=\"dead\"} : "
                           "(!runtime.scope,!F,!F)->!exec.outcome<(!F)>\n"
                           "   \"exec.dispatch\"(%dead)[^after_dead,^failed] : "
                           "(!exec.outcome<(!F)>)->()\n"
                           " ^after_dead(%unused:!F):\n"
                           "   %result = \"exec.returned\"(%r)");
      }
      auto source = parse(context, text);
      RealizationWork work;
      uint64_t copies = 1000000, sites = 16 * 1024 * 1024;
      std::optional<CapacityCause> capacity;
      auto candidate =
          protocol::prepareScopedFinite(*source, work, copies, sites, capacity);
      require(
          candidate && hasLoop(*candidate) == bool(pin) &&
              bool(operation(*candidate, "numerical.sum")) == !pin &&
              succeeded(protocol::verifyScopedFinitePreparation(
                  *source, *candidate, work)),
          "native formula erased a live or dead implementation restriction");
    });
  for (unsigned variant = 0; variant != 3; ++variant)
    cases.run(
        "mapped aggregate retains complete source domain " + Twine(variant),
        [&] {
          std::string text = R"mlir(
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!E = EXTRA_CONTAINER
!X = EXTRA_ELEMENT
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V,%extra:!E):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   %e = "data.domain_elements"(%extra) : (!E)->!data.domain<!X>
   %d = "data.domain_zip"(%x,%e) : (!data.domain<!F>,!data.domain<!X>)->!data.domain<!F,!X>
   "data.domain_yield"(%d) : (!data.domain<!F,!X>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!E)->!data.domain<!F,!X>} : ()->()
 func.func private @step(%s:!F,%x:!F,%unused:!X,%xs:!V,%extra:!E,%a:!F)->!F {
   %sq = algebra.field_multiply %x,%x : (!F,!F)->!F
   %t = algebra.field_add %sq,%a : (!F,!F)->!F
   %r = algebra.field_add %s,%t : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @total(%xs:!V,%extra:!E,%seed:!F,%a:!F)->!F attributes {data.preconditions=[#data.equal_extent<0,0,1,0>]} {
   %r = "algebra.finite_fold"(%xs,%extra,%seed,%a) {domain=@items,step=@step} : (!V,!E,!F,!F)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ "protocol.return"() : ()->() }) {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
          StringRef container = variant == 0 ? "!V"
                                : variant == 1
                                    ? "!algebra.group_vector<\"bls12-381.g1\">"
                                    : "!algebra.field_array<\"koala-bear\",2>";
          text = replaceText(text, "EXTRA_CONTAINER", container);
          text = replaceText(text, "EXTRA_ELEMENT",
                             variant == 1 ? "!algebra.group<\"bls12-381.g1\">"
                                          : "!F");
          if (!variant) {
            text = replaceText(text, "%extra:!E,%a:!F)->!F",
                               "%extra:!E,%a:!F,%unmeasured:!V)->!F");
            text = replaceText(text, "%extra:!E,%seed:!F,%a:!F)->!F",
                               "%extra:!E,%seed:!F,%a:!F,%unmeasured:!V)->!F");
            text =
                replaceText(text, "finite_fold\"(%xs,%extra,%seed,%a)",
                            "finite_fold\"(%xs,%extra,%seed,%a,%unmeasured)");
            text =
                replaceText(text, "(!V,!E,!F,!F)->!F", "(!V,!E,!F,!F,!V)->!F");
          }
          auto source = parse(context, text);
          auto candidate = emitFold(*source);
          require(
              hasLoop(*candidate) == bool(variant) &&
                  bool(operation(*candidate, "numerical.sum")) == !variant,
              "unused domain factor escaped original admission restrictions");
          if (!variant) {
            auto *call = operation(*candidate, "numerical.sum");
            require(binding(call).getArguments()[1] ==
                            DenseBoolArrayAttr::get(&context,
                                                    {true, true, false}) &&
                        compareFold(*source, *candidate),
                    "unused field-vector domain slot or its extent was lost");
            auto wrong = copy(*candidate);
            auto *changed = operation(*wrong, "numerical.sum");
            auto entry = cast<func::FuncOp>(changed->getParentOp());
            changed->setOperand(3, entry.getArgument(5));
            require(succeeded(computation::verifyRecipeOutput(*wrong)),
                    "unused vector substitution failed ordinary admission");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            require(!compareFold(*source, *wrong),
                    "unused numerical slot accepted an unmeasured vector");
          }
        });
  cases.run(
      "multiple or nonassociative state dependencies remain ordered", [&] {
        for (StringRef update :
             {"%r = algebra.field_add %s,%s",
              "%r = algebra.field_subtract %t,%s",
              "%r = algebra.field_multiply %s,%s",
              "%prefix = algebra.field_add %s,%t : (!F,!F)->!F\n"
              "   %r = algebra.field_add %prefix,%prefix",
              "%prefix = algebra.field_multiply %s,%t : (!F,!F)->!F\n"
              "   %r = algebra.field_multiply %prefix,%prefix"}) {
          auto source = parse(
              context, replaceText(foldText.str(),
                                   "%r = algebra.field_add %s,%t", update));
          auto candidate = emitFold(*source);
          require(hasLoop(*candidate) &&
                      !operation(*candidate, "numerical.sum") &&
                      !operation(*candidate, "numerical.product"),
                  "dependent recurrence was extracted as an aggregate");
        }
      });
  return cases.result();
}
