#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/MathematicalPreservation.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "../lib/Transforms/ScopedFinite.h"
#include "../lib/Transforms/ScopedPreparation.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"
#include <chrono>
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
const char *aliasSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%a:!F,%b:!F,%item:!F,%xs:!V,%copy:!V,%factor:!F,%enabled:i1)->!exec.outcome<(!F,!F)> attributes {no_inline,runtime.origin=["step",[]]} {
   %r = "exec.returned"(%b,%factor) : (!F,!F)->!exec.outcome<(!F,!F)>
   func.return %r : !exec.outcome<(!F,!F)>
 }
 func.func private @predicate(%scope:!runtime.scope,%item:!F,%xs:!V,%copy:!V,%factor:!F,%enabled:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["predicate",[]]} {
   %r = "exec.returned"(%enabled) : (i1)->!exec.outcome<(i1)>
   func.return %r : !exec.outcome<(i1)>
 }
 func.func @work(%scope:!runtime.scope,%xs:!V,%a:!F,%b:!F,%enabled:i1)->!exec.outcome<(!F,!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.fold"(%scope,%xs,%a,%b,%xs,%a,%enabled) {domain=@items,step=@step,predicate=@predicate,site="direct"} : (!runtime.scope,!V,!F,!F,!V,!F,i1)->!exec.outcome<(!F,!F)>
   "exec.dispatch"(%r)[^done,^failed] : (!exec.outcome<(!F,!F)>)->()
 ^done(%a1:!F,%b1:!F):
   %result = "exec.returned"(%a1,%b1) : (!F,!F)->!exec.outcome<(!F,!F)>
   func.return %result : !exec.outcome<(!F,!F)>
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(!F,!F)>
   func.return %failed : !exec.outcome<(!F,!F)>
 }
 "protocol.func"() ({ ^entry(%xs:!V,%a:!F,%b:!F,%enabled:i1):
   %r:2 = "protocol.local_call"(%xs,%a,%b,%enabled) {callee=@work,role="P",site="work"} : (!V,!F,!F,i1)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!F,!F,i1)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
const char *rangeAliasSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64>} : ()->()
 func.func private @step(%state:!F,%i:ui64,%lo:ui64,%hi:ui64,%capture:!F)->!F {
   func.return %capture : !F
 }
 "protocol.func"() ({ ^entry(%bound:ui64,%seed:!F):
   %r = "algebra.finite_fold"(%bound,%bound,%seed,%seed) {domain=@items,step=@step} : (ui64,ui64,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(ui64,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
void prepare(ModuleOp module) {
  PassManager passes(module.getContext());
  passes.addPass(protocol::createProjectProtocolPass(false, {false, false}));
  require(succeeded(passes.run(module)), "preparation failed");
}
void lower(ModuleOp module) {
  PassManager passes(module.getContext());
  passes.addPass(protocol::createLowerMathPass({false, false}));
  require(succeeded(passes.run(module)), "direct lowering failed");
}
class WithheldCatalog final : public target::CandidateCatalog {
  std::vector<std::string> withheld;

public:
  explicit WithheldCatalog(std::vector<std::string> withheld)
      : withheld(std::move(withheld)) {}
  llvm::Expected<std::vector<std::string>> implementations(
      const protocol::BindingApplication &application) const override {
    if (llvm::is_contained(withheld, application.contract))
      return std::vector<std::string>{};
    return target::installedCandidates().implementations(application);
  }
  std::vector<protocol::BindingApplication>
  conversions(const protocol::BoundType &from,
              const protocol::BoundType &to) const override {
    return target::installedCandidates().conversions(from, to);
  }
};
std::string dump(ModuleOp module) {
  std::string result;
  llvm::raw_string_ostream stream(result);
  module.print(stream);
  return result;
}
bool usesContract(ModuleOp module, StringRef contract) {
  bool found = false;
  module.walk([&](exec::ApplyOp op) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    found |= binding && binding.getContract() == contract;
  });
  return found;
}
struct Insertions : OpBuilder::Listener {
  unsigned operations = 0, blocks = 0, functions = 0, temporary = 0;
  void notifyOperationInserted(Operation *op, OpBuilder::InsertPoint) override {
    ++operations;
    functions += isa<func::FuncOp>(op);
    auto name = SymbolTable::getSymbolName(op);
    temporary += name && name.getValue().starts_with("_finite_expression_");
  }
  void notifyBlockInserted(Block *, Region *, Region::iterator) override {
    ++blocks;
  }
};
// The callbacks in this fixture only forward arguments. Interpret their
// immutable returned payload directly, without consulting emitted bindings,
// the realizer's environments, or its recipe selections.
FailureOr<finite::ScopedCallbackResult> forward(func::FuncOp helper,
                                                ValueRange args) {
  if (!helper.getBody().hasOneBlock() ||
      helper.front().getOperations().size() != 2)
    return failure();
  auto returned = dyn_cast<exec::ReturnOp>(helper.front().front());
  auto end = dyn_cast<func::ReturnOp>(helper.front().back());
  if (!returned || !end || end.getNumOperands() != 1 ||
      end.getOperand(0) != returned->getResult(0))
    return failure();
  SmallVector<Value> results;
  for (Value value : returned->getOperands()) {
    auto formal = dyn_cast<BlockArgument>(value);
    if (!formal || formal.getOwner() != &helper.front() ||
        formal.getArgNumber() == 0 || formal.getArgNumber() > args.size())
      return failure();
    results.push_back(args[formal.getArgNumber() - 1]);
  }
  return finite::ScopedCallbackResult{std::move(results), false};
}
struct DirectBody {
  OwningOpRef<ModuleOp> module;
  func::FuncOp function;
  SmallVector<Value> inputs, emitted;
  Insertions insertions;
  mathematical::RealizationWork work;
  uint64_t construction = 1000000, siteBytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;

  explicit DirectBody(exec::FoldOp source) {
    auto *context = source.getContext();
    auto location = source.getLoc();
    module = ModuleOp::create(location);
    OpBuilder builder(context, &insertions);
    builder.setInsertionPointToEnd(module->getBody());
    auto output = protocol_ir::ProtocolModuleOp::create(
        builder, location, protocol_ir::Profile::Exec);
    output.getBody().emplaceBlock();
    builder.setInsertionPointToEnd(&output.getBody().front());
    SmallVector<Value> unique;
    for (Value value : source.getInputs())
      if (!llvm::is_contained(unique, value))
        unique.push_back(value);
    SmallVector<Type> types{runtime::ScopeType::get(context)};
    llvm::append_range(types, ValueRange(unique).getTypes());
    function = func::FuncOp::create(
        builder, location, "direct_test",
        builder.getFunctionType(types, source->getResultTypes()));
    function.setNoInline(true);
    function->setAttr(
        "runtime.origin",
        builder.getArrayAttr(
            {builder.getStringAttr("direct_test"), builder.getArrayAttr({})}));
    auto *block = function.addEntryBlock();
    builder.setInsertionPointToEnd(block);
    IRMapping arguments;
    arguments.map(unique, block->getArguments().drop_front());
    for (Value value : source.getInputs())
      inputs.push_back(arguments.lookup(value));
    auto callback = [](func::FuncOp helper, ValueRange arguments, StringRef,
                       exec::ScopedExecutionBuilder &) {
      return forward(helper, arguments);
    };
    exec::ScopedExecutionBuilder control(builder, function);
    // Reset setup counts: only realizer insertions are under observation.
    insertions.operations = insertions.blocks = insertions.functions =
        insertions.temporary = 0;
    finite::ScopedEmissionBudget budget{construction, siteBytes, capacity};
    auto result = finite::realizeScopedExpression(
        source, inputs, builder, control, callback, work, {false, false},
        nullptr, {}, &budget);
    require(succeeded(result), "direct scoped emission failed");
    emitted = std::move(*result);
    control.returned(emitted);
  }

  bool corresponds(exec::FoldOp source) {
    // Every invocation reads a fresh immutable view, including after mutation.
    auto view = take(mathematical::ScopedCandidate::read(unit(*module)));
    finite::VerificationLimits limits;
    auto reader = [](func::FuncOp helper, ValueRange arguments, StringRef,
                     Operation *&) { return forward(helper, arguments); };
    limits.candidate = view.get();
    limits.callback = reader;
    limits.finiteSite = source.getSite();
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto pure = [](Operation *, ValueRange,
                   Operation *&) -> FailureOr<SmallVector<Value>> {
      return failure();
    };
    auto *cursor = view->first(&function.front());
    auto checked =
        finite::verifyExpression(source, inputs, cursor, pure,
                                 SymbolTable::getNearestSymbolTable(source),
                                 limits, outcome, {false, false});
    return succeeded(checked) && *checked == emitted && cursor &&
           isa<exec::ReturnOp>(cursor) &&
           cursor->getOperands() == ValueRange(emitted) && !view->next(cursor);
  }
};
exec::FoldOp fold(ModuleOp module) {
  exec::FoldOp result;
  module.walk([&](exec::FoldOp op) { result = op; });
  require(bool(result), "missing scoped fold");
  return result;
}
} // namespace
int main(int argc, char **argv) {
  bool measure = argc == 2 && StringRef(argv[1]) == "--measure";
  require(argc == 1 || measure, "expected optional --measure");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("direct aliases preserve scoped state and tracked outlines", [&] {
    auto source = parseSourceString<ModuleOp>(aliasSource, &context);
    require(bool(source), "alias source admission failed");
    auto original = fold(*source);
    DirectBody candidate(original);
    unsigned blocks = 0, functions = 0;
    candidate.module->walk([&](func::FuncOp function) {
      ++functions;
      blocks += function.getBody().getBlocks().size();
    });
    // The entry function and its entry block existed before observation.
    require(candidate.insertions.operations && blocks > 3 && functions >= 4 &&
                candidate.insertions.blocks == blocks - 1 &&
                candidate.insertions.functions == functions - 1 &&
                !candidate.insertions.temporary,
            "emission bypassed listener or constructed a temporary function");
    require(candidate.construction < 1000000 &&
                candidate.siteBytes < 16 * 1024 * 1024 && !candidate.capacity &&
                succeeded(verify(*candidate.module)),
            "direct candidate lost shared work or scoped ownership");
    require(candidate.corresponds(original),
            "fresh reader refused direct body");
    auto view =
        take(mathematical::ScopedCandidate::read(unit(*candidate.module)));
    exec::RangeOp loop;
    candidate.module->walk([&](exec::RangeOp op) {
      if (view->get(op)->outputs.size() == 2)
        loop = op;
    });
    require(bool(loop), "missing state loop");
    auto *step = view->get(loop);
    // Two states stay separate from the shared invariant seed capture.
    require(step->inputs.size() == 8 &&
                view->arguments(view->body(loop, 0)).size() == 7,
            "aliased invariant captures were not canonicalized");
    require(step->inputs[2] == candidate.inputs[1] &&
                step->inputs[3] == candidate.inputs[2],
            "zero-trip state no longer uses exact ordered seeds");
    runtime::BorrowTransferOp transfer;
    candidate.function.walk([&](runtime::BorrowTransferOp op) {
      if (op->getNumOperands() == 3)
        transfer = op;
    });
    require(bool(transfer), "missing initial state transfer");
    // The transfer's scope is followed by the actual ordered state payload.
    view.reset();
    transfer->setOperand(1, candidate.inputs[2]);
    require(succeeded(verify(*candidate.module)), "changed seed is malformed");
    require(!candidate.corresponds(original),
            "changed zero-trip seed escaped reader");
    transfer->setOperand(1, candidate.inputs[1]);
    view = take(mathematical::ScopedCandidate::read(unit(*candidate.module)));
    exec::TestOp branch;
    auto *body = view->body(loop, 0);
    cast<func::FuncOp>(body->getParentOp()).walk([&](exec::TestOp op) {
      branch = op;
    });
    require(bool(branch), "missing predicate branch");
    exec::CompleteOp returned;
    cast<func::FuncOp>(view->body(branch, 0)->getParentOp())
        .walk([&](exec::CompleteOp op) { returned = op; });
    require(bool(returned) && returned->getNumOperands() == 3,
            "missing predicate state completion");
    Value first = returned->getOperand(1), second = returned->getOperand(2);
    view.reset();
    returned->setOperand(1, second);
    returned->setOperand(2, first);
    require(succeeded(verify(*candidate.module)),
            "state permutation is malformed");
    require(!candidate.corresponds(original),
            "same-typed permutation escaped reader");
  });
  cases.run(
      "source callbacks and emitted bindings have independent roots", [&] {
        auto source = parseSourceString<ModuleOp>(aliasSource, &context);
        require(bool(source), "separate source admission failed");
        std::string before;
        llvm::raw_string_ostream(before) << *source;
        auto original = fold(*source);
        DirectBody candidate(original);
        require(succeeded(computation::verifyRecipeOutput(*candidate.module)),
                "separate-root output is malformed");
        require(
            !SymbolTable::lookupSymbolIn(unit(*candidate.module), "step") &&
                !SymbolTable::lookupSymbolIn(unit(*candidate.module), "items"),
            "emission copied source declarations into its target");
        require(candidate.corresponds(original),
                "reader conflated source and target roots");
        std::string unchanged;
        llvm::raw_string_ostream(unchanged) << *source;
        require(before == unchanged, "direct emission mutated its source");
      });
  cases.run("aliased range bounds canonicalize admission captures", [&] {
    auto source = parseSourceString<ModuleOp>(rangeAliasSource, &context);
    require(bool(source), "aliased range source refused");
    prepare(*source);
    auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    lower(*candidate);
    require(succeeded(mathematical::verifyMathLowering(unit(*source),
                                                       unit(*candidate))),
            "aliased range direct body did not correspond");
    auto logical = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
    require(succeeded(computation::realizeComputations(*candidate)) &&
                succeeded(computation::verifyComputationRealization(
                    *logical, *candidate)),
            "aliased range recipes did not correspond");
    auto view = take(mathematical::ScopedCandidate::read(unit(*candidate)));
    unsigned branches = 0;
    candidate->walk([&](exec::TestOp branch) {
      ++branches;
      require(view->get(branch)->inputs.size() == 2 &&
                  view->arguments(view->body(branch, 0)).size() == 1,
              "aliased admission bounds became duplicate captures");
    });
    require(branches == 1, "range admission disappeared");
  });
  cases.run("zero-state callback stop survives scoped preparation", [&] {
    auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_FINITE_FIXTURES) +
                                             "/unit-state.mlir");
    require(bool(bytes), "unit-state fixture missing");
    auto source = parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
    require(bool(source), "zero-state source admission failed");
    mathematical::RealizationWork work;
    uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> capacity;
    auto candidate =
        protocol::prepareScopedFinite(*source, work, copy, siteBytes, capacity);
    require(bool(candidate) &&
                succeeded(protocol::verifyScopedFinitePreparation(
                    *source, *candidate, work)),
            "zero-state preparation or independent reading failed");
    exec::RejectOp stop;
    candidate->walk([&](exec::RejectOp op) {
      if (op->getParentOfType<func::FuncOp>()->hasAttr("runtime.region"))
        stop = op;
    });
    require(bool(stop), "effectful zero-result callback was dropped");
    auto body = stop->getParentOfType<func::FuncOp>();
    require(
        cast<exec::OutcomeType>(body.getResultTypes()[0]).getPayload().empty(),
        "zero-state callback acquired a value result");
    // Replace stopped execution with a successful zero-result completion.
    // Both bodies form, but only the original preserves the reached effect.
    body.getBody().dropAllReferences();
    body.getBody().getBlocks().clear();
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(body.addEntryBlock());
    exec::ScopedExecutionBuilder control(builder, body);
    control.complete({});
    require(succeeded(verify(*candidate)),
            "zero-result completion did not form");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    mathematical::RealizationWork checking;
    require(failed(protocol::verifyScopedFinitePreparation(*source, *candidate,
                                                           checking)),
            "zero-state stop was erased without refusal");
  });
  for (bool match : {false, true})
    for (unsigned mutation : {0u, 1u, 2u, 3u})
      cases.run(
          (match ? "exhaustive stopping match "
                 : "exhaustive stopping branch ") +
              std::to_string(mutation),
          [&] {
            auto bytes = llvm::MemoryBuffer::getFile(
                std::string(ZKC_FINITE_FIXTURES) +
                (match ? "/match.mlir" : "/stopping-branches.mlir"));
            require(bool(bytes), "stopping fixture missing");
            auto source =
                parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
            require(bool(source), "stopping source refused");
            if (match) {
              OpBuilder builder(&context);
              builder.setInsertionPointToEnd(&unit(*source).getBody().front());
              auto field = algebra::FieldType::get(&context, "bls12-381.fr");
              auto halt = func::FuncOp::create(
                  builder, builder.getUnknownLoc(), "halt",
                  builder.getFunctionType(
                      {runtime::ScopeType::get(&context), field},
                      {exec::OutcomeType::get(&context, {field})}));
              halt.setPrivate();
              halt.setNoInline(true);
              halt->setAttr("runtime.origin",
                            builder.getArrayAttr({builder.getStringAttr("halt"),
                                                  builder.getArrayAttr({})}));
              builder.setInsertionPointToEnd(halt.addEntryBlock());
              exec::ScopedExecutionBuilder stop(builder, halt);
              stop.reject("abort", "halt");
              func::FuncOp arm;
              source->walk([&](exec::CompleteOp op) {
                arm = op->getParentOfType<func::FuncOp>();
              });
              require(bool(arm), "missing returning match arm");
              arm.getBody().dropAllReferences();
              arm.getBody().getBlocks().clear();
              builder.setInsertionPointToEnd(arm.addEntryBlock());
              exec::ScopedExecutionBuilder control(builder, arm);
              auto result = control.invoke(
                  "func.call", {field}, control.scoped(arm.getArgument(1)),
                  {builder.getNamedAttr(
                       "callee", FlatSymbolRefAttr::get(&context, "halt")),
                   builder.getNamedAttr("runtime.site",
                                        builder.getStringAttr("left"))});
              control.complete(result);
            }
            require(succeeded(verify(*source)),
                    "stopping call source is malformed");
            mathematical::RealizationWork work;
            uint64_t copy = 1000000, bytesLeft = 16 * 1024 * 1024;
            std::optional<CapacityCause> capacity;
            auto candidate = protocol::prepareScopedFinite(*source, work, copy,
                                                           bytesLeft, capacity);
            require(bool(candidate) &&
                        succeeded(protocol::verifyScopedFinitePreparation(
                            *source, *candidate, work)),
                    "stopping control did not independently correspond");
            exec::RejectOp unreachable, reached;
            candidate->walk([&](exec::RejectOp op) {
              if (op.getSite().starts_with("unreachable_"))
                unreachable = op;
              else if (op->getParentOfType<func::FuncOp>()->hasAttr(
                           "runtime.region") &&
                       cast<exec::OutcomeType>(
                           op->getParentOfType<func::FuncOp>()
                               .getResultTypes()[0])
                           .getPayload()
                           .empty())
                reached = op;
            });
            require(bool(unreachable) && bool(reached),
                    "stopped arms or unreachable continuation missing");
            if (!mutation)
              return;
            if (mutation == 1)
              reached.setReason(reached.getReason() == "abort" ? "reject"
                                                               : "abort");
            else if (mutation == 2)
              unreachable.setReason("reject");
            else {
              auto arm = reached->getParentOfType<func::FuncOp>();
              arm.getBody().dropAllReferences();
              arm.getBody().getBlocks().clear();
              OpBuilder builder(&context);
              builder.setInsertionPointToEnd(arm.addEntryBlock());
              exec::ScopedExecutionBuilder control(builder, arm);
              control.complete({});
            }
            require(succeeded(verify(*candidate)),
                    "stopping mutation did not form");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            mathematical::RealizationWork checking;
            require(failed(protocol::verifyScopedFinitePreparation(
                        *source, *candidate, checking)),
                    "changed stopped control escaped independent comparison");
          });
  for (auto family :
       {std::pair{"sum", "vector.sum"}, std::pair{"product", "vector.product"},
        std::pair{"dot-large", "vector.dot"},
        std::pair{"collect", "numerical.map"},
        std::pair{"bilinear", "matrix.bilinear"},
        std::pair{"msm", "curve.msm"}}) {
    auto fixture = family.first;
    auto contract = family.second;
    for (unsigned mutation : {0u, 1u, 2u, 3u, 4u, 5u})
      cases.run(
          Twine("scoped bulk ") + fixture + " mutation " + Twine(mutation),
          [&] {
            auto bytes = llvm::MemoryBuffer::getFile(
                (Twine(ZKC_FINITE_FIXTURES) + "/" + fixture + ".mlir").str());
            require(bool(bytes), "bulk fixture missing");
            auto source =
                parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
            require(bool(source), "bulk source admission failed");
            func::FuncOp helper;
            source->walk([&](Operation *op) {
              if (auto fold = dyn_cast<exec::FoldOp>(op))
                helper = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
                    fold, fold.getStepAttr());
              else if (auto collect = dyn_cast<exec::CollectOp>(op))
                helper = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
                    collect, collect.getBodyAttr());
            });
            require(bool(helper), "bulk callback missing");
            mathematical::RealizationWork work;
            uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
            std::optional<CapacityCause> capacity;
            auto candidate = protocol::prepareScopedFinite(*source, work, copy,
                                                           siteBytes, capacity);
            require(bool(candidate), "bulk preparation failed");
            bool selected = false;
            candidate->walk([&](exec::ApplyOp op) {
              auto binding =
                  SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      op, op.getBindingAttr());
              selected |= binding && binding.getContract() == contract;
            });
            require(selected, "expected bulk payload was not selected");
            MathematicalSelectionPolicy policy;
            if (mutation == 1) {
              exec::ReturnOp end;
              helper.walk([&](exec::ReturnOp op) { end = op; });
              require(end && end->getNumOperands() == 1,
                      "callback return missing");
              Value replacement;
              for (Value argument : helper.getArguments().drop_front())
                if (argument.getType() == end->getOperand(0).getType()) {
                  replacement = argument;
                  break;
                }
              require(replacement && replacement != end->getOperand(0),
                      "source mutation is vacuous");
              end->setOperand(0, replacement);
              // Keep the retained ordinary helper synchronized. Only the
              // already generated bulk payload now disagrees with its actual
              // source.
              auto retained = SymbolTable::lookupSymbolIn(unit(*candidate),
                                                          helper.getSymName());
              require(bool(retained), "retained callback missing");
              retained->erase();
              unit(*candidate).getBody().front().push_back(helper->clone());
            } else if (mutation == 2) {
              auto function = cast<func::FuncOp>(
                  SymbolTable::lookupSymbolIn(unit(*candidate), "work"));
              exec::ReturnOp end;
              function.walk([&](exec::ReturnOp op) { end = op; });
              require(end && end->getNumOperands() == 1, "bulk return missing");
              Value replacement;
              for (Value argument : function.getArguments().drop_front())
                if (argument.getType() == end->getOperand(0).getType()) {
                  replacement = argument;
                  break;
                }
              if (replacement) {
                require(replacement != end->getOperand(0),
                        "candidate mutation is vacuous");
                end->setOperand(0, replacement);
              } else {
                exec::ApplyOp equality;
                function.walk([&](exec::ApplyOp op) {
                  auto binding =
                      SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                          op, op.getBindingAttr());
                  if (binding && binding.getContract() == "curve.equal")
                    equality = op;
                });
                require(equality && equality.getInputs().size() == 2 &&
                            equality.getInputs()[0] != equality.getInputs()[1],
                        "candidate terminal equality missing");
                equality->setOperand(2, equality.getInputs()[0]);
              }
            } else if (mutation == 3)
              policy.finiteBulk = false;
            else if (mutation == 4) {
              exec::ApplyOp original;
              helper.walk([&](exec::ApplyOp op) { original = op; });
              require(bool(original), "source primitive missing");
              auto binding =
                  SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      original, original.getBindingAttr());
              auto retained =
                  cast<runtime::BindingOp>(SymbolTable::lookupSymbolIn(
                      unit(*candidate), binding.getSymName()));
              std::string implementation =
                  "arkworks/" + binding.getContract().str();
              binding.setImplementation(implementation);
              retained.setImplementation(implementation);
            } else if (mutation == 5) {
              exec::ApplyOp payload;
              candidate->walk([&](exec::ApplyOp op) {
                auto binding =
                    SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                        op, op.getBindingAttr());
                if (binding && binding.getContract() == contract)
                  payload = op;
              });
              require(bool(payload), "bulk occurrence missing");
              payload.setSite("changed_bulk_occurrence");
            }
            require(succeeded(verify(*source)) && succeeded(verify(*candidate)),
                    "bulk mutation is malformed");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            mathematical::RealizationWork checking;
            bool accepted = succeeded(protocol::verifyScopedFinitePreparation(
                *source, *candidate, checking, policy));
            require(accepted == (mutation == 0),
                    "independent bulk correspondence accepted a changed "
                    "obligation");
          });
  }
  for (bool numerical : {false, true})
    cases.run(
        numerical ? "unused mathematical call retains bulk policy"
                  : "unused primitive retains implementation pin",
        [&] {
          auto bytes = llvm::MemoryBuffer::getFile(
              std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
          require(bool(bytes), "unused-operation fixture missing");
          auto source =
              parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
          require(bool(source), "unused-operation source refused");
          auto owner = unit(*source);
          auto step =
              cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "step"));
          auto add = cast<runtime::BindingOp>(
              SymbolTable::lookupSymbolIn(owner, "add"));
          auto field = step.getArgument(1).getType();
          OpBuilder builder(&context);
          builder.setInsertionPointToEnd(&owner.getBody().front());
          if (numerical) {
            auto helper = func::FuncOp::create(
                builder, step.getLoc(), "unused_math",
                builder.getFunctionType({field, field}, {field}));
            helper.setPrivate();
            builder.setInsertionPointToEnd(helper.addEntryBlock());
            OperationState state(step.getLoc(),
                                 algebra::FieldAddOp::getOperationName());
            state.addOperands(helper.getArguments());
            state.addTypes(field);
            auto *value = builder.create(state);
            func::ReturnOp::create(builder, step.getLoc(), value->getResults());
          } else {
            auto copied = cast<runtime::BindingOp>(builder.clone(*add));
            copied.setSymName("unused_add");
          }
          step.getBody().dropAllReferences();
          step.getBody().getBlocks().clear();
          builder.setInsertionPointToEnd(step.addEntryBlock());
          exec::ScopedExecutionBuilder control(builder, step);
          auto args = step.getArguments().slice(1, 2);
          SmallVector<NamedAttribute> attributes{
              builder.getNamedAttr(
                  numerical ? "callee" : "binding",
                  FlatSymbolRefAttr::get(&context, numerical ? "unused_math"
                                                             : "unused_add")),
              builder.getNamedAttr("site", builder.getStringAttr("unused"))};
          if (!numerical)
            attributes.push_back(
                builder.getNamedAttr("parameters", builder.getArrayAttr({})));
          (void)control.invoke(numerical ? "exec.compute" : "exec.apply",
                               {field}, control.scoped(args), attributes);
          auto value = control.invoke(
              "exec.apply", {field}, control.scoped(args),
              {builder.getNamedAttr("binding",
                                    FlatSymbolRefAttr::get(&context, "add")),
               builder.getNamedAttr("parameters", builder.getArrayAttr({})),
               builder.getNamedAttr("site", builder.getStringAttr("sum"))});
          control.returned(value);
          require(succeeded(verify(*source)),
                  "unused-operation graph malformed");
          auto prepareCandidate = [&]() {
            mathematical::RealizationWork work;
            uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
            std::optional<CapacityCause> capacity;
            return protocol::prepareScopedFinite(*source, work, copy, siteBytes,
                                                 capacity);
          };
          auto candidate = prepareCandidate();
          require(bool(candidate), "unrestricted unused work refused");
          bool bulk = false;
          candidate->walk([&](runtime::BindingOp binding) {
            bulk |= binding.getContract() == "vector.sum";
          });
          require(bulk, "unrestricted unused work prevented the bulk control");
          for (ModuleOp module : {*source, *candidate}) {
            if (numerical) {
              auto retained = cast<func::FuncOp>(
                  SymbolTable::lookupSymbolIn(unit(module), "step"));
              retained.walk([&](exec::ComputeOp call) {
                call.setPolicyAttr(builder.getArrayAttr(
                    {builder.getBoolAttr(false), builder.getBoolAttr(true),
                     builder.getBoolAttr(true)}));
              });
            } else {
              auto retained = cast<runtime::BindingOp>(
                  SymbolTable::lookupSymbolIn(unit(module), "unused_add"));
              retained.setImplementation("arkworks/field.add");
            }
            require(succeeded(verify(module)),
                    "unused restriction mutation malformed");
          }
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          mathematical::RealizationWork checking;
          require(
              failed(protocol::verifyScopedFinitePreparation(
                  *source, *candidate, checking)),
              "independent reader dropped an unused replacement restriction");
          auto ordered = prepareCandidate();
          require(bool(ordered),
                  "restricted callback lost the ordered fallback");
          bool loop = false;
          ordered->walk([&](exec::RangeOp) { loop = true; });
          require(loop, "producer erased an unused replacement restriction");
        });
  cases.run(
      "physical requests independently restrict scoped bulk replacement", [&] {
        auto bytes = llvm::MemoryBuffer::getFile(
            std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
        require(bool(bytes), "physical-request fixture missing");
        auto source =
            parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
        require(bool(source), "physical-request source refused");
        auto binding = SymbolTable::lookupSymbolIn(unit(*source), "add");
        llvm::DenseSet<Operation *> fixed{binding};
        auto propose = [&](bool restricted) {
          mathematical::RealizationWork work;
          uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
          std::optional<CapacityCause> capacity;
          return protocol::prepareScopedFinite(*source, work, copy, siteBytes,
                                               capacity, {},
                                               restricted ? &fixed : nullptr);
        };
        auto bulk = propose(false);
        require(bool(bulk), "unrestricted bulk proposal failed");
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        mathematical::RealizationWork checking;
        require(failed(protocol::verifyScopedFinitePreparation(
                    *source, *bulk, checking, {}, nullptr, &fixed)),
                "independent reader ignored an explicit physical request");
        auto ordered = propose(true);
        require(bool(ordered),
                "explicit physical request lost ordered execution");
        bool loop = false;
        ordered->walk([&](exec::RangeOp) { loop = true; });
        require(loop, "physical request was erased by bulk selection");
      });
  for (auto family : {std::pair{"sum", "vector.sum"},
                      {"product", "vector.product"},
                      {"dot-large", "vector.dot"},
                      {"bilinear", "matrix.bilinear"},
                      {"collect", "numerical.map"},
                      {"msm", "curve.msm"}}) {
    auto fixture = family.first;
    auto contract = family.second;
    cases.run(Twine("physical catalog fallback for scoped ") + fixture, [&] {
      auto bytes = llvm::MemoryBuffer::getFile(
          (Twine(ZKC_FINITE_FIXTURES) + "/" + fixture + ".mlir").str());
      require(bool(bytes), "physical fallback fixture missing");
      auto source =
          parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
      require(bool(source), "physical fallback source refused");
      prepare(*source);
      lower(*source);
      auto baseline = take(target::proposePhysical(*source));
      auto baselineSubject = take(baseline.cloneSelectedSubject(*source));
      require(usesContract(*baselineSubject, contract),
              "available bulk control was not selected");
      auto before = dump(*source);
      WithheldCatalog catalog({contract});
      auto proposal = take(target::proposePhysical(*source, catalog));
      auto checked = take(target::validatePhysical(*source, proposal, catalog));
      auto selected = take(checked.cloneSelectedSubject(*source));
      require(!usesContract(*selected, contract),
              "unavailable bulk implementation survived selection");
      require(dump(*source) == before, "physical search mutated the source");
    });
  }
  cases.run("physical request survives scoped finite selection", [&] {
    auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_FINITE_FIXTURES) +
                                             "/sum.mlir");
    require(bool(bytes), "physical request fixture missing");
    auto source = parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
    require(bool(source), "physical request source refused");
    prepare(*source);
    lower(*source);
    auto proposal =
        take(target::proposePhysical(*source, target::installedCandidates(),
                                     {{"add", "arkworks/field.add"}}));
    auto checked = take(target::validatePhysical(*source, proposal));
    auto selected = take(checked.cloneSelectedSubject(*source));
    require(!usesContract(*selected, "vector.sum"),
            "explicit scalar request was replaced by bulk work");
    bool fixed = false;
    for (const auto &binding : checked.choices().bindings)
      fixed |=
          binding.binding.name == "add" && binding.fixed &&
          binding.binding.application.implementation == "arkworks/field.add";
    require(fixed, "physical request was lost from the checked plan");
  });
  cases.run(
      "scoped physical fallback retains an unrelated bulk occurrence", [&] {
        auto bytes = llvm::MemoryBuffer::getFile(
            std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
        require(bool(bytes), "mixed finite fixture missing");
        auto source =
            parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
        require(bool(source), "mixed finite source refused");
        auto owner = unit(*source);
        OpBuilder builder(&context);
        builder.setInsertionPointToEnd(&owner.getBody().front());
        auto multiply = cast<runtime::BindingOp>(
            builder.clone(*SymbolTable::lookupSymbolIn(owner, "add")));
        multiply.setSymName("multiply");
        multiply.setContract("field.mul");
        auto step = cast<func::FuncOp>(
            builder.clone(*SymbolTable::lookupSymbolIn(owner, "step")));
        step.setSymName("other_step");
        step->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr("other_step"),
                                            builder.getArrayAttr({})}));
        step.walk([&](exec::ApplyOp op) {
          op.setBindingAttr(FlatSymbolRefAttr::get(&context, "multiply"));
        });
        auto work = cast<func::FuncOp>(
            builder.clone(*SymbolTable::lookupSymbolIn(owner, "work")));
        work.setSymName("other_work");
        work->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr("other_work"),
                                            builder.getArrayAttr({})}));
        work.walk([&](exec::FoldOp op) {
          op.setStepAttr(FlatSymbolRefAttr::get(&context, "other_step"));
          op.setSite("other_fold");
        });
        prepare(*source);
        lower(*source);
        auto before = dump(*source);
        WithheldCatalog catalog(
            {"vector.sum", "numerical.sum", "numerical.map", "vector.map"});
        auto proposal = take(target::proposePhysical(*source, catalog));
        auto checked =
            take(target::validatePhysical(*source, proposal, catalog));
        auto selected = take(checked.cloneSelectedSubject(*source));
        require(
            !usesContract(*selected, "vector.sum") &&
                !usesContract(*selected, "numerical.sum") &&
                usesContract(*selected, "vector.product"),
            "targeted fallback discarded an available independent bulk recipe");
        bool loop = false;
        selected->walk([&](exec::RangeOp) { loop = true; });
        require(loop, "unavailable sum did not reach its ordered endpoint");
        require(dump(*source) == before, "mixed fallback changed the original");
      });
  cases.run(
      "unrelated finite choices preserve outlined invocation identities", [&] {
        auto bytes = llvm::MemoryBuffer::getFile(
            std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
        require(bool(bytes), "invocation identity fixture missing");
        auto source =
            parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
        require(bool(source), "invocation identity source refused");
        auto owner = unit(*source);
        OpBuilder builder(&context);
        builder.setInsertionPointToEnd(&owner.getBody().front());
        auto step = cast<func::FuncOp>(
            builder.clone(*SymbolTable::lookupSymbolIn(owner, "step")));
        step.setSymName("other_step");
        step->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr("other_step"),
                                            builder.getArrayAttr({})}));
        auto work = cast<func::FuncOp>(
            builder.clone(*SymbolTable::lookupSymbolIn(owner, "work")));
        work.setSymName("other_work");
        work->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr("other_work"),
                                            builder.getArrayAttr({})}));
        work.walk([&](exec::FoldOp op) {
          op.setStepAttr(FlatSymbolRefAttr::get(&context, "other_step"));
        });
        auto field = step.getArgument(1).getType();
        auto helper = func::FuncOp::create(
            builder, step.getLoc(), "other_math",
            builder.getFunctionType({field, field}, {field}));
        helper.setPrivate();
        builder.setInsertionPointToEnd(helper.addEntryBlock());
        OperationState multiply(step.getLoc(),
                                algebra::FieldMultiplyOp::getOperationName());
        multiply.addOperands(helper.getArguments());
        multiply.addTypes(field);
        auto *product = builder.create(multiply);
        func::ReturnOp::create(builder, step.getLoc(), product->getResults());
        exec::ApplyOp original;
        step.walk([&](exec::ApplyOp op) { original = op; });
        builder.setInsertionPoint(original);
        OperationState compute(original.getLoc(),
                               exec::ComputeOp::getOperationName());
        compute.addOperands(original->getOperands());
        compute.addTypes(original->getResultTypes());
        compute.addAttribute("callee",
                             FlatSymbolRefAttr::get(&context, "other_math"));
        compute.addAttribute("site", builder.getStringAttr("other_compute"));
        compute.addAttribute("policy",
                             builder.getArrayAttr({builder.getBoolAttr(false),
                                                   builder.getBoolAttr(true),
                                                   builder.getBoolAttr(true)}));
        auto *replacement = builder.create(compute);
        original->replaceAllUsesWith(replacement->getResults());
        original.erase();
        require(succeeded(verify(*source)), "invocation control is malformed");
        auto prepared = [&] {
          mathematical::RealizationWork budget;
          uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
          std::optional<CapacityCause> capacity;
          auto result = protocol::prepareScopedFinite(*source, budget, copy,
                                                      siteBytes, capacity);
          require(bool(result), "invocation control preparation refused");
          return result;
        };
        auto before = prepared();
        auto binding =
            cast<runtime::BindingOp>(SymbolTable::lookupSymbolIn(owner, "add"));
        binding.setImplementation("arkworks/field.add");
        auto after = prepared();
        auto identities = [&](ModuleOp module) {
          std::map<std::string, std::string> result;
          module.walk([&](exec::ComputeOp op) {
            auto function = op->getParentOfType<func::FuncOp>();
            if (function && function->hasAttr("runtime.region"))
              require(
                  result
                      .emplace(op.getSite().str(), function.getSymName().str())
                      .second,
                  "duplicate outlined invocation coordinate");
          });
          return result;
        };
        require(usesContract(*before, "vector.sum") &&
                    !usesContract(*after, "vector.sum"),
                "identity control did not change the unrelated recipe");
        auto expected = identities(*before);
        require(!expected.empty() && expected == identities(*after),
                "unrelated fallback renumbered a numerical invocation");
      });
  cases.run(
      "scoped bulk retries when a provider conversion is unavailable", [&] {
        class ResidentSum final : public target::CandidateCatalog {
          bool adapters;

        public:
          explicit ResidentSum(bool adapters) : adapters(adapters) {}
          llvm::Expected<std::vector<std::string>> implementations(
              const protocol::BindingApplication &application) const override {
            if (application.contract == "vector.sum")
              return std::vector<std::string>{"blst/resident/vector.sum"};
            return target::installedCandidates().implementations(application);
          }
          std::vector<protocol::BindingApplication>
          conversions(const protocol::BoundType &from,
                      const protocol::BoundType &to) const override {
            return adapters
                       ? target::installedCandidates().conversions(from, to)
                       : std::vector<protocol::BindingApplication>{};
          }
        };
        auto bytes = llvm::MemoryBuffer::getFile(
            std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
        require(bool(bytes), "conversion fallback fixture missing");
        auto source =
            parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
        require(bool(source), "conversion fallback source refused");
        prepare(*source);
        lower(*source);
        ResidentSum available(true), unavailable(false);
        auto baseline = take(target::proposePhysical(*source, available));
        auto checkedBaseline =
            take(target::validatePhysical(*source, baseline, available));
        bool resident = false;
        for (const auto &binding : checkedBaseline.choices().bindings)
          resident |= binding.binding.application.implementation ==
                      "blst/resident/vector.sum";
        require(resident, "resident conversion control did not select sum");
        auto proposal = take(target::proposePhysical(*source, unavailable));
        auto checked =
            take(target::validatePhysical(*source, proposal, unavailable));
        auto selected = take(checked.cloneSelectedSubject(*source));
        require(!usesContract(*selected, "vector.sum"),
                "missing physical conversion did not advance the finite "
                "occurrence");
        bool loop = false;
        selected->walk([&](exec::RangeOp) { loop = true; });
        require(loop || usesContract(*selected, "numerical.sum"),
                "resident conversion refusal lost an executable sum");
      });
  cases.run("scoped bulk respects attributable program capacity", [&] {
    auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_FINITE_FIXTURES) +
                                             "/sum.mlir");
    require(bool(bytes), "program capacity fixture missing");
    auto source = parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
    require(bool(source), "program capacity source refused");
    prepare(*source);
    lower(*source);
    target::PhysicalPlanOptions options;
    unsigned refused = 0;
    options.programCapacity = [&](ModuleOp candidate,
                                  const target::PhysicalPlan &)
        -> llvm::Expected<SmallVector<target::OperationIndex>> {
      SmallVector<target::OperationIndex> result;
      for (auto entry :
           llvm::enumerate(target::physicalPlanOperations(candidate))) {
        auto op = dyn_cast<exec::ApplyOp>(entry.value());
        if (!op)
          continue;
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            op, op.getBindingAttr());
        if (binding && binding.getContract() == "vector.sum") {
          result.push_back(entry.index());
          ++refused;
        }
      }
      return result;
    };
    auto proposal = take(target::proposePhysical(
        *source, target::installedCandidates(), {}, options));
    auto checked = take(target::validatePhysical(*source, proposal));
    auto selected = take(checked.cloneSelectedSubject(*source));
    require(refused && !usesContract(*selected, "vector.sum"),
            "attributable escaped-program capacity did not trigger a retry");
  });
  for (unsigned limit : {0u, 1u, 2u, 3u, 4u})
    cases.run(Twine("physical scoped finite reserve ") + Twine(limit), [&] {
      auto bytes = llvm::MemoryBuffer::getFile(
          std::string(ZKC_FINITE_FIXTURES) + "/sum.mlir");
      require(bool(bytes), "physical reserve fixture missing");
      auto source =
          parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
      require(bool(source), "physical reserve source refused");
      prepare(*source);
      lower(*source);
      mathematical::RealizationWork work;
      if (limit == 0)
        work.discardedRecipeCopy = 1;
      if (limit == 1)
        work.discardedRecipeSiteBytes = 1;
      if (limit == 2)
        work.discardedRecipeExpansion = 0;
      if (limit == 3)
        work.optionalFiniteChecking = 0;
      if (limit == 4)
        work.requiredFiniteChecking = 0;
      target::PhysicalPlanOptions options;
      options.numericalWork = &work;
      uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
      options.numericalCopy = &copy;
      options.numericalSiteBytes = &siteBytes;
      auto proposal = target::proposePhysical(
          *source, target::installedCandidates(), {}, options);
      if (limit == 4) {
        refuses(std::move(proposal), "computation-realization");
        require(!work.requiredFiniteChecking,
                "required checking was replenished on refusal");
        return;
      }
      auto checked =
          take(target::validatePhysical(*source, take(std::move(proposal))));
      auto selected = take(checked.cloneSelectedSubject(*source));
      require(!usesContract(*selected, "vector.sum"),
              "exhausted optional reserve retained a bulk candidate");
      bool loop = false;
      selected->walk([&](exec::RangeOp) { loop = true; });
      require(
          loop && copy < 1000000 && siteBytes < 16 * 1024 * 1024,
          "required endpoint or cumulative construction accounting was lost");
      require(!work.numericalSelection && !work.numericalOccurrence,
              "caller retained transient selection pointers");
    });
  for (unsigned limit : {0u, 1u, 2u, 3u, 4u, 5u, 6u})
    cases.run(Twine("scoped bulk cumulative capacity ") + Twine(limit), [&] {
      auto bytes = llvm::MemoryBuffer::getFile(
          std::string(ZKC_FINITE_FIXTURES) + "/collect.mlir");
      require(bool(bytes), "capacity fixture missing");
      auto source =
          parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
      require(bool(source), "capacity source refused");
      mathematical::RealizationWork work;
      MathematicalSelectionPolicy policy;
      if (limit == 0)
        policy.finiteBulk = false;
      else if (limit == 1)
        work.matching.structural = 0;
      else if (limit == 2)
        work.matching.equations = 0;
      else if (limit == 3)
        work.lanes = 0;
      else if (limit == 4)
        work.optionalFiniteChecking = 0;
      else if (limit == 5)
        work.discardedRecipeCopy = 1;
      else
        work.requiredFiniteChecking = 0;
      uint64_t copy = 1000000, siteBytes = 16 * 1024 * 1024;
      std::optional<CapacityCause> capacity;
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      auto candidate = protocol::prepareScopedFinite(
          *source, work, copy, siteBytes, capacity, policy);
      if (limit == 6) {
        require(!candidate, "required admission exhaustion was bypassed");
        return;
      }
      require(bool(candidate), "optional capacity lost the ordered path");
      bool loop = false;
      candidate->walk([&](exec::RangeOp) { loop = true; });
      require(loop, "optional refusal did not retain ordered traversal");
      mathematical::RealizationWork checking;
      require(succeeded(protocol::verifyScopedFinitePreparation(
                  *source, *candidate, checking, policy)),
              "ordered retry failed independent comparison");
      if (limit == 1)
        require(work.matching.structural == 0,
                "structural work was replenished");
      if (limit == 4)
        require(work.optionalFiniteChecking == 0 &&
                    work.discardedRecipeCopy <
                        mathematical::RealizationWork{}.discardedRecipeCopy,
                "discarded proposal was not cumulatively accounted");
    });
  for (StringRef fixture :
       {"total-state", "total-predicate", "total-collect", "nested-total"})
    cases.run("full direct source/candidate correspondence " + fixture, [&] {
      auto bytes = llvm::MemoryBuffer::getFile(
          (Twine(ZKC_FINITE_FIXTURES) + "/" + fixture + ".mlir").str());
      require(bool(bytes), "fixture missing");
      auto source =
          parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
      require(bool(source), "source admission failed");
      prepare(*source);
      auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
      lower(*candidate);
      require(succeeded(mathematical::verifyMathLowering(unit(*source),
                                                         unit(*candidate))),
              "independent complete reader refused direct lowering");
      auto logical = OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate->clone()));
      require(succeeded(computation::realizeComputations(*candidate)) &&
                  succeeded(computation::verifyComputationRealization(
                      *logical, *candidate)),
              "complete Kernel recipe reader refused direct lowering");
      if (measure) {
        auto time = [](auto action) {
          auto start = std::chrono::steady_clock::now();
          require(succeeded(action()), "measurement check refused");
          return std::chrono::duration<double, std::micro>(
                     std::chrono::steady_clock::now() - start)
              .count();
        };
        SmallVector<double> formation, correspondence;
        for (unsigned i = 0; i < 34; ++i) {
          double f = time([&] { return verify(*candidate); });
          double c = time([&] {
            return computation::verifyComputationRealization(*logical,
                                                             *candidate);
          });
          if (i >= 3) {
            formation.push_back(f);
            correspondence.push_back(c);
          }
        }
        llvm::sort(formation);
        llvm::sort(correspondence);
        unsigned sourceOps = 0, candidateOps = 0;
        source->walk([&](Operation *) { ++sourceOps; });
        candidate->walk([&](Operation *) { ++candidateOps; });
        llvm::outs() << "measurement " << fixture << " source_ops=" << sourceOps
                     << " candidate_ops=" << candidateOps
                     << " formation_median_us=" << formation[15]
                     << " formation_p95_us=" << formation[29]
                     << " correspondence_median_us=" << correspondence[15]
                     << " correspondence_p95_us=" << correspondence[29] << '\n';
      }
      unsigned temporary = 0;
      candidate->walk([&](func::FuncOp function) {
        temporary += function.getSymName().starts_with("_finite_expression_");
      });
      require(!temporary, "temporary emission function retained");
    });
  return cases.result();
}
