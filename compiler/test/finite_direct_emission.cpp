#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "../lib/Transforms/ScopedCandidate.h"
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
#include "zkc/Transforms/Kernel.h"
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
        require(succeeded(kernel::verifyRecipeOutput(*candidate.module)),
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
    require(succeeded(kernel::lowerKernels(*candidate)) &&
                succeeded(kernel::verifyKernelLowering(*logical, *candidate)),
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
      require(succeeded(kernel::lowerKernels(*candidate)) &&
                  succeeded(kernel::verifyKernelLowering(*logical, *candidate)),
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
            return kernel::verifyKernelLowering(*logical, *candidate);
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
