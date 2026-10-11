#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
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
 func.func private @step(%a:!F,%b:!F,%item:!F,%xs:!V,%copy:!V,%factor:!F,%enabled:i1)->(!F,!F) {
   func.return %b,%factor : !F,!F
 }
 func.func private @predicate(%item:!F,%xs:!V,%copy:!V,%factor:!F,%enabled:i1)->i1 {
   func.return %enabled : i1
 }
 "protocol.func"() ({ ^entry(%xs:!V,%a:!F,%b:!F,%enabled:i1):
   %r:2 = "algebra.finite_fold"(%xs,%a,%b,%xs,%a,%enabled) {domain=@items,step=@step,predicate=@predicate} : (!V,!F,!F,!V,!F,i1)->(!F,!F)
   "protocol.return"(%r#0,%r#1) : (!F,!F)->()
 }) {sym_name="main",function_type=(!V,!F,!F,i1)->(!F,!F),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
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
 }) {sym_name="main",function_type=(ui64,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
void prepare(ModuleOp module) {
  PassManager passes(module.getContext());
  passes.addPass(protocol::createProjectProtocolPass(false, {false, false}));
  passes.addPass(protocol::createEliminatePolynomialsPass());
  require(succeeded(passes.run(module)), "preparation failed");
}
void lower(ModuleOp module) {
  PassManager passes(module.getContext());
  passes.addPass(protocol::createLowerMathPass({false, false}));
  require(succeeded(passes.run(module)), "direct lowering failed");
}
Operation *expression(ModuleOp module) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    if (finite::isComputation(op) && !finite::isDeclaration(op))
      result = op;
  });
  require(result, "missing expression");
  return result;
}
struct Insertions : OpBuilder::Listener {
  unsigned operations = 0, blocks = 0, functions = 0, temporary = 0;
  void notifyOperationInserted(Operation *op, OpBuilder::InsertPoint) override {
    ++operations;
    functions += isa<local::FuncOp>(op);
    auto name = SymbolTable::getSymbolName(op);
    temporary += name && name.getValue().starts_with("_finite_expression_");
  }
  void notifyBlockInserted(Block *, Region *, Region::iterator) override {
    ++blocks;
  }
};
} // namespace
int main(int argc, char **argv) {
  bool measure = argc == 2 && StringRef(argv[1]) == "--measure";
  require(argc == 1 || measure, "expected optional --measure");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "direct inline aliases use tracked blocks and fresh reader ABI", [&] {
        auto source = parseSourceString<ModuleOp>(aliasSource, &context);
        require(bool(source), "alias source admission failed");
        prepare(*source);
        auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
        auto *original = expression(*source);
        // The public emitter operates inside an existing Local candidate,
        // after the parent phase has assigned an occurrence site.
        SmallVector<Value> unique;
        for (Value value : original->getOperands())
          if (!llvm::is_contained(unique, value))
            unique.push_back(value);
        OpBuilder setup(&context);
        setup.setInsertionPointToEnd(&unit(*candidate).getBody().front());
        auto function = local::FuncOp::create(
            setup, original->getLoc(), "direct_test",
            setup.getFunctionType(ValueRange(unique).getTypes(),
                                  original->getResultTypes()));
        function->setAttr(
            "logical_origin",
            setup.getArrayAttr(
                {setup.getStringAttr("direct_test"), setup.getArrayAttr({})}));
        auto *block = function.addEntryBlock();
        setup.setInsertionPointToEnd(block);
        IRMapping mapping;
        for (auto [before, after] : llvm::zip(unique, block->getArguments()))
          mapping.map(before, after);
        auto *op = setup.clone(*original, mapping);
        auto after = local::ReturnOp::create(setup, original->getLoc(),
                                             op->getResults());
        SmallVector<Value> inputs(op->getOperands());
        op->setAttr("site", StringAttr::get(&context, "direct"));
        Insertions listener;
        OpBuilder builder(&context, &listener);
        builder.setInsertionPoint(op);
        mathematical::RealizationWork work;
        auto emitted = finite::realizeExpression(op, inputs, builder,
                                                 {false, false}, &work);
        require(succeeded(emitted), "direct body emission failed");
        Operation *begin = &block->front();
        IRRewriter rewriter(&context);
        rewriter.replaceOp(op, *emitted);
        require(
            listener.operations && listener.blocks >= 3 &&
                !listener.functions && !listener.temporary,
            "emission bypassed listener or constructed a temporary function");
        require(work.helperOperations < 100000 && succeeded(verify(*candidate)),
                "direct candidate lost shared work or isolated ownership");
        // This fixture's callbacks only forward formals. Interpret the
        // immutable source return directly, never the emitter's environments or
        // selections.
        auto reader = [&](Operation *helper, ValueRange args,
                          Operation *&) -> FailureOr<SmallVector<Value>> {
          auto &body = helper->getRegion(0).front();
          if (body.getOperations().size() != 1 ||
              !isa<func::ReturnOp>(body.back()))
            return failure();
          SmallVector<Value> results;
          for (Value value : body.back().getOperands()) {
            auto formal = dyn_cast<BlockArgument>(value);
            if (!formal || formal.getOwner() != &body ||
                formal.getArgNumber() >= args.size())
              return failure();
            results.push_back(args[formal.getArgNumber()]);
          }
          return results;
        };
        auto *cursor = begin;
        auto checked = finite::verifyExpression(original, inputs, cursor,
                                                reader, unit(*source));
        require(succeeded(checked) && *checked == *emitted && cursor == after,
                "independent inline reader refused direct body");
        local::LocalForOp loop;
        candidate->walk([&](local::LocalForOp value) {
          if (value->getNumResults() == 2)
            loop = value;
        });
        require(bool(loop), "missing state loop");
        // Two states stay separate from one shared invariant seed capture.
        require(loop->getNumOperands() == 8 &&
                    loop->getRegion(0).front().getNumArguments() == 7,
                "aliased invariant captures were not canonicalized");
        require(loop->getOperand(2) == inputs[1] &&
                    loop->getOperand(3) == inputs[2],
                "zero-trip state no longer uses exact ordered seeds");
        loop->setOperand(2, inputs[2]);
        require(succeeded(verify(*candidate)), "changed seed is not admitted");
        cursor = begin;
        require(failed(finite::verifyExpression(original, inputs, cursor,
                                                reader, unit(*source))),
                "changed zero-trip seed escaped correspondence");
        loop->setOperand(2, inputs[1]);
        local::LocalIfOp branch;
        loop.walk([&](local::LocalIfOp value) { branch = value; });
        require(bool(branch), "missing predicate branch");
        auto &returned = branch->getRegion(0).front().back();
        Value first = returned.getOperand(0), second = returned.getOperand(1);
        returned.setOperands({second, first});
        require(succeeded(verify(*candidate)),
                "return permutation is not admitted");
        cursor = begin;
        require(failed(finite::verifyExpression(original, inputs, cursor,
                                                reader, unit(*source))),
                "same-typed state permutation escaped actual inline reading");
      });
  cases.run("aliased range bounds canonicalize admission branch captures", [&] {
    auto source = parseSourceString<ModuleOp>(rangeAliasSource, &context);
    require(bool(source), "aliased range source refused");
    prepare(*source);
    auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    lower(*candidate);
    require(succeeded(mathematical::verifyMathLowering(unit(*source),
                                                       unit(*candidate))),
            "aliased range direct body did not correspond");
    unsigned branches = 0;
    candidate->walk([&](local::LocalIfOp branch) {
      ++branches;
      require(branch->getNumOperands() == 2 &&
                  branch->getRegion(0).front().getNumArguments() == 1,
              "aliased admission bounds became duplicate captures");
    });
    require(branches == 1, "range admission disappeared");
  });
  cases.run("zero-state Local stop survives declaration body emission", [&] {
    auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_FINITE_FIXTURES) +
                                             "/unit-state.mlir");
    require(bool(bytes), "unit-state fixture missing");
    auto source = parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
    require(bool(source), "zero-state source admission failed");
    auto candidate = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
    require(succeeded(finite::realizeLocals(*candidate, {false, false})) &&
                succeeded(finite::verifyRealizations(*source, *candidate)),
            "zero-state stop realization or independent reading failed");
    auto function = dyn_cast_or_null<local::FuncOp>(
        SymbolTable::lookupSymbolIn(unit(*candidate), "fold"));
    require(bool(function) && function.getFunctionType().getNumResults() == 0,
            "zero-state fold became a collect");
    local::ApplyOp step;
    function.walk([&](local::ApplyOp call) {
      if (call.getCallee() == "step")
        step = call;
    });
    require(bool(step), "effectful zero-result step was dropped");
    // The remaining loop still forms after dropping the zero-result call,
    // but correspondence must observe that the terminal effect disappeared.
    step.erase();
    require(succeeded(verify(*candidate)),
            "zero-result call removal did not form");
    ScopedDiagnosticHandler handler(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(finite::verifyRealizations(*source, *candidate)),
            "zero-state stop was erased without correspondence refusal");
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
            return mathematical::verifyMathLowering(unit(*source),
                                                    unit(*candidate));
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
      candidate->walk([&](local::FuncOp function) {
        temporary += function.getSymName().starts_with("_finite_expression_");
      });
      require(!temporary, "temporary emission function retained");
    });
  return cases.result();
}
