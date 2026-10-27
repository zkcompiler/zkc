#include "../lib/Transforms/Computation/Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/ComputationRecipes.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include <functional>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace sc = scopedComputation;
namespace sf = scopedFinite;
constexpr llvm::StringLiteral realization = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @difference(%a:!F,%b:!F)->!F {
   %v = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %v : !F
 }
 func.func @realized(%scope:!runtime.scope,%a:!F,%b:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["realized",[]]} {
   %call = "exec.compute"(%scope,%a,%b) {callee=@difference,site="kernel"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 func.func @work(%scope:!runtime.scope,%a:!F,%b:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %call = "func.call"(%scope,%a,%b) {callee=@realized,runtime.site="difference"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(!F)>)->()
 ^done(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^failed(%stop:!exec.stop):
   %failure = "exec.failed"(%stop) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %v = "protocol.local_call"(%a,%b) {callee=@work,site="work",role="P"} : (!F,!F)->!F
   "protocol.return"(%v) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr llvm::StringLiteral demanded = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %product = algebra.field_multiply %difference,%b : (!F,!F)->!F
   "protocol.return"(%difference,%product) : (!F,!F)->()
 }) {sym_name="main",function_type=(!F,!F)->(!F,!F),roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr llvm::StringLiteral guarded = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %condition = algebra.field_equal %a,%b : (!F,!F)->i1
   protocol.guard %condition {site="check",owner="P"}
   "protocol.return"(%a) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
OwningOpRef<mlir::ModuleOp> parse(StringRef text, MLIRContext &context) {
  auto result = parseSourceString<mlir::ModuleOp>(text, &context);
  require(bool(result), "fixture did not parse/admit");
  return result;
}
OwningOpRef<mlir::ModuleOp> copy(mlir::ModuleOp module) {
  return OwningOpRef<mlir::ModuleOp>(cast<mlir::ModuleOp>(module->clone()));
}
protocol_ir::ProtocolModuleOp owner(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
void run(mlir::ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "compiler pass refused");
}
exec::ComputeOp computationFixture(mlir::ModuleOp module) {
  exec::ComputeOp result;
  module.walk([&](exec::ComputeOp call) {
    if (!result)
      result = call;
  });
  require(bool(result), "missing actual computation request");
  return result;
}
func::FuncOp numericalEntry(mlir::ModuleOp module) {
  SymbolTableCollection symbols;
  auto result = computationFixture(module).resolveCallee(symbols);
  require(bool(result), "missing actual mathematical helper");
  return result;
}
mlir::ModuleOp numericalUnit(mlir::ModuleOp module) {
  auto result = dyn_cast<mlir::ModuleOp>(numericalEntry(module)->getParentOp());
  require(result && mathematical::isComputationUnit(result),
          "expected a closed selected calculation");
  return result;
}
func::FuncOp scopedFunction(mlir::ModuleOp module, StringRef name) {
  auto result = SymbolTable(owner(module)).lookup<func::FuncOp>(name);
  require(bool(result), "missing scoped function");
  return result;
}
OwningOpRef<mlir::ModuleOp> close(func::FuncOp helper) {
  uint64_t remaining = 1000000;
  auto result = computation::closeComputation(helper, remaining);
  require(bool(result), "mathematical closure refused");
  return result;
}
OwningOpRef<mlir::ModuleOp> closedFixture(mlir::ModuleOp source) {
  auto result = copy(source);
  auto call = computationFixture(*result);
  SymbolTableCollection symbols;
  auto closure = close(call.resolveCallee(symbols));
  auto entry = mathematical::getComputationEntry(*closure);
  SymbolTable table(owner(*result));
  auto name = table.insert(closure.release());
  call.setCalleeAttr(SymbolRefAttr::get(
      name, {FlatSymbolRefAttr::get(entry.getSymNameAttr())}));
  require(succeeded(verify(*result)), "closed computation fixture refused");
  return result;
}
OwningOpRef<mlir::ModuleOp> fixture(MLIRContext &context, StringRef path) {
  auto bytes = llvm::MemoryBuffer::getFile(
      (Twine(ZKC_COMPUTATION_FIXTURES) + "/" + path).str());
  require(bool(bytes), "cannot read computation fixture");
  return parse((*bytes)->getBuffer(), context);
}
void expectRefusal(mlir::ModuleOp candidate, StringRef code,
                   llvm::function_ref<LogicalResult()> check) {
  bool diagnostic = false;
  std::string messages;
  ScopedDiagnosticHandler handler(
      candidate.getContext(), [&](Diagnostic &value) {
        messages += value.str();
        diagnostic |= value.str().find(code.str()) != std::string::npos;
        return success();
      });
  require(failed(check()), "mutated correspondence was accepted");
  require(diagnostic, "refusal lost " + code + ": " + messages);
}
OwningOpRef<mlir::ModuleOp>
formExecutable(mlir::ModuleOp source, MathematicalSelectionPolicy policy = {}) {
  auto result = copy(source);
  run(*result, protocol::createProjectProtocolPass(false, policy));
  run(*result, protocol::createLowerMathPass(policy));
  require(owner(*result).getProfile() == protocol_ir::Profile::Exec,
          "lower-math did not produce Exec");
  return result;
}
protocol_ir::LocalCallOp appendReturns(func::FuncOp function,
                                       protocol_ir::LocalCallOp invocation,
                                       ValueRange values) {
  auto returned = sc::returned(function);
  returned->insertOperands(returned.getNumOperands(), values);
  auto outcome = exec::OutcomeType::get(
      function.getContext(), llvm::to_vector(returned->getOperandTypes()));
  returned.getOutcome().setType(outcome);
  function.walk(
      [&](exec::FailureOp failure) { failure.getResult().setType(outcome); });
  OpBuilder builder(invocation);
  function.setFunctionType(
      builder.getFunctionType(function.getArgumentTypes(), outcome));
  OperationState state(invocation.getLoc(),
                       protocol_ir::LocalCallOp::getOperationName());
  state.addOperands(invocation.getInputs());
  state.addTypes(outcome.getPayload());
  state.addAttributes(invocation->getAttrs());
  auto replacement = cast<protocol_ir::LocalCallOp>(builder.create(state));
  invocation->replaceAllUsesWith(
      replacement.getResults().take_front(invocation.getNumResults()));
  invocation.erase();
  return replacement;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "direct computation recipe output retains the immutable source", [&] {
        auto original = parse(demanded, context);
        auto logical = formExecutable(*original);
        auto unit = numericalUnit(*logical);
        auto entry = mathematical::getComputationEntry(unit);
        OpBuilder builder(&context);
        entry->setAttr("sym_visibility", builder.getStringAttr("public"));
        entry->setAttr("data.preconditions", builder.getArrayAttr({}));
        require(succeeded(verify(*logical)), "recipe source metadata refused");
        auto before = copy(*logical);
        mathematical::RealizationWork work;
        uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
        auto output = computation::realizeEntry(unit, "direct", {}, work,
                                                remaining, bytes);
        require(bool(output) &&
                    succeeded(computation::verifyRecipeOutput(*output)) &&
                    succeeded(computation::verifyEntryRecipes(unit, *output,
                                                              "direct")),
                "direct numerical recipe publication failed");
        auto executable = computationRecipeOutput(*output);
        auto result =
            SymbolTable(executable).lookup<func::FuncOp>(entry.getSymName());
        require(result &&
                    protocol::scopedDataSignature(result) ==
                        entry.getFunctionType() &&
                    result->getAttrs().size() == 5 && result.isPrivate() &&
                    result.getNoInline() &&
                    !result->hasAttr("data.preconditions") &&
                    result->getAttr("runtime.origin") ==
                        builder.getArrayAttr(
                            {builder.getStringAttr(entry.getSymName()),
                             builder.getArrayAttr({})}),
                "recipe entry did not preserve its executable interface");
        require(OperationEquivalence::isEquivalentTo(
                    *logical, *before, OperationEquivalence::IgnoreLocations),
                "numerical recipe production changed its source");
        require(remaining < 1000000 && bytes < 16 * 1024 * 1024,
                "direct conversion failed to charge source/site work");
        for (StringRef mutation :
             {"return", "operand", "site", "interface", "declaration", "module",
              "owner-argument", "owner-operand", "owner-result",
              "module-argument", "module-operand", "module-result"}) {
          auto changed = copy(*output);
          auto function = SymbolTable(computationRecipeOutput(*changed))
                              .lookup<func::FuncOp>(entry.getSymName());
          auto returned = sc::returned(function);
          auto calls = sf::applications(function);
          OpBuilder builder(&context);
          if (mutation == "return")
            returned->setOperand(0, returned->getOperand(1));
          else if (mutation == "operand")
            calls.front()->setOperand(2, calls.front().getInputs()[0]);
          else if (mutation == "site")
            calls.front()->setAttr("site", builder.getStringAttr("other-call"));
          else if (mutation == "interface")
            function->setAttr(
                "runtime.origin",
                builder.getArrayAttr({builder.getStringAttr("extra"),
                                      builder.getArrayAttr({})}));
          else if (mutation == "declaration") {
            builder.setInsertionPointToEnd(
                &computationRecipeOutput(*changed).getBody().front());
            auto extra = func::FuncOp::create(builder, entry.getLoc(), "extra",
                                              builder.getFunctionType({}, {}));
            extra.setPrivate();
            builder.setInsertionPointToEnd(extra.addEntryBlock());
            func::ReturnOp::create(builder, entry.getLoc());
          } else if (mutation == "owner-argument")
            computationRecipeOutput(*changed).getBody().front().addArgument(
                builder.getI1Type(), entry.getLoc());
          else if (mutation == "owner-operand" || mutation == "owner-result") {
            auto previous = computationRecipeOutput(*changed);
            builder.setInsertionPoint(previous);
            OperationState state(previous.getLoc(), previous->getName());
            state.addAttributes(previous->getAttrs());
            if (mutation == "owner-operand")
              state.addOperands(function.getArguments()[0]);
            else
              state.addTypes(builder.getI1Type());
            state.addRegion();
            auto *replacement = builder.create(state);
            replacement->getRegion(0).takeBody(previous.getBody());
            previous.erase();
            require(replacement->getNumOperands() +
                            replacement->getNumResults() ==
                        1,
                    "owner mutation did not change its structural arity");
          } else if (mutation == "module-argument")
            changed->getBody()->addArgument(builder.getI1Type(),
                                            entry.getLoc());
          else if (mutation == "module-operand" ||
                   mutation == "module-result") {
            OperationState state(changed->getLoc(), (*changed)->getName());
            if (mutation == "module-operand")
              state.addOperands(function.getArguments()[0]);
            else
              state.addTypes(builder.getI1Type());
            state.addRegion();
            auto *replacement = Operation::create(state);
            replacement->getRegion(0).takeBody(changed->getBodyRegion());
            changed =
                OwningOpRef<mlir::ModuleOp>(cast<mlir::ModuleOp>(replacement));
            require(
                (*changed)->getNumOperands() + (*changed)->getNumResults() == 1,
                "module mutation did not change its structural arity");
          } else
            (*changed)->setAttr("unexpected", builder.getUnitAttr());
          finite::VerificationResult outcome{
              finite::VerificationStatus::Verified, {}};
          require(failed(computation::verifyEntryRecipes(
                      unit, *changed, "direct", {}, {}, &outcome)) &&
                      outcome.status == finite::VerificationStatus::Mismatch,
                  ("recipe reader accepted " + mutation).str());
        }
        uint64_t noCopy = 0, siteBytes = 16 * 1024 * 1024;
        require(
            !computation::realizeEntry(unit, "direct", {}, work, noCopy,
                                       siteBytes) &&
                OperationEquivalence::isEquivalentTo(
                    *logical, *before, OperationEquivalence::IgnoreLocations),
            "source copy exhaustion published or edited a numerical body");
      });
  cases.run("unused helper may call the public computation entry", [&] {
    auto source = parse(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
 module @numerical attributes {exec.computation} {
   func.func @square(%x:!F)->!F {
     %r = algebra.field_multiply %x,%x : (!F,!F)->!F
     func.return %r : !F
   }
   func.func private @unused_caller(%x:!F)->!F {
     %r = func.call @square(%x) : (!F)->!F
     func.return %r : !F
   }
 }
}
)mlir",
                        context);
    require(succeeded(verify(*source)), "unused caller source refused");
    auto unit = cast<mlir::ModuleOp>(source->getBody()->front());
    auto before = copy(*source);
    mathematical::RealizationWork work;
    auto output = realizeComputationEntry(unit, "square", {}, work);
    require(
        output && succeeded(computation::verifyRecipeOutput(*output)) &&
            succeeded(computation::verifyEntryRecipes(unit, *output, "square")),
        "unused caller prevented recipe publication");
    auto executable = computationRecipeOutput(*output);
    require(SymbolTable(executable).lookup<func::FuncOp>("square") &&
                !SymbolTable(executable).lookup("unused_caller"),
            "source helper escaped into executable output");
    require(OperationEquivalence::isEquivalentTo(
                *source, *before, OperationEquivalence::IgnoreLocations),
            "recipe production changed the unused caller or public entry");
  });
  cases.run("identity recipe rejects an extra scoped return attribute", [&] {
    auto source = parse(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
 module @numerical attributes {exec.computation} {
   func.func @identity(%x:!F)->!F {
     func.return %x : !F
   }
 }
}
)mlir",
                        context);
    auto unit = cast<mlir::ModuleOp>(source->getBody()->front());
    auto before = copy(*source);
    mathematical::RealizationWork work;
    auto output = realizeComputationEntry(unit, "identity", {}, work);
    require(output && succeeded(computation::verifyRecipeOutput(*output)) &&
                succeeded(
                    computation::verifyEntryRecipes(unit, *output, "identity")),
            "identity recipe publication failed");
    computationRecipeOutput(*output);
    auto changed = copy(*output);
    auto result = scopedFunction(*changed, "identity");
    auto returned = sc::returned(result);
    require(result.getBody().hasOneBlock() &&
                std::distance(result.front().begin(), result.front().end()) ==
                    2,
            "identity fixture unexpectedly contains executable work");
    returned->setAttr("unexpected", UnitAttr::get(&context));
    require(failed(computation::verifyRecipeOutput(*changed)),
            "malformed scoped recipe was admitted");
    expectRefusal(*changed, "mathematical-lowering-preservation", [&] {
      return computation::verifyEntryRecipes(unit, *changed, "identity");
    });
    require(OperationEquivalence::isEquivalentTo(
                *source, *before, OperationEquivalence::IgnoreLocations),
            "identity recipe checking changed its source");
  });
  cases.run("data.is recipe rejects duplicate generated sites", [&] {
    auto source = fixture(context, "mathematical/optional-traces.mlir");
    auto original = copy(*source);
    data::IsOp observation;
    source->walk([&](data::IsOp op) {
      if (!observation)
        observation = op;
    });
    require(bool(observation), "missing variant observation fixture");
    auto numerical = computationRecipeUnit(owner(*source));
    OpBuilder builder(numerical->getBody(), numerical->getBody()->end());
    auto entry = func::FuncOp::create(
        builder, observation.getLoc(), "present",
        builder.getFunctionType(observation->getOperandTypes(),
                                observation->getResultTypes()));
    entry.setPublic();
    builder.setInsertionPointToEnd(entry.addEntryBlock());
    IRMapping values;
    values.map(observation->getOperands(), entry.getArguments());
    auto *result = builder.clone(*observation.getOperation(), values);
    func::ReturnOp::create(builder, entry.getLoc(), result->getResults());
    require(succeeded(verify(*numerical)), "variant recipe source refused");
    OwningOpRef<mlir::ModuleOp> before(
        cast<mlir::ModuleOp>(numerical->clone()));
    mathematical::RealizationWork work;
    auto output = realizeComputationEntry(*numerical, "presence", {}, work);
    require(output && succeeded(computation::verifyRecipeOutput(*output)) &&
                succeeded(computation::verifyEntryRecipes(*numerical, *output,
                                                          "presence")),
            "variant observation recipe publication failed");
    computationRecipeOutput(*output);
    auto changed = copy(*output);
    SmallVector<exec::BooleanOp> constants;
    changed->walk([&](exec::BooleanOp op) { constants.push_back(op); });
    require(constants.size() == 2, "variant recipe lost its two alternatives");
    auto first = constants[0]->getAttrOfType<StringAttr>("site");
    auto second = constants[1]->getAttrOfType<StringAttr>("site");
    auto prefix = computationRecipeSite("presence", 0) + "_recipe_";
    require(first && second && first != second &&
                first.getValue().starts_with(prefix) &&
                second.getValue().starts_with(prefix),
            "variant recipe did not generate distinct owned sites");
    constants[1]->setAttr("site", first);
    require(failed(computation::verifyRecipeOutput(*changed)),
            "malformed scoped recipe was admitted");
    expectRefusal(*changed, "mathematical-lowering-preservation", [&] {
      return computation::verifyEntryRecipes(*numerical, *changed, "presence");
    });
    require(OperationEquivalence::isEquivalentTo(
                *numerical, *before, OperationEquivalence::IgnoreLocations) &&
                OperationEquivalence::isEquivalentTo(
                    *source, *original, OperationEquivalence::IgnoreLocations),
            "variant recipe production or checking changed its source");
  });
  cases.run("scoped computation owns its immutable mathematical closure", [&] {
    auto source = parse(realization, context);
    auto prepared = closedFixture(*source);
    auto wrapper = scopedFunction(*prepared, "realized");
    require(isa<exec::ComputeOp>(wrapper.front().front()),
            "wrapper lost its typed mathematical request");
    auto original =
        SymbolTable(owner(*source)).lookup<func::FuncOp>("difference");
    require(succeeded(computation::verifyComputationClosure(
                owner(*source), original, numericalUnit(*prepared))),
            "exact closure with entry visibility change failed");
    auto logical = formExecutable(*prepared, {false, false});
    auto lowered = copy(*logical);
    require(succeeded(computation::realizeComputations(*lowered)) &&
                succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
            "scoped numerical edge failed");
    bool residual = false;
    lowered->walk([&](Operation *op) {
      residual |=
          mathematical::isComputationUnit(op) || isa<exec::ComputeOp>(op);
    });
    require(!residual, "unresolved numerical code survived");
    auto result = scopedFunction(*lowered, "realized");
    auto call = sf::application(result, "field.sub");
    auto originalCall = cast<exec::ComputeOp>(
        scopedFunction(*logical, "realized").front().front());
    require(call.getSite() == computationRecipeSite(originalCall.getSite(), 0),
            "normalized ordinal lost the actual ordered call site");
    require(result->getAttr("runtime.origin") ==
                wrapper->getAttr("runtime.origin"),
            "source origin changed");
  });
  cases.run("closure rejects same-type helper operand permutation", [&] {
    auto source = parse(realization, context);
    auto helper = numericalEntry(*source);
    auto candidate = close(helper);
    auto &op = mathematical::getComputationEntry(*candidate).front().front();
    auto first = op.getOperand(0);
    op.setOperand(0, op.getOperand(1));
    op.setOperand(1, first);
    require(succeeded(verify(*candidate)), "mutation malformed");
    expectRefusal(*candidate, "kernel-closure-correspondence", [&] {
      return computation::verifyComputationClosure(owner(*source), helper,
                                                   *candidate);
    });
  });
  cases.run("lowering rejects a permuted original computation capture", [&] {
    auto source = parse(realization, context);
    auto logical = formExecutable(*source);
    auto candidate = copy(*logical);
    auto call = computationFixture(*candidate);
    auto first = call.getInputs()[0];
    call->setOperand(1, call.getInputs()[1]);
    call->setOperand(2, first);
    require(succeeded(verify(*candidate)) &&
                succeeded(computation::realizeComputations(*candidate)),
            "permuted candidate was not admitted and lowered");
    expectRefusal(*candidate, "numerical-lowering-correspondence", [&] {
      return computation::verifyComputationRealization(*logical, *candidate);
    });
  });
  cases.run(
      "actual scoped recipe same-type operand permutation is refused", [&] {
        auto source = parse(realization, context);
        auto logical = formExecutable(*source);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "lowering failed");
        auto op =
            sf::application(scopedFunction(*lowered, "realized"), "field.sub");
        auto first = op.getInputs()[0];
        op->setOperand(1, op.getInputs()[1]);
        op->setOperand(2, first);
        require(succeeded(verify(*lowered)), "mutation malformed");
        expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
          return computation::verifyComputationRealization(*logical, *lowered);
        });
      });
  cases.run("independent lowering rejects a changed numerical root site", [&] {
    auto source = parse(realization, context);
    auto logical = formExecutable(*source);
    auto lowered = copy(*logical);
    require(succeeded(computation::realizeComputations(*lowered)),
            "lowering failed");
    auto op =
        sf::application(scopedFunction(*lowered, "realized"), "field.sub");
    op->setAttr("site", StringAttr::get(&context, "kernel"));
    require(succeeded(verify(*lowered)), "mutation malformed");
    expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
      return computation::verifyComputationRealization(*logical, *lowered);
    });
  });
  cases.run(
      "participant extraction retains both escaped numerical results", [&] {
        auto source = parse(demanded, context);
        auto participant = copy(*source);
        run(*participant, protocol::createProjectProtocolPass(false));
        auto logical = copy(*participant);
        run(*logical, protocol::createLowerMathPass());
        require(numericalEntry(*logical).getNumResults() == 2,
                "escaped intermediate result lost");
        require(succeeded(mathematical::verifyProjectionPreserved(*participant,
                                                                  *logical)),
                "actual demand correspondence failed");
        auto returned =
            cast<func::ReturnOp>(numericalEntry(*logical).front().back());
        auto first = returned.getOperand(0);
        returned.setOperand(0, returned.getOperand(1));
        returned.setOperand(1, first);
        require(succeeded(verify(*logical)), "result permutation malformed");
        expectRefusal(*logical, "mathematical-lowering-preservation", [&] {
          return mathematical::verifyProjectionPreserved(*participant,
                                                         *logical);
        });
      });
  cases.run("partial guard remains ordered in wrapper outside total unit", [&] {
    auto source = parse(guarded, context);
    auto participant = copy(*source);
    run(*participant, protocol::createProjectProtocolPass(false));
    auto logical = copy(*participant);
    run(*logical, protocol::createLowerMathPass());
    bool partial = false;
    numericalUnit(*logical).walk([&](Operation *op) {
      partial |= isa<exec::RejectOp, exec::TestOp>(op);
    });
    require(!partial, "partial control entered numerical unit");
    exec::RejectOp stop;
    logical->walk([&](exec::RejectOp op) {
      if (op.getSite() == "check")
        stop = op;
    });
    require(bool(stop), "ordered source rejection disappeared");
    auto lowered = copy(*logical);
    require(succeeded(computation::realizeComputations(*lowered)),
            "guarded lowering failed");
    stop->setAttr("site", StringAttr::get(&context, "different_check"));
    expectRefusal(*logical, "mathematical-lowering-preservation", [&] {
      return mathematical::verifyProjectionPreserved(*participant, *logical);
    });
  });
  for (bool optimize : {false, true})
    for (StringRef name :
         {"finite/total-state.mlir", "finite/total-collect.mlir",
          "finite/total-predicate.mlir"})
      cases.run(Twine(optimize ? "optimized " : "ordered ") + name, [&] {
        auto source = fixture(context, name);
        auto logical = formExecutable(*source, {optimize, false});
        auto entry = numericalEntry(*logical);
        require(
            entry.front().front().getName().getStringRef().contains("finite"),
            "finite mathematics lowered before explicit Kernel edge");
        auto lowered = copy(*logical);
        // The stored per-call policy survives the fallback argument here.
        require(succeeded(computation::realizeComputations(*lowered,
                                                           {!optimize, false})),
                "finite lowering failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "finite logical-to-scoped check failed");
      });
  for (bool optimize : {false, true})
    cases.run(optimize ? "stored finite policy selects bulk"
                       : "stored finite policy retains ordered traversal",
              [&] {
                auto source = fixture(
                    context, "structured-source/realization-finite.mlir");
                auto logical = formExecutable(*source, {optimize, false});
                logical->walk([&](exec::ComputeOp call) {
                  call->setAttr("policy", Builder(&context).getBoolArrayAttr(
                                              {optimize, false, false}));
                });
                auto lowered = copy(*logical);
                require(succeeded(computation::realizeComputations(
                            *lowered, {!optimize, false})),
                        "finite policy lowering failed");
                bool loop = false;
                lowered->walk([&](exec::RangeOp) { loop = true; });
                require(loop == !optimize,
                        "fallback policy replaced retained per-call policy");
              });
  cases.run(
      "domain admission loops cannot authorize a disabled bulk payload", [&] {
        auto source =
            fixture(context, "structured-source/realization-finite.mlir");
        auto domain =
            SymbolTable(owner(*source)).lookup<data::DomainOp>("items");
        auto &body = domain.getBody().front();
        Value values = body.back().getOperand(0);
        auto type = cast<data::DomainType>(values.getType());
        SmallVector<Type> items(type.getItemTypes());
        llvm::append_range(items, type.getItemTypes());
        OpBuilder builder(&body.back());
        OperationState product(domain.getLoc(),
                               data::DomainProductOp::getOperationName());
        product.addOperands({values, values});
        product.addTypes(data::DomainType::get(&context, items));
        builder.create(product);
        require(succeeded(verify(*source)),
                "unused product source not admitted");
        auto logical = formExecutable(*source, {true, false});
        auto bulk = copy(*logical);
        require(succeeded(computation::realizeComputations(*bulk)),
                "bulk control failed");
        unsigned admissionLoops = 0, traversals = 0;
        bool reduction = false;
        auto closure = take(protocol::readSourceExecutionClosure(owner(*bulk)));
        for (const auto &[name, steps] : closure.bodies)
          for (const auto &step : steps)
            if (isa<exec::RangeOp>(step.operation)) {
              if (step.outputs.empty())
                ++admissionLoops;
              else
                ++traversals;
            }
        bulk->walk([&](runtime::BindingOp binding) {
          reduction |= binding.getContract() == "vector.sum";
        });
        require(
            admissionLoops && !traversals && reduction,
            "control lacks bulk reduction beside mandatory admission loops");
        logical->walk([&](exec::ComputeOp call) {
          call->setAttr("policy",
                        builder.getBoolArrayAttr({false, false, false}));
        });
        require(succeeded(verify(*logical)), "disabled source not admitted");
        expectRefusal(*bulk, "numerical-lowering-correspondence", [&] {
          return computation::verifyComputationRealization(*logical, *bulk);
        });
        auto ordered = copy(*logical);
        require(succeeded(computation::realizeComputations(*ordered)) &&
                    succeeded(computation::verifyComputationRealization(
                        *logical, *ordered)),
                "ordered fallback lost mandatory domain admission");
      });
  for (bool optimize : {false, true})
    cases.run(
        optimize ? "omitted policy uses bulk request"
                 : "omitted policy uses ordered request",
        [&] {
          auto source =
              fixture(context, "structured-source/realization-finite.mlir");
          auto logical = formExecutable(*source);
          logical->walk(
              [](exec::ComputeOp call) { call->removeAttr("policy"); });
          auto lowered = copy(*logical);
          MathematicalSelectionPolicy policy{optimize, false};
          require(
              succeeded(computation::realizeComputations(*lowered, policy)) &&
                  succeeded(computation::verifyComputationRealization(
                      *logical, *lowered, policy)),
              "fallback policy was not shared with verification");
          bool loop = false;
          lowered->walk([&](exec::RangeOp) { loop = true; });
          require(loop == !optimize, "omitted policy ignored lowering request");
        });
  cases.run(
      "isolated units resolve identical private names independently", [&] {
        auto source =
            fixture(context, "structured-source/realization-finite.mlir");
        auto closed = closedFixture(*source);
        auto logical = formExecutable(*closed, {false, false});
        OpBuilder builder(numericalUnit(*logical));
        auto second = cast<mlir::ModuleOp>(
            builder.clone(*numericalUnit(*logical).getOperation()));
        SymbolTable::setSymbolName(second, "second_numerical");
        auto wrapper = scopedFunction(*logical, "realized");
        builder.setInsertionPoint(wrapper);
        auto secondWrapper =
            cast<func::FuncOp>(builder.clone(*wrapper.getOperation()));
        SymbolTable::setSymbolName(secondWrapper, "second_realized");
        secondWrapper.walk([&](exec::ComputeOp call) {
          auto reference = call.getCallee();
          call->setAttr("callee",
                        SymbolRefAttr::get(&context, "second_numerical",
                                           reference.getNestedReferences()));
        });
        auto callback = SymbolTable(second).lookup<func::FuncOp>("step");
        auto *original = &callback.front().front();
        builder.setInsertionPoint(original);
        OperationState operation(original->getLoc(), "algebra.field_subtract");
        operation.addOperands(original->getOperands());
        operation.addTypes(original->getResultTypes());
        auto *difference = builder.create(operation);
        original->getResult(0).replaceAllUsesWith(difference->getResult(0));
        original->erase();
        require(succeeded(verify(*logical)), "isolated closures malformed");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "colliding private identities prevented lowering");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "isolated closure correspondence failed");
        bool addition = false, subtraction = false;
        for (auto binding :
             owner(*lowered).getBody().front().getOps<runtime::BindingOp>()) {
          addition |= binding.getContract() == "field.add";
          subtraction |= binding.getContract() == "field.sub";
        }
        require(addition && subtraction,
                "private callbacks resolved through the wrong unit");
      });
  cases.run(
      "finite closure rejects renamed nominal domain despite identical "
      "descriptor",
      [&] {
        auto source =
            fixture(context, "structured-source/realization-finite.mlir");
        auto helper = numericalEntry(*source);
        auto candidate = close(helper);
        auto unit = *candidate;
        auto domain = *unit.getBody()->getOps<data::DomainOp>().begin();
        auto oldName = SymbolTable::getSymbolName(domain);
        SymbolTable::setSymbolName(domain, "other_items");
        unit.walk([&](Operation *op) {
          if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>("domain");
              reference && reference.getValue() == oldName.getValue())
            op->setAttr("domain",
                        FlatSymbolRefAttr::get(&context, "other_items"));
        });
        require(succeeded(verify(*candidate)), "nominal mutation malformed");
        expectRefusal(*candidate, "kernel-closure-correspondence", [&] {
          return computation::verifyComputationClosure(owner(*source), helper,
                                                       *candidate);
        });
      });
  cases.run("finite closure checks actual callback computation", [&] {
    auto source = fixture(context, "structured-source/realization-finite.mlir");
    auto helper = numericalEntry(*source);
    auto candidate = close(helper);
    auto step = SymbolTable(*candidate).lookup<func::FuncOp>("step");
    step.front().back().setOperand(0, step.getArgument(0));
    require(succeeded(verify(*candidate)), "callback mutation malformed");
    expectRefusal(*candidate, "kernel-closure-correspondence", [&] {
      return computation::verifyComputationClosure(owner(*source), helper,
                                                   *candidate);
    });
  });
  cases.run(
      "checked polynomial math stays numerical until explicit lowering", [&] {
        auto source = fixture(context, "mathematical/helper-realization.mlir");
        auto logical = formExecutable(*source, {false, false});
        require(bool(numericalEntry(*logical)),
                "polynomial realization did not form a unit");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "polynomial lowering failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "polynomial edge failed");
      });
  cases.run("dormant owned units are checked and removed without execution",
            [&] {
              auto source = parse(realization, context);
              auto closed = closedFixture(*source);
              auto logical = formExecutable(*closed);
              OpBuilder builder(numericalUnit(*logical));
              auto dormant = cast<mlir::ModuleOp>(
                  builder.clone(*numericalUnit(*logical).getOperation()));
              SymbolTable::setSymbolName(dormant, "dormant");
              require(succeeded(verify(*logical)), "dormant closure malformed");
              auto lowered = copy(*logical);
              require(succeeded(computation::realizeComputations(*lowered)),
                      "dormant unit prevented lowering");
              require(succeeded(computation::verifyComputationRealization(
                          *logical, *lowered)),
                      "dormant edge failed");
              dormant->setAttr("test.unsupported", builder.getUnitAttr());
              auto frozen = copy(*logical);
              expectRefusal(*logical, "computation-formation", [&] {
                return computation::realizeComputations(*logical);
              });
              require(OperationEquivalence::isEquivalentTo(
                          logical->getOperation(), frozen->getOperation(),
                          OperationEquivalence::IgnoreLocations),
                      "failed transaction changed source");
            });
  cases.run("exact readback expands authored standard helper calls", [&] {
    auto source = parse(realization, context);
    auto logical = formExecutable(*source);
    auto entry = numericalEntry(*logical);
    OpBuilder builder(entry);
    auto helper = cast<func::FuncOp>(builder.clone(*entry.getOperation()));
    SymbolTable::setSymbolName(helper, "nested_difference");
    helper.setPrivate();
    entry.getBody().getBlocks().clear();
    builder.setInsertionPointToEnd(entry.addEntryBlock());
    auto call =
        func::CallOp::create(builder, entry.getLoc(), helper.getSymName(),
                             helper.getResultTypes(), entry.getArguments());
    func::ReturnOp::create(builder, entry.getLoc(), call.getResults());
    require(succeeded(verify(*logical)), "authored helper closure malformed");
    auto lowered = copy(*logical);
    require(succeeded(computation::realizeComputations(*lowered)),
            "exact helper substitution failed");
    require(succeeded(
                computation::verifyComputationRealization(*logical, *lowered)),
            "helper edge failed");
  });
  cases.run(
      "raw authored polynomial entry lowers through checked normalization",
      [&] {
        auto source = fixture(context, "mathematical/helper-realization.mlir");
        auto logical = formExecutable(*source);
        auto original =
            SymbolTable(owner(*source)).lookup<func::FuncOp>("polynomial");
        auto entry = numericalEntry(*logical);
        auto raw =
            OwningOpRef<func::FuncOp>(cast<func::FuncOp>(original->clone()));
        entry.getBody().takeBody(raw->getBody());
        require(succeeded(verify(*logical)),
                "raw closed polynomial fixture malformed");
        auto frozen = copy(*logical);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "raw polynomial lowering failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "raw polynomial recipe correspondence failed");
        require(OperationEquivalence::isEquivalentTo(
                    logical->getOperation(), frozen->getOperation(),
                    OperationEquivalence::IgnoreLocations),
                "lowering changed its immutable original source root");
      });
  cases.run(
      "scoped helper expansion distinguishes repeated ordered calls", [&] {
        auto source = parse(realization, context);
        auto wrapper = scopedFunction(*source, "work");
        auto *again =
            sc::duplicateInvocation(&wrapper.front().front(), wrapper, "again");
        again->removeAttr("site");
        again->setAttr("runtime.site", StringAttr::get(&context, "again"));
        auto first = again->getOperand(1);
        again->setOperand(1, again->getOperand(2));
        again->setOperand(2, first);
        require(succeeded(verify(*source)), "repeated scoped source refused");
        std::vector<protocol::AlgorithmOrigin> origins;
        auto expanded = protocol::expandScopedHelpers(*source, &origins);
        require(bool(expanded) &&
                    succeeded(protocol::verifyScopedHelperExpansionPreserved(
                        *source, *expanded)),
                "independent scoped substitution failed");
        auto repeated = protocol::expandScopedHelpers(*expanded);
        require(bool(repeated) &&
                    succeeded(protocol::verifyScopedHelperExpansionPreserved(
                        *expanded, *repeated)),
                "repeated preparation changed expanded calls");
        auto work = scopedFunction(*expanded, "work");
        llvm::StringSet<> invocationSites;
        unsigned count = 0;
        work.walk([&](exec::ComputeOp call) {
          require(!call->hasAttr("occurrences"),
                  "retired constituent evidence survived");
          require(invocationSites.insert(call.getSite()).second,
                  "repeated invocation collapsed ordered call identity");
          require(llvm::any_of(origins,
                               [&](const auto &origin) {
                                 return origin.function == "work" &&
                                        origin.site == call.getSite() &&
                                        origin.originalSite == "kernel" &&
                                        !origin.path.empty();
                               }),
                  "ordered call lost original provenance");
          ++count;
        });
        require(count == 2, "repeated calls lost numerical work");
        auto logical = formExecutable(*expanded);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "repeated call realization failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "repeated call checked edge failed");
      });
  cases.run(
      "fixed opaque binding survives and cannot be silently repinned", [&] {
        std::string text = realization.str();
        text.insert(text.find(" func.func private"), R"mlir(
      "runtime.binding"() {sym_name="pinned",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
    )mlir");
        auto source = parse(text, context);
        auto logical = formExecutable(*source);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "pinned context prevented lowering");
        auto pinned =
            SymbolTable(owner(*lowered)).lookup<runtime::BindingOp>("pinned");
        require(pinned.getImplementation() == "arkworks-msb/poly.fold",
                "pin changed during numerical lowering");
        pinned->setAttr("implementation", StringAttr::get(&context, ""));
        require(succeeded(verify(*lowered)), "repinned context malformed");
        expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
          return computation::verifyComputationRealization(*logical, *lowered);
        });
      });
  cases.run(
      "raw helper and mixed polynomial results survive preparation and "
      "projection",
      [&] {
        auto source = fixture(context, "kernel/mixed-helper.mlir");
        auto prepared = closedFixture(*source);
        auto unit = numericalUnit(*prepared);
        auto mixed = SymbolTable(unit).lookup<func::FuncOp>("mixed");
        auto original =
            SymbolTable(owner(*source)).lookup<func::FuncOp>("mixed");
        require(mixed &&
                    OperationEquivalence::isEquivalentTo(
                        mixed, original, OperationEquivalence::IgnoreLocations),
                "formation replaced the original helper body");
        require(isa<func::CallOp>(numericalEntry(*prepared).front().front()),
                "formation expanded the raw helper call");
        auto logical = formExecutable(*prepared);
        require(isa<func::CallOp>(numericalEntry(*logical).front().front()),
                "projection erased the raw helper call");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "mixed helper lowering failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "mixed helper coordinates failed correspondence");
        auto result = scopedFunction(*lowered, "realized");
        auto returned = sc::returned(result);
        auto first = returned.getOperand(0);
        returned.setOperand(0, returned.getOperand(2));
        returned.setOperand(2, first);
        require(succeeded(verify(*lowered)), "mixed result mutation malformed");
        expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
          return computation::verifyComputationRealization(*logical, *lowered);
        });
      });
  for (bool batching : {false, true})
    cases.run(
        Twine("shared interpolation crosses a guard with batching=") +
            (batching ? "true" : "false"),
        [&] {
          MathematicalSelectionPolicy policy;
          policy.calculationBatching = batching;
          auto source = fixture(context, "kernel/shared-polynomial.mlir");
          auto participant = copy(*source);
          run(*participant, protocol::createProjectProtocolPass(false));
          auto logical = copy(*participant);
          run(*logical, protocol::createLowerMathPass(policy));
          require(
              succeeded(mathematical::verifyProjectionPreserved(
                  *participant, *logical, policy)),
              "raw descriptor reconstruction or transitive escape differed");
          unsigned descriptors = 0;
          logical->walk([&](Operation *op) {
            descriptors += op->getName().getStringRef() == "poly.interpolate";
          });
          require(descriptors == 2,
                  "raw descriptor was not reconstructed at both cuts");
          auto normalized =
              computation::prepareComputationRealization(*logical);
          require(bool(normalized), "shared normalization frontier refused");
          unsigned extraInputs = 0, extraOutputs = 0;
          for (auto function :
               owner(*normalized).getBody().front().getOps<func::FuncOp>()) {
            if (!protocol::isScopedExecutionFunction(function) ||
                function->hasAttr("runtime.region"))
              continue;
            auto before = SymbolTable(owner(*logical))
                              .lookup<func::FuncOp>(function.getSymName());
            require(bool(before),
                    "normalization added an unrelated scoped function");
            extraInputs +=
                function.getNumArguments() - before.getNumArguments();
            extraOutputs +=
                protocol::scopedDataSignature(function).getNumResults() -
                protocol::scopedDataSignature(before).getNumResults();
          }
          require(extraInputs && extraOutputs,
                  "shared coefficients were recomputed instead of exported");
          auto lowered = copy(*logical);
          require(succeeded(computation::realizeComputations(*lowered)),
                  "shared frontier recipe lowering failed");
          require(succeeded(computation::verifyComputationRealization(
                      *logical, *lowered)),
                  "shared frontier actual candidate failed correspondence");
          protocol_ir::LocalCallOp consumer;
          lowered->walk([&](protocol_ir::ParticipantOp participant) {
            participant.walk([&](protocol_ir::LocalCallOp call) {
              auto before = SymbolTable(owner(*logical))
                                .lookup<func::FuncOp>(call.getCallee());
              if (before &&
                  call.getNumOperands() + 1 > before.getNumArguments())
                consumer = call;
            });
          });
          require(bool(consumer), "frontier consumer lost its concrete inputs");
          bool changed = false;
          for (Value input : consumer.getInputs().drop_back())
            if (input != consumer.getInputs().back() &&
                input.getType() == consumer.getInputs().back().getType()) {
              consumer->setOperand(consumer.getNumOperands() - 1, input);
              changed = true;
              break;
            }
          require(changed, "frontier fixture has no same-typed mutation");
          require(succeeded(verify(*lowered)),
                  "frontier coordinate mutation malformed");
          expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
            return computation::verifyComputationRealization(*logical,
                                                             *lowered);
          });
        });
  cases.run("the independent outliner reader binds the selected schedule", [&] {
    auto source = fixture(context, "kernel/shared-polynomial.mlir");
    Operation *second = nullptr, *guard = nullptr;
    source->walk([&](Operation *op) {
      if (op->getName().getStringRef() == "poly.evaluate")
        second = op;
      if (op->getName().getStringRef() == "protocol.guard")
        guard = op;
    });
    require(second && guard, "missing scheduling fixture operations");
    second->moveBefore(guard);
    require(succeeded(verify(*source)), "early observation fixture malformed");
    auto participant = copy(*source);
    run(*participant, protocol::createProjectProtocolPass(false));
    for (bool batching : {false, true}) {
      MathematicalSelectionPolicy policy;
      policy.calculationBatching = batching;
      auto logical = copy(*participant);
      run(*logical, protocol::createLowerMathPass(policy));
      require(succeeded(mathematical::verifyProjectionPreserved(
                  *participant, *logical, policy)),
              "selected schedule failed its independent reader");
      policy.calculationBatching = !batching;
      expectRefusal(*logical, "mathematical-lowering-preservation", [&] {
        return mathematical::verifyProjectionPreserved(*participant, *logical,
                                                       policy);
      });
    }
  });
  cases.run(
      "mixed helper concrete work is not replayed across action cuts", [&] {
        auto source = fixture(context, "kernel/mixed-helper-cuts.mlir");
        auto logical = formExecutable(*source);
        unsigned differences = 0;
        uint64_t remaining = 1000000;
        SymbolTableCollection symbols;
        logical->walk([&](exec::ComputeOp call) {
          auto helper = call.resolveCallee(symbols);
          auto body = computation::exactReadback(helper, helper->getParentOp(),
                                                 remaining);
          require(bool(body), "actual computation closure did not read back");
          body->walk([&](algebra::SubtractFieldOp) { ++differences; });
        });
        require(differences == 1,
                "mixed helper replayed an already concrete dependency");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "mixed helper cuts failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "mixed helper cut coordinates failed correspondence");
      });
  cases.run(
      "authored forwarding wrapper is admitted before and after projection",
      [&] {
        auto source = parse(realization, context);
        require(succeeded(verify(*source)), "authored scoped wrapper refused");
        auto function = scopedFunction(*source, "realized");
        sc::returned(function)->setOperand(0, function.getArgument(2));
        require(succeeded(verify(*source)),
                "original profile refused a forwarding scoped return");
        auto normalized = computation::prepareComputationRealization(*source);
        require(bool(normalized) && succeeded(verify(*normalized)),
                "original forwarding wrapper normalization failed");
        auto logical = formExecutable(*source);
        require(succeeded(verify(*logical)),
                "projected authored forwarding wrapper was refused");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)) &&
                    succeeded(computation::verifyComputationRealization(
                        *logical, *lowered)),
                "authored forwarding wrapper lost correspondence");
        auto actual = scopedFunction(*lowered, "realized");
        require(actual.getFunctionType() == function.getFunctionType() &&
                    sc::returned(actual)->getOperand(0) ==
                        actual.getArgument(2),
                "authored forwarding interface changed");
      });
  for (StringRef wiring : {"identity", "permuted", "duplicated"})
    cases.run(
        "admitted generated forwarding ports with " + wiring +
            " numerical inputs",
        [&] {
          auto source = fixture(context, "kernel/shared-polynomial.mlir");
          auto logical = formExecutable(*source);
          SmallVector<protocol_ir::LocalCallOp> invocations;
          logical->walk([&](protocol_ir::ParticipantOp participant) {
            participant.walk([&](protocol_ir::LocalCallOp call) {
              invocations.push_back(call);
            });
          });
          require(invocations.size() == 2,
                  "shared fixture no longer has two calculation cuts");
          auto first = scopedFunction(*logical, invocations[0].getCallee());
          auto second = scopedFunction(*logical, invocations[1].getCallee());
          auto call = cast<exec::ComputeOp>(first.getBody().front().front());
          if (wiring != "identity") {
            bool changed = false;
            for (unsigned i = 0; i < call.getNumOperands() && !changed; ++i)
              for (unsigned j = i + 1; j < call.getNumOperands(); ++j)
                if (call.getOperand(i).getType() ==
                    call.getOperand(j).getType()) {
                  auto a = call.getOperand(i), b = call.getOperand(j);
                  call->setOperand(i, b);
                  if (wiring == "permuted")
                    call->setOperand(j, a);
                  changed = true;
                  break;
                }
            require(changed, "fixture has no matching numerical inputs");
          }
          unsigned firstResults =
              protocol::scopedDataSignature(first).getNumResults();
          SmallVector<Value> forwarded(first.getArguments().drop_front());
          forwarded.push_back(first.getArgument(1));
          forwarded.push_back(sc::payload(call).front());
          forwarded.push_back(sc::payload(call).front());
          invocations[0] = appendReturns(first, invocations[0], forwarded);
          // This original wrapper port imports an earlier forwarding
          // alias without passing it to the Kernel at all. Kernel and
          // wrapper argument coordinates must therefore stay separate.
          auto alias = invocations[0].getResult(firstResults);
          auto inputPosition = second.getNumArguments();
          require(succeeded(
                      second.insertArgument(inputPosition, alias.getType(),
                                            DictionaryAttr{}, alias.getLoc())),
                  "cannot append forwarded input");
          auto argument = second.getArgument(inputPosition);
          invocations[1]->insertOperands(invocations[1].getNumOperands(),
                                         alias);
          unsigned secondResults =
              protocol::scopedDataSignature(second).getNumResults();
          invocations[1] = appendReturns(
              second, invocations[1],
              ValueRange{argument, argument, second.getArgument(1)});
          require(succeeded(verify(*logical)),
                  "projected profile refused genuine forwarding ports");
          auto snapshot = copy(*logical);
          auto normalized =
              computation::prepareComputationRealization(*logical);
          require(bool(normalized) && succeeded(verify(*normalized)),
                  "admitted forwarding frontier was refused");
          require(
              OperationEquivalence::isEquivalentTo(
                  *logical, *snapshot, OperationEquivalence::IgnoreLocations),
              "frontier preparation changed the admitted source");
          auto actualFirst = scopedFunction(*normalized, first.getSymName());
          auto actualSecond = scopedFunction(*normalized, second.getSymName());
          auto returned = sc::returned(actualFirst);
          for (auto [index, input] : llvm::enumerate(
                   actualFirst.getArguments().drop_front().take_front(
                       first.getNumArguments() - 1)))
            require(returned.getOperand(firstResults + index) == input,
                    "original forwarding coordinate changed");
          require(
              returned.getOperand(firstResults + first.getNumArguments() - 1) ==
                      actualFirst.getArgument(1) &&
                  returned.getOperand(firstResults + first.getNumArguments()) ==
                      returned.getOperand(firstResults +
                                          first.getNumArguments() + 1),
              "duplicate original return aliases diverged");
          returned = sc::returned(actualSecond);
          require(returned.getOperand(secondResults) ==
                          actualSecond.getArgument(argument.getArgNumber()) &&
                      returned.getOperand(secondResults + 1) ==
                          returned.getOperand(secondResults),
                  "earlier imported forwarding aliases changed");
          if (wiring == "identity")
            require(
                protocol::scopedDataSignature(actualFirst).getNumResults() >
                        protocol::scopedDataSignature(first).getNumResults() &&
                    actualSecond.getNumArguments() > second.getNumArguments(),
                "forwarding fixture did not exercise frontier exports");
          auto lowered = copy(*logical);
          require(succeeded(computation::realizeComputations(*lowered)) &&
                      succeeded(computation::verifyComputationRealization(
                          *logical, *lowered)),
                  "forwarding frontier recipe correspondence failed");
          // A same-typed return mutation remains profile-admitted but
          // must fail exact original-coordinate correspondence.
          auto changed = scopedFunction(*lowered, first.getSymName());
          bool mutated = false;
          for (Value input : changed.getArguments().drop_front(2))
            if (input.getType() == changed.getArgument(1).getType()) {
              sc::returned(changed)->setOperand(firstResults, input);
              mutated = true;
              break;
            }
          require(mutated && succeeded(verify(*lowered)),
                  "forwarding coordinate mutation malformed");
          expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
            return computation::verifyComputationRealization(*logical,
                                                             *lowered);
          });
        });
  for (unsigned flags : {1u, 2u, 3u})
    cases.run("computation policy survives concrete port growth " +
                  Twine(flags),
              [&] {
                auto source = fixture(context, "kernel/shared-polynomial.mlir");
                auto logical = formExecutable(*source);
                Builder builder(&context);
                auto policy = builder.getBoolArrayAttr(
                    {bool(flags & 1), bool(flags & 2), false});
                logical->walk([&](exec::ComputeOp call) {
                  call->setAttr("policy", policy);
                });
                require(succeeded(verify(*logical)),
                        "retained policy source refused");
                auto normalized =
                    computation::prepareComputationRealization(*logical);
                require(bool(normalized) && succeeded(verify(*normalized)),
                        "policy prevented port growth");
                unsigned count = 0;
                normalized->walk([&](exec::ComputeOp call) {
                  ++count;
                  require(call.getPolicyAttr() == policy,
                          "port growth changed retained policy");
                });
                require(count == 2, "policy fixture lost its computation cuts");
                auto lowered = copy(*logical);
                require(succeeded(computation::realizeComputations(*lowered)) &&
                            succeeded(computation::verifyComputationRealization(
                                *logical, *lowered)),
                        "retained policy lost checked realization");
              });
  cases.run("descriptor operands cannot change across reconstructed cuts", [&] {
    auto source = fixture(context, "kernel/shared-polynomial.mlir");
    auto participant = copy(*source);
    run(*participant, protocol::createProjectProtocolPass(false));
    auto logical = copy(*participant);
    run(*logical, protocol::createLowerMathPass());
    Operation *evaluation = nullptr;
    logical->walk([&](Operation *op) {
      if (op->getName().getStringRef() == "poly.evaluate")
        evaluation = op;
    });
    require(bool(evaluation), "missing raw evaluation");
    auto entry = evaluation->getParentOfType<func::FuncOp>();
    bool changed = false;
    for (Value argument : entry.getArguments())
      if (argument.getType() == evaluation->getOperand(1).getType() &&
          argument != evaluation->getOperand(1)) {
        evaluation->setOperand(1, argument);
        changed = true;
        break;
      }
    // Some cuts capture only one field point. Mutate the first raw array's
    // concrete coordinate instead; its type and degree admission stay valid.
    if (!changed)
      logical->walk([&](Operation *op) {
        if (!changed &&
            op->getName().getStringRef() == "algebra.array_from_elements" &&
            op->getNumOperands() == 2) {
          op->setOperand(0, op->getOperand(1));
          changed = true;
        }
      });
    require(changed && succeeded(verify(*logical)),
            "descriptor mutation malformed");
    expectRefusal(*logical, "mathematical-lowering-preservation", [&] {
      return mathematical::verifyProjectionPreserved(*participant, *logical);
    });
  });
  cases.run("normalized naming charges bounds before allocation", [&] {
    uint64_t budget = 4;
    auto name = protocol::algorithmSite({{"outer", "kernel"}}, "0", budget);
    require(!name, "undersized naming budget was ignored");
    consumeError(name.takeError());
    uint64_t bytes = 4096;
    auto first = protocol::algorithmSite({{std::string(512, 'x'), "kernel"}},
                                         "0", bytes);
    auto second = protocol::algorithmSite({{std::string(512, 'x'), "kernel"}},
                                          "1", bytes);
    require(first && second && *first != *second && first->size() <= 128 &&
                second->size() <= 128,
            "bounded digest naming collided or exceeded admitted length");
  });
  cases.run(
      "original .zkc polynomial helper stays raw until Kernel lowering", [&] {
        auto bytes = llvm::MemoryBuffer::getFile(
            (Twine(ZKC_COMPUTATION_FIXTURES) + "/kernel/raw-polynomial.zkc")
                .str());
        require(bool(bytes), "missing source fixture");
        auto captured =
            take(language::capture({{"raw_kernel", (*bytes)->getBuffer().str(),
                                     "raw-polynomial.zkc"}}));
        auto project = take(language::analyze(captured).checkedProject());
        auto closed = take(zkc::test::closeProtocolDeployment(
            project, "raw_computation::Demo"));
        auto original =
            parse(take(language::emitOriginal(closed, context)), context);
        take(language::compareOriginal(closed, *original));
        auto prepared = copy(*original);
        auto closure = close(numericalEntry(*prepared));
        bool polynomial = false;
        closure->walk([&](Operation *op) {
          polynomial |= op->getName().getDialectNamespace() == "poly";
        });
        require(polynomial, "original-source polynomial helper was normalized "
                            "before formation");
        auto logical = formExecutable(*prepared);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "original-source raw Kernel failed");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "original-source recipe edge differed");
      });
  for (bool collectFoldFusion : {false, true})
    cases.run(
        Twine("call policy mutation cannot admit a forbidden bulk recipe") +
            (collectFoldFusion ? " with collect-fold fusion" : ""),
        [&] {
          auto source =
              fixture(context, "structured-source/realization-finite.mlir");
          auto logical = formExecutable(*source, {true, false});
          auto lowered = copy(*logical);
          require(succeeded(computation::realizeComputations(*lowered)),
                  "bulk fixture failed");
          logical->walk([&](exec::ComputeOp call) {
            Builder builder(call.getContext());
            call->setAttr("policy", builder.getBoolArrayAttr(
                                        {false, false, collectFoldFusion}));
          });
          require(succeeded(verify(*logical)), "policy mutation malformed");
          expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
            return computation::verifyComputationRealization(*logical,
                                                             *lowered);
          });
        });
  cases.run("empty helper premises remain part of the immutable closure", [&] {
    auto source = fixture(context, "structured-source/realization-finite.mlir");
    auto original = numericalEntry(*source);
    auto prepared = close(original);
    auto helper = SymbolTable(*prepared).lookup<func::FuncOp>("step");
    helper->setAttr("data.preconditions", ArrayAttr::get(&context, {}));
    require(succeeded(verify(*prepared)), "premise mutation malformed");
    expectRefusal(*prepared, "kernel-closure-correspondence", [&] {
      return computation::verifyComputationClosure(owner(*source), original,
                                                   *prepared);
    });
  });
  cases.run("an extra concrete recipe cannot be replayed", [&] {
    auto source = parse(realization, context);
    auto logical = formExecutable(*source);
    auto lowered = copy(*logical);
    require(succeeded(computation::realizeComputations(*lowered)),
            "lowering failed");
    auto function = scopedFunction(*lowered, "realized");
    auto instruction = sf::application(function, "field.sub");
    sc::duplicateInvocation(instruction, function, "extra_concrete_work");
    require(succeeded(verify(*lowered)),
            "replayed instruction mutation malformed");
    expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
      return computation::verifyComputationRealization(*logical, *lowered);
    });
  });
  cases.run(
      "concrete work cannot move from before to after a source guard", [&] {
        auto source = fixture(context, "kernel/shared-polynomial.mlir");
        auto logical = formExecutable(*source);
        func::FuncOp wrapper;
        logical->walk([&](exec::TestOp op) {
          wrapper = op->getParentOfType<func::FuncOp>();
        });
        require(bool(wrapper), "missing guarded calculation");
        auto call = cast<exec::ComputeOp>(wrapper.getBody().front().front());
        SymbolTableCollection symbols;
        auto entry = call.resolveCallee(symbols);
        OpBuilder builder(&entry.front().back());
        OperationState literal(entry.getLoc(), "algebra.constant");
        literal.addTypes(entry.getArgument(0).getType());
        literal.addAttribute("value", builder.getStringAttr("123"));
        auto *constantOp = builder.create(literal);
        auto returned = cast<func::ReturnOp>(entry.front().back());
        // Keep the literal live so the total helper simplifier cannot erase it.
        OperationState sum(entry.getLoc(), "algebra.field_add");
        sum.addOperands({entry.getArgument(0), constantOp->getResult(0)});
        sum.addTypes(constantOp->getResultTypes());
        auto *pack = returned.getOperand(0).getDefiningOp();
        require(pack && isa<algebra::ArrayFromElementsOp>(pack),
                "missing returned pack");
        auto *addition = builder.create(sum);
        constantOp->moveBefore(pack);
        addition->moveBefore(pack);
        pack->setOperand(0, addition->getResult(0));
        require(succeeded(verify(*logical)),
                "authored concrete work malformed");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "guard fixture lowering failed");
        auto actual = scopedFunction(*lowered, wrapper.getSymName());
        Operation *constant = nullptr;
        exec::TestOp guard;
        actual.walk([&](Operation *op) {
          if (auto branch = dyn_cast<exec::TestOp>(op))
            guard = branch;
          if (auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
              parameters && parameters.size() == 1)
            if (auto value = dyn_cast<StringAttr>(parameters[0]);
                value && value.getValue() == "123")
              constant = op;
        });
        require(constant && guard, "guard ordering mutation targets missing");
        constant->moveAfter(guard);
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(failed(computation::verifyComputationRealization(*logical,
                                                                 *lowered)),
                "guard ordering mutation escaped correspondence");
      });
  cases.run(
      "equivalent unpinned recipe bindings share one imported declaration",
      [&] {
        auto source = parse(realization, context);
        auto closed = closedFixture(*source);
        auto logical = formExecutable(*closed);
        OpBuilder builder(numericalUnit(*logical));
        auto secondUnit = cast<mlir::ModuleOp>(
            builder.clone(*numericalUnit(*logical).getOperation()));
        SymbolTable::setSymbolName(secondUnit, "second_unit");
        auto wrapper = scopedFunction(*logical, "realized");
        builder.setInsertionPoint(wrapper);
        auto second =
            cast<func::FuncOp>(builder.clone(*wrapper.getOperation()));
        SymbolTable::setSymbolName(second, "second_wrapper");
        second.walk([&](exec::ComputeOp call) {
          call->setAttr("callee", SymbolRefAttr::get(
                                      &context, "second_unit",
                                      call.getCallee().getNestedReferences()));
        });
        require(succeeded(verify(*logical)),
                "duplicate invocation fixture malformed");
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "duplicate lowering failed");
        unsigned bindings = 0;
        for (auto binding :
             owner(*lowered).getBody().front().getOps<runtime::BindingOp>())
          bindings += binding.getContract() == "field.sub" &&
                      binding.getImplementation().empty();
        require(bindings == 1,
                "equivalent binding signatures were duplicated per call");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "shared binding was not independently checked");
      });
  cases.run(
      "projection aliases share captures without merging distinct leaves", [&] {
        auto source = parse(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @identity(%x:!F)->!F {func.return %x:!F}
 func.func @work(%scope:!runtime.scope,%a:!F,%b:!F,%flag:i1)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.returned"(%a):(!F)->!exec.outcome<(!F)>
   func.return %r:!exec.outcome<(!F)>
 }
 "protocol.func"() ({^entry(%a:!F,%b:!F,%flag:i1):
   %result = "protocol.local_call"(%a,%b,%flag) {callee=@work,site="work",role="P"}:(!F,!F,i1)->!F
   "protocol.return"(%result):(!F)->()
 }) {sym_name="main",function_type=(!F,!F,i1)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]}:()->()
}) {profile=#protocol.profile<protocol>}:()->() }
)mlir",
                            context);
        auto identity =
            SymbolTable(owner(*source)).lookup<func::FuncOp>("identity");
        OpBuilder builder(identity);
        auto field = identity.getArgument(0).getType();
        auto root = scopedFunction(*source, "work");
        root.getBody().getBlocks().clear();
        builder.setInsertionPointToEnd(root.addEntryBlock());
        exec::ScopedExecutionBuilder control(builder, root);
        auto invoke = [&](Value value, StringRef site) {
          return control
              .invoke(
                  "exec.compute", field, control.scoped(value),
                  {builder.getNamedAttr(
                       "callee",
                       FlatSymbolRefAttr::get(identity.getSymNameAttr())),
                   builder.getNamedAttr("site", builder.getStringAttr(site))})
              .front();
        };
        auto alias = invoke(root.getArgument(1), "identity");
        auto other = invoke(root.getArgument(2), "other");
        auto again = invoke(root.getArgument(1), "again");
        SmallVector<Value> captures{root.getArgument(1), alias,
                                    root.getArgument(2), other, again};
        auto result = control.conditional(
            root.getArgument(3), captures, field, "choose",
            [&](unsigned branch) {
              auto region =
                  sc::region(builder, root, branch ? "otherwise" : "then",
                             TypeRange(captures), field);
              exec::ScopedExecutionBuilder action(builder, region);
              action.complete(region.getArgument(branch ? 4 : 5));
              return region;
            });
        control.returned(result);
        require(succeeded(verify(*source)), "authored scoped aliases refused");
        auto logical = formExecutable(*source);
        auto lowered = copy(*logical);
        require(succeeded(computation::realizeComputations(*lowered)),
                "alias capture lowering failed");
        auto function = scopedFunction(*lowered, "work");
        exec::TestOp test;
        function.walk([&](exec::TestOp op) { test = op; });
        require(bool(test), "conditional test disappeared");
        SmallVector<runtime::EnterScopeOp> entries;
        function.walk([&](runtime::EnterScopeOp enter) {
          if (enter.getSite() == test.getSite())
            entries.push_back(enter);
        });
        require(entries.size() == 2, "conditional alternatives disappeared");
        for (auto enter : entries)
          require(enter.getInputs().size() == 2,
                  "shared leaf was not captured once");
        require(succeeded(computation::verifyComputationRealization(*logical,
                                                                    *lowered)),
                "alias layout correspondence failed");
        for (auto enter : entries) {
          auto inputs = enter.getInputsMutable();
          auto left = enter.getInputs()[0], right = enter.getInputs()[1];
          inputs.assign(ValueRange{right, left});
          auto dispatch = cast<exec::DispatchOp>(enter->getNextNode());
          auto invocation = cast<func::CallOp>(dispatch.getReturned()->front());
          invocation->setOperand(1, right);
          invocation->setOperand(2, left);
        }
        require(succeeded(verify(*lowered)),
                "same-type capture mutation must remain formed");
        expectRefusal(*lowered, "numerical-lowering-correspondence", [&] {
          return computation::verifyComputationRealization(*logical, *lowered);
        });
      });
  return cases.result();
}
