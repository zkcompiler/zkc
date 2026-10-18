#include "../lib/Transforms/Kernel/Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/KernelRecipes.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Kernel.h"
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
constexpr llvm::StringLiteral realization = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 func.func private @difference(%a:!F,%b:!F)->!F {
   %v = algebra.field_subtract %a,%b : (!F,!F)->!F
   func.return %v : !F
 }
 local.realize @realized = @difference : (!F,!F)->!F
 local.func @work(%a:!F,%b:!F)->!F attributes {logical_origin=["work",[]]} {
   %v = local.apply @realized(%a,%b) {site="difference"} : (!F,!F)->!F
   local.return %v : !F
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
kernel::ModuleOp numericalUnit(mlir::ModuleOp module) {
  auto units = owner(module).getBody().front().getOps<kernel::ModuleOp>();
  require(!units.empty(), "missing logical numerical unit");
  return *units.begin();
}
func::FuncOp numericalEntry(mlir::ModuleOp module) {
  return kernel::getEntry(numericalUnit(module));
}
local::FuncOp localFunction(mlir::ModuleOp module, StringRef name) {
  auto result = SymbolTable(owner(module)).lookup<local::FuncOp>(name);
  require(bool(result), "missing Local function");
  return result;
}
OwningOpRef<mlir::ModuleOp> fixture(MLIRContext &context, StringRef path) {
  auto bytes = llvm::MemoryBuffer::getFile(
      (Twine(ZKC_KERNEL_FIXTURES) + "/" + path).str());
  require(bool(bytes), "cannot read Kernel fixture");
  return parse((*bytes)->getBuffer(), context);
}
void expectRefusal(mlir::ModuleOp candidate, StringRef code,
                   llvm::function_ref<LogicalResult()> check) {
  bool diagnostic = false;
  ScopedDiagnosticHandler handler(
      candidate.getContext(), [&](Diagnostic &value) {
        diagnostic |= value.str().find(code.str()) != std::string::npos;
        return success();
      });
  require(failed(check()), "mutated correspondence was accepted");
  require(diagnostic, "refusal lost its diagnostic identifier");
}
OwningOpRef<mlir::ModuleOp> exec(mlir::ModuleOp source,
                                 MathematicalSelectionPolicy policy = {}) {
  auto result = copy(source);
  run(*result, protocol::createProjectProtocolPass(false, policy));
  run(*result, protocol::createLowerMathPass(policy));
  require(owner(*result).getProfile() == protocol_ir::Profile::Exec,
          "lower-math did not produce Exec");
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("direct Kernel recipe output retains the immutable source", [&] {
    auto original = parse(demanded, context);
    auto logical = exec(*original);
    auto unit = numericalUnit(*logical);
    auto entry = kernel::getEntry(unit);
    OpBuilder builder(&context);
    entry->setAttr("sym_visibility", builder.getStringAttr("public"));
    entry->setAttr("data.preconditions", builder.getArrayAttr({}));
    require(succeeded(verify(*logical)), "recipe source metadata refused");
    auto before = copy(*logical);
    mathematical::RealizationWork work;
    uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
    auto output =
        kernel::realizeEntry(unit, "direct", {}, work, remaining, bytes);
    require(bool(output) && succeeded(kernel::verifyRecipeOutput(*output)) &&
                succeeded(kernel::verifyEntryRecipes(unit, *output, "direct")),
            "direct numerical recipe publication failed");
    auto executable = kernelRecipeOutput(*output);
    auto result =
        SymbolTable(executable).lookup<local::FuncOp>(entry.getSymName());
    require(
        result && result.getFunctionType() == entry.getFunctionType() &&
            result->getAttrs().size() == 3 &&
            !result->hasAttr("sym_visibility") &&
            !result->hasAttr("data.preconditions") &&
            result->getAttr("logical_origin") ==
                builder.getArrayAttr({builder.getStringAttr(entry.getSymName()),
                                      builder.getArrayAttr({})}),
        "recipe entry did not preserve its executable interface");
    require(OperationEquivalence::isEquivalentTo(
                *logical, *before, OperationEquivalence::IgnoreLocations),
            "numerical recipe production changed its source");
    require(remaining < 1000000 && bytes < 16 * 1024 * 1024,
            "direct conversion failed to charge source/site work");
    for (StringRef mutation :
         {"return", "operand", "site", "interface", "declaration", "module",
          "owner-argument", "owner-operand", "owner-result", "module-argument",
          "module-operand"}) {
      auto changed = copy(*output);
      auto function = SymbolTable(kernelRecipeOutput(*changed))
                          .lookup<local::FuncOp>(entry.getSymName());
      auto &body = function.getBody().front();
      OpBuilder builder(&context);
      if (mutation == "return")
        body.back().setOperand(0, body.back().getOperand(1));
      else if (mutation == "operand")
        body.front().setOperand(1, body.front().getOperand(0));
      else if (mutation == "site")
        body.front().setAttr("site", builder.getStringAttr("other-call"));
      else if (mutation == "interface")
        function->setAttr("logical_origin",
                          builder.getArrayAttr({builder.getStringAttr("extra"),
                                                builder.getArrayAttr({})}));
      else if (mutation == "declaration") {
        builder.setInsertionPointToEnd(
            &kernelRecipeOutput(*changed).getBody().front());
        auto extra = func::FuncOp::create(builder, entry.getLoc(), "extra",
                                          builder.getFunctionType({}, {}));
        extra.setPrivate();
        builder.setInsertionPointToEnd(extra.addEntryBlock());
        func::ReturnOp::create(builder, entry.getLoc());
      } else if (mutation == "owner-argument")
        kernelRecipeOutput(*changed).getBody().front().addArgument(
            builder.getI1Type(), entry.getLoc());
      else if (mutation == "owner-operand" || mutation == "owner-result") {
        auto previous = kernelRecipeOutput(*changed);
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
        require(replacement->getNumOperands() + replacement->getNumResults() ==
                    1,
                "owner mutation did not change its structural arity");
      } else if (mutation == "module-argument")
        changed->getBody()->addArgument(builder.getI1Type(), entry.getLoc());
      else if (mutation == "module-operand") {
        OperationState state(changed->getLoc(), (*changed)->getName());
        state.addOperands(function.getArguments()[0]);
        state.addRegion();
        auto *replacement = Operation::create(state);
        replacement->getRegion(0).takeBody(changed->getBodyRegion());
        changed =
            OwningOpRef<mlir::ModuleOp>(cast<mlir::ModuleOp>(replacement));
        require((*changed)->getNumOperands() == 1,
                "module mutation did not add its operand");
      } else
        (*changed)->setAttr("unexpected", builder.getUnitAttr());
      finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                         {}};
      require(failed(kernel::verifyEntryRecipes(unit, *changed, "direct", {},
                                                {}, &outcome)) &&
                  outcome.status == finite::VerificationStatus::Mismatch,
              ("recipe reader accepted " + mutation).str());
    }
    uint64_t noCopy = 0, siteBytes = 16 * 1024 * 1024;
    require(
        !kernel::realizeEntry(unit, "direct", {}, work, noCopy, siteBytes) &&
            OperationEquivalence::isEquivalentTo(
                *logical, *before, OperationEquivalence::IgnoreLocations),
        "source copy exhaustion published or edited a numerical body");
  });
  cases.run("unused helper may call the public Kernel entry", [&] {
    auto source = parse(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
 kernel.module @numerical {
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
    auto unit = cast<kernel::ModuleOp>(source->getBody()->front());
    auto before = copy(*source);
    mathematical::RealizationWork work;
    auto output = realizeKernelEntry(unit, "square", {}, work);
    require(output && succeeded(kernel::verifyRecipeOutput(*output)) &&
                succeeded(kernel::verifyEntryRecipes(unit, *output, "square")),
            "unused caller prevented recipe publication");
    auto executable = kernelRecipeOutput(*output);
    require(SymbolTable(executable).lookup<local::FuncOp>("square") &&
                !SymbolTable(executable).lookup("unused_caller"),
            "source helper escaped into executable output");
    require(OperationEquivalence::isEquivalentTo(
                *source, *before, OperationEquivalence::IgnoreLocations),
            "recipe production changed the unused caller or public entry");
  });
  cases.run("identity recipe rejects an extra Local return attribute", [&] {
    auto source = parse(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
 kernel.module @numerical {
   func.func @identity(%x:!F)->!F {
     func.return %x : !F
   }
 }
}
)mlir",
                        context);
    auto unit = cast<kernel::ModuleOp>(source->getBody()->front());
    auto before = copy(*source);
    mathematical::RealizationWork work;
    auto output = realizeKernelEntry(unit, "identity", {}, work);
    require(
        output && succeeded(kernel::verifyRecipeOutput(*output)) &&
            succeeded(kernel::verifyEntryRecipes(unit, *output, "identity")),
        "identity recipe publication failed");
    kernelRecipeOutput(*output);
    auto changed = copy(*output);
    auto &body = localFunction(*changed, "identity").getBody().front();
    require(llvm::hasSingleElement(body) && isa<local::ReturnOp>(body.back()),
            "identity fixture unexpectedly contains executable work");
    body.back().setAttr("unexpected", UnitAttr::get(&context));
    expectRefusal(*changed, "interactive-unknown-attribute",
                  [&] { return kernel::verifyRecipeOutput(*changed); });
    expectRefusal(*changed, "mathematical-lowering-preservation", [&] {
      return kernel::verifyEntryRecipes(unit, *changed, "identity");
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
    auto numerical = kernelRecipeUnit(owner(*source));
    OpBuilder builder(&numerical->getBody().front(),
                      numerical->getBody().front().end());
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
    OwningOpRef<kernel::ModuleOp> before(
        cast<kernel::ModuleOp>(numerical->clone()));
    mathematical::RealizationWork work;
    auto output = realizeKernelEntry(*numerical, "presence", {}, work);
    require(output && succeeded(kernel::verifyRecipeOutput(*output)) &&
                succeeded(kernel::verifyEntryRecipes(*numerical, *output,
                                                     "presence")),
            "variant observation recipe publication failed");
    kernelRecipeOutput(*output);
    auto changed = copy(*output);
    SmallVector<local::BoolConstantOp> constants;
    localFunction(*changed, "present").walk([&](local::BoolConstantOp op) {
      constants.push_back(op);
    });
    require(constants.size() == 2, "variant recipe lost its two alternatives");
    auto first = constants[0]->getAttrOfType<StringAttr>("site");
    auto second = constants[1]->getAttrOfType<StringAttr>("site");
    auto prefix = kernelRecipeSite("presence", 0) + "_recipe_";
    require(first && second && first != second &&
                first.getValue().starts_with(prefix) &&
                second.getValue().starts_with(prefix),
            "variant recipe did not generate distinct owned sites");
    constants[1]->setAttr("site", first);
    expectRefusal(*changed, "interactive-site",
                  [&] { return kernel::verifyRecipeOutput(*changed); });
    expectRefusal(*changed, "mathematical-lowering-preservation", [&] {
      return kernel::verifyEntryRecipes(*numerical, *changed, "presence");
    });
    require(OperationEquivalence::isEquivalentTo(
                *numerical, *before, OperationEquivalence::IgnoreLocations) &&
                OperationEquivalence::isEquivalentTo(
                    *source, *original, OperationEquivalence::IgnoreLocations),
            "variant recipe production or checking changed its source");
  });
  cases.run(
      "Local realization owns mathematics through public Exec phase", [&] {
        auto source = parse(realization, context);
        auto prepared = copy(*source);
        require(succeeded(mathematical::expandMathRealizations(*prepared)),
                "formation failed");
        auto wrapper = localFunction(*prepared, "realized");
        require(isa<kernel::CallOp>(wrapper.getBody().front().front()),
                "wrapper did not call Kernel");
        require(succeeded(mathematical::verifyMathRealizationsPreserved(
                    *source, *prepared)),
                "actual helper/closure correspondence failed");
        auto original =
            SymbolTable(owner(*source)).lookup<func::FuncOp>("difference");
        require(succeeded(kernel::verifyKernelClosure(
                    owner(*source), original, numericalUnit(*prepared))),
                "exact closure with entry rename failed");
        auto logical = exec(*prepared, {false, false});
        require(bool(numericalEntry(*logical)),
                "Kernel did not survive projection/lower-math");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "explicit lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "checked edge failed");
        bool residual = false;
        lowered->walk([&](Operation *op) {
          residual |= isa<kernel::ModuleOp, kernel::CallOp>(op);
        });
        require(!residual, "unresolved numerical code survived");
        auto result = localFunction(*lowered, "realized");
        auto site =
            result.getBody().front().front().getAttrOfType<StringAttr>("site");
        uint64_t bytes = 1024;
        auto expected =
            protocol::algorithmSite({{"kernel", "kernel"}}, "0", bytes);
        require(expected && site && site.getValue() == *expected,
                "normalized ordinal did not use the actual ordered call site");
        require(result->getAttr("logical_origin") ==
                    wrapper->getAttr("logical_origin"),
                "logical origin changed");
      });
  cases.run("formation rejects same-type helper operand permutation", [&] {
    auto source = parse(realization, context);
    auto candidate = copy(*source);
    require(succeeded(mathematical::expandMathRealizations(*candidate)),
            "formation failed");
    auto &op = numericalEntry(*candidate).front().front();
    auto first = op.getOperand(0);
    op.setOperand(0, op.getOperand(1));
    op.setOperand(1, first);
    require(succeeded(verify(*candidate)), "mutation malformed");
    expectRefusal(*candidate, "local-realization-correspondence", [&] {
      return mathematical::verifyMathRealizationsPreserved(*source, *candidate);
    });
  });
  cases.run("formation rejects wrapper capture permutation", [&] {
    auto source = parse(realization, context);
    auto candidate = copy(*source);
    require(succeeded(mathematical::expandMathRealizations(*candidate)),
            "formation failed");
    auto &call =
        localFunction(*candidate, "realized").getBody().front().front();
    auto first = call.getOperand(0);
    call.setOperand(0, call.getOperand(1));
    call.setOperand(1, first);
    require(succeeded(verify(*candidate)), "mutation malformed");
    expectRefusal(*candidate, "local-realization-correspondence", [&] {
      return mathematical::verifyMathRealizationsPreserved(*source, *candidate);
    });
  });
  cases.run(
      "actual Local recipe same-type operand permutation is refused", [&] {
        auto source = parse(realization, context);
        auto logical = exec(*source);
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)), "lowering failed");
        auto &op =
            localFunction(*lowered, "realized").getBody().front().front();
        auto first = op.getOperand(0);
        op.setOperand(0, op.getOperand(1));
        op.setOperand(1, first);
        require(succeeded(verify(*lowered)), "mutation malformed");
        expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
          return kernel::verifyKernelLowering(*logical, *lowered);
        });
      });
  cases.run("independent lowering rejects a changed numerical root site", [&] {
    auto source = parse(realization, context);
    auto logical = exec(*source);
    auto lowered = copy(*logical);
    require(succeeded(kernel::lowerKernels(*lowered)), "lowering failed");
    auto &op = localFunction(*lowered, "realized").getBody().front().front();
    op.setAttr("site", StringAttr::get(&context, "kernel"));
    require(succeeded(verify(*lowered)), "mutation malformed");
    expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
      return kernel::verifyKernelLowering(*logical, *lowered);
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
      partial |= isa<local::StopOp, local::GuardOp, local::LocalIfOp>(op);
    });
    require(!partial, "partial control entered numerical unit");
    local::StopOp stop;
    logical->walk([&](local::StopOp op) {
      if (op.getSite() == "check")
        stop = op;
    });
    require(bool(stop), "ordered source rejection disappeared");
    auto lowered = copy(*logical);
    require(succeeded(kernel::lowerKernels(*lowered)),
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
        auto logical = exec(*source, {optimize, false});
        auto entry = numericalEntry(*logical);
        require(
            entry.front().front().getName().getStringRef().contains("finite"),
            "finite mathematics lowered before explicit Kernel edge");
        auto lowered = copy(*logical);
        // The stored per-call policy survives the fallback argument here.
        require(succeeded(kernel::lowerKernels(*lowered, {!optimize, false})),
                "finite lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "finite logical-to-Local check failed");
      });
  for (bool optimize : {false, true})
    cases.run(
        optimize ? "stored finite policy selects bulk"
                 : "stored finite policy retains ordered traversal",
        [&] {
          auto source =
              fixture(context, "structured-source/realization-finite.mlir");
          auto logical = exec(*source, {optimize, false});
          auto lowered = copy(*logical);
          require(succeeded(kernel::lowerKernels(*lowered, {!optimize, false})),
                  "finite policy lowering failed");
          bool loop = false;
          lowered->walk([&](local::LocalForOp) { loop = true; });
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
        auto logical = exec(*source, {true, false});
        auto bulk = copy(*logical);
        require(succeeded(kernel::lowerKernels(*bulk)), "bulk control failed");
        unsigned admissionLoops = 0, traversals = 0;
        bool reduction = false;
        bulk->walk([&](local::LocalForOp loop) {
          if (loop.getNumResults())
            ++traversals;
          else
            ++admissionLoops;
        });
        bulk->walk([&](local::OperationBindingOp binding) {
          reduction |= binding.getContract() == "vector.sum";
        });
        require(
            admissionLoops && !traversals && reduction,
            "control lacks bulk reduction beside mandatory admission loops");
        logical->walk([&](kernel::CallOp call) {
          call->setAttr("policy",
                        builder.getBoolArrayAttr({false, false, false}));
        });
        require(succeeded(verify(*logical)), "disabled source not admitted");
        expectRefusal(*bulk, "kernel-lowering-correspondence", [&] {
          return kernel::verifyKernelLowering(*logical, *bulk);
        });
        auto ordered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*ordered)) &&
                    succeeded(kernel::verifyKernelLowering(*logical, *ordered)),
                "ordered fallback lost mandatory domain admission");
      });
  for (bool optimize : {false, true})
    cases.run(
        optimize ? "omitted policy uses bulk request"
                 : "omitted policy uses ordered request",
        [&] {
          auto source =
              fixture(context, "structured-source/realization-finite.mlir");
          auto logical = exec(*source);
          logical->walk(
              [](kernel::CallOp call) { call->removeAttr("policy"); });
          auto lowered = copy(*logical);
          MathematicalSelectionPolicy policy{optimize, false};
          require(succeeded(kernel::lowerKernels(*lowered, policy)) &&
                      succeeded(kernel::verifyKernelLowering(*logical, *lowered,
                                                             policy)),
                  "fallback policy was not shared with verification");
          bool loop = false;
          lowered->walk([&](local::LocalForOp) { loop = true; });
          require(loop == !optimize, "omitted policy ignored lowering request");
        });
  cases.run(
      "isolated units resolve identical private names independently", [&] {
        auto source =
            fixture(context, "structured-source/realization-finite.mlir");
        auto logical = exec(*source, {false, false});
        OpBuilder builder(numericalUnit(*logical));
        auto second = cast<kernel::ModuleOp>(
            builder.clone(*numericalUnit(*logical).getOperation()));
        SymbolTable::setSymbolName(second, "second_numerical");
        auto wrapper = localFunction(*logical, "realized");
        builder.setInsertionPoint(wrapper);
        auto secondWrapper =
            cast<local::FuncOp>(builder.clone(*wrapper.getOperation()));
        SymbolTable::setSymbolName(secondWrapper, "second_realized");
        secondWrapper.walk([&](kernel::CallOp call) {
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
        require(succeeded(kernel::lowerKernels(*lowered)),
                "colliding private identities prevented lowering");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "isolated closure correspondence failed");
        bool addition = false, subtraction = false;
        for (auto binding : owner(*lowered)
                                .getBody()
                                .front()
                                .getOps<local::OperationBindingOp>()) {
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
        auto candidate = copy(*source);
        require(succeeded(mathematical::expandMathRealizations(*candidate)),
                "formation failed");
        auto unit = numericalUnit(*candidate);
        auto domain = *unit.getBody().front().getOps<data::DomainOp>().begin();
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
          return mathematical::verifyMathRealizationsPreserved(*source,
                                                               *candidate);
        });
      });
  cases.run("finite closure checks actual callback computation", [&] {
    auto source = fixture(context, "structured-source/realization-finite.mlir");
    auto candidate = copy(*source);
    require(succeeded(mathematical::expandMathRealizations(*candidate)),
            "formation failed");
    auto step =
        SymbolTable(numericalUnit(*candidate)).lookup<func::FuncOp>("step");
    step.front().back().setOperand(0, step.getArgument(0));
    require(succeeded(verify(*candidate)), "callback mutation malformed");
    expectRefusal(*candidate, "kernel-closure-correspondence", [&] {
      return mathematical::verifyMathRealizationsPreserved(*source, *candidate);
    });
  });
  cases.run(
      "checked polynomial math stays numerical until explicit lowering", [&] {
        auto source = fixture(context, "mathematical/helper-realization.mlir");
        auto logical = exec(*source, {false, false});
        require(bool(numericalEntry(*logical)),
                "polynomial realization did not form a unit");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "polynomial lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "polynomial edge failed");
      });
  cases.run(
      "dormant owned units are checked and removed without execution", [&] {
        auto source = parse(realization, context);
        auto logical = exec(*source);
        OpBuilder builder(numericalUnit(*logical));
        auto dormant = cast<kernel::ModuleOp>(
            builder.clone(*numericalUnit(*logical).getOperation()));
        SymbolTable::setSymbolName(dormant, "dormant");
        require(succeeded(verify(*logical)), "dormant closure malformed");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "dormant unit prevented lowering");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "dormant edge failed");
        dormant->setAttr("unsupported", builder.getUnitAttr());
        auto frozen = copy(*logical);
        expectRefusal(*logical, "kernel-formation",
                      [&] { return kernel::lowerKernels(*logical); });
        require(OperationEquivalence::isEquivalentTo(
                    logical->getOperation(), frozen->getOperation(),
                    OperationEquivalence::IgnoreLocations),
                "failed transaction changed source");
      });
  cases.run("exact readback expands authored standard helper calls", [&] {
    auto source = parse(realization, context);
    auto logical = exec(*source);
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
    require(succeeded(kernel::lowerKernels(*lowered)),
            "exact helper substitution failed");
    require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
            "helper edge failed");
  });
  cases.run(
      "raw authored polynomial entry lowers through checked normalization",
      [&] {
        auto source = fixture(context, "mathematical/helper-realization.mlir");
        auto logical = exec(*source);
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
        require(succeeded(kernel::lowerKernels(*lowered)),
                "raw polynomial lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "raw polynomial recipe correspondence failed");
        require(OperationEquivalence::isEquivalentTo(
                    logical->getOperation(), frozen->getOperation(),
                    OperationEquivalence::IgnoreLocations),
                "lowering changed its immutable original source root");
      });
  cases.run("repeated staged Local expansion distinguishes ordered calls", [&] {
    std::string text = realization.str();
    auto position = text.find("   local.return %v : !F");
    require(position != std::string::npos, "missing repeated-use insertion");
    text.insert(position, "   %again = local.apply @realized(%b,%a) "
                          "{site=\"again\"} : (!F,!F)->!F\n");
    auto source = parse(text, context);
    require(succeeded(mathematical::expandMathRealizations(*source)),
            "formation failed");
    protocol::AlgorithmExpansionState state;
    require(succeeded(protocol::expandAlgorithms(
                *source, protocol::AlgorithmExpansionPhase::RetainMaps, state)),
            "retaining algorithms failed");
    auto before = copy(*source);
    auto beforeState = state;
    std::vector<protocol::AlgorithmOrigin> origins;
    require(succeeded(protocol::expandAlgorithms(
                *source, protocol::AlgorithmExpansionPhase::Finish, state,
                &origins)),
            "finishing algorithms failed");
    require(succeeded(protocol::verifyStagedAlgorithmExpansionPreserved(
                *before, *source, protocol::AlgorithmExpansionPhase::Finish,
                beforeState, state)),
            "independent algorithm correspondence failed");
    auto work = localFunction(*source, "work");
    llvm::StringSet<> invocationSites;
    unsigned count = 0;
    work.walk([&](kernel::CallOp call) {
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
    auto logical = exec(*source);
    auto lowered = copy(*logical);
    require(succeeded(kernel::lowerKernels(*lowered)),
            "repeated call realization failed");
    require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
            "repeated call checked edge failed");
  });
  cases.run(
      "fixed opaque binding survives and cannot be silently repinned", [&] {
        std::string text = realization.str();
        text.insert(text.find(" func.func private"), R"mlir(
      "local.binding"() {sym_name="pinned",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
    )mlir");
        auto source = parse(text, context);
        auto logical = exec(*source);
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "pinned context prevented lowering");
        auto pinned = SymbolTable(owner(*lowered))
                          .lookup<local::OperationBindingOp>("pinned");
        require(pinned.getImplementation() == "arkworks-msb/poly.fold",
                "pin changed during numerical lowering");
        pinned->setAttr("implementation", StringAttr::get(&context, ""));
        require(succeeded(verify(*lowered)), "repinned context malformed");
        expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
          return kernel::verifyKernelLowering(*logical, *lowered);
        });
      });
  cases.run(
      "raw helper and mixed polynomial results survive preparation and "
      "projection",
      [&] {
        auto source = fixture(context, "kernel/mixed-helper.mlir");
        auto prepared = copy(*source);
        require(succeeded(mathematical::expandMathRealizations(*prepared)),
                "raw formation failed");
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
        auto logical = exec(*prepared);
        require(isa<func::CallOp>(numericalEntry(*logical).front().front()),
                "projection erased the raw helper call");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "mixed helper lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "mixed helper coordinates failed correspondence");
        auto result = localFunction(*lowered, "realized");
        auto returned = cast<local::ReturnOp>(result.getBody().front().back());
        auto first = returned.getOperand(0);
        returned.setOperand(0, returned.getOperand(2));
        returned.setOperand(2, first);
        require(succeeded(verify(*lowered)), "mixed result mutation malformed");
        expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
          return kernel::verifyKernelLowering(*logical, *lowered);
        });
      });
  cases.run(
      "shared interpolation crosses an ordered guard through concrete ports",
      [&] {
        auto source = fixture(context, "kernel/shared-polynomial.mlir");
        auto participant = copy(*source);
        run(*participant, protocol::createProjectProtocolPass(false));
        auto logical = copy(*participant);
        run(*logical, protocol::createLowerMathPass());
        require(succeeded(mathematical::verifyProjectionPreserved(*participant,
                                                                  *logical)),
                "raw descriptor reconstruction or transitive escape differed");
        unsigned descriptors = 0;
        logical->walk([&](Operation *op) {
          descriptors += op->getName().getStringRef() == "poly.interpolate";
        });
        require(descriptors == 2,
                "raw descriptor was not reconstructed at both cuts");
        auto normalized = kernel::prepareKernelLowering(*logical);
        require(bool(normalized), "shared normalization frontier refused");
        unsigned extraInputs = 0, extraOutputs = 0;
        for (auto function :
             owner(*normalized).getBody().front().getOps<local::FuncOp>()) {
          auto before = SymbolTable(owner(*logical))
                            .lookup<local::FuncOp>(function.getSymName());
          require(bool(before),
                  "normalization added an unrelated Local function");
          extraInputs += function.getNumArguments() - before.getNumArguments();
          extraOutputs += function.getNumResults() - before.getNumResults();
        }
        require(extraInputs && extraOutputs,
                "shared coefficients were recomputed instead of exported");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "shared frontier recipe lowering failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "shared frontier actual candidate failed correspondence");
        local::CallOp consumer;
        lowered->walk([&](protocol_ir::ParticipantOp participant) {
          participant.walk([&](local::CallOp call) {
            auto before = SymbolTable(owner(*logical))
                              .lookup<local::FuncOp>(call.getCallee());
            if (before && call.getNumOperands() > before.getNumArguments())
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
        expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
          return kernel::verifyKernelLowering(*logical, *lowered);
        });
      });
  cases.run(
      "mixed helper concrete work is not replayed across action cuts", [&] {
        auto source = fixture(context, "kernel/mixed-helper-cuts.mlir");
        auto logical = exec(*source);
        unsigned differences = 0;
        logical->walk([&](Operation *op) {
          differences +=
              op->getName().getStringRef() == "algebra.field_subtract";
        });
        require(differences == 1,
                "mixed helper replayed an already concrete dependency");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "mixed helper cuts failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "mixed helper cut coordinates failed correspondence");
      });
  for (unsigned ports : {1u, 2u, 3u})
    cases.run(
        "standard call metadata survives concrete port growth " + Twine(ports),
        [&] {
          auto source = fixture(context, "kernel/shared-polynomial.mlir");
          auto logical = exec(*source);
          logical->walk([&](kernel::CallOp call) {
            auto empty = DictionaryAttr::get(&context);
            if (ports & 1)
              call.setArgAttrsAttr(ArrayAttr::get(
                  &context,
                  SmallVector<Attribute>(call.getNumOperands(), empty)));
            if (ports & 2)
              call.setResAttrsAttr(ArrayAttr::get(
                  &context,
                  SmallVector<Attribute>(call.getNumResults(), empty)));
          });
          require(succeeded(verify(*logical)),
                  "standard empty call metadata was refused");
          auto normalized = kernel::prepareKernelLowering(*logical);
          require(bool(normalized) && succeeded(verify(*normalized)),
                  "port growth invalidated standard call metadata");
          auto lowered = copy(*logical);
          require(succeeded(kernel::lowerKernels(*lowered)),
                  "standard metadata prevented numerical realization");
          require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                  "standard metadata lost checked correspondence");
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
            (Twine(ZKC_KERNEL_FIXTURES) + "/kernel/raw-polynomial.zkc").str());
        require(bool(bytes), "missing source fixture");
        auto captured =
            take(language::capture({{"raw_kernel", (*bytes)->getBuffer().str(),
                                     "raw-polynomial.zkc"}}));
        auto project = take(language::analyze(captured).checkedProject());
        auto closed = take(language::closeEntry(project, "raw_kernel::Demo"));
        auto original =
            parse(take(language::emitOriginal(closed, context)), context);
        take(language::compareOriginal(closed, *original));
        auto prepared = copy(*original);
        require(succeeded(mathematical::expandMathRealizations(*prepared)),
                "source realization formation failed");
        bool polynomial = false;
        prepared->walk([&](kernel::ModuleOp unit) {
          unit.walk([&](Operation *op) {
            polynomial |= op->getName().getDialectNamespace() == "poly";
          });
        });
        require(polynomial, "original-source polynomial helper was normalized "
                            "before formation");
        auto logical = exec(*prepared);
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "original-source raw Kernel failed");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "original-source recipe edge differed");
      });
  for (bool collectFoldFusion : {false, true})
    cases.run(
        Twine("call policy mutation cannot admit a forbidden bulk recipe") +
            (collectFoldFusion ? " with collect-fold fusion" : ""),
        [&] {
          auto source =
              fixture(context, "structured-source/realization-finite.mlir");
          auto logical = exec(*source, {true, false});
          auto lowered = copy(*logical);
          require(succeeded(kernel::lowerKernels(*lowered)),
                  "bulk fixture failed");
          logical->walk([&](kernel::CallOp call) {
            Builder builder(call.getContext());
            call->setAttr("policy", builder.getBoolArrayAttr(
                                        {false, false, collectFoldFusion}));
          });
          require(succeeded(verify(*logical)), "policy mutation malformed");
          expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
            return kernel::verifyKernelLowering(*logical, *lowered);
          });
        });
  cases.run("empty helper premises remain part of the immutable closure", [&] {
    auto source = fixture(context, "structured-source/realization-finite.mlir");
    auto prepared = copy(*source);
    require(succeeded(mathematical::expandMathRealizations(*prepared)),
            "formation failed");
    auto helper =
        SymbolTable(numericalUnit(*prepared)).lookup<func::FuncOp>("step");
    helper->setAttr("data.preconditions", ArrayAttr::get(&context, {}));
    require(succeeded(verify(*prepared)), "premise mutation malformed");
    expectRefusal(*prepared, "kernel-closure-correspondence", [&] {
      return mathematical::verifyMathRealizationsPreserved(*source, *prepared);
    });
  });
  cases.run("an extra concrete recipe cannot be replayed", [&] {
    auto source = parse(realization, context);
    auto logical = exec(*source);
    auto lowered = copy(*logical);
    require(succeeded(kernel::lowerKernels(*lowered)), "lowering failed");
    auto function = localFunction(*lowered, "realized");
    auto *instruction = &function.getBody().front().front();
    OpBuilder builder(instruction);
    auto *extra = builder.clone(*instruction);
    extra->setAttr("site", builder.getStringAttr("extra_concrete_work"));
    require(succeeded(verify(*lowered)),
            "replayed instruction mutation malformed");
    expectRefusal(*lowered, "kernel-lowering-correspondence", [&] {
      return kernel::verifyKernelLowering(*logical, *lowered);
    });
  });
  cases.run(
      "concrete work cannot move from before to after a source guard", [&] {
        auto source = fixture(context, "kernel/shared-polynomial.mlir");
        auto logical = exec(*source);
        local::FuncOp wrapper;
        logical->walk([&](local::FuncOp function) {
          if (llvm::any_of(
                  function.getBody().front().without_terminator(),
                  [](Operation &op) { return isa<local::LocalIfOp>(op); }))
            wrapper = function;
        });
        require(bool(wrapper), "missing guarded calculation");
        auto call = cast<kernel::CallOp>(wrapper.getBody().front().front());
        SymbolTableCollection symbols;
        auto entry = kernel::resolve(call, symbols);
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
        require(succeeded(kernel::lowerKernels(*lowered)),
                "guard fixture lowering failed");
        auto actual = localFunction(*lowered, wrapper.getSymName());
        Operation *constant = nullptr;
        local::LocalIfOp guard;
        for (auto &op : actual.getBody().front()) {
          if (auto branch = dyn_cast<local::LocalIfOp>(op))
            guard = branch;
          if (auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
              parameters && parameters.size() == 1)
            if (auto value = dyn_cast<StringAttr>(parameters[0]);
                value && value.getValue() == "123")
              constant = &op;
        }
        require(constant && guard, "guard ordering mutation targets missing");
        constant->moveAfter(guard);
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(failed(kernel::verifyKernelLowering(*logical, *lowered)),
                "guard ordering mutation escaped correspondence");
      });
  cases.run(
      "equivalent unpinned recipe bindings share one imported declaration",
      [&] {
        auto source = parse(realization, context);
        auto logical = exec(*source);
        OpBuilder builder(numericalUnit(*logical));
        auto secondUnit = cast<kernel::ModuleOp>(
            builder.clone(*numericalUnit(*logical).getOperation()));
        SymbolTable::setSymbolName(secondUnit, "second_unit");
        auto wrapper = localFunction(*logical, "realized");
        builder.setInsertionPoint(wrapper);
        auto second =
            cast<local::FuncOp>(builder.clone(*wrapper.getOperation()));
        SymbolTable::setSymbolName(second, "second_wrapper");
        second.walk([&](kernel::CallOp call) {
          call->setAttr("callee", SymbolRefAttr::get(
                                      &context, "second_unit",
                                      call.getCallee().getNestedReferences()));
        });
        require(succeeded(verify(*logical)),
                "duplicate invocation fixture malformed");
        auto lowered = copy(*logical);
        require(succeeded(kernel::lowerKernels(*lowered)),
                "duplicate lowering failed");
        unsigned bindings = 0;
        for (auto binding : owner(*lowered)
                                .getBody()
                                .front()
                                .getOps<local::OperationBindingOp>())
          bindings += binding.getContract() == "field.sub" &&
                      binding.getImplementation().empty();
        require(bindings == 1,
                "equivalent binding signatures were duplicated per call");
        require(succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
                "shared binding was not independently checked");
      });
  return cases.result();
}
