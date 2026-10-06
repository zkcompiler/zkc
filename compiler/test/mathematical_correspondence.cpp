#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
using namespace mlir;
using namespace zkc;
namespace {
void require(bool result, StringRef message) {
  if (!result) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "test compiler pass refused");
}
Operation *site(ModuleOp module, StringRef name, StringRef role) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto participant = op->getParentOfType<protocol_ir::ParticipantOp>();
    auto attr = op->getAttrOfType<StringAttr>("site");
    if (participant && participant.getRole() == role && attr &&
        attr.getValue() == name)
      result = op;
  });
  require(result != nullptr, "missing test occurrence");
  return result;
}
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
  func.func private @identity(%x:i1) -> i1 { return %x : i1 }
  "protocol.func"() ({
  ^entry(%n:ui64, %x:i1, %y:i1, %rng:!protocol.service_ref<"random.bls12-381.fr/1">):
    %actual = func.call @identity(%x) : (i1) -> i1
    %rx = protocol.exchange %actual {site="first", sender="P",receiver="V"} : i1
    %ry = protocol.exchange %y {site="second", sender="P",receiver="V"} : i1
    protocol.guard %rx {site="check",owner="V"}
    %a = "protocol.query"(%rng) {site="draw_a",owner="V",method="draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
    %b = "protocol.query"(%rng) {site="draw_b",owner="V",method="draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">) -> !algebra.field<"bls12-381.fr">
    %draw = protocol.exchange %b {site="draw_message",sender="V",receiver="P"} : !algebra.field<"bls12-381.fr">
    %out:2 = "protocol.repeat"(%n,%rx,%ry,%x,%y) ({
    ^body(%i:ui64,%state_a:i1,%state_b:i1,%capture_x:i1,%capture_y:i1):
      protocol.guard %capture_x {site="capture",owner="V"}
      "protocol.yield"(%state_a,%state_b) : (i1,i1) -> ()
    }) {site="round",carried=2:i64,maximum=8:i64,roles=["V"],carried_roles=[["V"],["V"]]} : (ui64,i1,i1,i1,i1) -> (i1,i1)
    "protocol.finish_if"(%out#0,%out#0,%out#1) {site="done",owner="V"} : (i1,i1,i1) -> ()
    "protocol.return"(%out#0,%out#1) : (i1,i1) -> ()
  }) {sym_name="main",function_type=(ui64,i1,i1,!protocol.service_ref<"random.bls12-381.fr/1">)->(i1,i1),roles=["P","V"],input_roles=[["V"],["P","V"],["P","V"],["V"]],output_roles=[["V"],["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () })mlir";
void negative(ModuleOp source, ModuleOp projected, StringRef name,
              const std::function<void(ModuleOp)> &mutate) {
  auto candidate = copy(projected);
  mutate(*candidate);
  require(succeeded(verify(*candidate)), "mutation must remain well formed");
  for (auto before : {source, projected}) {
    bool code = false;
    ScopedDiagnosticHandler expected(source.getContext(), [&](Diagnostic &d) {
      code |= d.str().find("mathematical-correspondence") != std::string::npos;
      return success();
    });
    require(
        failed(mathematical::verifyProjectionPreserved(before, *candidate)) &&
            code,
        name);
  }
  llvm::outs() << "refused: " << name << '\n';
}
std::string rewriteProgram(StringRef body, StringRef result = "%r",
                           StringRef scalar = "%x", StringRef group = "%g") {
  return (Twine(R"mlir(!f = !algebra.field<"bls12-381.fr">
!g = !algebra.group<"bls12-381.g1">
module { "protocol.module"() ({ "protocol.func"() ({
^entry(%c:i1,%d:i1,%x:!f,%y:!f,%g:!g,%h:!g):
)mlir") + body +
          "\n\"protocol.return\"(" + result + "," + scalar + "," + group +
          R"mlir() : (i1,!f,!g)->()
}) {sym_name="main",function_type=(i1,i1,!f,!f,!g,!g)->(i1,!f,!g),roles=["P"],input_roles=[["P"],["P"],["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir")
      .str();
}
void rewrite(MLIRContext &context, StringRef name, StringRef before,
             StringRef after, bool accepts) {
  auto a = parseSourceString<ModuleOp>(before, &context),
       b = parseSourceString<ModuleOp>(after, &context);
  require(bool(a) && bool(b), "rewrite fixture refused");
  run(*a, protocol::createProjectProtocolPass(false));
  run(*b, protocol::createProjectProtocolPass(false));
  bool code = false;
  ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
    code |= d.str().find("mathematical-correspondence") != std::string::npos;
    return success();
  });
  bool accepted = succeeded(mathematical::verifyProjectionPreserved(*a, *b));
  require(accepted == accepts && (accepts || code), name);
  llvm::outs() << "rewrite: " << name << '\n';
}
void rewrites(MLIRContext &context) {
  rewrite(
      context, "shared Boolean subterm retains correlation",
      rewriteProgram("%t = arith.andi %c,%d : i1\n%r = arith.andi %c,%t : i1"),
      rewriteProgram("%r = arith.andi %c,%d : i1"), true);
  rewrite(context, "comparison negation",
          rewriteProgram("%yes = arith.constant true\n%e = arith.cmpi eq,%c,%d "
                         ": i1\n%r = arith.xori %e,%yes : i1"),
          rewriteProgram("%r = arith.cmpi ne,%c,%d : i1"), true);
  rewrite(
      context, "typed selection laws",
      rewriteProgram(
          "%yes = arith.constant true\n%r = arith.select %c,%yes,%c : i1\n%s = "
          "arith.select %yes,%x,%y : !f\n%t = arith.select %d,%g,%g : !g",
          "%r", "%s", "%t"),
      rewriteProgram("", "%c"), true);
  rewrite(context, "nested field selection",
          rewriteProgram("%inner = arith.select %c,%y,%x : !f\n%s = "
                         "arith.select %c,%x,%inner : !f",
                         "%c", "%s"),
          rewriteProgram("", "%c"), true);
  rewrite(context, "Boolean operation mutation",
          rewriteProgram("%r = arith.andi %c,%d : i1"),
          rewriteProgram("%r = arith.ori %c,%d : i1"), false);
  rewrite(
      context, "unrecognized field commutation",
      rewriteProgram("%s = algebra.field_add %x,%y : (!f,!f)->!f", "%c", "%s"),
      rewriteProgram("%s = algebra.field_add %y,%x : (!f,!f)->!f", "%c", "%s"),
      false);
  std::string chain;
  for (unsigned i = 1; i <= 1500; ++i)
    chain += "%v" + std::to_string(i) + " = arith.andi %v" +
             std::to_string(i - 1) + ",%d : i1\n";
  rewrite(context, "long chain around a local Boolean fold",
          rewriteProgram("%yes = arith.constant true\n%e = arith.cmpi eq,%c,%d "
                         ": i1\n%v0 = arith.xori %e,%yes : i1\n" +
                             chain,
                         "%v1500"),
          rewriteProgram("%v0 = arith.cmpi ne,%c,%d : i1\n" + chain, "%v1500"),
          true);
}

void substitutions(MLIRContext &context) {
  auto source =
      parseSourceString<ModuleOp>(R"mlir(module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    "protocol.return"(%a) : (i1)->()
  }) {sym_name="component",function_type=(i1,i1)->i1,roles=["A"],input_roles=[["A"],["A"]],output_roles=[["A"]]} : ()->()
  "protocol.func"() ({ ^entry(%x:i1,%y:i1):
    %result = "protocol.apply"(%x,%y) {callee=@component,roles=["P"],site="invoke"} : (i1,i1)->i1
    "protocol.return"(%result) : (i1)->()
  }) {sym_name="main",function_type=(i1,i1)->i1,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
  }) {profile=#protocol.profile<protocol>} : ()->() })mlir",
                                  &context);
  require(bool(source), "application fixture refused");
  auto prepared = copy(*source);
  run(*prepared, protocol::createPrepareProtocolPass(false));
  require(succeeded(mathematical::verifyProtocolPreparationPreserved(
              unit(*source), unit(*prepared))),
          "application substitution control refused");
  for (bool remove : {false, true}) {
    auto candidate = copy(*prepared);
    bool changed = false;
    candidate->walk([&](protocol_ir::MathematicalOp function) {
      if (function.getSymName() != "main")
        return;
      auto &block = function.getBody().front();
      for (auto restriction : llvm::make_early_inc_range(
               block.getOps<protocol_ir::RestrictRolesOp>())) {
        if (restriction.getInput() != block.getArgument(0))
          continue;
        if (remove) {
          restriction.getOutput().replaceAllUsesWith(restriction.getInput());
          restriction.erase();
        } else
          restriction->setOperand(0, block.getArgument(1));
        changed = true;
        break;
      }
    });
    require(changed && succeeded(verify(*candidate)),
            "application mutant must be formed");
    bool code = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
      code |= d.str().find("mathematical-correspondence") != std::string::npos;
      return success();
    });
    require(failed(mathematical::verifyProtocolPreparationPreserved(
                unit(*source), unit(*candidate))) &&
                code,
            remove ? "application restriction removal passed"
                   : "application actual-argument swap passed");
  }
}
void polynomialMutations(MLIRContext &context) {
  auto source = parseSourceFile<ModuleOp>(
      std::string(ZKC_MATH_FIXTURES) + "/fixing.mlir", &context);
  require(bool(source), "polynomial fixture refused");
  run(*source, protocol::createProjectProtocolPass(false));
  for (bool coefficients : {false, true}) {
    auto candidate = copy(*source);
    run(*candidate, coefficients ? protocol::createEliminatePolynomialsPass()
                                 : protocol::createFixPolynomialFactorsPass());
    bool changed = false;
    candidate->walk([&](Operation *op) {
      if (changed)
        return;
      if (!coefficients && isa<poly::FixTableOp>(op)) {
        op->setOperand(0, op->getBlock()->getArgument(1));
        changed = true;
      } else if (coefficients) {
        auto constant = dyn_cast<algebra::ConstantFieldOp>(op);
        if (constant && constant.getValue() != "0" &&
            constant.getValue() != "1" && constant.getValue() != "2") {
          constant.setValue("0");
          changed = true;
        }
      }
    });
    require(changed && succeeded(verify(*candidate)),
            "polynomial mutant must be formed");
    bool code = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
      code |= d.str().find("mathematical-correspondence") != std::string::npos;
      return success();
    });
    require(
        failed(mathematical::verifyProjectionPreserved(*source, *candidate)) &&
            code,
        coefficients ? "wrong interpolation weight passed"
                     : "wrong fixed table passed");
  }
}

} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  rewrites(context);
  substitutions(context);
  polynomialMutations(context);
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "source fixture refused");
  auto projected = copy(*source);
  run(*projected, protocol::createProjectProtocolPass(false));
  require(
      succeeded(mathematical::verifyProjectionPreserved(*source, *projected)),
      "projection control refused");
  negative(*source, *projected, "same-typed send substitution", [](ModuleOp m) {
    auto *send = site(m, "first", "P");
    send->setOperand(0, send->getBlock()->getArgument(1));
  });
  negative(*source, *projected, "guard uses other receive", [](ModuleOp m) {
    site(m, "check", "V")->setOperand(0, site(m, "second", "V")->getResult(0));
  });
  negative(*source, *projected, "guard uses shared input instead of receive",
           [](ModuleOp m) {
             auto *guard = site(m, "check", "V");
             guard->setOperand(0, guard->getBlock()->getArgument(1));
           });
  negative(*source, *projected, "distinct draws remain distinct",
           [](ModuleOp m) {
             site(m, "draw_message", "V")
                 ->setOperand(0, site(m, "draw_a", "V")->getResult(0));
           });
  negative(*source, *projected, "carried entry swapped", [](ModuleOp m) {
    auto *loop = site(m, "round", "V");
    loop->setOperand(1, loop->getOperand(2));
  });
  negative(*source, *projected, "immutable capture swapped", [](ModuleOp m) {
    auto *guard = site(m, "capture", "V");
    auto *loop = guard->getParentOp();
    loop->setOperand(3, loop->getOperand(4));
  });
  negative(*source, *projected, "ordered yields swapped", [](ModuleOp m) {
    auto &yield = site(m, "round", "V")->getRegion(0).front().back();
    auto x = yield.getOperand(0);
    yield.setOperand(0, yield.getOperand(1));
    yield.setOperand(1, x);
  });
  negative(*source, *projected, "completion predicate swapped", [](ModuleOp m) {
    auto *done = site(m, "done", "V");
    done->setOperand(0, done->getOperand(2));
  });
  negative(*source, *projected, "completion output swapped", [](ModuleOp m) {
    auto *done = site(m, "done", "V");
    done->setOperand(1, done->getOperand(2));
  });
  negative(*source, *projected, "entry output swapped", [](ModuleOp m) {
    auto &finish = site(m, "done", "V")->getBlock()->back();
    finish.setOperand(0, finish.getOperand(1));
  });
  auto prepared = copy(*source);
  run(*prepared, protocol::createPrepareProtocolPass());
  require(succeeded(mathematical::verifyProtocolPreparationPreserved(
              unit(*source), unit(*prepared))),
          "helper substitution refused");
  prepared->walk([&](protocol_ir::ExchangeOp op) {
    if (op.getSite() == "first")
      op->setOperand(0, op->getBlock()->getArgument(2));
  });
  require(succeeded(verify(*prepared)), "preparation mutation malformed");
  bool code = false;
  ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
    code |= d.str().find("mathematical-correspondence") != std::string::npos;
    return success();
  });
  require(failed(mathematical::verifyProtocolPreparationPreserved(
              unit(*source), unit(*prepared))) &&
              code,
          "helper argument substitution passed");
  llvm::outs() << "preparation, projection and participant value "
                  "correspondence controls passed\n";
}
