#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace zkc;

int main() {
  DialectRegistry registry;
  registry.insert<algebra::AlgebraDialect, arith::ArithDialect,
                  func::FuncDialect>();
  registerMathematicalInterfaces(registry);
  MLIRContext context(registry);
  auto module = parseSourceString<ModuleOp>(R"mlir(
module {
  func.func @forms(%a: i1, %b: i1, %i: i32,
                  %f: !algebra.field<"bls12-381.fr">,
                  %g: !algebra.field<"bls12-381.fr">) {
    %c = arith.constant true
    %and = arith.andi %a, %b : i1
    %or = arith.ori %a, %b : i1
    %xor = arith.xori %a, %b : i1
    %eq = arith.cmpi eq, %a, %b : i1
    %ne = arith.cmpi ne, %a, %b : i1
    %sum = algebra.field_add %f, %g :
      (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      -> !algebra.field<"bls12-381.fr">
    %selected = arith.select %a, %f, %g : !algebra.field<"bls12-381.fr">
    %integer = arith.andi %i, %i : i32
    %ordering = arith.cmpi slt, %a, %b : i1
    %unmodeled = arith.addi %i, %i : i32
    return
  }
})mlir",
                                            &context);
  if (!module)
    return 1;
  const MathematicalIdentity expected[] = {
      MathematicalIdentity::BooleanConstant,
      MathematicalIdentity::BooleanAnd,
      MathematicalIdentity::BooleanOr,
      MathematicalIdentity::BooleanXor,
      MathematicalIdentity::BooleanEqual,
      MathematicalIdentity::BooleanNotEqual,
      MathematicalIdentity::FieldAdd,
      MathematicalIdentity::Select};
  unsigned index = 0, unsupported = 0, failures = 0;
  module->walk([&](Operation *op) {
    auto meaning = dyn_cast<MathematicalOpInterface>(op);
    if (!meaning)
      return;
    auto identity = meaning.getMathematicalIdentity();
    if (!identity) {
      ++unsupported;
      return;
    }
    if (index >= std::size(expected) || *identity != expected[index++])
      ++failures;
    auto dependencies = meaning.getOperandDependencies(0);
    // Even field-valued select depends on the Boolean condition. A literal
    // alone has no dependencies; no argument role is manufactured for it.
    if (dependencies.size() != op->getNumOperands())
      ++failures;
    for (auto [i, operand] : llvm::enumerate(dependencies))
      if (i != operand)
        ++failures;
  });
  if (index != std::size(expected) || unsupported != 2 ||
      context.getLoadedDialect("protocol"))
    ++failures;
  if (failures)
    llvm::errs() << "mathematical interface failures: " << failures << '\n';
  return failures != 0;
}
