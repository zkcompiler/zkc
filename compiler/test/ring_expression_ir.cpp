#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace zkc;
int main() {
  DialectRegistry registry;
  registry.insert<algebra::AlgebraDialect, func::FuncDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  OpBuilder builder(&context);
  auto location = builder.getUnknownLoc();
  auto field = algebra::FieldType::get(&context, "koala-bear");
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  builder.setInsertionPointToEnd(module->getBody());
  auto function = func::FuncOp::create(
      builder, location, "formula",
      builder.getFunctionType({field, field, field}, {field}));
  auto *body = function.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  auto product = algebra::FieldMultiplyOp::create(
      builder, location, field, body->getArgument(0), body->getArgument(1));
  auto difference = algebra::SubtractFieldOp::create(
      builder, location, field, product.getValue(), body->getArgument(0));
  auto returned =
      func::ReturnOp::create(builder, location, difference.getValue());
  unsigned failures = 0;
  auto check = [&](bool condition, llvm::StringRef name) {
    if (!condition) {
      llvm::errs() << "ring SSA view: " << name << '\n';
      ++failures;
    }
  };
  auto expression =
      algebra::describeRingExpression(*body, returned.getOperands());
  if (!expression) {
    llvm::errs() << llvm::toString(expression.takeError()) << '\n';
    return 1;
  }
  check(expression->inputs().size() == 3, "unused argument is retained");
  auto dependencies = expression->usedInputs({0});
  check(bool(dependencies), "dependencies available");
  if (dependencies)
    check(*dependencies == std::vector<uint32_t>({0, 1}),
          "ordered dependencies");
  else
    llvm::consumeError(dependencies.takeError());
  auto degrees = expression->degrees({3, 4, 0});
  check(bool(degrees), "weighted degree available");
  if (degrees)
    check((*degrees)[expression->outputs()[0]] == 7, "substitution degree");
  else
    llvm::consumeError(degrees.takeError());
  auto identity = expression->identity();
  builder.setInsertionPoint(returned);
  auto unused = algebra::FieldAddOp::create(
      builder, location, field, body->getArgument(2), body->getArgument(2));
  auto pruned = algebra::describeRingExpression(*body, returned.getOperands());
  check(bool(pruned), "unused valid formula is admitted");
  if (pruned)
    check(pruned->identity() == identity,
          "unused nodes do not change expression");
  else
    llvm::consumeError(pruned.takeError());
  unused.erase();
  auto refuse = [&](llvm::StringRef expected) {
    auto result =
        algebra::describeRingExpression(*body, returned.getOperands());
    check(!result, expected);
    if (!result)
      check(llvm::toString(result.takeError()).find(expected.str()) !=
                std::string::npos,
            "refusal identifier");
  };
  auto equality =
      algebra::FieldEqualOp::create(builder, location, builder.getI1Type(),
                                    body->getArgument(0), body->getArgument(1));
  refuse("ring-formula-operation");
  equality.erase();
  auto malformed =
      algebra::ConstantFieldOp::create(builder, location, field, "00");
  refuse("ring-literal");
  malformed.erase();
  product->setAttr("unreviewed", builder.getUnitAttr());
  refuse("ring-formula-operation");
  product->removeAttr("unreviewed");
  Block outside;
  auto capture = outside.addArgument(field, location);
  product->setOperand(1, capture);
  refuse("ring-formula-capture");
  product->setOperand(1, body->getArgument(1));
  return failures != 0;
}
