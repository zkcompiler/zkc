#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/Dialect.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
using namespace mlir;
using namespace zkc;
namespace {
unsigned folds = 0;
class ActionOp : public Op<ActionOp, OpTrait::OneOperand, OpTrait::OneResult> {
public:
  using Op::Op;
  static StringRef getOperationName() { return "scope.action"; }
  static ArrayRef<StringRef> getAttributeNames() { return {}; }
  LogicalResult fold(ArrayRef<Attribute>, SmallVectorImpl<OpFoldResult> &) {
    ++folds;
    return failure();
  }
};
class ReadOnlyOp
    : public Op<ReadOnlyOp, OpTrait::OneOperand, OpTrait::OneResult,
                MemoryEffectOpInterface::Trait> {
public:
  using Op::Op;
  static StringRef getOperationName() { return "scope.read"; }
  static ArrayRef<StringRef> getAttributeNames() { return {}; }
  void getEffects(SmallVectorImpl<MemoryEffects::EffectInstance> &effects) {
    effects.emplace_back(MemoryEffects::Read::get());
  }
};
class TestDialect : public Dialect {
public:
  explicit TestDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context, TypeID::get<TestDialect>()) {
    addOperations<ActionOp, ReadOnlyOp>();
    allowUnknownOperations();
  }
  static StringRef getDialectNamespace() { return "scope"; }
};
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<TestDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // The test-only effectful operation deliberately bypasses closed profile
  // admission. This directly exercises the rewrite driver's fold worklist.
  auto module = parseSourceString<ModuleOp>(R"mlir(module {
    "scope.body"() ({ ^entry(%a: i1):
      %same = arith.cmpi eq, %a, %a : i1
      %first = "scope.action"(%same) : (i1) -> i1
      %second = "scope.action"(%same) : (i1) -> i1
      "scope.sink"(%first, %second) : (i1, i1) -> ()
    }) : () -> ()
  })mlir",
                                            &context);
  test::require(bool(module), "scope fixture refused");
  auto *body = &module->getBody()->front();
  test::require(succeeded(mathematical::simplifyCalculations(body)),
                "scoped simplification failed");
  test::require(folds == 0, "non-total fold hook ran");
  unsigned actions = 0;
  bool compare = false, constant = false;
  body->walk([&](Operation *op) {
    actions += isa<ActionOp>(op);
    compare |= op->getName().getStringRef() == "arith.cmpi";
    constant |= op->getName().getStringRef() == "arith.constant";
  });
  test::require(actions == 2 && !compare && constant,
                "action survival or total folding changed");
  auto readonly = parseSourceString<ModuleOp>(R"mlir(module {
    "scope.body"() ({ ^entry(%a: i1):
      %read = "scope.read"(%a) : (i1) -> i1
      "scope.sink"(%read) : (i1) -> ()
    }) : () -> ()
  })mlir",
                                              &context);
  test::require(bool(readonly), "read-only fixture refused");
  ScopedDiagnosticHandler expected(&context,
                                   [](Diagnostic &) { return success(); });
  test::require(
      failed(mathematical::simplifyCalculations(&readonly->getBody()->front())),
      "a read-only declaration granted action optimization permission");
}
