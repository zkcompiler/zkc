#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/ScopeExit.h"
#include <map>

using namespace mlir;
namespace zkc::poly {
namespace {
// Prefix substitution is a ring homomorphism. Keep multiplication symbolic;
// only multilinear leaves materialize a smaller table. The memo preserves
// repeated factors across fixes in this block, with SSA values as keys.
class FactorFixing {
  OpBuilder builder;
  Operation *anchor = nullptr;
  unsigned depth = 0, remaining = 10000;
  using Key = std::pair<void *, std::vector<void *>>;
  std::map<Key, Value> fixed;

  Value make(StringRef name, Type type, ValueRange inputs) {
    if (!remaining || llvm::any_of(inputs, [](Value value) { return !value; }))
      return {};
    --remaining;
    OperationState state(anchor->getLoc(), name);
    state.addOperands(inputs);
    state.addTypes(type);
    return builder.create(state)->getResult(0);
  }
  Value fix(Value input, ValueRange prefix) {
    if (prefix.empty())
      return input;
    if (!remaining || depth == 128)
      return {};
    --remaining;
    ++depth;
    auto restore = llvm::scope_exit([&] { --depth; });
    Key key{input.getAsOpaquePointer(), {}};
    for (auto point : prefix)
      key.second.push_back(point.getAsOpaquePointer());
    if (auto found = fixed.find(key); found != fixed.end())
      return found->second;
    auto original = cast<PolynomialType>(input.getType());
    auto type = PolynomialType::get(builder.getContext(), original.getDomain(),
                                    original.getArity() - prefix.size());
    auto *op = input.getDefiningOp();
    Value result;
    if (isa_and_nonnull<AddPolynomialOp, MultiplyPolynomialOp>(op)) {
      auto left = fix(op->getOperand(0), prefix);
      auto right = fix(op->getOperand(1), prefix);
      result =
          make(op->getName().getStringRef(), type, ValueRange{left, right});
    } else if (auto table = dyn_cast_if_present<MultilinearPolynomialOp>(op)) {
      auto field =
          algebra::FieldType::get(builder.getContext(), type.getDomain());
      auto data = RankedTensorType::get(
          {int64_t(uint64_t(1) << type.getArity())}, field);
      SmallVector<Value> inputs{table.getTable()};
      llvm::append_range(inputs, prefix);
      auto smaller = make(FixTableOp::getOperationName(), data, inputs);
      if (smaller)
        result =
            make(MultilinearPolynomialOp::getOperationName(), type, smaller);
    } else if (auto constant = dyn_cast_if_present<ConstantPolynomialOp>(op)) {
      result = make(ConstantPolynomialOp::getOperationName(), type,
                    constant.getScalar());
    } else if (auto nested = dyn_cast_if_present<FixPolynomialOp>(op)) {
      SmallVector<Value> combined(nested.getPrefix());
      llvm::append_range(combined, prefix);
      result = fix(nested.getInput(), combined);
    } else {
      SmallVector<Value> inputs{input};
      llvm::append_range(inputs, prefix);
      result = make(FixPolynomialOp::getOperationName(), type, inputs);
    }
    if (result)
      fixed.emplace(std::move(key), result);
    return result;
  }

public:
  explicit FactorFixing(MLIRContext *context) : builder(context) {}
  LogicalResult run(Block &body) {
    for (auto &op : body)
      for (auto &region : op.getRegions())
        for (auto &nested : region)
          if (failed(FactorFixing(builder.getContext()).run(nested)))
            return failure();
    Degrees degrees;
    if (failed(deriveDegrees(body, degrees)))
      return failure();
    eraseUnusedPolynomials(body, degrees);
    SmallVector<FixPolynomialOp> observations;
    for (auto op : body.getOps<FixPolynomialOp>())
      observations.push_back(op);
    for (auto op : observations) {
      anchor = op;
      builder.setInsertionPoint(op);
      auto result = fix(op.getInput(), op.getPrefix());
      if (!result)
        return diagnostics::emit(op.emitOpError(), "polynomial-fixing-limit",
                                 "exceeded 10000 work units or depth 128");
      op.getPolynomial().replaceAllUsesWith(result);
    }
    // Keep original nodes alive while their SSA identities are memo keys.
    for (auto op : llvm::reverse(observations))
      op.erase();
    return success();
  }
};
struct FixPolynomialFactorsPass
    : PassWrapper<FixPolynomialFactorsPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(FixPolynomialFactorsPass)
  StringRef getArgument() const final { return "zkc-fix-polynomial-factors"; }
  StringRef getDescription() const final {
    return "Fix ordered prefixes through shared polynomial factors and MLE "
           "tables";
  }
  void runOnOperation() final {
    auto source = getOperation();
    if (failed(verify(source)) || !llvm::hasSingleElement(*source.getBody()))
      return signalPassFailure();
    auto original =
        dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    if (!original ||
        original.getProfile() != protocol_ir::Profile::Participant) {
      diagnostics::emit(source.emitError(), "polynomial-fixing-profile",
                        "expected participant mathematics");
      return signalPassFailure();
    }
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    for (auto participant :
         unit.getBody().front().getOps<protocol_ir::ParticipantOp>())
      if (failed(
              FactorFixing(&getContext()).run(participant.getBody().front())))
        return signalPassFailure();
    if (failed(verify(*candidate)) ||
        failed(mathematical::verifyProjectionPreserved(source, *candidate)))
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
} // namespace
} // namespace zkc::poly
std::unique_ptr<mlir::Pass> zkc::protocol::createFixPolynomialFactorsPass() {
  return std::make_unique<poly::FixPolynomialFactorsPass>();
}
