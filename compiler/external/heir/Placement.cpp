#include "Admission.h"
#include "lib/Dialect/ModArith/IR/ModArithAttributes.h"
#include "lib/Dialect/Polynomial/IR/PolynomialOps.h"
#include "lib/Dialect/Polynomial/Transforms/Passes.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include <optional>

namespace zkc::heir {
namespace {
// Root selection belongs to the admitted coordinate boundary. For a qualified
// prime and power-of-two degree, r^n = -1 establishes exact order 2n. Testing
// a^((q-1)/(2n)) avoids factoring q-1 or searching for a full field generator.
// This is a bounded proposal: failure to find a root does not reject the ring.
std::optional<uint64_t> selectRoot(const ArithmeticMeaning &meaning,
                                   uint64_t &remaining) {
  for (uint64_t candidate = 2; candidate < meaning.modulus && candidate < 258;
       ++candidate) {
    if (remaining < 128) {
      remaining = 0;
      return std::nullopt;
    }
    remaining -= 128;
    auto root =
        modularPower(candidate, (meaning.modulus - 1) / (2 * meaning.degree),
                     meaning.modulus);
    if (modularPower(root, meaning.degree, meaning.modulus) ==
        meaning.modulus - 1)
      return root;
  }
  return std::nullopt;
}
} // namespace
mlir::FailureOr<mlir::OwningOpRef<mlir::ModuleOp>>
placeTransforms(mlir::ModuleOp source, PlacementStatus *status,
                uint64_t *allowance) {
  namespace poly = mlir::heir::polynomial;
  namespace modular = mlir::heir::mod_arith;
  uint64_t standalone = 1000000;
  auto &remaining = allowance ? *allowance : standalone;
  if (status)
    *status = PlacementStatus::Unsupported;
  bool exhausted = false;
  auto meaning = readArithmetic(source, remaining, &exhausted);
  if (mlir::failed(meaning)) {
    if (status && exhausted)
      *status = PlacementStatus::Unavailable;
    return mlir::failure();
  }
  if (status)
    *status = PlacementStatus::Unavailable;
  auto root = selectRoot(*meaning, remaining);
  if (!root || remaining < 64)
    return mlir::failure();
  remaining -= 64;
  auto inverse = modularPower(*root, meaning->modulus - 2, meaning->modulus);
  mlir::OwningOpRef<mlir::ModuleOp> candidate(source.clone());
  mlir::PassManager placement(source.getContext());
  placement.addNestedPass<mlir::func::FuncOp>(poly::createPolyMulToNTT());
  if (mlir::failed(placement.run(*candidate)))
    return mlir::failure();
  mlir::OpBuilder builder(source.getContext());
  bool typed = true;
  candidate->walk([&](mlir::Operation *op) {
    if (!mlir::isa<poly::NTTOp, poly::INTTOp>(op) || op->hasAttr("root"))
      return;
    auto type =
        mlir::dyn_cast<poly::PolynomialType>(op->getResult(0).getType());
    auto scalar = type ? mlir::dyn_cast<modular::ModArithType>(
                             type.getRing().getCoefficientType())
                       : modular::ModArithType{};
    if (!scalar) {
      typed = false;
      return;
    }
    auto value = modular::ModArithAttr::get(
        source.getContext(), scalar,
        builder.getI32IntegerAttr(mlir::isa<poly::NTTOp>(op) ? *root
                                                             : inverse));
    op->setAttr("root", poly::PrimitiveRootAttr::get(
                            source.getContext(), value,
                            builder.getI64IntegerAttr(2 * meaning->degree)));
  });
  if (!typed) {
    if (status)
      *status = PlacementStatus::Mismatch;
    return mlir::failure();
  }
  mlir::PassManager cleanup(source.getContext());
  cleanup.addPass(mlir::createCanonicalizerPass());
  cleanup.addPass(mlir::createCSEPass());
  if (mlir::failed(cleanup.run(*candidate)))
    return mlir::failure();
  if (status)
    *status = PlacementStatus::Mismatch;
  if (mlir::failed(
          compareArithmetic(source, *candidate, &remaining, &exhausted))) {
    if (status && exhausted)
      *status = PlacementStatus::Unavailable;
    return mlir::failure();
  }
  if (status)
    *status = PlacementStatus::Verified;
  return candidate;
}
} // namespace zkc::heir
