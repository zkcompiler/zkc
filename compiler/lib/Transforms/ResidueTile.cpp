#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Arith/Transforms/BufferizableOpInterfaceImpl.h"
#include "mlir/Dialect/Bufferization/IR/Bufferization.h"
#include "mlir/Dialect/Bufferization/Transforms/FuncBufferizableOpInterfaceImpl.h"
#include "mlir/Dialect/Bufferization/Transforms/OneShotModuleBufferize.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Linalg/Transforms/BufferizableOpInterfaceImpl.h"
#include "mlir/Dialect/Linalg/Transforms/Transforms.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/Dialect/Tensor/Transforms/BufferizableOpInterfaceImpl.h"
#include "mlir/Dialect/UB/IR/UBOps.h"
#include "mlir/Dialect/Vector/IR/VectorOps.h"
#include "mlir/Dialect/Vector/Transforms/BufferizableOpInterfaceImpl.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "zkc/Analysis/ResidueArithmetic.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "zkc/Transforms/Residue.h"

using namespace mlir;
namespace zkc::residue {
void registerTileDialects(DialectRegistry &registry) {
  registry.insert<ResidueDialect, arith::ArithDialect, func::FuncDialect,
                  linalg::LinalgDialect, tensor::TensorDialect,
                  vector::VectorDialect, memref::MemRefDialect,
                  bufferization::BufferizationDialect, ub::UBDialect>();
  arith::registerBufferizableOpInterfaceExternalModels(registry);
  linalg::registerBufferizableOpInterfaceExternalModels(registry);
  tensor::registerBufferizableOpInterfaceExternalModels(registry);
  vector::registerBufferizableOpInterfaceExternalModels(registry);
  bufferization::func_ext::registerBufferizableOpInterfaceExternalModels(
      registry);
}
void initializeTileDialects(MLIRContext &context) {
  DialectRegistry dependencies;
  registerTileDialects(dependencies);
  auto names = dependencies.getRegisteredDialectNames();
  if (dependencies.isSubsetOf(context.getDialectRegistry()) &&
      llvm::all_of(names, [&](StringRef name) {
        return context.getLoadedDialect(name) != nullptr;
      }))
    return;
  context.appendDialectRegistry(dependencies);
  for (StringRef name : names)
    context.getOrLoadDialect(name);
}
OwningOpRef<ModuleOp> proposeTile(ModuleOp source, ArrayRef<bool> rowwise,
                                  unsigned lanes) {
  if (!source || !lanes || lanes > 256)
    return {};
  auto *context = source.getContext();
  initializeTileDialects(*context);
  auto words = lowerArithmetic(source);
  if (!words || !consumeArithmetic(source, *words))
    return {};
  auto scalar = *words->getOps<func::FuncOp>().begin();
  if (scalar.getNumArguments() != rowwise.size())
    return {};
  auto element = scalar.getResultTypes()[0];
  auto tile = RankedTensorType::get({lanes}, element);
  auto loc = source.getLoc();
  OwningOpRef<ModuleOp> candidate(ModuleOp::create(loc));
  OpBuilder builder(candidate->getBodyRegion());
  SmallVector<Type> inputs;
  SmallVector<AffineMap> maps;
  auto identity = AffineMap::getMultiDimIdentityMap(1, context);
  auto broadcast = AffineMap::get(1, 0, {}, context);
  for (bool row : rowwise) {
    inputs.push_back(row ? Type(tile) : element);
    maps.push_back(row ? identity : broadcast);
  }
  maps.push_back(identity);
  auto function = func::FuncOp::create(builder, loc, scalar.getSymName(),
                                       builder.getFunctionType(inputs, {tile}));
  auto *body = function.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  auto empty = tensor::EmptyOp::create(builder, loc, tile.getShape(), element);
  auto generic = linalg::GenericOp::create(
      builder, loc, TypeRange{tile}, body->getArguments(), ValueRange{empty},
      maps, ArrayRef<utils::IteratorType>{utils::IteratorType::parallel},
      [&](OpBuilder &nested, Location location, ValueRange args) {
        IRMapping mapping;
        mapping.map(scalar.getArguments(), args.drop_back());
        for (Operation &op : scalar.front().without_terminator())
          nested.clone(op, mapping);
        linalg::YieldOp::create(
            nested, location,
            mapping.lookup(scalar.front().back().getOperand(0)));
      });
  func::ReturnOp::create(builder, loc, generic.getResult(0));
  if (failed(verify(*candidate)))
    return {};
  IRRewriter rewriter(context);
  rewriter.setInsertionPoint(generic);
  auto vectorized = linalg::vectorize(rewriter, generic);
  if (failed(vectorized))
    return {};
  rewriter.replaceOp(generic, vectorized->replacements);
  bufferization::OneShotBufferizationOptions options;
  options.bufferizeFunctionBoundaries = true;
  options.setFunctionBoundaryTypeConversion(
      bufferization::LayoutMapOption::IdentityLayoutMap);
  bufferization::BufferizationState state;
  if (failed(
          bufferization::runOneShotModuleBufferize(*candidate, options, state)))
    return {};
  bufferization::removeBufferizationAttributesInModule(*candidate);
  PassManager cleanup(context);
  cleanup.addPass(createCSEPass());
  if (failed(cleanup.run(*candidate)) || failed(verify(*candidate)))
    return {};
  return candidate;
}
} // namespace zkc::residue
