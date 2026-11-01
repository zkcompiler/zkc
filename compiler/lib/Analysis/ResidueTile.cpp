#include "zkc/Analysis/ResidueTile.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/UB/IR/UBOps.h"
#include "mlir/Dialect/Vector/IR/VectorOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ResidueArithmetic.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/MathExtras.h"

using namespace mlir;
namespace zkc::residue {
namespace {
constexpr unsigned maximumInstructions = 4096;
bool attrs(Operation *op, ArrayRef<StringRef> names) {
  return llvm::all_of(op->getAttrs(), [&](NamedAttribute attr) {
    return llvm::is_contained(names, attr.getName().getValue());
  });
}
func::FuncOp function(ModuleOp module) {
  if (!module || !module.getBodyRegion().hasOneBlock() ||
      !llvm::hasSingleElement(*module.getBody()) || !module->getAttrs().empty())
    return {};
  auto function = dyn_cast<func::FuncOp>(module.getBody()->front());
  if (!function || !function.getBody().hasOneBlock() ||
      !attrs(function, {"sym_name", "function_type"}) ||
      function.getNumArguments() > 256 || function.getNumResults() != 1)
    return {};
  unsigned count = 0;
  for (Operation &op : function.front())
    if (++count > maximumInstructions || op.getNumRegions() ||
        op.getNumSuccessors() || op.getNumResults() > 1 ||
        op.getNumOperands() > 256)
      return {};
  return function;
}
IntegerType word(Type type) {
  auto value = dyn_cast<IntegerType>(type);
  return value && value.isSignless() && value.getWidth() <= 2 * MaximumWordWidth
             ? value
             : IntegerType{};
}
IntegerType vectorWord(Type type, unsigned lanes) {
  auto vector = dyn_cast<VectorType>(type);
  return vector && !vector.isScalable() && vector.getRank() == 1 &&
                 vector.getDimSize(0) == lanes
             ? word(vector.getElementType())
             : IntegerType{};
}
IntegerType bufferWord(Type type, unsigned lanes) {
  auto buffer = dyn_cast<MemRefType>(type);
  return buffer && buffer.getRank() == 1 && buffer.getDimSize(0) == lanes &&
                 buffer.getLayout().isIdentity() && !buffer.getMemorySpace()
             ? word(buffer.getElementType())
             : IntegerType{};
}
struct Object {
  MemRefType type;
  Value contents;
  bool owned, live;
  uint64_t bytes;
};

std::optional<Tile> read(ModuleOp source, ArrayRef<bool> rowwise,
                         ModuleOp candidate) {
  auto original = function(source), actual = function(candidate);
  if (!original || !actual || original.getSymName() != actual.getSymName() ||
      original.getNumArguments() != rowwise.size() ||
      actual.getNumArguments() != rowwise.size())
    return {};
  auto residue = dyn_cast<ValueType>(original.getResultTypes()[0]);
  if (!residue || !llvm::all_of(original.getArgumentTypes(),
                                [&](Type type) { return type == residue; }))
    return {};
  auto modulus = residue.getModulus();
  auto modulusWord =
      modulus ? dyn_cast<IntegerType>(modulus.getType()) : IntegerType{};
  if (!modulusWord || !modulusWord.isUnsigned() ||
      modulusWord.getWidth() > MaximumWordWidth || modulus.getValue().ult(2))
    return {};
  auto output = dyn_cast<MemRefType>(actual.getResultTypes()[0]);
  if (!output || output.getRank() != 1 || output.getDimSize(0) < 1 ||
      output.getDimSize(0) > 256)
    return {};
  unsigned lanes = output.getDimSize(0);
  auto element = IntegerType::get(source.getContext(), residue.getWidth());
  if (bufferWord(output, lanes) != element)
    return {};
  for (auto [argument, row] : llvm::zip(actual.getArguments(), rowwise))
    if ((row ? bufferWord(argument.getType(), lanes)
             : word(argument.getType())) != element)
      return {};
  // Bound nesting and all value shapes before generic MLIR verification.
  for (Operation &op : actual.front())
    for (Type type : op.getResultTypes())
      if (!isa<IndexType>(type) && !word(type) && !vectorWord(type, lanes) &&
          !bufferWord(type, lanes))
        return {};
  if (failed(verify(candidate)))
    return {};

  OwningOpRef<ModuleOp> words(ModuleOp::create(candidate.getLoc()));
  OpBuilder builder(words->getBodyRegion());
  SmallVector<Type> inputs(rowwise.size(), element);
  auto scalar =
      func::FuncOp::create(builder, actual.getLoc(), actual.getSymName(),
                           builder.getFunctionType(inputs, {element}));
  auto *body = scalar.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  IRMapping values;
  llvm::DenseSet<Value> zeroIndices, padding;
  llvm::DenseMap<Value, unsigned> owners;
  SmallVector<Object> objects;
  uint64_t liveBytes = 0, peakBytes = 0;
  for (auto [index, row] : llvm::enumerate(rowwise)) {
    Value argument = actual.getArgument(index),
          meaning = body->getArgument(index);
    if (row) {
      owners.try_emplace(argument, objects.size());
      objects.push_back(
          {cast<MemRefType>(argument.getType()), meaning, false, true, 0});
    } else {
      values.map(argument, meaning);
    }
  }
  auto owner = [&](Value value) -> Object * {
    auto found = owners.find(value);
    return found != owners.end() && objects[found->second].live
               ? &objects[found->second]
               : nullptr;
  };
  auto access = [&](Value buffer, ValueRange indices, Type vector,
                    AffineMap map, Value mask) -> Object * {
    auto *object = owner(buffer);
    return object && indices.size() == 1 && zeroIndices.contains(indices[0]) &&
                   vectorWord(vector, lanes) == object->type.getElementType() &&
                   map == AffineMap::getMultiDimIdentityMap(
                              1, source.getContext()) &&
                   !mask
               ? object
               : nullptr;
  };
  for (Operation &op : actual.front()) {
    if (auto allocate = dyn_cast<memref::AllocOp>(op)) {
      auto type = allocate.getType();
      auto alignment = allocate.getAlignment();
      if (!attrs(&op, {"alignment", "operandSegmentSizes"}) ||
          allocate.getNumOperands() ||
          (alignment && (!llvm::isPowerOf2_64(*alignment) || *alignment > 64)))
        return {};
      uint64_t bytes = lanes * ((bufferWord(type, lanes).getWidth() + 7) / 8);
      owners.try_emplace(allocate.getResult(), objects.size());
      objects.push_back({type, {}, true, true, bytes});
      liveBytes += bytes;
      peakBytes = std::max(peakBytes, liveBytes);
    } else if (auto cast = dyn_cast<memref::CastOp>(op)) {
      auto *object = owner(cast.getSource());
      if (!object || !op.getAttrs().empty() || object->type != cast.getType())
        return {};
      owners.try_emplace(cast.getResult(), owners.at(cast.getSource()));
    } else if (auto release = dyn_cast<memref::DeallocOp>(op)) {
      auto *object = owner(release.getMemref());
      if (!object || !object->owned || !op.getAttrs().empty())
        return {};
      object->live = false;
      liveBytes -= object->bytes;
    } else if (auto copy = dyn_cast<memref::CopyOp>(op)) {
      auto *from = owner(copy.getSource()), *to = owner(copy.getTarget());
      if (!from || !to || !to->owned || !from->contents ||
          from->type != to->type || !op.getAttrs().empty())
        return {};
      to->contents = from->contents;
    } else if (auto index = dyn_cast<arith::ConstantIndexOp>(op)) {
      if (index.value() != 0 || !attrs(&op, {"value"}))
        return {};
      zeroIndices.insert(index);
    } else if (auto poison = dyn_cast<ub::PoisonOp>(op)) {
      if (!word(poison.getType()) || !attrs(&op, {"value"}) ||
          (poison.getValue() && !isa<ub::PoisonAttr>(poison.getValue())))
        return {};
      padding.insert(poison.getResult());
    } else if (auto load = dyn_cast<vector::TransferReadOp>(op)) {
      auto *object = access(load.getBase(), load.getIndices(), load.getType(),
                            load.getPermutationMap(), load.getMask());
      if (!object || !object->contents ||
          (!padding.contains(load.getPadding()) &&
           !values.contains(load.getPadding())) ||
          !attrs(&op, {"permutation_map", "in_bounds", "operandSegmentSizes"}))
        return {};
      // The actual extent/map/index establishes that no padding lane is read.
      // The producer's in_bounds assertion is deliberately not evidence.
      values.map(load.getResult(), object->contents);
    } else if (auto store = dyn_cast<vector::TransferWriteOp>(op)) {
      auto *object = access(store.getBase(), store.getIndices(),
                            store.getVector().getType(),
                            store.getPermutationMap(), store.getMask());
      auto value = values.lookupOrNull(store.getVector());
      if (!object || !object->owned || !value ||
          !attrs(&op, {"permutation_map", "in_bounds", "operandSegmentSizes"}))
        return {};
      object->contents = value;
    } else if (auto broadcast = dyn_cast<vector::BroadcastOp>(op)) {
      auto value = values.lookupOrNull(broadcast.getSource());
      if (!value || !word(broadcast.getSource().getType()) ||
          !op.getAttrs().empty())
        return {};
      values.map(broadcast.getResult(), value);
    } else if (auto returned = dyn_cast<func::ReturnOp>(op)) {
      if (&op != &actual.front().back() || !op.getAttrs().empty())
        return {};
      auto *object = owner(returned.getOperand(0));
      if (!object || !object->owned || !object->contents ||
          object->type != output)
        return {};
      for (auto &other : objects)
        if (&other != object && other.owned && other.live)
          return {};
      func::ReturnOp::create(builder, returned.getLoc(), object->contents);
      auto decoded = consumeArithmetic(source, *words);
      if (!decoded)
        return {};
      return Tile{std::move(decoded), lanes, peakBytes};
    } else if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      if (!attrs(&op, {"value"}))
        return {};
      auto type = word(constant.getType());
      IntegerAttr literal;
      if (type) {
        literal = dyn_cast<IntegerAttr>(constant.getValue());
      } else {
        type = vectorWord(constant.getType(), lanes);
        auto splat = dyn_cast<DenseIntElementsAttr>(constant.getValue());
        if (type && splat && splat.isSplat())
          literal = IntegerAttr::get(type, splat.getSplatValue<llvm::APInt>());
      }
      if (!literal)
        return {};
      values.map(
          constant.getResult(),
          arith::ConstantOp::create(builder, constant.getLoc(), type, literal));
    } else {
      // Clone only scalarizable word operations. The independent scalar reader
      // subsequently checks every flag, range and operation, including dead
      // code.
      if (!isa<arith::ExtUIOp, arith::TruncIOp, arith::AddIOp, arith::SubIOp,
               arith::MulIOp, arith::RemUIOp, arith::CmpIOp, arith::SelectOp>(
              op) ||
          !llvm::all_of(op.getOperands(), [&](Value operand) {
            return values.contains(operand);
          }))
        return {};
      auto type = word(op.getResult(0).getType());
      if (!type)
        type = vectorWord(op.getResult(0).getType(), lanes);
      auto *copy = builder.clone(op, values);
      copy->getResult(0).setType(type);
    }
  }
  return {};
}
} // namespace
std::optional<Tile> readTile(ModuleOp source, ArrayRef<bool> rowwise,
                             ModuleOp candidate) {
  auto result = read(source, rowwise, candidate);
  if (!result && candidate)
    diagnostics::emit(
        candidate.emitError(), "represented-tile",
        "private tile lacks checked value, extent or ownership semantics");
  return result;
}
} // namespace zkc::residue
