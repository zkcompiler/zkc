#include "zkc/Dialect/Evm/Evm.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Target/Evm/Layout.h"
#include "zkc/Target/Evm/Transcript.h"
#include "zkc/Target/Evm/Wire.h"

using namespace mlir;
namespace zkc::evm {
EvmDialect::EvmDialect(MLIRContext *context)
    : Dialect(getDialectNamespace(), context, TypeID::get<EvmDialect>()) {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Evm/Ops.cpp.inc"
      >();
}
namespace {
// Shared layout checking does not choose an operation or its behavior. Each
// ODS operation below supplies its own named signature and semantic premises.
struct LayoutCheck {
  Operation *op;
  NativeLayouts layouts;
  Type type;
  const ValueLayout *layout = nullptr;
  Type i1, i64, i256;
  explicit LayoutCheck(Operation *op)
      : op(op), layouts(*op->getContext()),
        i1(IntegerType::get(op->getContext(), 1)),
        i64(IntegerType::get(op->getContext(), 64)),
        i256(IntegerType::get(op->getContext(), 256)) {}
  LogicalResult load() {
    auto attr = op->getAttrOfType<TypeAttr>("value_type");
    if (!attr)
      return op->emitOpError(
          "[evm.value-type] requires exact native value_type");
    type = attr.getValue();
    auto found = layouts.get(type);
    if (!found) {
      llvm::consumeError(found.takeError());
      return op->emitOpError(
          "[evm.value-type] unsupported complete native layout");
    }
    layout = *found;
    return success();
  }
  LogicalResult signature(TypeRange inputs, TypeRange outputs) {
    if (!llvm::equal(inputs, op->getOperandTypes()) ||
        !llvm::equal(outputs, op->getResultTypes()))
      return op->emitOpError("[evm.signature] incorrect exact layout lanes");
    return success();
  }
  LogicalResult field() {
    if (!isa<algebra::FieldType>(type))
      return op->emitOpError("[evm.value-type] field requires FieldType");
    return success();
  }
  LogicalResult collection(CollectionLayout::Storage storage) {
    if (!layout->collection || layout->collection->storage != storage)
      return op->emitOpError("[evm.value-type] incorrect collection family");
    return success();
  }
  FailureOr<SmallVector<Type>> element() {
    if (layout->kind == ValueLayout::Kind::Bytes)
      return SmallVector<Type>{i64};
    auto child = layouts.get(layout->collection->element);
    if (!child) {
      llvm::consumeError(child.takeError());
      return failure();
    }
    return llvm::to_vector((*child)->lanes);
  }
  bool literal(Attribute value) {
    auto literal = dyn_cast_or_null<algebra::FieldLiteralAttr>(value);
    auto field = dyn_cast<algebra::FieldType>(type);
    return literal && literal.getField() == field &&
           succeeded(algebra::FieldLiteralAttr::verify(
               [&] { return op->emitOpError(); }, field, literal.getValue()));
  }
};
template <typename Op> LogicalResult attributes(Op op) {
  for (auto attr : op->getAttrs())
    if (!llvm::is_contained(Op::getAttributeNames(), attr.getName().strref()))
      return op.emitOpError("[evm.attributes] unexpected attribute: ")
             << attr.getName();
  return success();
}
LogicalResult origin(Operation *op, bool observation,
                     llvm::StringRef method = "draw") {
  auto attr = op->getAttrOfType<runtime::NativeOriginAttr>("origin");
  auto value = runtime::exportNativeOrigin(attr);
  if (!value) {
    llvm::consumeError(value.takeError());
    return op->emitOpError("[evm.origin] invalid shared source occurrence");
  }
  if (llvm::any_of(value->path, [](const auto &step) {
        return step.kind == protocol::NativeOriginStep::Kind::Branch;
      }))
    return op->emitOpError(
        "[evm.origin] unsupported selected-control transcript origin");
  if (observation) {
    if (!std::holds_alternative<protocol::NativeMessageOrigin>(value->event))
      return op->emitOpError(
          "[evm.origin] observation requires message occurrence");
  } else {
    auto *query = std::get_if<protocol::NativeQueryOrigin>(&value->event);
    if (!query || query->method != method)
      return op->emitOpError(
          "[evm.origin] transcript query method differs from operation");
  }
  return success();
}
LogicalResult indexSuite(Operation *op, bool block) {
  auto suite = op->getAttrOfType<StringAttr>("suite");
  if (!suite)
    return op->emitOpError("[evm.construction] requires transcript suite");
  NativeLayouts layouts(*op->getContext());
  auto realized =
      realizeTranscript(layouts, *op->getContext(), suite.getValue());
  if (!realized) {
    llvm::consumeError(realized.takeError());
    return op->emitOpError("[evm.construction] unsupported transcript suite");
  }
  if (block ? !realized->indexBlock : !realized->index)
    return op->emitOpError("[evm.construction] suite lacks index capability");
  return origin(op, false, block ? "indices" : "index");
}
LogicalResult indexBlock(Operation *op, bool gated) {
  if (failed(indexSuite(op, true)))
    return failure();
  auto bound = op->getAttrOfType<IntegerAttr>("bound").getUInt();
  auto count = op->getAttrOfType<IntegerAttr>("count").getUInt();
  if (!bound || bound > (uint64_t(1) << 63) || (bound & (bound - 1)) ||
      !count || count > 1048576 ||
      (gated && op->getAttrOfType<IntegerAttr>("difficulty").getUInt() > 64))
    return op->emitOpError("[evm.construction] invalid native index block");
  return success();
}
LogicalResult wire(LayoutCheck &check) {
  if (auto error = verifyWireType(check.layouts, check.type)) {
    llvm::consumeError(std::move(error));
    return check.op->emitOpError(
        "[evm.wire-type] complete message permission and codec required");
  }
  return success();
}
LogicalResult stop(Operation *op) {
  if (auto site = op->getAttr("site");
      site &&
      (!isa<StringAttr>(site) || cast<StringAttr>(site).getValue().empty()))
    return op->emitOpError("[evm.site] requires nonempty source stop site");
  return success();
}
} // namespace
LogicalResult FieldConstantOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  if (!c.literal(getValueAttr()))
    return emitOpError("[evm.literal] requires exact canonical field literal");
  return c.signature({}, c.layout->lanes);
}
LogicalResult FieldAddOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  SmallVector<Type> inputs(c.layout->lanes.begin(), c.layout->lanes.end());
  llvm::append_range(inputs, c.layout->lanes);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult FieldSubOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  SmallVector<Type> inputs(c.layout->lanes.begin(), c.layout->lanes.end());
  llvm::append_range(inputs, c.layout->lanes);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult FieldMulOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  SmallVector<Type> inputs(c.layout->lanes.begin(), c.layout->lanes.end());
  llvm::append_range(inputs, c.layout->lanes);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult FieldNegOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  return c.signature(c.layout->lanes, c.layout->lanes);
}
LogicalResult FieldEqualOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  SmallVector<Type> inputs(c.layout->lanes.begin(), c.layout->lanes.end());
  llvm::append_range(inputs, c.layout->lanes);
  return c.signature(inputs, TypeRange(c.i1));
}
LogicalResult FieldFromIndexOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  return c.signature({c.i64}, c.layout->lanes);
}
LogicalResult FieldEmbedOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  auto facts = c.layouts.field(cast<algebra::FieldType>(c.type));
  if (!facts) {
    llvm::consumeError(facts.takeError());
    return failure();
  }
  if ((*facts)->degree <= 1)
    return emitOpError("[evm.value-type] embedding requires extension field");
  return c.signature({c.i256}, c.layout->lanes);
}
LogicalResult FieldInverseOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.field()))
    return failure();
  return c.signature(c.layout->lanes, c.layout->lanes);
}
LogicalResult VectorConstantOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  auto scalar = dyn_cast<algebra::FieldType>(c.layout->collection->element);
  if (!scalar)
    return emitOpError("[evm.value-type] requires field elements");
  auto values = getValues();
  auto saved = c.type;
  c.type = scalar;
  if (!llvm::all_of(values, [&](Attribute value) { return c.literal(value); }))
    return emitOpError("[evm.literal] requires exact collection literals");
  c.type = saved;
  uint64_t count = values.size();
  if (auto array = dyn_cast<data::FieldArrayType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  if (auto array = dyn_cast<data::FixedVectorType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  return c.signature({}, c.layout->lanes);
}
LogicalResult VectorEmptyOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  uint64_t count = 0;
  if (auto array = dyn_cast<data::FieldArrayType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  if (auto array = dyn_cast<data::FixedVectorType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  return c.signature({}, c.layout->lanes);
}
LogicalResult VectorLengthOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  return c.signature(c.layout->lanes, {c.i64});
}
LogicalResult VectorAppendOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  if (isa<data::FieldArrayType, data::FixedVectorType>(c.type))
    return emitOpError("[evm.signature] cannot append fixed collection");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult VectorSplitOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  if (c.layout->kind != ValueLayout::Kind::FieldVector)
    return emitOpError("[evm.value-type] split requires field vector");
  return c.signature(c.layout->lanes, {c.i64, c.i64, c.i64, c.i64});
}
LogicalResult VectorSumOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  return c.signature(c.layout->lanes, *element);
}
LogicalResult VectorAllocOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  return c.signature({c.i64}, {c.i64});
}
LogicalResult VectorGetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  return c.signature({c.i64, c.i64, c.i64}, *element);
}
LogicalResult VectorSetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  inputs.push_back(c.i64);
  auto allocation = getData().getDefiningOp<VectorAllocOp>();
  if (!allocation || allocation.getValueType() != c.type ||
      allocation.getCapacity() != getCount())
    return emitOpError("[evm.construction] stores require exact fresh "
                       "construction buffer and count");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, {});
}
LogicalResult VectorEqualOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::FieldCoefficients)))
    return failure();
  return c.signature({c.i64, c.i64, c.i64, c.i64}, {c.i1});
}
LogicalResult SequenceEmptyOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  uint64_t count = 0;
  if (auto array = dyn_cast<data::FieldArrayType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  if (auto array = dyn_cast<data::FixedVectorType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  return c.signature({}, c.layout->lanes);
}
LogicalResult SequenceAppendOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  if (isa<data::FieldArrayType, data::FixedVectorType>(c.type))
    return emitOpError("[evm.signature] cannot append fixed collection");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult SequenceLengthOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  return c.signature(c.layout->lanes, {c.i64});
}
LogicalResult SequenceGetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  return c.signature({c.i64, c.i64, c.i64}, *element);
}
LogicalResult SequenceAllocOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  return c.signature({c.i64}, {c.i64});
}
LogicalResult SequenceSetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  inputs.push_back(c.i64);
  auto allocation = getData().getDefiningOp<SequenceAllocOp>();
  if (!allocation || allocation.getValueType() != c.type ||
      allocation.getCapacity() != getCount())
    return emitOpError("[evm.construction] stores require exact fresh "
                       "construction buffer and count");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, {});
}
LogicalResult BytesEmptyOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::PackedBytes)))
    return failure();
  uint64_t count = 0;
  if (auto array = dyn_cast<data::FieldArrayType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  if (auto array = dyn_cast<data::FixedVectorType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  return c.signature({}, c.layout->lanes);
}
LogicalResult BytesLengthOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::PackedBytes)))
    return failure();
  return c.signature(c.layout->lanes, {c.i64});
}
LogicalResult BytesGetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::PackedBytes)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  return c.signature({c.i64, c.i64, c.i64}, *element);
}
LogicalResult BytesAppendOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::PackedBytes)))
    return failure();
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  if (isa<data::FieldArrayType, data::FixedVectorType>(c.type))
    return emitOpError("[evm.signature] cannot append fixed collection");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult IndicesEmptyOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  if (c.layout->kind != ValueLayout::Kind::Indices)
    return emitOpError("[evm.value-type] requires indices");
  uint64_t count = 0;
  if (auto array = dyn_cast<data::FieldArrayType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  if (auto array = dyn_cast<data::FixedVectorType>(c.type);
      array && array.getLength() != count)
    return emitOpError("[evm.signature] incorrect fixed collection length");
  return c.signature({}, c.layout->lanes);
}
LogicalResult IndicesAppendOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(c.collection(CollectionLayout::Storage::LaneCells)))
    return failure();
  if (c.layout->kind != ValueLayout::Kind::Indices)
    return emitOpError("[evm.value-type] requires indices");
  auto element = c.element();
  if (failed(element))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  if (isa<data::FieldArrayType, data::FixedVectorType>(c.type))
    return emitOpError("[evm.signature] cannot append fixed collection");
  llvm::append_range(inputs, *element);
  return c.signature(inputs, TypeRange(c.layout->lanes));
}
LogicalResult VariantMakeOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  auto variant = dyn_cast<data::VariantType>(c.type);
  if (!variant)
    return emitOpError("[evm.value-type] requires complete VariantType");
  uint64_t alternative = getAlternativeAttr().getUInt();
  if (alternative >= variant.getAlternatives().size())
    return emitOpError("[evm.alternative] invalid alternative index");
  auto payload = c.layouts.payload(variant, alternative);
  if (!payload) {
    llvm::consumeError(payload.takeError());
    return failure();
  }
  return c.signature(payload->lanes, {c.i64});
}
LogicalResult VariantTagOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  auto variant = dyn_cast<data::VariantType>(c.type);
  if (!variant)
    return emitOpError("[evm.value-type] requires complete VariantType");
  return c.signature({c.i64}, {c.i64});
}
LogicalResult VariantGetOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  auto variant = dyn_cast<data::VariantType>(c.type);
  if (!variant)
    return emitOpError("[evm.value-type] requires complete VariantType");
  uint64_t alternative = getAlternativeAttr().getUInt();
  if (alternative >= variant.getAlternatives().size())
    return emitOpError("[evm.alternative] invalid alternative index");
  auto payload = variant.getAlternatives()[alternative].getPayload();
  auto index = getPayloadAttr().getUInt();
  if (index >= payload.size())
    return emitOpError("[evm.payload] invalid payload index");
  auto child = c.layouts.get(payload[index]);
  if (!child) {
    llvm::consumeError(child.takeError());
    return failure();
  }
  return c.signature({c.i64}, (*child)->lanes);
}
LogicalResult ProofReceiveOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(wire(c)))
    return failure();
  return c.signature({}, c.layout->lanes);
}
LogicalResult TranscriptObserveOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(origin(*this, true)))
    return failure();
  if (failed(wire(c)))
    return failure();
  SmallVector<Type> inputs{c.i64, c.i64};
  llvm::append_range(inputs, c.layout->lanes);
  inputs.append({c.i64, c.i64});
  return c.signature(inputs, {c.i64});
}
LogicalResult TranscriptChallengeOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  LayoutCheck c(*this);
  if (failed(c.load()))
    return failure();
  if (failed(origin(*this, false)))
    return failure();
  auto scalar = dyn_cast<algebra::FieldType>(c.type);
  if (!scalar ||
      !realizedChallengeField(c.layouts, *getContext(), scalar.getDomain()))
    return emitOpError("[evm.value-type] requires realized challenge field");
  SmallVector<Type> outputs(c.layout->lanes.begin(), c.layout->lanes.end());
  outputs.push_back(c.i64);
  return c.signature({c.i64, c.i64, c.i64, c.i64}, outputs);
}
LogicalResult TranscriptIndexOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  return indexSuite(*this, false);
}
LogicalResult TranscriptIndicesOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  return indexBlock(*this, false);
}
LogicalResult TranscriptIndicesGatedOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  return indexBlock(*this, true);
}
LogicalResult SourceStopOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  return stop(*this);
}
LogicalResult SourceGuardOp::verify() {
  if (failed(attributes(*this)))
    return failure();
  return stop(*this);
}
LogicalResult IndexAddOp::verify() { return attributes(*this); }
LogicalResult IndexSubOp::verify() { return attributes(*this); }
LogicalResult IndexMulOp::verify() { return attributes(*this); }
LogicalResult IndexDivOp::verify() { return attributes(*this); }
LogicalResult IndexModOp::verify() { return attributes(*this); }
LogicalResult IndexPowerOfTwoOp::verify() { return attributes(*this); }
LogicalResult IndexLogicalShiftRightOp::verify() { return attributes(*this); }
LogicalResult ScopeCurrentOp::verify() { return attributes(*this); }
LogicalResult ScopeEnterOp::verify() { return attributes(*this); }
LogicalResult ScopeExitOp::verify() { return attributes(*this); }
LogicalResult ScopeCheckOp::verify() { return attributes(*this); }
LogicalResult TransferMakeOp::verify() { return attributes(*this); }
LogicalResult TransferAcceptOp::verify() { return attributes(*this); }
LogicalResult TransferReleaseOp::verify() { return attributes(*this); }
LogicalResult TransferCheckOp::verify() { return attributes(*this); }
LogicalResult LoopBoundOp::verify() { return attributes(*this); }
LogicalResult RangeCheckOp::verify() { return attributes(*this); }
LogicalResult RangeAdmitOp::verify() { return attributes(*this); }
} // namespace zkc::evm

#define GET_OP_CLASSES
#include "zkc/Dialect/Evm/Ops.cpp.inc"
