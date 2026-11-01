#include "zkc/Dialect/Evm/Evm.h"
#include "mlir/IR/Builders.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Target/Evm/Layout.h"
#include "zkc/Target/Evm/Wire.h"
#include "llvm/ADT/StringSwitch.h"

using namespace mlir;
namespace zkc::evm {
EvmDialect::EvmDialect(MLIRContext *context)
    : Dialect(getDialectNamespace(), context, TypeID::get<EvmDialect>()) {
  addOperations<WordOp, CheckedOp>();
}
ArrayRef<StringRef> WordOp::getAttributeNames() {
  static StringRef names[] = {"opcode"};
  return names;
}
void WordOp::build(OpBuilder &b, OperationState &s, StringRef opcode, Value a,
                   Value c, Value modulus) {
  s.addOperands({a, c, modulus});
  s.addTypes(b.getIntegerType(256));
  s.addAttribute("opcode", b.getStringAttr(opcode));
}
StringRef WordOp::opcode() {
  auto attr = (*this)->getAttrOfType<StringAttr>("opcode");
  return attr ? attr.getValue() : StringRef();
}
WordOp WordOp::create(OpBuilder &builder, Location loc, StringRef opcode,
                      Value a, Value b, Value p) {
  OperationState state(loc, getOperationName());
  build(builder, state, opcode, a, b, p);
  return cast<WordOp>(builder.create(state));
}
LogicalResult WordOp::verify() {
  if (opcode() != "addmod" && opcode() != "mulmod")
    return emitOpError("[evm.opcode] unsupported word opcode");
  if (!(*this)->getResult(0).getType().isInteger(256) ||
      llvm::any_of(getOperandTypes(), [](Type t) { return !t.isInteger(256); }))
    return emitOpError("[evm.type] word operands/results must be i256");
  return success();
}
ArrayRef<StringRef> CheckedOp::getAttributeNames() {
  static StringRef names[] = {"opcode",      "value_type", "value",  "values",
                              "alternative", "payload",    "origin", "site"};
  return names;
}
void CheckedOp::build(OpBuilder &b, OperationState &s, TypeRange types,
                      StringRef opcode, ValueRange operands,
                      ArrayRef<NamedAttribute> attributes) {
  s.addOperands(operands);
  s.addTypes(types);
  s.addAttributes(attributes);
  s.addAttribute("opcode", b.getStringAttr(opcode));
}
StringRef CheckedOp::opcode() {
  auto attr = (*this)->getAttrOfType<StringAttr>("opcode");
  return attr ? attr.getValue() : StringRef();
}
CheckedOp CheckedOp::create(OpBuilder &builder, Location loc, TypeRange results,
                            StringRef opcode, ValueRange args,
                            ArrayRef<NamedAttribute> attributes) {
  OperationState state(loc, getOperationName());
  build(builder, state, results, opcode, args, attributes);
  return cast<CheckedOp>(builder.create(state));
}
bool isCheckedOpcode(StringRef name) {
  return llvm::StringSwitch<bool>(name)
      .Cases({"index.add", "index.sub", "index.mul", "index.div"}, true)
      .Cases({"index.mod", "index.shl", "index.shr", "index.pow2"}, true)
      .Case("index.power_of_two", true)
      .Cases({"index.wrapping_add", "index.wrapping_sub", "index.bit_and",
              "index.logical_shift_right"},
             true)
      .Cases({"field.constant", "field.add", "field.sub", "field.mul",
              "field.neg", "field.equal", "field.from_index", "field.embed",
              "field.inverse", "field.pow", "field.div"},
             true)
      .Case("vector.constant", true)
      .Cases({"sequence.empty", "sequence.append", "sequence.length",
              "sequence.get", "sequence.alloc", "sequence.set"},
             true)
      .Cases({"variant.make", "variant.tag", "variant.get"}, true)
      .Cases({"bytes.empty", "bytes.length", "bytes.get", "bytes.append"}, true)
      .Cases({"vector.empty", "vector.length", "vector.append"}, true)
      .Cases({"vector.split", "vector.sum", "vector.alloc"}, true)
      .Cases({"vector.get", "vector.set", "vector.equal"}, true)
      .Cases({"indices.empty", "indices.append"}, true)
      .Cases({"scope.root", "scope.enter", "scope.exit", "scope.check"}, true)
      .Case("scope.current", true)
      .Cases({"transfer.make", "transfer.accept", "transfer.release"}, true)
      .Case("transfer.check", true)
      .Cases({"transcript.observe", "transcript.challenge"}, true)
      .Cases({"proof.receive", "source.stop", "loop.bound", "range.check",
              "range.admit"},
             true)
      .Default(false);
}
LogicalResult CheckedOp::verify() {
  StringRef code = opcode();
  if (!isCheckedOpcode(code))
    return emitOpError("[evm.opcode] unsupported checked opcode: ") << code;
  auto valid = [](Type t) {
    auto integer = dyn_cast<IntegerType>(t);
    return integer && integer.isSignless() &&
           llvm::is_contained({1u, 32u, 64u, 256u}, integer.getWidth());
  };
  if (!llvm::all_of(getOperandTypes(), valid) ||
      !llvm::all_of(getResultTypes(), valid))
    return emitOpError(
        "[evm.type] checked operands/results must be EVM integers");
  for (auto attribute : (*this)->getAttrs()) {
    StringRef name = attribute.getName().strref();
    bool allowed =
        name == "opcode" || (name == "site" && code == "source.stop") ||
        (name == "value_type" &&
         (code.starts_with("field.") || code.starts_with("vector.") ||
          code.starts_with("sequence.") || code.starts_with("variant.") ||
          code.starts_with("bytes.") || code.starts_with("indices.") ||
          code == "proof.receive" || code.starts_with("transcript."))) ||
        (name == "value" && code == "field.constant") ||
        (name == "values" && code == "vector.constant") ||
        (name == "alternative" &&
         (code == "variant.make" || code == "variant.get")) ||
        (name == "payload" && code == "variant.get") ||
        (name == "origin" && code.starts_with("transcript."));
    if (!allowed)
      return emitOpError("[evm.attributes] unexpected checked attribute: ")
             << name;
  }
  auto i1 = IntegerType::get(getContext(), 1);
  auto i64 = IntegerType::get(getContext(), 64);
  auto i256 = IntegerType::get(getContext(), 256);
  auto signature = [&](TypeRange inputs, TypeRange outputs) {
    return llvm::equal(inputs, getOperandTypes()) &&
           llvm::equal(outputs, getResultTypes());
  };
  NativeLayouts layouts(*getContext());
  auto type = (*this)->getAttrOfType<TypeAttr>("value_type");
  bool typed = code.starts_with("field.") || code.starts_with("vector.") ||
               code.starts_with("sequence.") || code.starts_with("variant.") ||
               code.starts_with("bytes.") || code.starts_with("indices.") ||
               code == "proof.receive" || code.starts_with("transcript.");
  const ValueLayout *layout = nullptr;
  if (typed) {
    if (!type)
      return emitOpError("[evm.value-type] requires exact native value_type");
    auto result = layouts.get(type.getValue());
    if (!result) {
      llvm::consumeError(result.takeError());
      return emitOpError("[evm.value-type] unsupported complete native layout");
    }
    layout = *result;
  }
  auto literalValid = [&](Attribute attribute, algebra::FieldType expected) {
    auto literal = dyn_cast_or_null<algebra::FieldLiteralAttr>(attribute);
    return literal && literal.getField() == expected &&
           succeeded(algebra::FieldLiteralAttr::verify(
               [&] { return emitOpError(); }, expected, literal.getValue()));
  };
  auto number = [&](StringRef name) -> std::optional<uint32_t> {
    auto value = (*this)->getAttrOfType<IntegerAttr>(name);
    if (!value || !value.getType().isInteger(32))
      return std::nullopt;
    return uint32_t(value.getUInt());
  };
  bool correct = false;
  if (code.starts_with("field.")) {
    auto scalar = dyn_cast<algebra::FieldType>(type.getValue());
    if (!scalar)
      return emitOpError("[evm.value-type] field operation requires FieldType");
    if (code == "field.constant") {
      if (!literalValid((*this)->getAttr("value"), scalar))
        return emitOpError(
            "[evm.literal] requires exact canonical field literal");
      correct = signature({}, layout->lanes);
    } else if (code == "field.from_index")
      correct = signature({i64}, layout->lanes);
    else if (code == "field.embed") {
      auto facts = layouts.field(scalar);
      if (!facts) {
        llvm::consumeError(facts.takeError());
        return failure();
      }
      correct = (*facts)->degree > 1 && signature({i256}, layout->lanes);
    } else if (code == "field.inverse" || code == "field.neg")
      correct = signature(layout->lanes, layout->lanes);
    else {
      SmallVector<Type> inputs(layout->lanes.begin(), layout->lanes.end());
      if (code == "field.pow")
        inputs.push_back(i64);
      else
        llvm::append_range(inputs, layout->lanes);
      correct =
          signature(inputs, code == "field.equal" ? TypeRange(i1)
                                                  : TypeRange(layout->lanes));
    }
  } else if (code.starts_with("vector.") || code.starts_with("sequence.") ||
             code.starts_with("indices.") || code.starts_with("bytes.")) {
    bool coefficients = code.starts_with("vector.");
    bool bytes = code.starts_with("bytes.");
    bool indices = code.starts_with("indices.");
    if (!layout->collection ||
        (coefficients && layout->collection->storage !=
                             CollectionLayout::Storage::FieldCoefficients) ||
        (bytes && layout->kind != ValueLayout::Kind::Bytes) ||
        (indices && layout->kind != ValueLayout::Kind::Indices) ||
        (!coefficients && !bytes && !indices &&
         layout->collection->storage != CollectionLayout::Storage::LaneCells))
      return emitOpError("[evm.value-type] incorrect collection family");
    SmallVector<Type> element{i64};
    if (!bytes) {
      auto child = layouts.get(layout->collection->element);
      if (!child) {
        llvm::consumeError(child.takeError());
        return failure();
      }
      element.assign((*child)->lanes.begin(), (*child)->lanes.end());
    }
    StringRef action = code.split('.').second;
    if (action == "constant") {
      auto values = (*this)->getAttrOfType<ArrayAttr>("values");
      auto scalar = dyn_cast<algebra::FieldType>(layout->collection->element);
      if (!values || !scalar || !llvm::all_of(values, [&](Attribute a) {
            return literalValid(a, scalar);
          }))
        return emitOpError("[evm.literal] requires exact collection literals");
      correct = signature({}, layout->lanes);
      if (auto array = dyn_cast<algebra::FieldArrayType>(type.getValue()))
        correct &= values.size() == array.getLength();
    } else if (action == "empty") {
      correct = signature({}, layout->lanes);
      if (auto array = dyn_cast<algebra::FieldArrayType>(type.getValue()))
        correct &= array.getLength() == 0;
      if (auto fixed = dyn_cast<algebra::FixedVectorType>(type.getValue()))
        correct &= fixed.getLength() == 0;
    } else if (action == "length")
      correct = signature(layout->lanes, {i64});
    else if (action == "alloc")
      correct = signature({i64}, {i64});
    else if (action == "get")
      correct = signature({i64, i64, i64}, element);
    else if (action == "sum")
      correct = coefficients && signature(layout->lanes, element);
    else if (action == "equal")
      correct = signature({i64, i64, i64, i64}, {i1});
    else if (action == "split")
      correct = layout->kind == ValueLayout::Kind::FieldVector &&
                signature(layout->lanes, {i64, i64, i64, i64});
    else {
      SmallVector<Type> inputs{i64, i64};
      if (action == "set")
        inputs.push_back(i64);
      llvm::append_range(inputs, element);
      correct = action == "set" ? signature(inputs, {})
                                : signature(inputs, layout->lanes);
      if (action == "append" &&
          isa<algebra::FieldArrayType, algebra::FixedVectorType>(
              type.getValue()))
        correct = false;
    }
  } else if (code.starts_with("variant.")) {
    auto variant = dyn_cast<data::VariantType>(type.getValue());
    if (!variant)
      return emitOpError("[evm.value-type] requires complete VariantType");
    if (code == "variant.tag")
      correct = signature({i64}, {i64});
    else {
      auto alternative = number("alternative");
      if (!alternative || *alternative >= variant.getAlternatives().size())
        return emitOpError("[evm.alternative] invalid alternative index");
      if (code == "variant.make") {
        auto payload = layouts.payload(variant, *alternative);
        if (!payload) {
          llvm::consumeError(payload.takeError());
          return failure();
        }
        correct = signature(payload->lanes, {i64});
      } else {
        auto index = number("payload");
        auto payload = variant.getAlternatives()[*alternative].getPayload();
        if (!index || *index >= payload.size())
          return emitOpError("[evm.payload] invalid payload index");
        auto child = layouts.get(payload[*index]);
        if (!child) {
          llvm::consumeError(child.takeError());
          return failure();
        }
        correct = signature({i64}, (*child)->lanes);
      }
    }
  } else if (code == "proof.receive" || code == "transcript.observe") {
    if (auto error = verifyWireType(layouts, type.getValue())) {
      llvm::consumeError(std::move(error));
      return emitOpError("[evm.wire-type] complete native message permission "
                         "and codec required");
    }
    if (code == "proof.receive")
      correct = signature({}, layout->lanes);
    else {
      SmallVector<Type> inputs{i64, i64};
      llvm::append_range(inputs, layout->lanes);
      inputs.append({i64, i64});
      correct = signature(inputs, {i64});
    }
  } else if (code == "transcript.challenge") {
    auto scalar = dyn_cast<algebra::FieldType>(type.getValue());
    correct = scalar && scalar.getDomain() == "bls12-381.fr" &&
              signature({i64, i64, i64, i64}, {i256, i64});
  } else if (code.starts_with("index.")) {
    if (code == "index.pow2")
      correct = signature({i64}, {i64});
    else if (code == "index.power_of_two")
      correct = signature({i64, i64}, {i1});
    else
      correct = signature({i64, i64}, {i64});
  } else if (code == "scope.root" || code == "scope.current")
    correct = signature({}, {i64});
  else if (code == "scope.enter")
    correct = signature({i64, i64}, {i64});
  else if (code == "scope.exit")
    correct = signature({i64, i64}, {i64}) || signature({i64, i64}, {});
  else if (code == "scope.check" || code == "transfer.check" ||
           code == "transfer.release")
    correct = signature({i64}, {});
  else if (code == "transfer.make")
    correct = signature({i64}, {i64});
  else if (code == "transfer.accept" || code == "loop.bound" ||
           code == "range.check" || code == "range.admit")
    correct = signature({i64, i64}, {});
  else if (code == "source.stop")
    correct = signature({}, {}) || signature({i1}, {});
  if (!correct)
    return emitOpError("[evm.signature] incorrect operands/results for ")
           << code;
  if (code == "vector.set" || code == "sequence.set") {
    auto allocation = getOperand(0).getDefiningOp<CheckedOp>();
    StringRef expected =
        code == "vector.set" ? "vector.alloc" : "sequence.alloc";
    if (!allocation || allocation.opcode() != expected ||
        allocation->getAttr("value_type") != type ||
        allocation->getNumOperands() != 1 ||
        allocation.getOperand(0) != getOperand(1))
      return emitOpError("[evm.construction] stores require their exact fresh "
                         "construction buffer and count");
  }

  if (auto site = (*this)->getAttr("site");
      site &&
      (!isa<StringAttr>(site) || cast<StringAttr>(site).getValue().empty()))
    return emitOpError("[evm.site] requires nonempty source stop site");
  if (code.starts_with("transcript.")) {
    auto origin = (*this)->getAttrOfType<StringAttr>("origin");
    if (!origin || origin.getValue().empty())
      return emitOpError(
          "[evm.origin] transition requires an occurrence template");
    auto occurrence = protocol::decodeNativeOriginTemplate(origin.getValue());
    if (!occurrence) {
      llvm::consumeError(occurrence.takeError());
      return emitOpError("[evm.origin] invalid exact occurrence template");
    }
  }
  return success();
}
void CheckedOp::getEffects(
    SmallVectorImpl<MemoryEffects::EffectInstance> &effects) {
  effects.emplace_back(MemoryEffects::Read::get());
  effects.emplace_back(MemoryEffects::Write::get());
}
} // namespace zkc::evm
