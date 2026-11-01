#include "zkc/Dialect/Evm/Evm.h"
#include "mlir/IR/Builders.h"
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
  static StringRef names[] = {"opcode"};
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
      .Cases({"field.inverse", "field.pow", "field.div"}, true)
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
  if (!isCheckedOpcode(opcode()))
    return emitOpError("[evm.opcode] unsupported checked opcode: ") << opcode();
  auto valid = [](Type t) {
    return t.isInteger(1) || t.isInteger(32) || t.isInteger(64) ||
           t.isInteger(256);
  };
  if (!llvm::all_of(getOperandTypes(), valid) ||
      !llvm::all_of(getResultTypes(), valid))
    return emitOpError(
        "[evm.type] checked operands/results must be EVM integers");
  auto signature = [&](ArrayRef<unsigned> inputs, ArrayRef<unsigned> outputs) {
    if (inputs.size() != getNumOperands() || outputs.size() != getNumResults())
      return false;
    for (auto [type, width] : llvm::zip(getOperandTypes(), inputs))
      if (!type.isInteger(width))
        return false;
    for (auto [type, width] : llvm::zip(getResultTypes(), outputs))
      if (!type.isInteger(width))
        return false;
    return true;
  };
  StringRef code = opcode();
  bool correct = false;
  if (code.starts_with("index.")) {
    if (code == "index.pow2")
      correct = signature({64}, {64});
    else if (code == "index.power_of_two")
      correct = signature({64, 64}, {1});
    else
      correct = signature({64, 64}, {64});
  } else if (code == "field.inverse")
    correct = signature({256}, {256});
  else if (code == "field.pow")
    correct = signature({256, 64}, {256});
  else if (code == "field.div")
    correct = signature({256, 256}, {256});
  else if (code == "vector.empty" || code == "indices.empty")
    correct = signature({}, {64, 64});
  else if (code == "vector.length")
    correct = signature({64, 64}, {64});
  else if (code == "vector.append")
    correct = signature({64, 64, 256}, {64, 64});
  else if (code == "indices.append")
    correct = signature({64, 64, 64}, {64, 64});
  else if (code == "vector.split")
    correct = signature({64, 64}, {64, 64, 64, 64});
  else if (code == "vector.sum")
    correct = signature({64, 64}, {256});
  else if (code == "vector.alloc")
    correct = signature({64}, {64});
  else if (code == "vector.get")
    correct = signature({64, 64, 64}, {256});
  else if (code == "vector.set")
    correct = signature({64, 64, 64, 256}, {});
  else if (code == "vector.equal")
    correct = signature({64, 64, 64, 64}, {1});
  else if (code == "scope.root" || code == "scope.current")
    correct = signature({}, {64});
  else if (code == "scope.enter")
    correct = signature({64, 64}, {64});
  else if (code == "scope.exit")
    correct = signature({64, 64}, {64}) || signature({64, 64}, {});
  else if (code == "scope.check" || code == "transfer.check" ||
           code == "transfer.release")
    correct = signature({64}, {});
  else if (code == "transfer.make")
    correct = signature({64}, {64});
  else if (code == "transfer.accept" || code == "loop.bound" ||
           code == "range.check" || code == "range.admit")
    correct = signature({64, 64}, {});
  else if (code == "proof.receive")
    correct = signature({}, {256});
  else if (code == "source.stop")
    correct = signature({}, {}) || signature({1}, {});
  else if (code == "transcript.observe")
    correct = signature({64, 64, 256, 64, 64}, {64});
  else if (code == "transcript.challenge")
    correct = signature({64, 64, 64, 64}, {256, 64});
  if (!correct)
    return emitOpError("[evm.signature] incorrect operands/results for ")
           << code;
  if (code.starts_with("transcript.")) {
    auto origin = (*this)->getAttrOfType<StringAttr>("origin");
    if (!origin || origin.getValue().empty())
      return emitOpError(
          "[evm.origin] transition requires an occurrence template");
  }
  return success();
}
void CheckedOp::getEffects(
    SmallVectorImpl<MemoryEffects::EffectInstance> &effects) {
  effects.emplace_back(MemoryEffects::Read::get());
  effects.emplace_back(MemoryEffects::Write::get());
}
} // namespace zkc::evm
