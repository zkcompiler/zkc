#include "zkc/Target/Evm/Wire.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/raw_ostream.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
namespace {
using Kind = ValueLayout::Kind;

struct Frame {
  const ValueLayout *layout = nullptr;
  const FieldLayout *field = nullptr;
  unsigned tag = 0, coefficientWidth = 0;
  std::string name;
  const FieldLayout *digestField = nullptr;
  unsigned digestWordWidth = 0, pathLimit = 0;
};

// These are native codec byte identities, not a field/layout registry. Degree,
// modulus, local strides and lanes always come from the shared layout owner.
Expected<std::pair<unsigned, unsigned>> fieldFrame(StringRef identity) {
  auto result = llvm::StringSwitch<std::pair<unsigned, unsigned>>(identity)
                    .Case("zkcv.field.bls12-381.fr/0", {1, 32})
                    .Case("zkcv.field.bn254.fr/0", {40, 32})
                    .Case("zkcv.field.ristretto255.scalar/0", {13, 32})
                    .Case("zkcv.field.koala-bear/0", {19, 4})
                    .Case("zkcv.field.koala-bear.ext4-binomial3/0", {21, 4})
                    .Case("zkcv.field.koala-bear.ext8-binomial3/0", {26, 4})
                    .Case("zkcv.field.baby-bear/0", {90, 4})
                    .Case("zkcv.field.baby-bear.ext4-binomial11/0", {93, 4})
                    .Case("zkcv.field.goldilocks/0", {96, 8})
                    .Case("zkcv.field.goldilocks.ext2-binomial7/0", {99, 8})
                    .Case("zkcv.vector.bls12-381.fr/0", {66, 32})
                    .Case("zkcv.vector.bn254.fr/0", {41, 32})
                    .Case("zkcv.vector.ristretto255.scalar/0", {14, 32})
                    .Case("zkcv.vector.koala-bear/0", {20, 4})
                    .Case("zkcv.vector.koala-bear.ext4-binomial3/0", {22, 4})
                    .Case("zkcv.vector.koala-bear.ext8-binomial3/0", {27, 4})
                    .Case("zkcv.vector.baby-bear/0", {91, 4})
                    .Case("zkcv.vector.baby-bear.ext4-binomial11/0", {94, 4})
                    .Case("zkcv.vector.goldilocks/0", {97, 8})
                    .Case("zkcv.vector.goldilocks.ext2-binomial7/0", {100, 8})
                    .Default({0, 0});
  if (!result.first)
    return zkc::error("evm.wire-type", "no exact supported native field codec");
  return result;
}

Expected<Frame> frame(NativeLayouts &layouts, Type type) {
  auto layout = layouts.get(type);
  if (!layout)
    return layout.takeError();
  auto permission = mathematical::nativeTypePolicy(type);
  if (!permission || !permission->wire || permission->affine)
    return zkc::error("evm.wire-type",
                      "complete type has no native wire permission");
  Frame result;
  result.layout = *layout;
  StringRef kind, domain;
  switch (result.layout->kind) {
  case Kind::Boolean:
    kind = "bool";
    result.tag = 5;
    break;
  case Kind::Index:
    kind = "index";
    result.tag = 31;
    break;
  case Kind::Indices:
    kind = "indices";
    result.tag = 68;
    break;
  case Kind::Bytes:
    kind = "bytes";
    result.tag = 70;
    break;
  case Kind::FieldArray: {
    auto array = cast<algebra::FieldArrayType>(type);
    if (array.getDomain() != "bls12-381.fr")
      return zkc::error("evm.wire-type",
                        "no native fixed-array codec for this field");
    auto field = layouts.field(
        algebra::FieldType::get(type.getContext(), array.getDomain()));
    if (!field)
      return field.takeError();
    result.field = *field;
    result.tag = 64;
    result.coefficientWidth = 32;
    return result;
  }
  case Kind::FixedVector:
    return zkc::error("evm.wire-type",
                      "no supported complete native codec for this collection");
  case Kind::Root:
  case Kind::Path: {
    auto object = cast<commitment::VectorObjectType>(type);
    kind = object.getKind();
    domain = object.getScheme();
    break;
  }
  case Kind::Sequence:
    result.tag = 69;
    return result;
  case Kind::Variant:
    result.tag = 65;
    return result;
  case Kind::Field:
    kind = "field";
    domain = cast<algebra::FieldType>(type).getDomain();
    break;
  case Kind::FieldVector:
    kind = "vector";
    domain = cast<algebra::FieldVectorType>(type).getDomain();
    break;
  }
  if (!protocol::nativeMessageAtom(kind, domain))
    return zkc::error("evm.wire-type",
                      "type is outside the native message grammar");
  auto *codec = protocol::installedDomains().defaultCodec(kind, domain);
  if (!codec)
    return zkc::error("evm.wire-type", "no uniquely selected native codec");
  if (result.layout->kind == Kind::Root || result.layout->kind == Kind::Path) {
    bool root = result.layout->kind == Kind::Root;
    auto identity = StringRef(codec->identity);
    StringRef prefix = root ? "zkcv.commitment." : "zkcv.proof.";
    if (!identity.consume_front(prefix))
      return zkc::error("evm.wire-type", "incompatible native envelope codec");
    unsigned keccak =
        llvm::StringSwitch<unsigned>(identity)
            .Case("rows-merkle-keccak256.koala-bear/0", root ? 33 : 34)
            .Case("rows-merkle-keccak256.koala-bear.ext8-binomial3/0",
                  root ? 35 : 36)
            .Case("rows-merkle-keccak256.koala-bear.ext4-binomial3/0",
                  root ? 79 : 80)
            .Default(0);
    if (keccak) {
      result.tag = keccak;
      result.pathLimit = 24;
    } else {
      result.digestWordWidth =
          llvm::StringSwitch<unsigned>(identity)
              .Cases({"rows-merkle-poseidon2-16.koala-bear/0",
                      "rows-merkle-poseidon2-16.koala-bear.ext4-binomial3/0"},
                     4)
              .Cases({"rows-merkle-poseidon2-16.baby-bear/0",
                      "rows-merkle-poseidon2-16.baby-bear.ext4-binomial11/0"},
                     4)
              .Cases({"rows-merkle-poseidon2-8.goldilocks/0",
                      "rows-merkle-poseidon2-8.goldilocks.ext2-binomial7/0"},
                     8)
              .Default(0);
      if (!result.digestWordWidth)
        return zkc::error("evm.wire-type", "unsupported exact root/path codec");
      auto valueField =
          protocol::installedDomains().associatedIdentity(domain, "ValueField");
      auto facts =
          layouts.field(algebra::FieldType::get(type.getContext(), valueField));
      if (!facts)
        return facts.takeError();
      result.digestField = *facts;
      result.tag = root ? 71 : 72;
    }
    return result;
  }
  if (kind == "field" || kind == "vector") {
    auto bytes = fieldFrame(codec->identity);
    if (!bytes)
      return bytes.takeError();
    result.tag = bytes->first;
    result.coefficientWidth = bytes->second;
    auto field =
        layouts.field(algebra::FieldType::get(type.getContext(), domain));
    if (!field)
      return field.takeError();
    result.field = *field;
  } else if (codec->identity != ("zkcv." + kind + "/0").str()) {
    return zkc::error("evm.wire-type", "unsupported native codec identity");
  }
  return result;
}

Error verify(NativeLayouts &layouts, Type type, unsigned depth,
             llvm::DenseSet<Type> &visited) {
  if (depth >= 64)
    return zkc::error("evm.wire-type",
                      "wire type nesting exceeds native bound");
  if (!visited.insert(type).second)
    return Error::success();
  auto selected = frame(layouts, type);
  if (!selected)
    return selected.takeError();
  if (auto sequence = dyn_cast<data::SequenceType>(type))
    return verify(layouts, sequence.getElementType(), depth + 1, visited);
  if (auto variant = dyn_cast<data::VariantType>(type))
    for (auto alternative : variant.getAlternatives())
      for (Type child : alternative.getPayload())
        if (auto failure = verify(layouts, child, depth + 1, visited))
          return failure;
  return Error::success();
}

std::string number(const APInt &value) {
  SmallString<80> text;
  value.toString(text, 16, false);
  return "0x" + text.str().str();
}
std::string lanes(unsigned count, StringRef prefix = "v") {
  std::string text;
  for (unsigned i = 0; i < count; ++i) {
    if (i)
      text += ", ";
    text += prefix.str() + std::to_string(i);
  }
  return text;
}
std::string loads(unsigned count, StringRef address) {
  std::string text;
  for (unsigned i = 0; i < count; ++i) {
    if (i)
      text += ", ";
    text += "mload(add(" + address.str() + ", " + std::to_string(i * 32) + "))";
  }
  return text;
}
void stores(raw_ostream &out, unsigned count, StringRef address,
            StringRef prefix = "v") {
  for (unsigned i = 0; i < count; ++i)
    out << "mstore(add(" << address << ", " << i * 32 << "), " << prefix << i
        << ")\n";
}
std::string header(unsigned tag) {
  return "0x5a4b435600" + utohexstr(tag, true, 2);
}
} // namespace

Error verifyWireType(NativeLayouts &layouts, Type type) {
  llvm::DenseSet<Type> visited;
  return verify(layouts, type, 0, visited);
}

struct WireGenerator::Storage {
  NativeLayouts &layouts;
  const EvmLimits limits;
  llvm::DenseMap<Type, std::unique_ptr<Frame>> frames;
  StringMap<std::string> operations;
  std::string text;
  raw_string_ostream out;
  Storage(NativeLayouts &layouts, const EvmLimits &limits)
      : layouts(layouts), limits(limits), out(text) {}
  Expected<Frame *> require(Type);
  void emit(const Frame &);
  Expected<std::string> operation(CheckedOp);
  const Frame &child(Type type) { return *frames.find(type)->second; }
  unsigned width(const Frame &f) {
    return f.coefficientWidth * f.field->degree;
  }
  void scan(const Frame &);
  void canonical(const Frame &);
  void read(const Frame &);
  void size(const Frame &);
  void write(const Frame &);
};

Expected<Frame *> WireGenerator::Storage::require(Type type) {
  if (auto found = frames.find(type); found != frames.end())
    return found->second.get();
  if (auto failure = verifyWireType(layouts, type))
    return std::move(failure);
  auto selected = frame(layouts, type);
  if (!selected)
    return selected.takeError();
  selected->name = "evm_wire_" + std::to_string(frames.size());
  auto value = std::make_unique<Frame>(std::move(*selected));
  Frame *result = value.get();
  frames[type] = std::move(value);
  if (auto sequence = dyn_cast<data::SequenceType>(type)) {
    auto nested = require(sequence.getElementType());
    if (!nested)
      return nested.takeError();
  }
  if (auto variant = dyn_cast<data::VariantType>(type))
    for (auto alternative : variant.getAlternatives())
      for (Type payload : alternative.getPayload()) {
        auto nested = require(payload);
        if (!nested)
          return nested.takeError();
      }
  emit(*result);
  return result;
}

// The scanner is deliberately allocation-free. A single caller-owned budget
// is passed through all children. It charges logical values, never coefficient
// words, and derives rounded retained allocation before materialization.
void WireGenerator::Storage::scan(const Frame &f) {
  auto kind = f.layout->kind;
  out << "function " << f.name << "_scan(p, n, budget, depth) {\n"
      << "if gt(n, " << limits.frameBytes << ") { evm_resource(13) }\n"
      << "evm_wire_node(budget, depth)\n";
  if (kind == Kind::Root || kind == Kind::Path) {
    bool root = kind == Kind::Root;
    if (root)
      out << "if iszero(eq(n, 38)) { evm_decode(2) }\n";
    else
      out << "if lt(n, 10) { evm_decode(2) }\n";
    out << "if iszero(eq(shr(208, mload(p)), " << header(f.tag)
        << ")) { evm_decode(3) }\n";
    if (root)
      out << "evm_wire_elements(budget, 1)\n";
    else {
      out << "let count := evm_le(add(p, 6), 4) evm_wire_elements(budget, "
             "count)\n";
      if (f.pathLimit)
        out << "if gt(count, " << f.pathLimit << ") { evm_resource(2) }\n";
      out << "if iszero(eq(n, add(10, evm_wire_mul(count, 32)))) { "
             "evm_decode(2) }\n";
    }
    out << "evm_wire_retain(budget, n)\n}\n";
    return;
  }
  bool aggregate = kind == Kind::Sequence || kind == Kind::Variant;
  bool fixed = kind == Kind::FieldArray;
  bool collection = f.layout->collection.has_value() && !fixed;
  if (!aggregate && !collection) {
    uint64_t bytes =
        kind == Kind::Boolean ? 7
        : kind == Kind::Index ? 14
        : fixed
            ? 6 + cast<algebra::FieldArrayType>(f.layout->logical).getLength() *
                      uint64_t(width(f))
            : 6 + width(f);
    out << "if iszero(eq(n, " << bytes << ")) { evm_decode(2) }\n";
  } else {
    out << "if lt(n, 10) { evm_decode(2) }\n";
  }
  out << "if iszero(eq(shr(208, mload(p)), " << header(f.tag)
      << ")) { evm_decode(3) }\n";
  if (collection || kind == Kind::Variant)
    out << "let count := evm_le(add(p, 6), 4)\n";
  if (kind == Kind::Field || kind == Kind::Index)
    out << "evm_wire_elements(budget, 1)\n";
  if (kind == Kind::Field && f.field->degree > 1)
    out << "evm_wire_retain(budget, " << f.field->coefficientBytes() << ")\n";
  if (fixed) {
    uint64_t count =
        cast<algebra::FieldArrayType>(f.layout->logical).getLength();
    out << "evm_wire_elements(budget, " << count << ")\n"
        << "evm_wire_retain(budget, evm_wire_mul(" << count << ", "
        << f.layout->collection->strideBytes << "))\n";
  } else if (kind == Kind::Bytes) {
    out << "if gt(count, " << limits.frameBytes << ") { evm_resource(13) }\n"
        << "if iszero(eq(n, add(10, count))) { evm_decode(2) }\n"
        << "evm_wire_retain(budget, count)\n";
  } else if (kind == Kind::FieldVector || kind == Kind::Indices) {
    auto wireStride = kind == Kind::Indices ? 8 : width(f);
    out << "evm_wire_elements(budget, count)\n"
        << "let bytes := evm_wire_mul(count, " << wireStride << ")\n"
        << "if iszero(eq(n, add(10, bytes))) { evm_decode(2) }\n"
        << "evm_wire_retain(budget, evm_wire_mul(count, "
        << f.layout->collection->strideBytes << "))\n";
  } else if (kind == Kind::Sequence) {
    const auto &element =
        child(cast<data::SequenceType>(f.layout->logical).getElementType());
    out << "evm_wire_count(count)\n"
        << "evm_wire_retain(budget, evm_wire_mul(count, "
        << f.layout->collection->strideBytes << "))\n"
        << "let cursor := add(p, 10) let end := add(p, n)\n"
        << "for { let i := 0 } lt(i, count) { i := add(i, 1) } {\n"
        << "let cp, cn, next := evm_wire_child(cursor, end)\n"
        << element.name << "_scan(cp, cn, budget, add(depth, 1))\n"
        << "cursor := next\n}\n"
        << "if iszero(eq(cursor, end)) { evm_decode(2) }\n";
  } else if (kind == Kind::Variant) {
    auto variant = cast<data::VariantType>(f.layout->logical);
    out << "switch count\n";
    for (auto [index, alternative] : enumerate(variant.getAlternatives())) {
      auto payload = cantFail(layouts.payload(variant, index));
      out << "case " << index << " {\n"
          << "evm_wire_retain(budget, " << 32 + payload.lanes.size() * 32
          << ")\n"
          << "let cursor := add(p, 10) let end := add(p, n)\n";
      for (Type type : alternative.getPayload())
        out << "{ let cp, cn, next := evm_wire_child(cursor, end)\n"
            << child(type).name << "_scan(cp, cn, budget, add(depth, 1))\n"
            << "cursor := next }\n";
      out << "if iszero(eq(cursor, end)) { evm_decode(2) }\n}\n";
    }
    out << "default { evm_decode(3) }\n";
  }
  out << "}\n";
}

void WireGenerator::Storage::canonical(const Frame &f) {
  auto kind = f.layout->kind;
  out << "function " << f.name << "_canonical(p) {\n";
  if (f.digestField) {
    bool root = kind == Kind::Root;
    out << "let count := " << (root ? "1" : "evm_le(add(p, 6), 4)") << "\n"
        << "for { let i := 0 } lt(i, mul(count, " << 32 / f.digestWordWidth
        << ")) { i := add(i, 1) } {\n"
        << "if iszero(lt(evm_le(add(add(p, " << (root ? 6 : 10) << "), mul(i, "
        << f.digestWordWidth << ")), " << f.digestWordWidth << "), "
        << number(f.digestField->modulus) << ")) { evm_decode(4) }\n}\n";
  }
  if (kind == Kind::Boolean)
    out << "if gt(byte(0, mload(add(p, 6))), 1) { evm_decode(4) }\n";
  if (f.field) {
    unsigned start = kind == Kind::Field || kind == Kind::FieldArray ? 6 : 10;
    std::string length =
        kind == Kind::Field ? "1"
        : kind == Kind::FieldArray
            ? std::to_string(
                  cast<algebra::FieldArrayType>(f.layout->logical).getLength())
            : "evm_le(add(p, 6), 4)";
    out << "let count := " << length << "\n"
        << "for { let i := 0 } lt(i, mul(count, " << f.field->degree
        << ")) { i := add(i, 1) } {\n"
        << "if iszero(lt(evm_le(add(add(p, " << start << "), mul(i, "
        << f.coefficientWidth << ")), " << f.coefficientWidth << "), "
        << number(f.field->modulus) << ")) { evm_decode(4) }\n}\n";
  }
  if (kind == Kind::Sequence) {
    const auto &element =
        child(cast<data::SequenceType>(f.layout->logical).getElementType());
    out << "let cursor := add(p, 10)\n"
        << "for { let i := 0 } lt(i, evm_le(add(p, 6), 4)) { i := add(i, 1) } "
           "{\n"
        << element.name << "_canonical(add(cursor, 4))\n"
        << "cursor := add(add(cursor, 4), evm_le(cursor, 4))\n}\n";
  } else if (kind == Kind::Variant) {
    out << "switch evm_le(add(p, 6), 4)\n";
    auto variant = cast<data::VariantType>(f.layout->logical);
    for (auto [index, alternative] : enumerate(variant.getAlternatives())) {
      out << "case " << index << " { let cursor := add(p, 10)\n";
      for (Type type : alternative.getPayload())
        out << child(type).name << "_canonical(add(cursor, 4))\n"
            << "cursor := add(add(cursor, 4), evm_le(cursor, 4))\n";
      out << "}\n";
    }
    out << "default { evm_fault(10) }\n";
  }
  out << "}\n";
}

void WireGenerator::Storage::read(const Frame &f) {
  auto kind = f.layout->kind;
  unsigned count = f.layout->lanes.size();
  out << "function " << f.name << "_read(p) -> " << lanes(count) << " {\n";
  if (kind == Kind::Root || kind == Kind::Path) {
    out << "v1 := "
        << (kind == Kind::Root ? "38"
                               : "add(10, mul(evm_le(add(p, 6), 4), 32))")
        << " v0 := evm_alloc(v1) mcopy(v0, p, v1)\n";
  } else if (kind == Kind::Boolean)
    out << "v0 := byte(0, mload(add(p, 6)))\n";
  else if (kind == Kind::Index)
    out << "v0 := evm_le(add(p, 6), 8)\n";
  else if (kind == Kind::Field && f.field->degree == 1)
    out << "v0 := evm_le(add(p, 6), " << f.coefficientWidth << ")\n";
  else if (kind == Kind::Field || kind == Kind::FieldVector ||
           kind == Kind::FieldArray || kind == Kind::Indices) {
    bool scalar = kind == Kind::Field;
    unsigned degree = kind == Kind::Indices ? 1 : f.field->degree;
    unsigned coefficient = kind == Kind::Indices ? 8 : f.coefficientWidth;
    if (!scalar)
      out << "v1 := "
          << (kind == Kind::FieldArray
                  ? std::to_string(
                        cast<algebra::FieldArrayType>(f.layout->logical)
                            .getLength())
                  : "evm_le(add(p, 6), 4)")
          << "\n";
    std::string length = scalar ? "1" : "v1";
    uint64_t stride = scalar ? f.field->coefficientBytes()
                             : f.layout->collection->strideBytes;
    out << "v0 := evm_alloc(mul(" << length << ", " << stride << "))\n"
        << "for { let i := 0 } lt(i, mul(" << length << ", " << degree
        << ")) { i := add(i, 1) } {\n"
        << "mstore(add(v0, mul(i, 32)), evm_le(add(add(p, "
        << (scalar || kind == Kind::FieldArray ? 6 : 10) << "), mul(i, "
        << coefficient << ")), " << coefficient << "))\n}\n";
  } else if (kind == Kind::Bytes) {
    out << "v1 := evm_le(add(p, 6), 4) v0 := evm_alloc(v1)\n"
        << "mcopy(v0, add(p, 10), v1)\n";
  } else if (kind == Kind::Sequence) {
    const auto &element =
        child(cast<data::SequenceType>(f.layout->logical).getElementType());
    unsigned childLanes = element.layout->lanes.size();
    out << "v1 := evm_le(add(p, 6), 4)\n"
        << "v0 := evm_alloc(mul(v1, " << f.layout->collection->strideBytes
        << "))\n"
        << "let cursor := add(p, 10)\n"
        << "for { let i := 0 } lt(i, v1) { i := add(i, 1) } {\n"
        << "let " << lanes(childLanes, "c") << " := " << element.name
        << "_read(add(cursor, 4))\n"
        << "let cell := add(v0, mul(i, " << f.layout->collection->strideBytes
        << "))\n";
    stores(out, childLanes, "cell", "c");
    out << "cursor := add(add(cursor, 4), evm_le(cursor, 4))\n}\n";
  } else if (kind == Kind::Variant) {
    auto variant = cast<data::VariantType>(f.layout->logical);
    out << "let tag := evm_le(add(p, 6), 4)\nswitch tag\n";
    for (auto [index, alternative] : enumerate(variant.getAlternatives())) {
      auto payload = cantFail(layouts.payload(variant, index));
      out << "case " << index << " {\n"
          << "v0 := evm_alloc(" << 32 + payload.lanes.size() * 32 << ")\n"
          << "mstore(v0, tag) let cursor := add(p, 10)\n";
      unsigned offset = 32;
      for (Type type : alternative.getPayload()) {
        const auto &nested = child(type);
        unsigned childLanes = nested.layout->lanes.size();
        out << "{ let " << lanes(childLanes, "c") << " := " << nested.name
            << "_read(add(cursor, 4))\n";
        stores(out, childLanes, "add(v0, " + std::to_string(offset) + ")", "c");
        out << "cursor := add(add(cursor, 4), evm_le(cursor, 4)) }\n";
        offset += childLanes * 32;
      }
      out << "}\n";
    }
    out << "default { evm_fault(10) }\n";
  }
  out << "}\n";
}

void WireGenerator::Storage::size(const Frame &f) {
  auto kind = f.layout->kind;
  if (kind == Kind::Root || kind == Kind::Path) {
    out << "function " << f.name << "_size(v0, v1, budget, depth) -> n {\n"
        << "evm_memory(v0, v1) " << f.name << "_scan(v0, v1, budget, depth)\n"
        << f.name << "_canonical(v0) n := v1\n}\n";
    return;
  }
  out << "function " << f.name << "_size(" << lanes(f.layout->lanes.size())
      << ", budget, depth) -> n {\nevm_wire_node(budget, depth)\n";
  if (kind == Kind::Boolean) {
    out << "if gt(v0, 1) { evm_fault(10) } n := 7\n";
  } else if (kind == Kind::Index) {
    out << "if gt(v0, 0xffffffffffffffff) { evm_fault(10) }\n"
        << "evm_wire_elements(budget, 1) n := 14\n";
  } else if (f.field) {
    bool scalar = kind == Kind::Field;
    std::string length = scalar ? "1" : "v1";
    if (kind == Kind::FieldArray)
      out << "if iszero(eq(v1, "
          << cast<algebra::FieldArrayType>(f.layout->logical).getLength()
          << ")) { evm_fault(10) }\n";
    out << "evm_wire_elements(budget, " << length << ")\n";
    if (scalar && f.field->degree == 1)
      out << "if iszero(lt(v0, " << number(f.field->modulus)
          << ")) { evm_fault(10) }\n";
    else {
      uint64_t stride = scalar ? f.field->coefficientBytes()
                               : f.layout->collection->strideBytes;
      out << "let retained := evm_wire_mul(" << length << ", " << stride
          << ")\n"
          << "evm_memory(v0, retained) evm_wire_retain(budget, retained)\n"
          << "for { let i := 0 } lt(i, mul(" << length << ", "
          << f.field->degree << ")) { i := add(i, 1) } {\n"
          << "if iszero(lt(mload(add(v0, mul(i, 32))), "
          << number(f.field->modulus) << ")) { evm_fault(10) }\n}\n";
    }
    out << "n := evm_wire_add(" << (scalar || kind == Kind::FieldArray ? 6 : 10)
        << ", evm_wire_mul(" << length << ", " << width(f) << "))\n";
  } else if (kind == Kind::Bytes || kind == Kind::Indices) {
    if (kind == Kind::Indices)
      out << "evm_wire_elements(budget, v1)\n";
    else
      out << "if gt(v1, " << limits.frameBytes << ") { evm_resource(13) }\n";
    out << "let retained := evm_wire_mul(v1, "
        << f.layout->collection->strideBytes << ")\n"
        << "evm_memory(v0, retained) evm_wire_retain(budget, retained)\n"
        << "n := evm_wire_add(10, evm_wire_mul(v1, "
        << (kind == Kind::Bytes ? 1 : 8) << "))\n";
    if (kind == Kind::Indices)
      out << "for { let i := 0 } lt(i, v1) { i := add(i, 1) } {\n"
          << "if gt(mload(add(v0, mul(i, 32))), 0xffffffffffffffff) { "
             "evm_fault(10) }\n}\n";
  } else if (kind == Kind::Sequence) {
    const auto &element =
        child(cast<data::SequenceType>(f.layout->logical).getElementType());
    out << "evm_wire_count(v1)\n"
        << "let retained := evm_wire_mul(v1, "
        << f.layout->collection->strideBytes << ")\n"
        << "evm_memory(v0, retained) evm_wire_retain(budget, retained) n := "
           "10\n"
        << "for { let i := 0 } lt(i, v1) { i := add(i, 1) } {\n"
        << "let cell := add(v0, mul(i, " << f.layout->collection->strideBytes
        << "))\n"
        << "let length := " << element.name << "_size("
        << loads(element.layout->lanes.size(), "cell")
        << ", budget, add(depth, 1))\n"
        << "n := evm_wire_add(n, evm_wire_add(4, length))\n}\n";
  } else if (kind == Kind::Variant) {
    auto variant = cast<data::VariantType>(f.layout->logical);
    out << "evm_memory(v0, 32) n := 10\nswitch mload(v0)\n";
    for (auto [index, alternative] : enumerate(variant.getAlternatives())) {
      auto payload = cantFail(layouts.payload(variant, index));
      out << "case " << index << " {\n"
          << "evm_memory(v0, " << 32 + payload.lanes.size() * 32 << ")\n"
          << "evm_wire_retain(budget, " << 32 + payload.lanes.size() * 32
          << ")\n";
      unsigned offset = 32;
      for (Type type : alternative.getPayload()) {
        const auto &nested = child(type);
        out << "n := evm_wire_add(n, evm_wire_add(4, " << nested.name
            << "_size("
            << loads(nested.layout->lanes.size(),
                     "add(v0, " + std::to_string(offset) + ")")
            << ", budget, add(depth, 1))))\n";
        offset += nested.layout->lanes.size() * 32;
      }
      out << "}\n";
    }
    out << "default { evm_fault(10) }\n";
  }
  out << "if gt(n, " << limits.frameBytes << ") { evm_resource(13) }\n}\n";
}

// Writes directly into one pre-sized frame. Child lengths are filled from the
// final cursors; no child frame allocations or recursive temporary copies.
void WireGenerator::Storage::write(const Frame &f) {
  auto kind = f.layout->kind;
  if (kind == Kind::Root || kind == Kind::Path) {
    out << "function " << f.name << "_write(p, v0, v1) -> end {\n"
        << "mcopy(p, v0, v1) end := add(p, v1)\n}\n";
    return;
  }
  out << "function " << f.name << "_write(p, " << lanes(f.layout->lanes.size())
      << ") -> end {\nevm_wire_header(p, " << f.tag << ")\n";
  if (kind == Kind::Boolean)
    out << "mstore8(add(p, 6), v0) end := add(p, 7)\n";
  else if (kind == Kind::Index)
    out << "evm_write_le(add(p, 6), v0, 8) end := add(p, 14)\n";
  else if (f.field) {
    bool scalar = kind == Kind::Field;
    std::string length = scalar ? "1" : "v1";
    unsigned start = scalar || kind == Kind::FieldArray ? 6 : 10;
    if (!scalar && kind != Kind::FieldArray)
      out << "evm_write_le(add(p, 6), v1, 4)\n";
    if (scalar && f.field->degree == 1)
      out << "evm_write_le(add(p, 6), v0, " << f.coefficientWidth << ")\n";
    else
      out << "for { let i := 0 } lt(i, mul(" << length << ", "
          << f.field->degree << ")) { i := add(i, 1) } {\n"
          << "evm_write_le(add(add(p, " << start << "), mul(i, "
          << f.coefficientWidth << ")), mload(add(v0, mul(i, 32))), "
          << f.coefficientWidth << ")\n}\n";
    out << "end := add(add(p, " << start << "), mul(" << length << ", "
        << width(f) << "))\n";
  } else if (kind == Kind::Bytes || kind == Kind::Indices) {
    out << "evm_write_le(add(p, 6), v1, 4)\n";
    if (kind == Kind::Bytes)
      out << "mcopy(add(p, 10), v0, v1)\n";
    else
      out << "for { let i := 0 } lt(i, v1) { i := add(i, 1) } {\n"
          << "evm_write_le(add(add(p, 10), mul(i, 8)), mload(add(v0, mul(i, "
             "32))), 8)\n}\n";
    out << "end := add(add(p, 10), mul(v1, " << (kind == Kind::Bytes ? 1 : 8)
        << "))\n";
  } else if (kind == Kind::Sequence) {
    const auto &element =
        child(cast<data::SequenceType>(f.layout->logical).getElementType());
    out << "evm_write_le(add(p, 6), v1, 4) end := add(p, 10)\n"
        << "for { let i := 0 } lt(i, v1) { i := add(i, 1) } {\n"
        << "let cell := add(v0, mul(i, " << f.layout->collection->strideBytes
        << "))\n"
        << "let start := end\nend := " << element.name
        << "_write(add(start, 4), "
        << loads(element.layout->lanes.size(), "cell") << ")\n"
        << "evm_write_le(start, sub(sub(end, start), 4), 4)\n}\n";
  } else if (kind == Kind::Variant) {
    out << "evm_write_le(add(p, 6), mload(v0), 4) end := add(p, 10)\n"
        << "switch mload(v0)\n";
    auto variant = cast<data::VariantType>(f.layout->logical);
    for (auto [index, alternative] : enumerate(variant.getAlternatives())) {
      out << "case " << index << " {\n";
      unsigned offset = 32;
      for (Type type : alternative.getPayload()) {
        const auto &nested = child(type);
        out << "{ let start := end\nend := " << nested.name
            << "_write(add(start, 4), "
            << loads(nested.layout->lanes.size(),
                     "add(v0, " + std::to_string(offset) + ")")
            << ")\n"
            << "evm_write_le(start, sub(sub(end, start), 4), 4) }\n";
        offset += nested.layout->lanes.size() * 32;
      }
      out << "}\n";
    }
    out << "default { evm_fault(10) }\n";
  }
  out << "}\n";
}

void WireGenerator::Storage::emit(const Frame &f) {
  scan(f);
  canonical(f);
  read(f);
  size(f);
  write(f);
  std::string values = lanes(f.layout->lanes.size());
  out << "function " << f.name << "_decode(p, n) -> " << values << " {\n"
      << "evm_memory(p, n)\nlet budget := evm_wire_budget()\n"
      << f.name << "_scan(p, n, budget, 0)\n"
      << "evm_wire_peak(budget, n)\n"
      << f.name << "_canonical(p)\n"
      << "evm_wire_construct(budget)\n"
      << "mstore(0x40, budget)\n"
      << values << " := " << f.name << "_read(p)\n}\n"
      << "function " << f.name << "_encode(" << values << ") -> p, n {\n"
      << "let budget := evm_wire_budget()\n"
      << "n := " << f.name << "_size(" << values << ", budget, 0)\n"
      << "evm_wire_peak(budget, n)\nmstore(0x40, budget)\np := evm_alloc(n)\n"
      << "let end := " << f.name << "_write(p, " << values << ")\n"
      << "if iszero(eq(end, add(p, n))) { evm_fault(10) }\n}\n"
      << "function " << f.name << "_receive() -> " << values << " {\n"
      << "let p := mload(0x140) let end := mload(0x160)\n"
      << "if gt(p, end) { evm_fault(10) }\n"
      << "if lt(sub(end, p), 8) { evm_decode(5) }\n"
      << "let n := evm_le(p, 8) p := add(p, 8)\n"
      << "if gt(n, " << limits.frameBytes << ") { evm_resource(13) }\n"
      << "if gt(n, sub(end, p)) { evm_decode(5) }\n"
      << values << " := " << f.name << "_decode(p, n)\n"
      << "mstore(0x140, add(p, n))\n}\n";
}

Expected<std::string> WireGenerator::Storage::operation(CheckedOp op) {
  auto attribute = op->getAttrOfType<TypeAttr>("value_type");
  if (!attribute)
    return zkc::error("evm.wire-operation", "missing exact logical value_type");
  Type type = attribute.getValue();
  StringRef code = op.opcode();
  if (code == "proof.receive") {
    auto selected = require(type);
    if (!selected)
      return selected.takeError();
    return (*selected)->name + "_receive";
  }
  auto selected = layouts.get(type);
  if (!selected)
    return selected.takeError();
  const ValueLayout &layout = **selected;
  // Helpers are generated only for the closed, positively verified typed
  // inventory. Static selectors are embedded after exact range validation.
  std::string key;
  raw_string_ostream keyOut(key);
  keyOut << code << ':' << type.getAsOpaquePointer() << ':'
         << op->getAttr("alternative") << ':' << op->getAttr("payload");
  if (auto found = operations.find(key); found != operations.end())
    return found->second;
  std::string name = "evm_structure_" + std::to_string(operations.size());
  if (code.starts_with("sequence.") || code.starts_with("bytes.")) {
    if (!layout.collection || layout.collection->storage ==
                                  CollectionLayout::Storage::FieldCoefficients)
      return zkc::error(
          "evm.wire-operation",
          "structural operation requires lane cells or packed bytes");
    auto collection = *layout.collection;
    unsigned elementLanes = 1;
    if (collection.element) {
      auto element = layouts.get(collection.element);
      if (!element)
        return element.takeError();
      elementLanes = (*element)->lanes.size();
    }
    bool packed = collection.storage == CollectionLayout::Storage::PackedBytes;
    uint64_t stride = collection.strideBytes;
    std::string countCheck = packed ? "if gt(n, " +
                                          std::to_string(limits.frameBytes) +
                                          ") { evm_resource(13) }\n"
                                    : "evm_wire_count(n)\n";
    StringRef action = code.split('.').second;
    if (action == "empty") {
      out << "function " << name << "() -> p, n { p := evm_alloc(0) n := 0 }\n";
    } else if (action == "alloc") {
      out << "function " << name << "(n) -> p {\n"
          << countCheck << "p := evm_alloc(evm_wire_mul(n, " << stride
          << "))\n}\n";
    } else if (action == "length") {
      out << "function " << name << "(p, n) -> length {\n"
          << countCheck << "evm_memory(p, evm_wire_mul(n, " << stride
          << ")) length := n\n}\n";
    } else if (action == "get" || action == "set") {
      bool set = action == "set";
      out << "function " << name << "(p, n, i";
      if (set)
        out << ", " << lanes(elementLanes);
      out << ")";
      if (!set)
        out << " -> " << lanes(elementLanes);
      out << " {\n";
      if (set)
        out << "if iszero(lt(i, " << limits.publicElements
            << ")) { evm_resource(2) }\n";
      out << countCheck << "evm_memory(p, evm_wire_mul(n, " << stride << "))\n"
          << "if iszero(lt(i, n)) { "
          << (set ? "evm_fault(3)" : "evm_source(3)") << " }\n"
          << "let cell := add(p, mul(i, " << stride << "))\n";
      if (set) {
        if (packed)
          out << "if gt(v0, 255) { evm_source(3) } mstore8(cell, v0)\n";
        else
          stores(out, elementLanes, "cell");
      } else {
        for (unsigned i = 0; i < elementLanes; ++i)
          out << "v" << i << " := "
              << (packed ? "byte(0, mload(cell))"
                         : "mload(add(cell, " + std::to_string(i * 32) + "))")
              << "\n";
      }
      out << "}\n";
    } else if (action == "append") {
      out << "function " << name << "(p, n, " << lanes(elementLanes)
          << ") -> result, length {\n"
          << countCheck << "let bytes := evm_wire_mul(n, " << stride << ")\n"
          << "evm_memory(p, bytes)\n";
      if (packed)
        out << "if gt(v0, 255) { evm_source(3) }\n";
      out << "if iszero(lt(n, "
          << (packed ? limits.frameBytes : limits.publicElements)
          << ")) { evm_resource(2) }\n"
          << "length := add(n, 1)\n"
          << "result := evm_alloc(evm_wire_mul(length, " << stride << "))\n"
          << "mcopy(result, p, bytes) let cell := add(result, bytes)\n";
      if (packed)
        out << "mstore8(cell, v0)\n";
      else
        stores(out, elementLanes, "cell");
      out << "}\n";
    } else
      return zkc::error("evm.wire-operation",
                        "unsupported structural collection opcode");
    operations[key] = name;
    return name;
  }
  auto variant = dyn_cast<data::VariantType>(type);
  if (!variant || !code.starts_with("variant."))
    return zkc::error("evm.wire-operation",
                      "unsupported typed structural opcode");
  if (code == "variant.tag") {
    out << "function " << name
        << "(p) -> tag { evm_memory(p, 32) tag := mload(p)\n"
        << "if iszero(lt(tag, " << variant.getAlternatives().size()
        << ")) { evm_fault(10) } }\n";
    operations[key] = name;
    return name;
  }
  auto alternative = op->getAttrOfType<IntegerAttr>("alternative");
  if (!alternative || alternative.getValue().isNegative() ||
      alternative.getUInt() >= variant.getAlternatives().size())
    return zkc::error("evm.wire-operation",
                      "invalid static variant alternative");
  unsigned arm = alternative.getUInt();
  auto payload = layouts.payload(variant, arm);
  if (!payload)
    return payload.takeError();
  uint64_t bytes = 32 + payload->lanes.size() * 32;
  if (code == "variant.make") {
    out << "function " << name << "(" << lanes(payload->lanes.size())
        << ") -> p {\n"
        << "p := evm_alloc(" << bytes << ") mstore(p, " << arm << ")\n";
    stores(out, payload->lanes.size(), "add(p, 32)");
    out << "}\n";
    operations[key] = name;
    return name;
  }
  if (code == "variant.get") {
    auto index = op->getAttrOfType<IntegerAttr>("payload");
    if (!index || index.getValue().isNegative() ||
        index.getUInt() >= payload->values.size())
      return zkc::error("evm.wire-operation", "invalid static variant payload");
    auto slice = payload->values[index.getUInt()];
    out << "function " << name << "(p) -> " << lanes(slice.count) << " {\n"
        << "evm_memory(p, 32) if iszero(eq(mload(p), " << arm
        << ")) { evm_source(3) }\n"
        << "evm_memory(p, " << bytes << ")\n";
    for (unsigned i = 0; i < slice.count; ++i)
      out << "v" << i << " := mload(add(p, " << 32 + (slice.first + i) * 32
          << "))\n";
    out << "}\n";
    operations[key] = name;
    return name;
  }
  return zkc::error("evm.wire-operation", "unsupported typed variant opcode");
}

WireGenerator::WireGenerator(NativeLayouts &layouts, const EvmLimits &limits)
    : storage(std::make_unique<Storage>(layouts, limits)) {}
WireGenerator::~WireGenerator() = default;
Expected<std::string> WireGenerator::decoder(Type type) {
  auto value = storage->require(type);
  if (!value)
    return value.takeError();
  return (*value)->name + "_decode";
}
Expected<std::string> WireGenerator::encoder(Type type) {
  auto value = storage->require(type);
  if (!value)
    return value.takeError();
  return (*value)->name + "_encode";
}
Expected<std::string> WireGenerator::operation(CheckedOp op) {
  return storage->operation(op);
}
std::string WireGenerator::definitions() const {
  std::string text;
  raw_string_ostream out(text);
  const auto &limits = storage->limits;
  out << R"YUL(
function evm_wire_count(n) {
  if gt(n, )YUL"
      << limits.publicElements << R"YUL() { evm_resource(2) }
}
function evm_wire_add(a, b) -> n {
  if or(gt(a, )YUL"
      << limits.memoryBytes << "), gt(b, " << limits.memoryBytes
      << R"YUL()) { evm_resource(13) }
  n := add(a, b)
  if gt(n, )YUL"
      << limits.memoryBytes << R"YUL() { evm_resource(13) }
}
function evm_wire_mul(n, stride) -> bytes {
  // Bound before multiplication, even if n came from a 256-bit local lane.
  if gt(n, div()YUL"
      << limits.memoryBytes << R"YUL(, stride)) { evm_resource(13) }
  bytes := mul(n, stride)
}
function evm_wire_budget() -> p {
  p := evm_alloc(96) mstore(p, 0) mstore(add(p, 32), 0) mstore(add(p, 64), 0)
}
function evm_wire_node(p, depth) {
  if iszero(lt(depth, 64)) { evm_resource(13) }
  let nodes := add(mload(p), 1) evm_wire_count(nodes) mstore(p, nodes)
  // Conservative logical wrapper charge in addition to exact rounded storage.
  evm_wire_retain(p, 256)
}
function evm_wire_elements(p, n) {
  evm_wire_count(n)
  let total := add(mload(add(p, 32)), n) evm_wire_count(total)
  mstore(add(p, 32), total)
}
function evm_wire_retain(p, n) {
  if gt(n, )YUL"
      << limits.memoryBytes << R"YUL() { evm_resource(13) }
  let rounded := and(add(n, 31), not(31))
  let total := evm_wire_add(mload(add(p, 64)), rounded)
  mstore(add(p, 64), total)
}
function evm_wire_construct(p) {
  // The scanner's rounded retained estimate bounds every construction
  // allocation. Refuse before materializing a child if this invocation's
  // already retained memory leaves insufficient allocator capacity.
  if gt(mload(add(p, 64)), sub()YUL"
      << limits.memoryBytes << R"YUL(, p)) { evm_resource(13) }
}
function evm_wire_peak(p, wire) {
  let retained := mload(add(p, 64))
  let twice := evm_wire_mul(retained, 2)
  let observed := evm_wire_add(retained, evm_wire_mul(wire, 3))
  if or(gt(twice, )YUL"
      << limits.memoryBytes << "), gt(observed, " << limits.memoryBytes
      << R"YUL()) { evm_resource(13) }
}
function evm_wire_child(cursor, end) -> p, n, next {
  if gt(cursor, end) { evm_decode(2) }
  if lt(sub(end, cursor), 4) { evm_decode(2) }
  n := evm_le(cursor, 4) p := add(cursor, 4)
  if gt(n, sub(end, p)) { evm_decode(2) }
  next := add(p, n)
}
function evm_wire_header(p, tag) {
  mstore8(p, 90) mstore8(add(p, 1), 75) mstore8(add(p, 2), 67)
  mstore8(add(p, 3), 86) mstore8(add(p, 4), 0) mstore8(add(p, 5), tag)
}
)YUL";
  out << storage->text;
  return text;
}
} // namespace zkc::evm
