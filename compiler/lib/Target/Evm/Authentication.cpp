#include "Authentication.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Wire.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
Expected<KeccakRows> realizeKeccakRows(NativeLayouts &layouts, Type type) {
  auto root = dyn_cast_if_present<commitment::VectorObjectType>(type);
  const auto *scheme =
      root ? protocol::instances::domain(root.getScheme()) : nullptr;
  if (!root || root.getKind() != "commitment" || !scheme ||
      !scheme->commitment ||
      scheme->commitment->scheme !=
          protocol::instances::CommitmentScheme::Keccak256Rows ||
      scheme->commitment->digestBytes != 32)
    return zkc::error("evm.authentication",
                      "requires installed 32-byte Keccak rows");
  auto domain = protocol::installedDomains().associatedIdentity(
      root.getScheme(), "ValueField");
  auto field =
      layouts.field(algebra::FieldType::get(type.getContext(), domain));
  if (!field)
    return field.takeError();
  const auto &f = **field;
  // These are the sealed Element implementations in plonky3/oracle.rs. A new
  // installed hash scheme or field does not silently acquire this byte law.
  if (f.base.getDomain() != "koala-bear" ||
      !is_contained({1u, 4u, 8u}, f.degree) ||
      (f.degree != 1 && f.beta != APInt(256, 3)))
    return zkc::error("evm.authentication",
                      "unsupported Keccak element byte law");
  StringRef leafCodec;
  if (domain == "koala-bear" && f.degree == 1)
    leafCodec = "koala-bear.canonical-u32le/0";
  else if (domain == "koala-bear.ext4-binomial3" && f.degree == 4)
    leafCodec = "koala-bear.ext4-binomial3.ascending-u32le/0";
  else if (domain == "koala-bear.ext8-binomial3" && f.degree == 8)
    leafCodec = "koala-bear.ext8-binomial3.ascending-u32le/0";
  else
    return zkc::error("evm.authentication",
                      "no native sealed Element codec law");
  auto *codec = protocol::installedDomains().defaultCodec("field", domain);
  auto *rootCodec =
      protocol::installedDomains().defaultCodec("commitment", root.getScheme());
  auto *pathCodec =
      protocol::installedDomains().defaultCodec("proof", root.getScheme());
  auto *element = codec ? protocol::instances::codec(codec->identity) : nullptr;
  auto *r =
      rootCodec ? protocol::instances::codec(rootCodec->identity) : nullptr;
  auto *p =
      pathCodec ? protocol::instances::codec(pathCodec->identity) : nullptr;
  if (!element || !element->frame ||
      element->frame->elementBytes != 4 * f.degree || !r || !r->frame || !p ||
      !p->frame)
    return zkc::error("evm.authentication",
                      "missing canonical element/root/path codecs");
  if (auto error = verifyWireType(layouts, type))
    return std::move(error);
  if (auto error = verifyWireType(
          layouts, commitment::VectorObjectType::get(
                       type.getContext(), root.getScheme(), "proof")))
    return std::move(error);
  // Element::CODEC in the native tree is distinct from the catalog's zkcv
  // envelope codec identity. Bind exactly the former in the leaf preimage.
  return KeccakRows{*field, leafCodec.str(), r->frame->tag, p->frame->tag};
}
namespace detail {
std::string Authentication::helpers() const {
  std::string result;
  for (const auto &[name, body] : definitions)
    result += body;
  return result;
}
Expected<std::string> Authentication::helper(Operation *op) {
  if (!isa<OracleCheckOp>(op) || failed(verify(op)))
    return zkc::error("evm.authentication",
                      "requires checked row authentication");
  auto rows = realizeKeccakRows(
      layouts, op->getAttrOfType<TypeAttr>("value_type").getValue());
  if (!rows)
    return rows.takeError();
  const auto &f = *rows->field;
  std::string name = "evm_keccak_row_" + std::to_string(f.degree) + "_" +
                     toHex(rows->codec, true) + "_" +
                     std::to_string(rows->rootTag) + "_" +
                     std::to_string(rows->pathTag);
  if (definitions.count(name))
    return name;
  // Exact prefixes/byte law: crates/zkc-kernels/src/plonky3/oracle.rs,
  // LeafHash::new/hash_iter and NodeHash::compress, including terminal NULs.
  constexpr auto leafTag =
      StringLiteral::withInnerNUL("zkc.oracle.keccak256.leaf/0\0");
  constexpr auto nodeTag =
      StringLiteral::withInnerNUL("zkc.oracle.keccak256.node/0\0");
  const uint64_t header = leafTag.size() + 8 + rows->codec.size() + 16;
  std::string body;
  raw_string_ostream out(body);
  out << "function " << name
      << "(root, rootBytes, width, height, position, row, count, path, "
         "pathBytes) -> valid {\n"
      // A bool is a stack result; it has no target backing allocation. The
      // native scalar-output preflight has no additional EVM storage charge.
      << "if or(or(iszero(width), iszero(height)), gt(height, 16777216)) { "
         "evm_source(10) }\n"
      // Division preserves native checked multiplication/element-limit order
      // without overflowing a 64-bit or 256-bit product.
      << "if gt(width, div(1048576, height)) { evm_resource(16) }\n"
      << "if iszero(lt(position, height)) { evm_source(11) }\n"
      << "if gt(count, " << limits.publicElements << ") { evm_resource(2) }\n"
      << "evm_memory(root, rootBytes) evm_memory(path, pathBytes)\n"
      << "evm_memory(row, mul(count, " << f.coefficientBytes()
      << "))\n"
      // Complete envelopes have already passed native decode at ingress.
      // These checks defend target layout invariants, not a second decoder.
      << "if iszero(eq(rootBytes, 38)) { evm_fault(9) }\n"
      << "if lt(pathBytes, 10) { evm_fault(9) }\n"
      << "if or(iszero(eq(evm_le(root, 5), 0x56434b5a)), "
         "iszero(eq(byte(0,mload(add(root,5))), "
      << rows->rootTag << "))) { evm_fault(9) }\n"
      << "if or(iszero(eq(evm_le(path, 5), 0x56434b5a)), "
         "iszero(eq(byte(0,mload(add(path,5))), "
      << rows->pathTag << "))) { evm_fault(9) }\n"
      << "let siblings := evm_le(add(path,6),4)\n"
      << "if iszero(eq(pathBytes, add(10,mul(siblings,32)))) { evm_fault(9) }\n"
      << "if gt(siblings, " << limits.pathSiblings << ") { evm_resource(14) }\n"
      << "let depth := 0 for { let n := sub(height,1) } n { n := shr(1,n) } { "
         "depth := add(depth,1) }\n"
      << "if iszero(eq(count,width)) { leave }\n"
      << "if iszero(eq(siblings,depth)) { leave }\n"
      << "let length := add(" << header << ",mul(count," << 4 * f.degree
      << "))\n"
      << "let capacity := length if lt(capacity," << nodeTag.size() + 64
      << ") { capacity := " << nodeTag.size() + 64
      << " }\n"
      // Reserve all hash staging before the first ordered crypto operation.
      << "let scratch := evm_alloc(capacity)\n"
      << "mstore(scratch, \"zkc.oracle.keccak256.leaf/0\")\n"
      << "evm_write_le(add(scratch," << leafTag.size() << "),"
      << rows->codec.size() << ",8)\n";
  // Codec strings can exceed one Yul word. Exact literal chunks avoid a new
  // static-data representation and keep the installed identity authoritative.
  for (size_t offset = 0; offset < rows->codec.size(); offset += 32) {
    auto chunk = StringRef(rows->codec).substr(offset, 32);
    out << "mstore(add(scratch," << leafTag.size() + 8 + offset << "),0x"
        << toHex(chunk, true) << std::string((32 - chunk.size()) * 2, '0')
        << ")\n";
  }
  out << "evm_write_le(add(scratch," << header - 16 << "),width,8)\n"
      << "evm_write_le(add(scratch," << header - 8 << "),height,8)\n"
      << "for { let i := 0 } lt(i,mul(count," << f.degree
      << ")) { i := add(i,1) } {\n"
      << "let coefficient := mload(add(row,mul(i,32)))\n"
      << "if iszero(lt(coefficient," << f.modulus.getZExtValue()
      << ")) { evm_fault(9) }\n"
      << "evm_write_le(add(add(scratch," << header
      << "),mul(i,4)),coefficient,4) }\n"
      << "let digest := keccak256(scratch,length)\n"
      << "verbatim_1i_0o(hex\"50\",digest)\n"
      << "for { let i := 0 } lt(i,depth) { i := add(i,1) } {\n"
      << "let sibling := mload(add(add(path,10),mul(i,32)))\n"
      << "mstore(scratch, \"zkc.oracle.keccak256.node/0\")\n"
      << "let left := digest let right := sibling\n"
      << "if and(shr(i,position),1) { left := sibling right := digest }\n"
      << "mstore(add(scratch," << nodeTag.size() << "),left)\n"
      << "mstore(add(scratch," << nodeTag.size() + 32 << "),right)\n"
      << "digest := keccak256(scratch," << nodeTag.size() + 64 << ")\n"
      << "verbatim_1i_0o(hex\"50\",digest) }\n"
      << "valid := eq(digest,mload(add(root,6)))\n"
      << "mstore(0x40,scratch)\n}\n";
  definitions.emplace(name, std::move(body));
  return name;
}
} // namespace detail
} // namespace zkc::evm
