#include "zkc/Target/Evm/Curve.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallString.h"

using namespace llvm;
namespace zkc::evm {
namespace {
APInt baseModulus() {
  return APInt(384,
               "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f62"
               "41eabfffeb153ffffb9feffffffffaaab",
               16);
}
APInt subgroupOrder() {
  return APInt(
      256, "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
      16);
}
std::string word(const APInt &value) {
  SmallString<100> text;
  value.toStringUnsigned(text, 16);
  return "0x" + text.str().str();
}
} // namespace
Expected<GroupLayout> realizeGroup(algebra::GroupType type) {
  const auto &catalog = protocol::installedDomains();
  if (!type || type.getDomain() != "bls12-381.g1" ||
      !catalog.hasFact("Group", {type.getDomain().str()}) ||
      !catalog.hasFact("ScalarAction", {type.getDomain().str()}) ||
      catalog.associatedIdentity(type.getDomain(), "Scalar") !=
          "bls12-381.fr" ||
      !catalog.hasFact("PrimeField", {"bls12-381.fr"}))
    return zkc::error(
        "evm.group",
        "requires the supported BLS12-381 G1 ScalarAction adapter");
  const auto *scalar = catalog.domain("bls12-381.fr");
  APInt modulus;
  // This is also the EIP-2537 subgroup order, not its base-field modulus.
  APInt order = subgroupOrder();
  if (!scalar || StringRef(scalar->modulus).getAsInteger(10, modulus) ||
      modulus.getActiveBits() > 256 || modulus.zextOrTrunc(256) != order)
    return zkc::error(
        "evm.group",
        "installed Scalar differs from the adapter subgroup order");
  const auto *selected = catalog.defaultCodec("group", type.getDomain());
  const auto *codec =
      selected ? protocol::instances::codec(selected->identity) : nullptr;
  const auto *tag = codec && codec->frame
                        ? protocol::instances::frameTag(codec->frame->tag)
                        : nullptr;
  if (!codec || codec->identity != "zkcv.group.bls12-381.g1/0" ||
      codec->kind != "group" || codec->domain != type.getDomain() || !tag ||
      tag->layout != protocol::instances::FrameLayout::Scalar ||
      codec->frame->elementBytes != GroupLayout::compressedBytes ||
      codec->frame->bytes || codec->frame->bytesPerArity)
    return zkc::error(
        "evm.group-codec",
        "requires the exact installed native BLS G1 compressed codec");
  GroupLayout result;
  result.type = type;
  result.scalar = algebra::FieldType::get(type.getContext(), "bls12-381.fr");
  result.scalarModulus = order;
  result.baseModulus = baseModulus();
  result.frameTag = codec->frame->tag;
  return result;
}

Error verifyGroupFork(EvmFork fork) {
  switch (fork) {
  case EvmFork::Prague:
  case EvmFork::Osaka:
    return Error::success();
  default:
    return zkc::error("evm.group-fork",
                      "BLS12-381 G1 requires Prague or Osaka EIP-2537");
  }
}

namespace detail {
std::string curveHelpers() {
  // EIP-2537 (https://eips.ethereum.org/EIPS/eip-2537), native
  // ark-bls12-381 0.6.0 curves/{g1,util}.rs and the exact-reencoding wrapper in
  // crates/zkc-kernels/src/arkworks/codec.rs define this physical adapter.
  std::string text = R"YUL(
function evm_g1_ph() -> h { h := @PH@ }
function evm_g1_pl() -> l { l := @PL@ }
function evm_g1_less(ah, al, bh, bl) -> yes {
  yes := or(lt(ah, bh), and(eq(ah, bh), lt(al, bl)))
}
function evm_g1_coordinate(h, l) -> yes {
  yes := evm_g1_less(h, l, evm_g1_ph(), evm_g1_pl())
}
function evm_g1_negative(h, l) -> nh, nl {
  // Inputs are canonical two-word Fp values. Subtract the low word with borrow.
  nh := sub(sub(evm_g1_ph(), h), lt(evm_g1_pl(), l))
  nl := sub(evm_g1_pl(), l)
  if iszero(or(h, l)) { nh := 0 nl := 0 }
}
function evm_g1_sign(h, l) -> sign {
  let nh, nl := evm_g1_negative(h, l)
  sign := evm_g1_less(nh, nl, h, l)
}
function evm_g1_equal(a, b) -> yes {
  evm_g1_affine(a) evm_g1_affine(b)
  yes := and(and(eq(mload(a), mload(b)), eq(mload(add(a, 32)), mload(add(b, 32)))),
             and(eq(mload(add(a, 64)), mload(add(b, 64))), eq(mload(add(a, 96)), mload(add(b, 96)))))
}
function evm_g1_coordinates(a) -> yes {
  evm_memory(a, 128)
  yes := and(evm_g1_coordinate(mload(a), mload(add(a, 32))),
             evm_g1_coordinate(mload(add(a, 64)), mload(add(a, 96))))
}
function evm_g1_affine(a) {
  if iszero(evm_g1_coordinates(a)) { evm_fault(30) }
}
function evm_g1_output(a) {
  if iszero(evm_g1_coordinates(a)) { evm_fault(32) }
}
function evm_g1_fund(cost) {
  // Called after input/output memory expansion. Cover EIP-150 rounding and
  // at least 5000 gas of call setup, cold-address cost and refusal headroom.
  // Underfunding is a resource refusal, never an invalid point.
  if lt(gas(), add(add(cost, div(add(cost, 62), 63)), 5000)) { evm_resource(30) }
}
function evm_g1_return(ok, actual, expected, decoding, fault) {
  if iszero(ok) {
    if actual { evm_fault(fault) }
    if decoding { evm_decode(4) }
    evm_fault(fault)
  }
  if iszero(eq(actual, expected)) { evm_fault(fault) }
}
function evm_g1_modexp(ah, al, eh, el) -> rh, rl {
  // Fixed 48-byte base/exponent/modulus. 65536 exceeds both EIP-2565 and
  // EIP-7883 tariffs for these lengths (including the sqrt exponent). It is
  // unrelated to the scalar inverse helper, whose operands are only 32 bytes.
  let scratch := evm_alloc(304)
  mstore(scratch, 48) mstore(add(scratch, 32), 48) mstore(add(scratch, 64), 48)
  mstore(add(scratch, 96), shl(128, ah)) mstore(add(scratch, 112), al)
  mstore(add(scratch, 144), shl(128, eh)) mstore(add(scratch, 160), el)
  mstore(add(scratch, 192), shl(128, evm_g1_ph())) mstore(add(scratch, 208), evm_g1_pl())
  let result := add(scratch, 240)
  mstore(result, 0) mstore(add(result, 32), 0)
  evm_g1_fund(65536)
  let ok := staticcall(65536, 5, scratch, 240, add(result, 16), 48)
  evm_g1_return(ok, returndatasize(), 48, 0, 31)
  rh := mload(result) rl := mload(add(result, 32))
  if iszero(evm_g1_coordinate(rh, rl)) { evm_fault(31) }
  mstore(0x40, scratch)
}
function evm_g1_rhs(xh, xl) -> h, l {
  h, l := evm_g1_modexp(xh, xl, 0, 3)
  let low := add(l, 4)
  h := add(h, lt(low, l)) l := low
  if iszero(evm_g1_coordinate(h, l)) {
    h := sub(sub(h, evm_g1_ph()), lt(l, evm_g1_pl()))
    l := sub(l, evm_g1_pl())
  }
}
function evm_g1_msm(input, out, decoding) {
  // Exact one-term EIP-2537 MSM, also used for subgroup admission with scalar 1.
  evm_g1_fund(12000)
  let ok := staticcall(12000, 0x0c, input, 160, out, 128)
  // A missing precompile can report success with empty return data.
  evm_g1_return(ok, returndatasize(), 128, decoding, 32)
  evm_g1_output(out)
}
function evm_g1_subgroup(point) {
  let scratch := evm_alloc(288)
  mcopy(scratch, point, 128) mstore(add(scratch, 128), 1)
  let output := add(scratch, 160)
  mstore(output, 0) mstore(add(output, 32), 0)
  mstore(add(output, 64), 0) mstore(add(output, 96), 0)
  evm_g1_msm(scratch, output, 1)
  if iszero(evm_g1_equal(point, output)) { evm_fault(32) }
  mstore(0x40, scratch)
}
function evm_g1_decode(p) -> point {
  // Caller admits the exact 48-byte payload inside its native frame.
  evm_memory(p, 48)
  let flags := byte(0, mload(p))
  if iszero(and(flags, 0x80)) { evm_decode(4) }
  let xh := and(shr(128, mload(p)), 0x1fffffffffffffffffffffffffffffff)
  let xl := mload(add(p, 16))
  if iszero(evm_g1_coordinate(xh, xl)) { evm_decode(4) }
  point := evm_alloc(128)
  mstore(point, xh) mstore(add(point, 32), xl)
  mstore(add(point, 64), 0) mstore(add(point, 96), 0)
  if and(flags, 0x40) {
    if or(or(xh, xl), and(flags, 0x20)) { evm_decode(4) }
    leave
  }
  let h, l := evm_g1_rhs(xh, xl)
  // (p+1)/4 as a full 384-bit exponent, not an EVM-word shift of p.
  let yh, yl := evm_g1_modexp(h, l,
      @SQH@, @SQL@)
  let squareh, squarel := evm_g1_modexp(yh, yl, 0, 2)
  if iszero(and(eq(squareh, h), eq(squarel, l))) { evm_decode(4) }
  let sign := iszero(iszero(and(flags, 0x20)))
  if iszero(eq(evm_g1_sign(yh, yl), sign)) { yh, yl := evm_g1_negative(yh, yl) }
  // Reject a sign alias for y=0 as well as every noncanonical flag combination.
  if iszero(eq(evm_g1_sign(yh, yl), sign)) { evm_decode(4) }
  mstore(add(point, 64), yh) mstore(add(point, 96), yl)
  evm_g1_subgroup(point)
}
function evm_g1_encode(p, point) {
  evm_g1_affine(point)
  let xh := mload(point) let xl := mload(add(point, 32))
  let yh := mload(add(point, 64)) let yl := mload(add(point, 96))
  // Write exactly 48 bytes. mcopy prevents an unaligned mstore from corrupting
  // the next child in a nested frame.
  mcopy(p, add(point, 16), 48)
  let flags := or(0x80, shl(5, evm_g1_sign(yh, yl)))
  if iszero(or(or(xh, xl), or(yh, yl))) { flags := 0xc0 }
  mstore8(p, or(byte(0, mload(p)), flags))
}
function evm_g1_add(a, b) -> result {
  evm_g1_affine(a) evm_g1_affine(b)
  result := evm_alloc(128)
  let scratch := evm_alloc(256)
  mcopy(scratch, a, 128) mcopy(add(scratch, 128), b, 128)
  mstore(result, 0) mstore(add(result, 32), 0)
  mstore(add(result, 64), 0) mstore(add(result, 96), 0)
  evm_g1_fund(375)
  let ok := staticcall(375, 0x0b, scratch, 256, result, 128)
  evm_g1_return(ok, returndatasize(), 128, 0, 32)
  evm_g1_output(result)
  mstore(0x40, scratch)
}
function evm_g1_scale(a, scalar) -> result {
  evm_g1_affine(a)
  if iszero(lt(scalar, @ORDER@)) { evm_fault(30) }
  result := evm_alloc(128)
  let scratch := evm_alloc(160)
  mcopy(scratch, a, 128) mstore(add(scratch, 128), scalar)
  mstore(result, 0) mstore(add(result, 32), 0)
  mstore(add(result, 64), 0) mstore(add(result, 96), 0)
  evm_g1_msm(scratch, result, 0)
  mstore(0x40, scratch)
}
)YUL";
  auto replace = [&](StringRef marker, const APInt &value) {
    text.replace(text.find(marker.str()), marker.size(), word(value));
  };
  auto p = baseModulus();
  auto exponent = (p + 1).lshr(2);
  replace("@PH@", p.lshr(256).trunc(256));
  replace("@PL@", p.trunc(256));
  replace("@SQH@", exponent.lshr(256).trunc(256));
  replace("@SQL@", exponent.trunc(256));
  replace("@ORDER@", subgroupOrder());
  return text;
}
} // namespace detail
} // namespace zkc::evm
