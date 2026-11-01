#include "Runtime.h"

namespace zkc::evm::detail {
std::string runtimeHelpers(const EvmLimits &limits) {
  // The fixed [0, 0x400) state is outside memoryguard's movable region.
  // 0x40 allocator; 0x80 active scope; 0xa0 transcript owner; 0xc0 generation;
  // 0xe0 draws; 0x100 remaining transitions; 0x120 chain digest;
  // 0x140 proof cursor; 0x160 proof end; 0x180 transcript scratch;
  // 0x1a0 reusable scope records; 0x1c0 scratch length; 0x1e0 root scope;
  // 0x200 memoryguard base; all other addresses are allocator-owned.
  std::string text = R"YUL(
function evm_fail(kind, code) {
  // Stable format-0 four-byte classes, followed by one bounded u256 code.
  // Source stop ZKCS, decode ZKCD, target fault ZKCT, resource refusal ZKCR.
  mstore(0, shl(224, kind)) mstore(4, code) revert(0, 36)
}
function evm_decode(code) { evm_fail(0x5a4b4344, code) }
function evm_fault(code) { evm_fail(0x5a4b4354, code) }
function evm_resource(code) { evm_fail(0x5a4b4352, code) }
function evm_source(code) { evm_fail(0x5a4b4353, code) }
function evm_prime() -> p {
  p := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
}
function evm_alloc(n) -> p {
  p := mload(0x40)
  if gt(n, @MEMORY@) { evm_resource(1) }
  let end := add(p, and(add(n, 31), not(31)))
  if or(lt(end, p), gt(end, @MEMORY@)) { evm_resource(1) }
  mstore(0x40, end)
}
function evm_memory(p, n) {
  if or(lt(p, mload(0x200)), gt(p, mload(0x40))) { evm_fault(1) }
  if gt(n, sub(mload(0x40), p)) { evm_fault(1) }
}
function evm_calldata(p, n) {
  if gt(p, calldatasize()) { evm_decode(1) }
  if gt(n, sub(calldatasize(), p)) { evm_decode(1) }
}
function evm_le(p, n) -> value {
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    value := or(value, shl(mul(i, 8), byte(0, mload(add(p, i)))))
  }
}
function evm_write_le(p, value, n) {
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    mstore8(add(p, i), shr(mul(i, 8), value))
  }
}
function evm_reverse(value) -> r {
  // Fixed-width byte reversal, not arithmetic field normalization.
  for { let i := 0 } lt(i, 32) { i := add(i, 1) } {
    r := or(shl(8, r), and(value, 255)) value := shr(8, value)
  }
}
function evm_index_add(a, b) -> r {
  r := add(a, b) if gt(r, 0xffffffffffffffff) { evm_source(1) }
}
function evm_index_sub(a, b) -> r {
  if gt(b, a) { evm_source(1) } r := sub(a, b)
}
function evm_index_mul(a, b) -> r {
  r := mul(a, b) if gt(r, 0xffffffffffffffff) { evm_source(1) }
}
function evm_index_div(a, b) -> r {
  if iszero(b) { evm_source(2) } r := div(a, b)
}
function evm_index_mod(a, b) -> r {
  if iszero(b) { evm_source(2) } r := mod(a, b)
}
function evm_index_shl(a, b) -> r {
  if gt(b, 63) { evm_source(3) }
  r := shl(b, a) if gt(r, 0xffffffffffffffff) { evm_source(1) }
}
function evm_index_shr(a, b) -> r {
  if gt(b, 63) { evm_source(3) } r := shr(b, a)
}
function evm_index_pow2(a) -> r {
  if gt(a, 63) { evm_source(3) } r := shl(a, 1)
}
function evm_index_power_of_two(n, r) -> yes {
  yes := and(lt(r, 64), eq(n, shl(r, 1)))
}
function evm_index_wrapping_add(a, b) -> r { r := and(add(a, b), 0xffffffffffffffff) }
function evm_index_wrapping_sub(a, b) -> r { r := and(sub(a, b), 0xffffffffffffffff) }
function evm_index_bit_and(a, b) -> r { r := and(a, b) }
function evm_index_logical_shift_right(a, b) -> r { r := shr(b, a) }
function evm_field_pow(a, n) -> r {
  r := 1
  for {} n { n := shr(1, n) } {
    if and(n, 1) { r := mulmod(r, a, evm_prime()) }
    a := mulmod(a, a, evm_prime())
  }
}
function evm_field_inverse(a) -> r {
  if iszero(a) { evm_source(2) }
  r := evm_field_pow(a, sub(evm_prime(), 2))
}
function evm_field_div(a, b) -> r {
  let inverse := evm_field_inverse(b) r := mulmod(a, inverse, evm_prime())
}
function evm_vector_alloc(n) -> p {
  if gt(n, @ELEMENTS@) { evm_resource(2) } p := evm_alloc(mul(n, 32))
}
function evm_vector_empty() -> p, n { p := evm_alloc(0) n := 0 }
function evm_vector_length(p, n) -> length {
  evm_memory(p, mul(n, 32)) length := n
}
function evm_vector_get(p, n, i) -> v {
  if iszero(lt(i, n)) { evm_source(4) }
  evm_memory(p, mul(n, 32)) v := mload(add(p, mul(i, 32)))
}
function evm_vector_set(p, n, i, v) {
  if iszero(lt(i, n)) { evm_fault(3) }
  evm_memory(p, mul(n, 32)) mstore(add(p, mul(i, 32)), v)
}
function evm_vector_append(p, n, v) -> out, length {
  length := evm_index_add(n, 1) out := evm_vector_alloc(length)
  evm_memory(p, mul(n, 32)) mcopy(out, p, mul(n, 32))
  mstore(add(out, mul(n, 32)), v)
}
function evm_vector_split(p, n) -> a, an, b, bn {
  if and(n, 1) { evm_source(5) }
  evm_memory(p, mul(n, 32)) a := p an := div(n, 2)
  b := add(p, mul(an, 32)) bn := an
}
function evm_vector_sum(p, n) -> r {
  evm_memory(p, mul(n, 32))
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    r := addmod(r, mload(add(p, mul(i, 32))), evm_prime())
  }
}
function evm_vector_equal(a, an, b, bn) -> r {
  r := eq(an, bn)
  evm_memory(a, mul(an, 32)) evm_memory(b, mul(bn, 32))
  if r {
    for { let i := 0 } lt(i, an) { i := add(i, 1) } {
      if iszero(eq(mload(add(a, mul(i, 32))), mload(add(b, mul(i, 32))))) {
        r := 0 break
      }
    }
  }
}
function evm_indices_empty() -> p, n { p := evm_alloc(0) n := 0 }
function evm_indices_append(p, n, value) -> out, length {
  if gt(n, 63) { evm_resource(3) }
  length := add(n, 1) out := evm_alloc(mul(length, 32))
  evm_memory(p, mul(n, 32)) mcopy(out, p, mul(n, 32))
  mstore(add(out, mul(n, 32)), value)
}
function evm_scope_root() -> root { root := mload(0x1e0) evm_scope_check(root) }
function evm_scope_current() -> scope { scope := mload(0x80) evm_scope_check(scope) }
function evm_scope_check(scope) {
  if or(iszero(scope), iszero(eq(scope, mload(0x80)))) { evm_fault(4) }
}
function evm_scope_enter(parent, generation) -> child {
  evm_scope_check(parent)
  child := mload(0x1a0)
  switch child
  case 0 { child := evm_alloc(64) }
  default { mstore(0x1a0, mload(child)) }
  mstore(child, parent) mstore(add(child, 32), 1)
  if iszero(eq(generation, 0xffffffffffffffff)) {
    if or(iszero(eq(generation, mload(0xc0))),
          iszero(eq(mload(0xa0), parent))) { evm_fault(5) }
    mstore(0xa0, child)
  }
  mstore(0x80, child)
}
function evm_scope_exit(child, generation) -> ticket {
  evm_scope_check(child)
  let parent := mload(child)
  if iszero(eq(generation, 0xffffffffffffffff)) {
    if or(iszero(eq(generation, mload(0xc0))),
          iszero(eq(mload(0xa0), child))) { evm_fault(5) }
    mstore(0xa0, parent)
  }
  if eq(mload(0xa0), child) { evm_fault(5) }
  mstore(0x80, parent)
  mstore(child, mload(0x1a0)) mstore(0x1a0, child)
  ticket := evm_transfer_make(parent)
}
function evm_transfer_make(scope) -> ticket {
  evm_scope_check(scope) ticket := evm_alloc(64)
  mstore(ticket, scope) mstore(add(ticket, 32), 1)
}
function evm_transfer_accept(scope, ticket) {
  evm_scope_check(scope) evm_memory(ticket, 64)
  if or(iszero(eq(mload(ticket), scope)), iszero(mload(add(ticket, 32)))) {
    evm_fault(6)
  }
  mstore(add(ticket, 32), 0)
}
function evm_transfer_release(ticket) {
  evm_memory(ticket, 64)
  if iszero(mload(add(ticket, 32))) { evm_fault(6) }
  mstore(add(ticket, 32), 0)
}
function evm_transfer_check(ticket) {
  evm_memory(ticket, 64)
  if or(iszero(eq(mload(ticket), mload(0x80))),
        iszero(mload(add(ticket, 32)))) { evm_fault(6) }
}
function evm_loop_bound(count, maximum) {
  if gt(count, maximum) { evm_source(6) }
}
function evm_range_check(a, b) {
  if iszero(eq(a, b)) { evm_source(5) }
}
function evm_range_admit(lower, upper) {
  // Exact native local-range admission, including the empty reversed range.
  if or(gt(lower, 1048576), gt(upper, 1048576)) { evm_resource(13) }
}
function evm_field_decode(p, n) -> v {
  if iszero(eq(n, 38)) { evm_decode(2) }
  if iszero(eq(shr(208, mload(p)), 0x5a4b43560001)) { evm_decode(3) }
  v := evm_reverse(mload(add(p, 6)))
  if iszero(lt(v, evm_prime())) { evm_decode(4) }
}
function evm_index_decode(p, n) -> v {
  if iszero(eq(n, 14)) { evm_decode(2) }
  if iszero(eq(shr(208, mload(p)), 0x5a4b4356001f)) { evm_decode(3) }
  v := evm_le(add(p, 6), 8)
}
function evm_bool_decode(p, n) -> v {
  if iszero(eq(n, 7)) { evm_decode(2) }
  if iszero(eq(shr(208, mload(p)), 0x5a4b43560005)) { evm_decode(3) }
  v := byte(0, mload(add(p, 6))) if gt(v, 1) { evm_decode(4) }
}
function evm_vector_decode(p, n) -> out, length {
  if lt(n, 10) { evm_decode(2) }
  if iszero(eq(shr(208, mload(p)), 0x5a4b43560042)) { evm_decode(3) }
  length := evm_le(add(p, 6), 4)
  if iszero(eq(n, add(10, mul(length, 32)))) { evm_decode(2) }
  out := evm_vector_alloc(length)
  for { let i := 0 } lt(i, length) { i := add(i, 1) } {
    let v := evm_reverse(mload(add(add(p, 10), mul(i, 32))))
    if iszero(lt(v, evm_prime())) { evm_decode(4) }
    mstore(add(out, mul(i, 32)), v)
  }
}
function evm_proof_receive() -> value {
  let p := mload(0x140) let end := mload(0x160)
  if lt(sub(end, p), 8) { evm_decode(5) }
  let n := evm_le(p, 8) p := add(p, 8)
  if gt(n, @FRAME@) { evm_resource(4) }
  if gt(n, sub(end, p)) { evm_decode(5) }
  value := evm_field_decode(p, n) mstore(0x140, add(p, n))
}
function evm_tree_header(p, tag, n) -> end {
  mstore8(p, tag) evm_write_le(add(p, 1), n, 8) end := add(p, 9)
}
function evm_tree_hex(p, source, n) -> end {
  end := evm_tree_header(p, 0, mul(n, 2))
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    let b := byte(0, mload(add(source, i)))
    mstore8(end, byte(shr(4, b), "0123456789abcdef"))
    mstore8(add(end, 1), byte(and(b, 15), "0123456789abcdef"))
    end := add(end, 2)
  }
}
function evm_tree_natural(p, value) -> end {
  let digits := 1 let rest := div(value, 10)
  for {} rest { rest := div(rest, 10) } { digits := add(digits, 1) }
  end := evm_tree_header(p, 0, digits)
  for { let i := digits } i {} {
    i := sub(i, 1) mstore8(add(end, i), add(48, mod(value, 10)))
    value := div(value, 10)
  }
  end := add(end, digits)
}
function evm_abi_tail(p, cap) -> memory, length, next {
  evm_calldata(p, 32) length := calldataload(p)
  if gt(length, cap) { evm_resource(5) }
  let padded := and(add(length, 31), not(31))
  // length <= frozen cap makes the padding addition nonwrapping.
  let data := add(p, 32) evm_calldata(data, padded)
  for { let i := length } lt(i, padded) { i := add(i, 1) } {
    if byte(0, calldataload(add(data, i))) { evm_decode(6) }
  }
  memory := evm_alloc(length) calldatacopy(memory, data, length)
  next := add(data, padded)
}
function evm_sha256(p, n) -> digest {
  let out := evm_alloc(32)
  if iszero(staticcall(gas(), 2, p, n, out, 32)) { evm_fault(7) }
  if iszero(eq(returndatasize(), 32)) { evm_fault(7) }
  digest := mload(out) mstore(0x40, out)
}
function evm_scratch_begin() -> p { p := mload(0x180) mstore(0x1c0, 0) }
function evm_scratch_bytes(source, n) {
  let length := mload(0x1c0)
  if gt(n, sub(8192, length)) { evm_resource(6) }
  mcopy(add(mload(0x180), length), source, n) mstore(0x1c0, add(length, n))
}
function evm_scratch_word(value, n) {
  let length := mload(0x1c0)
  if gt(n, sub(8192, length)) { evm_resource(6) }
  mstore(add(mload(0x180), length), shl(mul(sub(32, n), 8), value))
  mstore(0x1c0, add(length, n))
}
function evm_scratch_frame(tag, label, labelLength, data, n) {
  evm_scratch_word(tag, 1) evm_scratch_word(labelLength, 8)
  evm_scratch_word(label, labelLength) evm_scratch_word(n, 8)
  evm_scratch_bytes(data, n)
}
function evm_absorb(tag, label, labelLength, data, n) {
  let p := evm_scratch_begin()
  // ASCII bytes with the terminal NUL included in the explicit length.
  mstore(p, "zkc.hash-chain.absorb/0") mstore(0x1c0, 24)
  evm_scratch_word(mload(0x120), 32)
  evm_scratch_frame(tag, label, labelLength, data, n)
  let next := keccak256(p, mload(0x1c0))
  verbatim_1i_0o(hex"50", next)
  mstore(0x120, next)
}
function evm_transcript_debit(scope, generation) -> next {
  evm_scope_check(scope)
  if or(iszero(eq(scope, mload(0xa0))), iszero(eq(generation, mload(0xc0)))) {
    evm_fault(5)
  }
  if or(eq(generation, 0xffffffffffffffff),
        eq(mload(0xe0), 0xffffffffffffffff)) { evm_resource(7) }
  next := add(generation, 1)
  let draws := add(mload(0xe0), 1)
  mstore(0xc0, next) mstore(0xe0, draws)
  if eq(next, 0xffffffffffffffff) { evm_resource(7) }
  let budget := mload(0x100)
  if iszero(budget) { evm_resource(8) }
  mstore(0x100, sub(budget, 1))
}
function evm_transcript_observe(scope, generation, value, occurrenceData, originLength)
  -> next {
  next := evm_transcript_debit(scope, generation)
  evm_absorb(1, 0x6f726967696e, 6, occurrenceData, originLength)
  let frame := evm_alloc(64)
  mstore(frame, shl(208, 0x5a4b43560001))
  mstore(add(frame, 6), evm_reverse(value))
  evm_absorb(1, 0x76616c7565, 5, frame, 38)
  mstore(0x40, frame)
}
function evm_transcript_challenge(scope, generation, occurrenceData, originLength)
  -> value, next {
  next := evm_transcript_debit(scope, generation)
  evm_absorb(1, 0x6f726967696e, 6, occurrenceData, originLength)
  let p := evm_scratch_begin()
  mstore(p, "zkc.hash-chain.request/0") mstore(0x1c0, 25)
  evm_scratch_word(mload(0x120), 32)
  let lengthData := evm_alloc(32) mstore(lengthData, shl(192, 64))
  evm_scratch_frame(2, 0x6368616c6c656e6765, 9, lengthData, 8)
  evm_scratch_word(0, 8)
  let n := mload(0x1c0)
  let high := keccak256(p, n)
  verbatim_1i_0o(hex"50", high)
  mstore(add(p, sub(n, 8)), shl(192, 1))
  let low := keccak256(p, n)
  verbatim_1i_0o(hex"50", low)
  // Full 512-bit reduction. 2^256 mod p is computed without overflowing.
  let radix := addmod(mod(not(0), evm_prime()), 1, evm_prime())
  value := addmod(mulmod(high, radix, evm_prime()), mod(low, evm_prime()), evm_prime())
  evm_absorb(2, 0x6368616c6c656e6765, 9, lengthData, 8)
  mstore(0x40, lengthData)
}
)YUL";
  auto replace = [&](llvm::StringRef key, uint64_t value) {
    size_t pos = 0;
    std::string replacement = std::to_string(value);
    while ((pos = text.find(key.str(), pos)) != std::string::npos) {
      text.replace(pos, key.size(), replacement);
      pos += replacement.size();
    }
  };
  replace("@MEMORY@", limits.memoryBytes);
  replace("@ELEMENTS@", limits.publicElements);
  replace("@FRAME@", limits.frameBytes);
  return text;
}
} // namespace zkc::evm::detail
