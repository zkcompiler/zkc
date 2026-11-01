#include "Arithmetic.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>

using namespace llvm;
using namespace mlir;
namespace zkc::evm::detail {
namespace {
std::string word(const APInt &value) {
  SmallString<80> result;
  value.toStringUnsigned(result, 16);
  return "0x" + result.str().str();
}
std::string commonHelpers() {
  return R"YUL(
function evm_math_zero(ptr, words) {
    for { let i := 0 } lt(i, words) { i := add(i, 1) } {
        mstore(add(ptr, mul(i, 32)), 0)
    }
}
function evm_math_get(ptr, i) -> value { value := mload(add(ptr, mul(i, 32))) }
function evm_math_set(ptr, i, value) { mstore(add(ptr, mul(i, 32)), value) }
function evm_math_base_power(a, n, p) -> r {
    r := 1
    for {} n { n := shr(1, n) } {
        if and(n, 1) { r := mulmod(r, a, p) }
        a := mulmod(a, a, p)
    }
}
function evm_math_base_inverse(a, p) -> r {
    // Source failure must happen before allocation and before any precompile.
    if iszero(a) { evm_source(2) }
    let scratch := evm_alloc(192)
    mstore(scratch, 32)
    mstore(add(scratch, 32), 32)
    mstore(add(scratch, 64), 32)
    mstore(add(scratch, 96), a)
    mstore(add(scratch, 128), sub(p, 2))
    mstore(add(scratch, 160), p)
    if iszero(staticcall(gas(), 5, scratch, 192, scratch, 32)) { evm_fault(7) }
    if iszero(eq(returndatasize(), 32)) { evm_fault(7) }
    r := mload(scratch)
    if or(iszero(lt(r, p)), iszero(eq(mulmod(a, r, p), 1))) { evm_fault(7) }
    // r is an SSA word. No pointer into scratch escapes this function.
    mstore(0x40, scratch)
}
function evm_math_extension_nonzero(a, d) {
    let anyCoefficient := 0
    for { let i := 0 } lt(i, d) { i := add(i, 1) } {
        anyCoefficient := or(anyCoefficient, evm_math_get(a, i))
    }
    if iszero(anyCoefficient) { evm_source(2) }
}
function evm_math_extension_multiply(a, b, d, nonresidue, p) -> out {
    out := evm_alloc(mul(d, 32))
    evm_math_zero(out, d)
    for { let i := 0 } lt(i, d) { i := add(i, 1) } {
        for { let j := 0 } lt(j, d) { j := add(j, 1) } {
            let k := add(i, j)
            let v := mulmod(evm_math_get(a, i), evm_math_get(b, j), p)
            if iszero(lt(k, d)) { k := sub(k, d) v := mulmod(v, nonresidue, p) }
            evm_math_set(out, k, addmod(evm_math_get(out, k), v, p))
        }
    }
}
// Bounded polynomial extended Euclid. r = a*t and s = a*u modulo f.
// Two degree-(<=d) remainders and two degree-(<d) Bezout residues are enough.
function evm_math_polynomial_length(ptr, length) -> result {
    result := length
    for {} result {} {
        if evm_math_get(ptr, sub(result, 1)) { break }
        result := sub(result, 1)
    }
}
function evm_math_polynomial_cancel(r, t, s, u, shift, factor, length, d, nonresidue, p) {
    for { let j := 0 } lt(j, length) { j := add(j, 1) } {
        let k := add(j, shift)
        evm_math_set(r, k, addmod(evm_math_get(r, k), sub(p, mulmod(factor, evm_math_get(s, j), p)), p))
    }
    // t <- t - factor*X^shift*u modulo f. shift <= d-1; at most one wrap.
    for { let j := 0 } lt(j, d) { j := add(j, 1) } {
        let k := add(j, shift)
        let value := mulmod(factor, evm_math_get(u, j), p)
        if iszero(lt(k, d)) { k := sub(k, d) value := mulmod(value, nonresidue, p) }
        evm_math_set(t, k, addmod(evm_math_get(t, k), sub(p, value), p))
    }
}
function evm_math_extension_inverse(a, d, nonresidue, p) -> out {
    evm_math_extension_nonzero(a, d)
    out := evm_alloc(mul(d, 32))
    let scratch := mload(0x40)
    let r := evm_alloc(mul(add(d, 1), 32))
    let s := evm_alloc(mul(add(d, 1), 32))
    let t := evm_alloc(mul(d, 32))
    let u := evm_alloc(mul(d, 32))
    evm_math_zero(r, add(d, 1)) evm_math_zero(s, add(d, 1))
    evm_math_zero(t, d) evm_math_zero(u, d)
    evm_math_set(r, 0, sub(p, nonresidue)) evm_math_set(r, d, 1)
    for { let i := 0 } lt(i, d) { i := add(i, 1) } { evm_math_set(s, i, evm_math_get(a, i)) }
    evm_math_set(u, 0, 1)
    let rLength := add(d, 1)
    let sLength := evm_math_polynomial_length(s, d)
    for { let round := 0 } and(gt(sLength, 1), lt(round, d)) { round := add(round, 1) } {
        let inverse := evm_math_base_inverse(evm_math_get(s, sub(sLength, 1)), p)
        for { let step := 0 } and(iszero(lt(rLength, sLength)), lt(step, add(d, 1)))
            { step := add(step, 1) } {
            let oldLength := rLength
            let factor := mulmod(evm_math_get(r, sub(rLength, 1)), inverse, p)
            evm_math_polynomial_cancel(r, t, s, u, sub(rLength, sLength), factor, sLength, d, nonresidue, p)
            rLength := evm_math_polynomial_length(r, rLength)
            if iszero(lt(rLength, oldLength)) { evm_fault(8) }
        }
        if iszero(lt(rLength, sLength)) { evm_fault(8) }
        let saved := r r := s s := saved
        saved := t t := u u := saved
        saved := rLength rLength := sLength sLength := saved
        if iszero(sLength) { evm_fault(8) }
    }
    if iszero(eq(sLength, 1)) { evm_fault(8) }
    let scale := evm_math_base_inverse(evm_math_get(s, 0), p)
    for { let i := 0 } lt(i, d) { i := add(i, 1) } {
        evm_math_set(out, i, mulmod(evm_math_get(u, i), scale, p))
    }
    // out was allocated before scratch; no input or scratch pointer escapes.
    mstore(0x40, scratch)
}

function evm_math_field_memory(a, d, p) {
  evm_memory(a, mul(d, 32))
  for { let i := 0 } lt(i, d) { i := add(i, 1) } {
    if iszero(lt(evm_math_get(a, i), p)) { evm_fault(9) }
  }
}
function evm_math_extension_power(a, n, d, beta, p) -> out {
  out := evm_alloc(mul(d, 32))
  let scratch := mload(0x40)
  let accumulator := evm_alloc(mul(d, 32))
  let power := evm_alloc(mul(d, 32))
  evm_math_zero(accumulator, d) evm_math_set(accumulator, 0, 1)
  mcopy(power, a, mul(d, 32))
  let temporary := mload(0x40)
  for {} n { n := shr(1, n) } {
    if and(n, 1) {
      let product := evm_math_extension_multiply(accumulator, power, d, beta, p)
      mcopy(accumulator, product, mul(d, 32)) mstore(0x40, temporary)
    }
    let square := evm_math_extension_multiply(power, power, d, beta, p)
    mcopy(power, square, mul(d, 32)) mstore(0x40, temporary)
  }
  mcopy(out, accumulator, mul(d, 32)) mstore(0x40, scratch)
}
)YUL";
}
} // namespace
struct Arithmetic::Storage {
  NativeLayouts &layouts;
  EvmLimits limits;
  std::map<std::string, std::string> definitions;
  Storage(NativeLayouts &layouts, const EvmLimits &limits)
      : layouts(layouts), limits(limits) {}
};
Arithmetic::Arithmetic(NativeLayouts &layouts, const EvmLimits &limits)
    : storage(std::make_unique<Storage>(layouts, limits)) {}
Arithmetic::~Arithmetic() = default;
std::string Arithmetic::helpers() const {
  if (storage->definitions.empty())
    return {};
  std::string result = commonHelpers();
  for (const auto &[name, body] : storage->definitions)
    result += body;
  return result;
}

Expected<std::string> Arithmetic::helper(CheckedOp op) {
  if (failed(op.verify()))
    return zkc::error("evm.arithmetic", "invalid checked arithmetic operation");
  auto attr = op->getAttrOfType<TypeAttr>("value_type");
  if (!attr || (!op.opcode().starts_with("field.") &&
                !op.opcode().starts_with("vector.")))
    return zkc::error(
        "evm.arithmetic",
        "requires typed field or coefficient collection operation");
  auto layout = storage->layouts.get(attr.getValue());
  if (!layout)
    return layout.takeError();
  bool vector = op.opcode().starts_with("vector.");
  auto scalar = dyn_cast<algebra::FieldType>(
      vector ? (*layout)->collection->element : attr.getValue());
  auto field = storage->layouts.field(scalar);
  if (!field)
    return field.takeError();
  const auto &f = **field;
  std::string p = word(f.modulus), d = std::to_string(f.degree),
              beta = word(f.beta);
  std::string stride = std::to_string(f.coefficientBytes());
  std::string code = op.opcode().str();
  std::string identity = p + "_" + d + "_" + beta;
  if (auto array = dyn_cast<data::FieldArrayType>(attr.getValue()))
    identity += "_array_" + std::to_string(array.getLength());
  auto literal = op->getAttrOfType<algebra::FieldLiteralAttr>("value");
  auto literals = op->getAttrOfType<ArrayAttr>("values");
  if (literal)
    identity += "_" + word(literal.getValue().getValue());
  if (literals) {
    std::string values;
    for (auto item : literals)
      values +=
          word(cast<algebra::FieldLiteralAttr>(item).getValue().getValue()) +
          ",";
    identity += "_" + toHex(SHA256::hash(arrayRefFromStringRef(values)), true);
  }
  std::replace(code.begin(), code.end(), '.', '_');
  std::string name = "evm_math_" + code + "_" + identity;
  if (storage->definitions.count(name))
    return name;
  std::string body;
  raw_string_ostream out(body);
  auto begin = [&](StringRef inputs, StringRef results) {
    out << "function " << name << "(" << inputs << ")";
    if (!results.empty())
      out << " -> " << results;
    out << " {\n";
  };
  auto check = [&](StringRef value) {
    if (f.degree == 1)
      out << "if iszero(lt(" << value << ", " << p << ")) { evm_fault(9) }\n";
    else
      out << "evm_math_field_memory(" << value << ", " << d << ", " << p
          << ")\n";
  };
  auto allocateField = [&] {
    out << "r := evm_alloc(" << stride << ") evm_math_zero(r, " << d << ")\n";
  };
  auto collectionCheck = [&](StringRef pointer, StringRef count) {
    out << "if gt(" << count << ", " << storage->limits.publicElements
        << ") { evm_resource(2) }\n";
    if (auto array = dyn_cast<data::FieldArrayType>(attr.getValue()))
      out << "if iszero(eq(" << count << ", " << array.getLength()
          << ")) { evm_fault(9) }\n";
    out << "evm_memory(" << pointer << ", mul(" << count << ", " << stride
        << "))\n";
  };
  StringRef opcode = op.opcode();
  if (!vector) {
    if (opcode == "field.constant") {
      begin("", "r");
      if (f.degree > 1) {
        allocateField();
        out << "mstore(r, " << word(literal.getValue().getValue()) << ")\n";
      } else
        out << "r := " << word(literal.getValue().getValue()) << "\n";
    } else if (opcode == "field.from_index" || opcode == "field.embed") {
      begin("a", "r");
      if (opcode == "field.embed")
        out << "if iszero(lt(a, " << p << ")) { evm_fault(9) }\n";
      else
        out << "if gt(a, 0xffffffffffffffff) { evm_fault(9) }\n";
      if (f.degree > 1) {
        allocateField();
        out << "mstore(r, mod(a, " << p << "))\n";
      } else
        out << "r := mod(a, " << p << ")\n";
    } else if (opcode == "field.inverse") {
      begin("a", "r");
      check("a");
      if (f.degree == 1)
        out << "r := evm_math_base_inverse(a, " << p << ")\n";
      else
        out << "r := evm_math_extension_inverse(a, " << d << ", " << beta
            << ", " << p << ")\n";
    } else if (opcode == "field.pow") {
      begin("a, n", "r");
      check("a");
      out << "if gt(n, 0xffffffffffffffff) { evm_fault(9) }\n";
      if (f.degree == 1)
        out << "r := evm_math_base_power(a, n, " << p << ")\n";
      else
        out << "r := evm_math_extension_power(a, n, " << d << ", " << beta
            << ", " << p << ")\n";
    } else if (opcode == "field.neg") {
      begin("a", "r");
      check("a");
      if (f.degree == 1)
        out << "r := mod(sub(" << p << ", a), " << p << ")\n";
      else {
        allocateField();
        out << "for { let i := 0 } lt(i, " << d
            << ") { i := add(i, 1) } { evm_math_set(r, i, mod(sub(" << p
            << ", evm_math_get(a, i)), " << p << ")) }\n";
      }
    } else {
      begin("a, b", "r");
      check("a");
      check("b");
      if (opcode == "field.equal") {
        if (f.degree == 1)
          out << "r := eq(a, b)\n";
        else
          out << "r := 1 for { let i := 0 } lt(i, " << d
              << ") { i := add(i, 1) } { if "
                 "iszero(eq(evm_math_get(a,i),evm_math_get(b,i))) { r := 0 "
                 "break } }\n";
      } else if (opcode == "field.div") {
        if (f.degree == 1)
          out << "r := mulmod(a, evm_math_base_inverse(b, " << p << "), " << p
              << ")\n";
        else
          out << "evm_math_extension_nonzero(b," << d << ") r := evm_alloc("
              << stride
              << ") let scratch := mload(0x40) let inverse := "
                 "evm_math_extension_inverse(b,"
              << d << "," << beta << "," << p
              << ") let product := evm_math_extension_multiply(a,inverse," << d
              << "," << beta << "," << p << ") mcopy(r,product," << stride
              << ") mstore(0x40,scratch)\n";
      } else if (opcode == "field.mul" && f.degree > 1) {
        out << "r := evm_math_extension_multiply(a,b," << d << "," << beta
            << "," << p << ")\n";
      } else {
        auto expression = [&](StringRef a, StringRef b) {
          if (opcode == "field.mul")
            out << "mulmod(" << a << "," << b << "," << p << ")";
          else {
            out << "addmod(" << a << ",";
            if (opcode == "field.sub")
              out << "sub(" << p << "," << b << ")";
            else
              out << b;
            out << "," << p << ")";
          }
        };
        if (f.degree == 1) {
          out << "r := ";
          expression("a", "b");
          out << "\n";
        } else {
          allocateField();
          out << "for { let i := 0 } lt(i," << d
              << ") { i := add(i,1) } { evm_math_set(r,i,";
          expression("evm_math_get(a,i)", "evm_math_get(b,i)");
          out << ") }\n";
        }
      }
    }
  } else if (opcode == "vector.empty" || opcode == "vector.constant") {
    begin("", "r, n");
    unsigned count = literals ? literals.size() : 0;
    if (count > storage->limits.publicElements)
      return zkc::error("evm.arithmetic",
                        "constant exceeds deployment element ceiling");
    out << "n := " << count << " r := evm_alloc("
        << uint64_t(count) * f.coefficientBytes() << ")\n";
    if (count) {
      out << "evm_math_zero(r," << uint64_t(count) * f.degree << ")\n";
      for (auto [i, value] : enumerate(literals))
        out << "mstore(add(r," << i * f.coefficientBytes() << "),"
            << word(
                   cast<algebra::FieldLiteralAttr>(value).getValue().getValue())
            << ")\n";
    }
  } else if (opcode == "vector.alloc") {
    begin("n", "r");
    out << "if gt(n," << storage->limits.publicElements
        << ") { evm_resource(2) } r := evm_alloc(mul(n," << stride << "))\n";
  } else if (opcode == "vector.get" || opcode == "vector.set") {
    begin(opcode == "vector.get" ? "a, n, i" : "a, n, i, v",
          opcode == "vector.get" ? "r" : "");
    if (opcode == "vector.set")
      out << "if iszero(lt(i," << storage->limits.publicElements
          << ")) { evm_resource(2) }\n";
    out << "if iszero(lt(i,n)) { "
        << (opcode == "vector.get" ? "evm_source(4)" : "evm_fault(3)")
        << " }\n";
    collectionCheck("a", "n");
    out << "let element := add(a,mul(i," << stride << "))\n";
    if (opcode == "vector.get") {
      if (f.degree == 1)
        out << "r := mload(element)\n";
      else
        out << "r := element\n";
      check("r");
    } else {
      check("v");
      if (f.degree == 1)
        out << "mstore(element,v)\n";
      else
        out << "mcopy(element,v," << stride << ")\n";
    }
  } else if (opcode == "vector.length") {
    begin("a, n", "r");
    collectionCheck("a", "n");
    out << "r := n\n";
  } else if (opcode == "vector.append") {
    begin("a, n, v", "r, length");
    collectionCheck("a", "n");
    check("v");
    out << "length := evm_index_add(n,1) if gt(length,"
        << storage->limits.publicElements
        << ") { evm_resource(2) } r := evm_alloc(mul(length," << stride
        << ")) mcopy(r,a,mul(n," << stride << ")) let element := add(r,mul(n,"
        << stride << "))\n";
    if (f.degree == 1)
      out << "mstore(element,v)\n";
    else
      out << "mcopy(element,v," << stride << ")\n";
  } else if (opcode == "vector.split") {
    begin("a, n", "left, ln, right, rn");
    out << "if or(iszero(n),and(n,1)) { evm_source(5) }\n";
    collectionCheck("a", "n");
    out << "left := a ln := div(n,2) right := add(a,mul(ln," << stride
        << ")) rn := ln\n";
  } else if (opcode == "vector.sum") {
    begin("a, n", "r");
    collectionCheck("a", "n");
    if (f.degree > 1)
      allocateField();
    out << "for { let i := 0 } lt(i,n) { i := add(i,1) } { let element := "
           "add(a,mul(i,"
        << stride << "))\n";
    if (f.degree == 1)
      out << "let v := mload(element) if iszero(lt(v," << p
          << ")) { evm_fault(9) } r := addmod(r,v," << p << ")\n";
    else
      out << "evm_math_field_memory(element," << d << "," << p
          << ") for { let j := 0 } lt(j," << d
          << ") { j := add(j,1) } { "
             "evm_math_set(r,j,addmod(evm_math_get(r,j),evm_math_get(element,j)"
             ","
          << p << ")) }\n";
    out << "}\n";
  } else if (opcode == "vector.equal") {
    begin("a, n, b, m", "r");
    collectionCheck("a", "n");
    collectionCheck("b", "m");
    out << "r := eq(n,m) if r { for { let i := 0 } lt(i,mul(n," << d
        << ")) { i := add(i,1) } { if "
           "iszero(eq(evm_math_get(a,i),evm_math_get(b,i))) { r := 0 break } } "
           "}\n";
  } else
    return zkc::error("evm.arithmetic",
                      "no coefficient collection implementation");
  out << "}\n";
  storage->definitions.emplace(name, std::move(body));
  return name;
}
} // namespace zkc::evm::detail
