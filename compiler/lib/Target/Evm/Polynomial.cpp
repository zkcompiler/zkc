#include "Polynomial.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm::detail {
namespace {
std::string word(const APInt &n) {
  SmallString<80> text;
  n.toStringUnsigned(text, 16);
  return "0x" + text.str().str();
}
} // namespace
Expected<std::string> polynomialHelper(Operation *op, const FieldLayout &f,
                                       const EvmLimits &limits,
                                       StringRef name) {
  std::string body;
  raw_string_ostream out(body);
  std::string p = word(f.modulus), beta = word(f.beta);
  const uint64_t stride = f.coefficientBytes();
  auto checkField = [&](StringRef value) {
    if (f.degree == 1)
      out << "if iszero(lt(" << value << "," << p << ")) { evm_fault(9) }\n";
    else
      out << "evm_math_field_memory(" << value << "," << f.degree << "," << p
          << ")\n";
  };
  auto allocateOutput = [&] {
    if (f.degree > 1)
      out << "r := evm_alloc(" << stride << ") evm_math_zero(r," << f.degree
          << ")\n";
  };
  auto checkCollection = [&] {
    out << "if gt(n," << limits.publicElements << ") { evm_resource(2) }\n"
        << "evm_memory(a,mul(n," << stride << "))\n"
        << "for { let i := 0 } lt(i,mul(n," << f.degree
        << ")) { i := add(i,1) } {\n"
        << "if iszero(lt(evm_math_get(a,i)," << p << ")) { evm_fault(9) } }\n";
  };
  if (isa<PolyDomainRootOp, PolyDomainPointOp>(op)) {
    bool point = isa<PolyDomainPointOp>(op);
    const auto *convention = protocol::cosetConvention(f.type.getDomain());
    APInt root;
    if (!convention || convention->rootField != f.base.getDomain() ||
        StringRef(convention->maximalRoot).getAsInteger(10, root) ||
        root.getActiveBits() > 256 || root.isZero() ||
        root.zextOrTrunc(256).uge(f.modulus) || convention->maxLogSize > 64)
      return zkc::error("evm.polynomial",
                        "missing exact installed base-subgroup convention");
    const auto maximum = word(APInt(256, 1).shl(convention->maxLogSize));
    out << "function " << name << (point ? "(shift,n,position)" : "(n)")
        << " -> r {\n";
    // Native scalar-output admission precedes domain checks. Prime results
    // are stack words; extension results need the same checked field backing.
    allocateOutput();
    out << "if or(or(iszero(n),and(n,sub(n,1))),gt(n," << maximum
        << ")) { evm_source(12) }\n"
        // The native Plonky3 wrapper maps Domain::ElementLimit to
        // refused:coset-element-limit, unlike the oracle's exhausted mapping.
        << "if gt(n,1048576) { evm_source(15) }\n";
    if (point) {
      checkField("shift");
      if (f.degree == 1)
        out << "if iszero(shift) { evm_source(13) }\n";
      else
        out << "let nonzero := 0 for { let i := 0 } lt(i," << f.degree
            << ") { i := add(i,1) } { nonzero := "
               "or(nonzero,evm_math_get(shift,i)) }\n"
            << "if iszero(nonzero) { evm_source(13) }\n";
      out << "if iszero(lt(position,n)) { evm_source(14) }\n";
    }
    // The generator is the catalog's maximalRoot, not an arbitrary root of
    // the same order. common/catalog/generate.py::DomainView.convention and
    // Contracts/Operations.cpp::cosetConvention inherit along BaseField only.
    out << "let root := " << word(root) << "\n"
        << "for { let size := n } lt(size," << maximum
        << ") { size := mul(size,2) } { root := mulmod(root,root," << p
        << ") }\n";
    if (point) {
      out << "let power := 1\n"
          << "for { let exponent := position } exponent { exponent := "
             "shr(1,exponent) } {\n"
          << "if and(exponent,1) { power := mulmod(power,root," << p << ") }\n"
          << "root := mulmod(root,root," << p << ") }\n";
      if (f.degree == 1)
        out << "r := mulmod(shift,power," << p << ")\n";
      else
        out << "for { let i := 0 } lt(i," << f.degree
            << ") { i := add(i,1) } {\n"
            << "evm_math_set(r,i,mulmod(evm_math_get(shift,i),power," << p
            << ")) }\n";
    } else if (f.degree == 1)
      out << "r := root\n";
    else
      out << "mstore(r,root)\n";
  } else if (isa<PolyFromCoefficientsOp>(op)) {
    out << "function " << name << "(a,n) -> r,length {\n";
    checkCollection();
    out << "length := n\n"
        << "for {} length {} {\nlet nonzero := 0\n"
        << "for { let i := 0 } lt(i," << f.degree << ") { i := add(i,1) } {\n"
        << "nonzero := or(nonzero,evm_math_get(a,add(mul(sub(length,1),"
        << f.degree << "),i))) }\n"
        << "if nonzero { break } length := sub(length,1) }\n"
        // Allocate/copy only the normalized prefix, including allocation(0).
        << "r := evm_alloc(mul(length," << stride << "))\n"
        << "mcopy(r,a,mul(length," << stride << "))\n";
  } else if (isa<PolyEvaluateOp>(op)) {
    out << "function " << name << "(a,n,x) -> r {\n";
    allocateOutput();
    checkCollection();
    checkField("x");
    out << "for { let i := n } i {} { i := sub(i,1)\n";
    if (f.degree == 1)
      out << "r := addmod(mulmod(r,x," << p << "),evm_math_get(a,i)," << p
          << ")\n";
    else
      out << "let scratch := mload(0x40)\n"
          << "let product := evm_math_extension_multiply(r,x," << f.degree
          << "," << beta << "," << p << ")\n"
          << "for { let j := 0 } lt(j," << f.degree << ") { j := add(j,1) } {\n"
          << "evm_math_set(r,j,addmod(evm_math_get(product,j),evm_math_get(a,"
             "add(mul(i,"
          << f.degree << "),j))," << p
          << ")) }\n"
          // r is distinct allocated output; the temporary product cannot
          // escape.
          << "mstore(0x40,scratch)\n";
    out << "}\n";
  } else
    return zkc::error("evm.polynomial",
                      "requires exact typed polynomial operation");
  out << "}\n";
  return body;
}
} // namespace zkc::evm::detail
