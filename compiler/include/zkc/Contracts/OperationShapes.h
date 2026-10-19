#ifndef ZKC_CONTRACTS_OPERATIONSHAPES_H
#define ZKC_CONTRACTS_OPERATIONSHAPES_H

#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Installed contract shapes shared by binding resolution.
struct OperationShape {
  llvm::StringRef key;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
  OperationContracts contracts{};
};
llvm::ArrayRef<OperationShape> operationShapes();
/// Formation of static operation attributes under an installed contract.
llvm::Error checkParameters(llvm::StringRef key, llvm::ArrayRef<std::string>,
                            llvm::StringRef field = {});
/// Attributes valid without choosing a field: field literals must be 0 or 1.
/// All ordinary arity and non-field attribute checks still apply.
llvm::Error checkGenericParameters(llvm::StringRef key,
                                   llvm::ArrayRef<std::string>);
/// Resolve the declared literal field from a closed operation application.
llvm::Error checkParameters(const BindingApplication &,
                            llvm::ArrayRef<std::string>);
/// Canonical modulus if installed; empty means no admitted constant domain.
llvm::StringRef fieldModulus(llvm::StringRef identity);
/// Coordinates over GF(2) of an installed binary field, whose constants also
/// have the bit-pattern literal form; zero for every other identity.
unsigned fieldBitPatternWidth(llvm::StringRef identity);
/// Whether `text` is the canonical bit-pattern literal of an element of a
/// binary field with `width` coordinates: `0x`, then lowercase hexadecimal
/// digits without leading zeros, denoting a value from 2 below 2^width.
bool isBitPatternLiteral(llvm::StringRef text, unsigned width);
} // namespace zkc::protocol
#endif
