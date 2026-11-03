#ifndef ZKC_TARGET_EVM_TRANSCRIPT_H
#define ZKC_TARGET_EVM_TRANSCRIPT_H

#include "zkc/Target/Evm/Layout.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace zkc::evm {
/// The EVM realization of one installed transcript suite. The suite is
/// selected by its declared transcript facts, never by its spelling: the
/// `hash-chain` family over `keccak256`, binding the suite identity at
/// initialization, with the `fr64be` decoder. Its challenge field is prime and
/// at most 256 bits wide; that field's modulus reduces every 512-bit answer.
struct TranscriptRealization {
  llvm::StringRef suite;
  const FieldLayout *challenge = nullptr;
};
/// Refuses a suite that is not installed, or whose facts the EVM does not
/// realize, with `evm.construction` and the refused fact.
llvm::Expected<TranscriptRealization>
realizeTranscript(NativeLayouts &layouts, mlir::MLIRContext &context,
                  llvm::StringRef suite);
/// Whether `field` is the challenge field of an installed suite that the EVM
/// realizes.
bool realizedChallengeField(NativeLayouts &layouts, mlir::MLIRContext &context,
                            llvm::StringRef field);
} // namespace zkc::evm
#endif
