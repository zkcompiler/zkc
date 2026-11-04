#ifndef ZKC_TARGET_EVM_TRANSCRIPT_H
#define ZKC_TARGET_EVM_TRANSCRIPT_H

#include "zkc/Target/Evm/Layout.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace zkc::evm {
/// The EVM realization of one installed transcript suite. The suite is
/// selected by its declared transcript facts, never by its spelling: the
/// `hash-chain` family over `keccak256`, binding the suite identity at
/// initialization. Decoding uses the declared challenge field's existing
/// layout: a prime word for fr64be, ascending coefficients for rejection31le.
struct TranscriptRealization {
  enum class Decoder { Fr64Be, Rejection31Le };
  llvm::StringRef suite;
  const FieldLayout *challenge = nullptr;
  Decoder decoder = Decoder::Fr64Be;
  bool index = false;
  bool indexBlock = false;
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
