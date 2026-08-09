//===- Interpreter.h - reference endpoint execution -------------*- C++ -*-===//
#ifndef ZKC_INTERPRETER_INTERPRETER_H
#define ZKC_INTERPRETER_INTERPRETER_H

#include "zkc/Dialect/Oir/OirOps.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/Error.h"

namespace zkc {
namespace interpreter {

class ExecutionProfile;

/// One execution of a verifier endpoint under an execution profile — a
/// closed supplier set (docs/spec/endpoints.md §4). `verdict` is "accept" or a
/// named reject class; sampled challenges are reported in order so Fiat-Shamir
/// determinism is externally checkable. A vocabulary the profile does not
/// supply (codec, sponge, sampling shape, check contract) is an error
/// carrying a stable [zkc-E4xx] id, never a verdict: "this proof is bad"
/// and "I cannot judge this proof" must not be conflated. The public
/// boundary authenticates the stored OIR identity before reading ABI
/// or program semantics.
struct ExecutionResult {
  std::string verdict;
  std::vector<std::string> challenges;
  std::string diag;
};

llvm::Expected<ExecutionResult>
execute(oir::ArtifactOp artifact, const ExecutionProfile &profile,
        const llvm::StringMap<std::string> &statement,
        llvm::ArrayRef<uint8_t> proof);

/// One run of a prover-skeleton endpoint under an execution profile
/// (docs/spec/endpoints.md §6.3). There is no accept verdict at
/// all: a prover run's success claim is only ever the emitted bytes —
/// acceptance belongs to verifiers. Witness payloads arrive opaque, by
/// their declared labels, as hex; the run record's challenge log makes
/// the replica-sponge derivation externally checkable against the
/// verifier's. "Cannot fill this hole" is a profile refusal naming the
/// contract digest (E407 in the versioning.md allocation); a fill that
/// violates its declared boundary (arity, range, canonicity) is a
/// defect (E408), never a proof verdict.
struct ProveResult {
  std::vector<uint8_t> proof;
  std::vector<std::string> challenges;
};

llvm::Expected<ProveResult> prove(oir::ArtifactOp artifact,
                                  const ExecutionProfile &profile,
                                  const llvm::StringMap<std::string> &statement,
                                  const llvm::StringMap<std::string> &witness);

/// Proof size in bytes from the sealed structure alone: the sum of wire
/// widths over the program's proof-stream reads, each read priced by the
/// profile codec the artifact's baked map routes it to. No execution —
/// but the identity gate and the codec route are execution's own, so a
/// class the profile cannot price is the same no-codec-route refusal,
/// never a zero that undercounts a proof.
llvm::Expected<uint64_t> proofSizeBytes(oir::ArtifactOp artifact,
                                        const ExecutionProfile &profile);

} // namespace interpreter
} // namespace zkc

#endif // ZKC_INTERPRETER_INTERPRETER_H
