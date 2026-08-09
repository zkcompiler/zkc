//===- SealBattery.h - the seal battery entry point -------------*- C++ -*-===//
#ifndef ZKC_SEMANTICS_SEALBATTERY_H
#define ZKC_SEMANTICS_SEALBATTERY_H

#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

#include <optional>

namespace mlir {
class ArrayAttr;
class Block;
class DictionaryAttr;
class Operation;
} // namespace mlir

namespace zkc {
namespace encoding {
struct CanonicalIndex;
} // namespace encoding

namespace registry {
class ConstructionProfileRegistry;
class ProtocolVocabulary;
} // namespace registry

namespace pir {

/// The resolved-vocabulary gate (kernel.md §8), shared by every sealed
/// consumer. The stamped table is closed and exact: the transitive protocol
/// vocabulary citations and the consumed construction profiles must match the
/// loaded authorities. No section names a security analysis; a theorem is
/// applied to a sealed protocol by a derivation, never carried inside it.
/// Every failure goes through `error`; there is no permissive mode.
/// The vocabulary authority is resolved at the ingress boundary before any
/// judgment runs, so it is taken by reference; the construction-profile
/// registry is genuinely optional (absent when kappa consumes no sponge or
/// codec) and stays a pointer.
bool verifyResolvedVocab(mlir::Block &body,
                         std::optional<mlir::DictionaryAttr> kappa,
                         std::optional<mlir::DictionaryAttr> vocab,
                         const registry::ProtocolVocabulary &protocolVocabulary,
                         const registry::ConstructionProfileRegistry *profiles,
                         llvm::function_ref<void(const llvm::Twine &)> error);

/// The exact transitive protocol-vocabulary citation closure of one body.
/// Direct carrier citations are expanded through terminal-rule and reduction-
/// contract references. Returned refs point into operation or vocabulary
/// storage; both must outlive the result.
struct ProtocolVocabularyCitations {
  llvm::SmallVector<llvm::StringRef> claimProfiles;
  llvm::SmallVector<llvm::StringRef> checkContracts;
  llvm::SmallVector<llvm::StringRef> reductionContracts;
  llvm::SmallVector<llvm::StringRef> terminalRules;
};

ProtocolVocabularyCitations collectCitedProtocolVocabulary(
    mlir::Block &body, const registry::ProtocolVocabulary &protocolVocabulary);

/// One projection obligation (kernel.md §6.1): what a semantic event
/// demands of every endpoint projection. The route class is
/// `executable` for every event — the carrier has no surface to
/// declare a non-executable route, and fail-closed absence means
/// executable (declared routes are a named extension,
/// vocabularies.md §4) — so only the two varying components are
/// materialized here.
struct ProjectionObligation {
  /// Canonical event position — the encoder's numbering, the same
  /// numbering OIR `src` provenance uses.
  int64_t eventRef;
  /// The endpoint-effect family that must realize the event, from
  /// the closed discharge-kind table of kernel.md §6.1.
  llvm::StringRef discharge;
};

/// One row of the closed discharge-kind table (kernel.md §6.1): the
/// discharge name COV_obl derives for an event-kind variant, paired
/// with the endpoint-effect families licensed to realize it at
/// projection (kernel.md §6.2, the no-phantom-coverage direction).
/// The pairing is defined exactly once (SealBattery.cpp) so the
/// obligation derivation and the projection-side licensing cannot
/// drift; growing the table is a kernel change, never a local
/// convenience.
struct DischargeKindRow {
  llvm::StringRef name;
  llvm::ArrayRef<llvm::StringRef> verifierFamilies;
  llvm::ArrayRef<llvm::StringRef> proverFamilies;
};

/// The closed discharge-kind table.
llvm::ArrayRef<DischargeKindRow> dischargeKindTable();

/// Table lookup by discharge name; nullptr outside the closed set.
const DischargeKindRow *findDischargeKind(llvm::StringRef name);

/// The projection obligation table of one container body — the
/// object COV_obl derives (kernel.md §6.1) and projection's
/// realization equality consumes (§6.2). A derived view in the
/// kernel §11 sense: a tabulation of the canonical event rows by the
/// closed discharge-kind table, recomputable by any consumer, never
/// part of canonical(P). Non-event members (the frame and the claim
/// graph) carry no obligation; a member kind outside the closed set
/// is refused by the battery and the projection walk, not here.
llvm::SmallVector<ProjectionObligation>
deriveObligations(mlir::Block &body,
                  const encoding::CanonicalIndex &canonicalEvents);

/// The seal battery over one container: the semantic halves of WF,
/// LIN, BIND, and COV_obl — obligation derivability, kernel.md
/// §6.1/§7. Verdict-only — the
/// caller owns stamping, identity, and artifact construction;
/// diagnostics accumulate on the container's ops so an author sees
/// every missed obligation, not the first. TerminalClosureOK is part
/// of this battery. In recheck mode the single resolved-vocabulary
/// table must additionally match all loaded authorities (the consumer
/// contract's second leg, boundaries.md §0). A caller that wants a verdict
/// without emitted diagnostics installs a scoped diagnostic handler
/// around this call and reads the LogicalResult.
mlir::LogicalResult runSealBattery(
    mlir::Operation *container, std::optional<mlir::DictionaryAttr> kappa,
    std::optional<mlir::DictionaryAttr> vocab,
    std::optional<llvm::ArrayRef<int64_t>> segments, llvm::StringRef policy,
    bool recheck, const registry::ProtocolVocabulary &protocolVocabulary,
    const registry::ConstructionProfileRegistry *profiles);

} // namespace pir
} // namespace zkc

#endif // ZKC_SEMANTICS_SEALBATTERY_H
