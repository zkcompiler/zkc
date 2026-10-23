#ifndef ZKC_TRANSFORMS_MATHEMATICALWORK_H
#define ZKC_TRANSFORMS_MATHEMATICALWORK_H

#include "zkc/Analysis/ComputationWork.h"
#include <cstddef>
#include <cstdint>
#include <optional>

namespace zkc::mathematical {
class NumericalSelection;
/// Compiler work for one mathematical realization stage. Share this object
/// across its definitions and nested expressions; it contains no IR evidence
/// and grants no admission. Optional lane exhaustion retains an ordered finite
/// path. Required helper/polynomial expansion must report a capacity refusal.
/// These counters are separate from runtime resource accounting.
struct RealizationWork {
  finite::ComputationWork matching;
  uint64_t collectFoldDiscovery = 100000;
  uint64_t lanes = 1000000;
  unsigned helperOperations = 100000;
  uint64_t helperSlots = 1000000;
  uint64_t polynomial = 100000;
  // Optional whole-quotient planning is cumulative across entries and retries.
  // It never borrows the mandatory coefficient construction/checking reserve.
  unsigned quotientPlacements = 16;
  uint64_t quotientInspection = 1000000;
  uint64_t quotientConstruction = 100000;
  uint64_t quotientSiteBytes = 16 * 1024 * 1024;
  unsigned finiteExpressions = 100000;
  // Separate cumulative reserve for discarded Kernel recipe construction.
  // Cap speculative copying/site construction by this reserve before copying.
  // Settle a successful attempt into the caller's selected quotas, or debit
  // discarded work here. Matching work is never replenished; expansion is
  // restored only after transferring its debit to the discard account.
  uint64_t discardedRecipeCopy = 1000000;
  uint64_t discardedRecipeSiteBytes = 16 * 1024 * 1024;
  // Aggregate helper operations/slots, polynomial work, finite expressions
  // and required map construction from rejected recipes. Transfer these
  // debits here before restoring the selected candidate's required reserve.
  uint64_t discardedRecipeExpansion = 16 * 1024 * 1024;
  // One late numerical transaction shares these checking balances across
  // declarations and retries. Optional native interpretation cannot consume
  // the mandatory guard/vector reserve. Exact exhaustion on success is valid.
  uint64_t requiredMapChecking = 1000000;
  uint64_t optionalMapChecking = 1000000;
  uint64_t numericalContextChecking = 1000000;
  uint64_t numericalCheckCopy = 1000000;
  uint64_t numericalCheckSiteBytes = 16 * 1024 * 1024;
  uint64_t requiredMapConstruction = 1000000;
  uint64_t optionalMapConstruction = 1000000;
  uint64_t requiredFiniteChecking = 1000000;
  uint64_t optionalFiniteChecking = 1000000;
  // Mandatory occurrence/catalog bookkeeping is independent of optional
  // equation recognition, including when matching.structural is zero.
  uint64_t selectionBookkeeping = 1000000;
  // Synchronous producer hook, never evidence or a persistent source pointer.
  // Finite emitters apply select() after recognition and before emission.
  NumericalSelection *numericalSelection = nullptr;
  std::optional<size_t> numericalOccurrence;
};
} // namespace zkc::mathematical
#endif
