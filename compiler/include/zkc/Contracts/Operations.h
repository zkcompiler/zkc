#ifndef ZKC_CONTRACTS_OPERATIONS_H
#define ZKC_CONTRACTS_OPERATIONS_H

#include "llvm/ADT/StringRef.h"
#include <optional>

namespace zkc::protocol {

enum class RandomnessProvider { Entropy, Transcript };
enum class SampleDomain { Field, FieldVector, BoundedIndex };

/// Port roles for an installed sampling operation. These facts describe
/// structural dataflow, not independence, uniformity, or Fiat-Shamir security.
struct SamplingContract {
  RandomnessProvider provider;
  SampleDomain domain;
  unsigned stateInput = 0;
  unsigned valueOutput = 0;
  unsigned stateOutput = 1;
  std::optional<unsigned> boundInput;
  /// Registered derived operation with matching sampled/parameter ports.
  /// Empty means no installed public-coin construction rule.
  llvm::StringRef derivedCounterpart;
};

struct ObservationContract {
  unsigned stateInput = 0;
  unsigned payloadInput = 1;
  unsigned stateOutput = 0;
};

/// Operand roles for the domain's declared scalar-action equations. These
/// facts say nothing about an installed buffer layout or rewrite accounting.
struct DiagonalMapContract {
  unsigned factorsOperand = 0, valuesOperand = 1, result = 0;
};
struct LinearContractionContract {
  unsigned coefficientsOperand = 0, valuesOperand = 1;
};

/// Ordered multiplicative coset used by a successful operation. sizeInput
/// supplies either an index or a vector whose length determines the size.
/// A vector result is associated with this domain (or its even/odd image),
/// without asserting a degree bound for its entries.
struct CosetContract {
  unsigned shiftInput, sizeInput;
  bool sizeIsLength = false;
  std::optional<unsigned> vectorOutput;
  bool foldedOutput = false;
};

/// Small exact-value vocabulary used by domain congruence. These are value
/// equations on successful operations, not permission to CSE or speculate.
enum class DomainValueRule { Constant, Length, Multiply, Divide };
struct DomainValueContract {
  DomainValueRule rule;
  unsigned output = 0, input = 0, otherInput = 1;
};

struct CosetConvention {
  llvm::StringRef identity, rootField, maximalRoot, order;
  unsigned maxLogSize;
};
/// Mathematical installation, independent of a selected physical layout.
/// Unknown nominal fields have no convention.
const CosetConvention *cosetConvention(llvm::StringRef field);

/// Independently consumed semantic facets of a registered operation. Absence
/// of a facet never grants purity, speculation, replay, or sampling authority.
struct OperationContracts {
  std::optional<SamplingContract> sampling;
  std::optional<ObservationContract> observation;
  std::optional<DiagonalMapContract> diagonalMap;
  std::optional<LinearContractionContract> linearContraction;
  std::optional<CosetContract> coset;
  std::optional<DomainValueContract> domainValue;
  bool publicReplay = false;
  bool acceptanceGuard = false;
  bool conjunction = false;

  static OperationContracts replay();
  static OperationContracts guard();
  static OperationContracts booleanConjunction();
  static OperationContracts transcriptObservation();
  static OperationContracts diagonal();
  static OperationContracts contraction();
  static OperationContracts onCoset(CosetContract);
  static OperationContracts exactDomainValue(DomainValueRule,
                                             bool replay = false);
  static OperationContracts sample(RandomnessProvider, SampleDomain,
                                   std::optional<unsigned> bound = {},
                                   llvm::StringRef derivedCounterpart = {});
};

/// Resolve a logical contract key, independently of physical implementation.
/// Unknown keys have no positive contract. Message/control syntax is separate.
const OperationContracts *operationContracts(llvm::StringRef key);
const SamplingContract *samplingContract(llvm::StringRef key);
/// Observation or sampling of an existing transcript history, including
/// installed external data-state constructions. Not a dataflow taint analysis.
bool isHistoryTransition(llvm::StringRef key);
bool isAcceptanceGuard(llvm::StringRef key);
bool isConjunction(llvm::StringRef key);
bool isPublicReplay(llvm::StringRef key);
bool isConstructionDraw(llvm::StringRef key);
/// Conservative coverage check for rng/transcript/nonce consumers; this detects
/// a gap, never infers a sampler. Nonce consumers currently lack transfer
/// facts.
bool hasUnclassifiedProviderEffect(llvm::StringRef key);

} // namespace zkc::protocol
#endif
