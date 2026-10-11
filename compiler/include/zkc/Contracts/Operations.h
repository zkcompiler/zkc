#ifndef ZKC_CONTRACTS_OPERATIONS_H
#define ZKC_CONTRACTS_OPERATIONS_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Mathematical.h"
#include "llvm/ADT/StringRef.h"
#include <optional>

namespace zkc::protocol {

/// Closed scalar laws used by computation analysis. A field ring and a group
/// module are different algebras; neither purity nor a user attribute grants
/// one of these facets. Applicability is checked on complete nominal ports.
enum class ComputationAlgebra { FieldRing, GroupModule, Access };
enum class ScalarIdentity { None, Zero, One, GroupIdentity };
enum class AccessRule { Element, MatrixCell };
struct ScalarLawContract {
  ComputationAlgebra algebra;
  bool associative = false;
  bool commutative = false;
  /// No logical stop on admitted scalar inputs. Does not describe resources.
  bool total = false;
  ScalarIdentity leftIdentity = ScalarIdentity::None;
  ScalarIdentity rightIdentity = ScalarIdentity::None;
  ScalarIdentity annihilator = ScalarIdentity::None;
  bool scalarAction = false;
  /// Scalar action source ports are (group, associated scalar).
  unsigned groupOperand = 0, scalarOperand = 1;
};
struct ComputationContract {
  llvm::StringRef key;
  MathematicalIdentity identity;
  ScalarLawContract law;
  std::optional<AccessRule> access;
};
/// Declaration-owned meaning without an executable operation choice.
struct MathematicalMeaning {
  MathematicalIdentity identity;
  ScalarLawContract law;
  std::optional<AccessRule> access;
};
const MathematicalMeaning *mathematicalMeaning(MathematicalIdentity identity);
const ComputationContract *computationContract(llvm::StringRef key);
/// Exact logical meaning, independent of physical availability. This does not
/// validate a pinned implementation or authorize replacement of that choice.
const ComputationContract *
admitMathematicalMeaning(const BindingApplication &,
                         llvm::ArrayRef<BoundType> inputs,
                         llvm::ArrayRef<BoundType> outputs,
                         llvm::ArrayRef<std::string> parameters = {});
/// Exact meaning plus eligibility for mathematical replacement. Explicit
/// implementations and physical representations remain nonreplaceable.
const ComputationContract *
admitComputationContract(const BindingApplication &,
                         llvm::ArrayRef<BoundType> inputs,
                         llvm::ArrayRef<BoundType> outputs,
                         llvm::ArrayRef<std::string> parameters = {});

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

/// A declared state successor, including copyable external snapshots. This
/// does not grant replay, entropy or transcript sampling authority.
struct HistoryContract {
  unsigned stateInput = 0;
  unsigned stateOutput = 0;
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
  std::optional<ComputationContract> mathematical;
  std::optional<HistoryContract> history;
  std::optional<SamplingContract> sampling;
  std::optional<ObservationContract> observation;
  std::optional<DiagonalMapContract> diagonalMap;
  std::optional<LinearContractionContract> linearContraction;
  std::optional<CosetContract> coset;
  std::optional<DomainValueContract> domainValue;
  bool publicReplay = false;
  bool acceptanceGuard = false;
  bool conjunction = false;
  /// Installed permission for ordinary source authoring of a copyable data
  /// history transition. It grants no managed resource or sampling authority.
  bool sourceHistory = false;
  /// Ordinary code can advance an existing affine transcript. Root acquisition
  /// stays with the selected construction; this grants no fresh resource.
  bool managedHistory = false;
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
