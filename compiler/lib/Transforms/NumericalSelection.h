#ifndef ZKC_TRANSFORMS_NUMERICAL_SELECTION_H
#define ZKC_TRANSFORMS_NUMERICAL_SELECTION_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <array>
#include <map>
#include <tuple>

namespace zkc::mathematical {
struct ComputationSelection;
struct MathematicalRecipes;
/// Snapshot only the selected recipe's expansion quotas. Matching, checking,
/// catalog and discarded work remain cumulative across attempts.
class RecipeConstructionWork {
  unsigned helpers, expressions;
  uint64_t slots, polynomial, requiredMaps;

public:
  explicit RecipeConstructionWork(const RealizationWork &);
  bool canDiscard(const RealizationWork &) const;
  bool discard(RealizationWork &) const;
};
using NumericalOccurrence = size_t;
enum class NumericalAlternative {
  Specialized,
  Expression,
  MapExpression,
  Vector,
  Ordered
};

/// Private, synchronous selection state. Identities are owned coordinates in
/// the once-prepared source, qualified by the actual invocation. No operation
/// or computation view from a discarded candidate is retained here.
class NumericalSelection {
  struct Coordinate {
    size_t invocation;
    RealizationSubject subject;
    bool operator<(const Coordinate &other) const {
      auto key = [](const Coordinate &value) {
        const auto &s = value.subject;
        return std::tie(value.invocation, s.declaration, s.site, s.operation,
                        s.position, s.definition, s.originalSite, s.occurrence);
      };
      return key(*this) < key(other);
    }
  };
  struct Occurrence {
    size_t invocation;
    RealizationSubject subject;
    NumericalAlternative alternative = NumericalAlternative::Specialized;
    bool replaceable = true;
    NumericalExpressionMode expressionMode =
        NumericalExpressionMode::PreferNative;
    std::array<bool, 5> legal = {true, true, false, true, true};
  };
  std::vector<Occurrence> occurrences;
  std::map<Coordinate, NumericalOccurrence> coordinates;
  size_t invocation = 0;
  bool optionalConstructionAllowed = true;
  RealizationWork *sharedWork = nullptr;
  RealizationWork &account() { return sharedWork ? *sharedWork : work; }
  const RealizationWork &account() const {
    return sharedWork ? *sharedWork : work;
  }

public:
  explicit NumericalSelection(RealizationWork *shared = nullptr)
      : sharedWork(shared) {}
  NumericalSelection(const NumericalSelection &) = delete;
  NumericalSelection &operator=(const NumericalSelection &) = delete;
  RealizationWork work;
  uint64_t remainingCopy = 1000000;
  uint64_t remainingSiteBytes = 16 * 1024 * 1024;
  /// Candidate pointers are transient. Clear before destroying the candidate;
  /// physical failure reports copy only occurrence ids and integer indices.
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<NumericalOccurrence>>
      origins;
  void enterInvocation(size_t coordinate) { invocation = coordinate; }
  /// A child coordinate counts finite occurrences in exact ordered callback
  /// substitution, independently of the number of emitted instructions. Both
  /// producer and reader reconstruct this path from the immutable closure.
  static RealizationSubject childSubject(const RealizationSubject &,
                                         llvm::StringRef operation,
                                         unsigned occurrence);
  llvm::Expected<NumericalOccurrence>
  discover(const RealizationSubject &, bool replaceable,
           NumericalExpressionMode = NumericalExpressionMode::PreferNative);
  llvm::Expected<NumericalOccurrence> discoverMap(const RealizationSubject &,
                                                  bool dot, bool sum,
                                                  NumericalExpressionMode);
  NumericalAlternative alternative(NumericalOccurrence) const;
  MathematicalSelectionPolicy policy(NumericalOccurrence,
                                     MathematicalSelectionPolicy) const;
  /// Called after equation recognition, before emitting any payload. It only
  /// selects from admitted equations; the actual candidate reader is unchanged.
  void select(NumericalOccurrence, ComputationSelection &,
              const MathematicalRecipes &);
  llvm::Expected<bool> advance(llvm::ArrayRef<NumericalOccurrence> implicated);
  llvm::Expected<bool> advanceSubject(const RealizationSubject &,
                                      std::optional<size_t> invocation = {});
  llvm::Expected<bool> advanceAll();
  llvm::Expected<bool> advanceInvocation();
  bool hasAlternatives(std::optional<size_t> invocation = {}) const;
  bool hasInvocationAlternatives() const { return hasAlternatives(invocation); }
  llvm::Expected<bool> order(const RealizationSubject &subject);
  bool canSpeculate() const;
  /// A required endpoint attempt must not discover fresh optional children.
  /// Returns the previous enclosing construction permission for scoped use.
  bool allowSpeculation(bool allowed) {
    bool previous = optionalConstructionAllowed;
    optionalConstructionAllowed = allowed;
    return previous;
  }
  bool chargeCatalog(uint64_t amount = 1);
  void record(mlir::Operation *, NumericalOccurrence);
  llvm::SmallVector<NumericalOccurrence> owners(mlir::Operation *) const;
};
/// Finite/map emitter integration: invoke after admitted equation selection and
/// before emitting any operation. The context is scoped by the containing
/// occurrence; it never authorizes replacement or supplies reader evidence.
void applyNumericalSelection(RealizationWork &, ComputationSelection &,
                             const MathematicalRecipes &);
} // namespace zkc::mathematical
#endif
