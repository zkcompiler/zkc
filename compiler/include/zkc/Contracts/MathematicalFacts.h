#ifndef ZKC_CONTRACTS_MATHEMATICAL_FACTS_H
#define ZKC_CONTRACTS_MATHEMATICAL_FACTS_H

#include "llvm/ADT/ArrayRef.h"
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>

namespace zkc::facts {

enum class Status { Proven, Unknown, Capacity };
template <typename T> struct Result {
  Status status = Status::Unknown;
  std::optional<T> value;
};

/// One cumulative allowance, shared by extraction and every nested query.
/// A failed charge is sticky. The callback must debit the adapter's existing
/// allowance and return false on exhaustion. Captured adapter state must
/// outlive this object.
class Work {
public:
  explicit Work(uint64_t &remaining);
  explicit Work(std::function<bool(uint64_t)> charger);
  Work(const Work &) = delete;
  Work &operator=(const Work &) = delete;
  bool charge(uint64_t amount = 1);
  bool exhausted() const { return exhausted_; }
  /// Mark an adapter structural/depth limit without a fabricated work debit.
  /// Sticky for this Work; does not invoke the callback or alter its counter.
  void exhaust() { exhausted_ = true; }

private:
  std::function<bool(uint64_t)> charger_;
  bool exhausted_ = false;
};

namespace detail {
struct Identity;
}
class Snapshot;

/// Opaque exact identity. Equal extents never make two Values equal. Adapters
/// assign roots and projection paths, or intern their own exact subjects as
/// roots. Exact forwarding reuses the same identity; reconstruction does not.
class Value {
public:
  Value() = default;
  bool operator==(const Value &other) const;
  bool operator!=(const Value &other) const { return !(*this == other); }

private:
  friend class Snapshot;
  std::shared_ptr<const detail::Identity> owner_;
  uint64_t index_ = 0;
};

class Scope {
public:
  Scope() = default;

private:
  friend class Snapshot;
  std::shared_ptr<const detail::Identity> owner_;
  uint64_t index_ = 0;
};

struct Extent {
  Value container;
  unsigned axis = 0;
  bool operator==(const Extent &other) const {
    return container == other.container && axis == other.axis;
  }
};

/// These are established premises, never ordered admission obligations.
/// Tags are retained by scope intersection. Knowing a shape does not erase
/// any ordered guard; the kernel has no reached-guard premise producer.
enum class Premise { Formation, Result };
enum class Precision { Exact, Upper };
struct Cardinality {
  uint64_t value = 0;
  Precision precision = Precision::Exact;
};

/// A noncopyable, nonmovable view of ONE immutable source/SSA subject. Rebuild
/// after any subject or helper mutation. Handles retain a unique owner token
/// and cannot be used in a different snapshot, even after address reuse.
/// Adapters independently establish all premises and validate axis/type
/// formation. This kernel does not interpret expressions, helpers or ui64 math.
/// Work must outlive the snapshot; neither object is thread-safe.
class Snapshot {
public:
  explicit Snapshot(Work &work);
  ~Snapshot();
  Snapshot(const Snapshot &) = delete;
  Snapshot &operator=(const Snapshot &) = delete;
  Snapshot(Snapshot &&) = delete;
  Snapshot &operator=(Snapshot &&) = delete;

  Scope root() const;
  Result<Value> intern(uint64_t root, llvm::ArrayRef<unsigned> path = {});

  /// Explicit fact-set copies. A child sees facts established before fork;
  /// later parent/child additions never propagate to another scope.
  Result<Scope> fork(Scope parent);
  /// Intersection of identical established premises (including their tags).
  /// May conservatively omit common consequences with different derivations.
  /// Empty input is Unknown. No backedge or zero-trip propagation is implicit.
  Result<Scope> intersect(llvm::ArrayRef<Scope> incoming);

  Status addEquality(Scope, Extent left, Extent right, Premise);
  Status addInteger(Scope, Value, uint64_t, Premise);
  Status addExtent(Scope, Extent, uint64_t, Premise);
  Status addBound(Scope, Value index, Extent, Premise);
  Status addCardinality(Scope, Extent, Cardinality, Premise);

  /// Unknown also covers foreign/default handles and absent evidence; it is
  /// not a proof of falsity. Failed charges return Capacity without a value.
  Status equal(Scope, Extent left, Extent right);
  Status bound(Scope, Value index, Extent);
  Result<uint64_t> integer(Scope, Value);
  Result<Cardinality> cardinality(Scope, Extent);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
  std::shared_ptr<const detail::Identity> owner_;
  Work &work_;
  bool owns(Value) const;
  bool owns(Scope) const;
};

/// Arithmetic on nonnegative mathematical counts, never wrapping ui64.
/// Overflow produces Unknown. Capacity propagates even in a zero product.
Result<Cardinality> product(Work &, llvm::ArrayRef<Result<Cardinality>>);
Result<Cardinality> sum(Work &, Result<Cardinality>, Result<Cardinality>);
Result<Cardinality> range(Work &, uint64_t lower, uint64_t upper);
/// Unfiltered collection preserves precision. Filtering gives only an upper
/// bound, except that a zero upper bound is necessarily exact zero.
Result<Cardinality> collect(Work &, Result<Cardinality>, bool filtered);

} // namespace zkc::facts
#endif
