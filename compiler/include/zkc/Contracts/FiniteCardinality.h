#ifndef ZKC_CONTRACTS_FINITE_CARDINALITY_H
#define ZKC_CONTRACTS_FINITE_CARDINALITY_H

#include "zkc/Contracts/MathematicalFacts.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <cstddef>
#include <cstdint>

namespace zkc::facts {

/// References are local to ONE borrowed adapter. They identify existing graph
/// nodes and exact input values, respectively; no numeric extent is an
/// identity.
using DomainRef = uintptr_t;
using DomainLeaf = uintptr_t;
struct DomainExtent {
  DomainLeaf value = 0;
  unsigned axis = 0;
};
enum class DomainKind {
  Unknown,
  Extent,
  Range,
  Zip,
  Product,
  MatrixCoordinates
};
struct DomainNode {
  DomainKind kind = DomainKind::Unknown;
  DomainExtent extent;
  DomainLeaf lower = 0, upper = 0;
  size_t children = 0;
};

/// A borrowed view of an independently validated constructor graph. Callbacks
/// expose existing nodes/edges and independently derived leaf evidence; they
/// must not read compiler-authored summary attributes as facts. All callbacks
/// and the immutable graph must outlive the query view. References must belong
/// to this adapter. No graph, identity, premise, or result cache is owned here.
///
/// Every callback is charged by the view. Nonconstant extraction must also use
/// the same Work. Leaf callbacks receive the depth from the view root,
/// including the leaf boundary, so recursive extraction preserves its limit.
/// Extent counts may be Upper for result analysis; exact() and
/// equal() never use a positive upper bound as exact formation evidence.
/// equalExtent may infer a required source formation equality and diagnose it.
struct DomainAdapter {
  llvm::function_ref<DomainNode(DomainRef)> node;
  llvm::function_ref<DomainRef(DomainRef, size_t)> child;
  llvm::function_ref<Result<Cardinality>(DomainExtent, unsigned)> extent;
  llvm::function_ref<Result<uint64_t>(DomainLeaf, unsigned)> integer;
  llvm::function_ref<Status(DomainLeaf, DomainLeaf, unsigned)> same;
  llvm::function_ref<Status(DomainExtent, DomainExtent, unsigned)> equalExtent;
};

/// Constructor cardinality rules only. A zip delegates to its first child;
/// this is NOT evidence that its other children have equal size. The adapter
/// retains all ordered zip/selector admission obligations, including in empty
/// products. Filtering belongs to facts::collect, outside this domain view.
class DomainCardinality {
public:
  DomainCardinality(Work &work, DomainAdapter adapter, unsigned maximumDepth)
      : work(work), adapter(adapter), maximumDepth(maximumDepth) {}
  Result<Cardinality> count(DomainRef domain) { return count(domain, 0); }
  Result<uint64_t> exact(DomainRef domain);
  Status equal(DomainRef left, DomainRef right) {
    return equal(left, right, 0);
  }

private:
  Work &work;
  DomainAdapter adapter;
  unsigned maximumDepth;
  bool enter(unsigned depth);
  Result<Cardinality> extent(DomainExtent leaf, unsigned depth);
  Result<uint64_t> integer(DomainLeaf leaf, unsigned depth);
  Status same(DomainLeaf left, DomainLeaf right, unsigned depth);
  Status equalExtent(DomainExtent left, DomainExtent right, unsigned depth);
  Result<Cardinality> count(DomainRef domain, unsigned depth);
  Status equal(DomainRef left, DomainRef right, unsigned depth);
};

} // namespace zkc::facts
#endif
