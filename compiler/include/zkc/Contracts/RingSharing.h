#ifndef ZKC_CONTRACTS_RING_SHARING_H
#define ZKC_CONTRACTS_RING_SHARING_H

#include "zkc/Contracts/RingExpression.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <vector>

namespace zkc::ring {

/// A structurally shared form of an admitted arena together with the node map
/// that relates the two. `nodeMap[i]` is the shared node standing for original
/// node `i`. The map is an in-process value for carrying per-node annotations
/// across the transformation; it is not an exchanged format.
struct Sharing {
  Expression expression;
  std::vector<uint32_t> nodeMap;
  /// False exactly when the map is the identity, in which case the shared
  /// arena has the original's canonical encoding and identity.
  bool changed = false;
};

/// Merge nodes whose kind, field, literal, input slot and already-mapped
/// children coincide exactly, in original index order, keeping the first
/// occurrence. Input declarations are copied unchanged, including unused ones;
/// every output position is kept in order, including repeated nodes. Nothing
/// algebraic is applied: no constant folding, zero elimination or operand
/// reordering, so every syntactic read and field fact survives. The result is
/// re-admitted; the work is one ordered lookup per node.
llvm::Expected<Sharing> shareExpression(const Expression &original);

/// Judge, without rerunning the transformation, that `shared` under `nodeMap`
/// is a label-preserving quotient of `original`: equal input declarations, a
/// map entry inside the shared arena for every original node, the same kind,
/// field, literal and input slot at each image with children that are the
/// images of the original children in the same order, and every output
/// position mapped. These checks imply equal per-node field facts, equal
/// degrees for every weight vector, equal used inputs per output position and
/// equal mathematical substitution under every compatible algebra. Resource
/// costs and budget-refusal behavior can differ. Refusals: ring-sharing-map,
/// ring-sharing-inputs, ring-sharing-node, ring-sharing-outputs.
llvm::Error checkSharing(const Expression &original, const Expression &shared,
                         llvm::ArrayRef<uint32_t> nodeMap);

} // namespace zkc::ring
#endif
