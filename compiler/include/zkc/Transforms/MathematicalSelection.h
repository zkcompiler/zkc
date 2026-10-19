#ifndef ZKC_TRANSFORMS_MATHEMATICAL_SELECTION_H
#define ZKC_TRANSFORMS_MATHEMATICAL_SELECTION_H

namespace zkc {
/// Algorithm family choices shared by Local preparation and total Math demand
/// lowering. Independent of generic simplification and physical storage
/// release. Optional selections preserve logical results and ordered shape
/// refusals under the declared primitive contracts and sufficient capacity, not
/// exhaustion.
struct MathematicalSelectionPolicy {
  bool finiteBulk = true;
  bool vectorReductionFusion = false;
  bool collectFoldFusion = false;
  /// With batching, each needed total operation is computed in the one
  /// calculation call before the first action whose demand reaches it.
  /// Without it, the call before each action computes every needed operation
  /// that precedes the action in source order, so values are computed where
  /// the source defines them.
  bool calculationBatching = true;
};
} // namespace zkc
#endif
