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
};
} // namespace zkc
#endif
