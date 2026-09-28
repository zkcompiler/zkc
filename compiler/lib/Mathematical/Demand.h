#ifndef ZKC_MATHEMATICAL_DEMAND_H
#define ZKC_MATHEMATICAL_DEMAND_H

#include "zkc/Mathematical/Placement.h"
#include <set>

namespace zkc::mathematical {
/// Derived data tied to one immutable admitted subject. Aliases retain their
/// own scoped bindings; actual capture and yield edges justify their mapping.
struct Demand {
  std::set<ComponentKey> live;
};
llvm::Expected<Demand> computeDemand(const Subject &, AdmissionBudget &);
SourceAddress bodyAddress(const ClosedInstance &, BindingId);
SourceAddress regionAddress(const ClosedInstance &, uint32_t step, BindingId);
} // namespace zkc::mathematical
#endif
