#ifndef ZKC_LANGUAGE_INSPECTIONDATA_H
#define ZKC_LANGUAGE_INSPECTIONDATA_H

#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"

namespace zkc::language {
/// Bounded, self-contained publication data for composition by native
/// exporters. These are projections of checked source, not an alternate source
/// or executable IR. The string inspection APIs encode these same values at
/// external boundaries.
llvm::Expected<llvm::json::Value> sourceClaimsData(const ClosedEntry &,
                                                   const Limits & = {});
llvm::Expected<llvm::json::Value>
componentDeclarationsData(const ClosedEntry &, const Limits & = {});
llvm::Expected<llvm::json::Value> writtenSourceData(const CheckedProject &,
                                                    const Limits & = {});
llvm::Expected<llvm::json::Value> sourceBindingsData(const CheckedProject &,
                                                     const Limits & = {});
llvm::Expected<llvm::json::Value> sourceInstancesData(const ClosedEntry &,
                                                      const Limits & = {});
} // namespace zkc::language
#endif
