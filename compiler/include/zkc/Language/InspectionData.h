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
/// One native site of an emitted definition and the authored expression of
/// the source operation emission assigned it to. `owner` is the span of the
/// declaration whose written syntax holds that expression.
struct EmittedSite {
  std::string definition, site;
  Span owner = {};
  std::optional<uint32_t> expression = {};
};
/// The written nodes of each site's originating expression, exactly as the
/// written-source index places that expression in its owner; a site without
/// an expression has none. Spans never select a node.
llvm::Expected<std::vector<llvm::json::Array>>
writtenSiteNodes(const CheckedProject &, llvm::ArrayRef<EmittedSite>,
                 const Limits & = {});
} // namespace zkc::language
#endif
