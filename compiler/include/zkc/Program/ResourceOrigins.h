#ifndef ZKC_PROGRAM_RESOURCE_ORIGINS_H
#define ZKC_PROGRAM_RESOURCE_ORIGINS_H

#include "zkc/Program/Admission.h"
#include <map>
#include <memory>

namespace zkc::program {
/// Exact affine result roots relative to the callable's formal arguments.
/// Missing roots are unknown. A noncontinuing body has no successful result;
/// it is not a returning body with unknown roots. Depth includes nested control
/// and calls, so a cached summary cannot bypass the caller's depth bound.
struct ResourceOriginSummary {
  std::map<unsigned, unsigned> roots;
  bool continues = true;
  unsigned depth = 1;
};
/// Invocation-local analysis of an owned, admitted snapshot. Later mutations of
/// the input model cannot change these facts. Each query consumes the same
/// caller-owned allowance, which must outlive the analysis. Cached summaries
/// retain their complete height and are checked at the query's actual depth.
class ResourceOriginAnalysis {
  struct Impl;
  std::unique_ptr<Impl> impl;
  explicit ResourceOriginAnalysis(std::unique_ptr<Impl> impl);

public:
  ~ResourceOriginAnalysis();
  static llvm::Expected<std::unique_ptr<ResourceOriginAnalysis>>
  create(LocalDefinitions definitions,
         std::vector<protocol::LocalRealization> realizations,
         uint64_t &remaining, unsigned depthLimit = 64);
  llvm::Expected<ResourceOriginSummary> get(llvm::StringRef function,
                                            unsigned depth = 1);
};
/// Admit the complete internal local view, then analyze one actual function.
/// The caller's cumulative allowance bounds fact analysis; native formation has
/// its own bounds. Summaries grant no executable or source-correspondence
/// claim.
llvm::Expected<ResourceOriginSummary>
analyzeResourceOrigins(const LocalDefinitions &definitions,
                       llvm::ArrayRef<protocol::LocalRealization> realizations,
                       llvm::StringRef function, uint64_t &remaining,
                       unsigned depthLimit = 64);
} // namespace zkc::program
#endif
