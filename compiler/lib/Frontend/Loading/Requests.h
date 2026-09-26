#ifndef ZKC_FRONTEND_LOADING_REQUESTS_H
#define ZKC_FRONTEND_LOADING_REQUESTS_H

#include "Paths.h"
#include "zkc/Frontend/Dependencies.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"

namespace zkc::frontend::loading {
/// Count logical imports, including repeated paths. Physical read caching and
/// storage deduplication do not reduce the work charged for relation decoding.
class RequestBudget {
  size_t count = 0, bytes = 0;

public:
  /// Validate the entire declaration batch before invoking any reader/resolver.
  llvm::Error preflight(llvm::ArrayRef<RelationReference> requests) {
    if (requests.size() > relation::DependencyLimits::count - count)
      return zkc::error("relation-dependency-limit");
    for (const auto &request : requests)
      if (!relativeAsset(request.path))
        return zkc::error("relation-asset-path");
    count += requests.size();
    return llvm::Error::success();
  }

  llvm::Expected<size_t>
  maximum(const RelationReference &request,
          llvm::StringRef exhausted = "relation-dependency-limit") const {
    if (bytes == relation::DependencyLimits::bytes)
      return zkc::error(exhausted);
    const auto family = request.family == "air" ? relation::AIRLimits::bytes
                                                : relation::Limits::bytes;
    return std::min(family, relation::DependencyLimits::bytes - bytes);
  }

  llvm::Error charge(size_t size, size_t maximum) {
    if (size > maximum)
      return zkc::error("relation-dependency-limit");
    bytes += size;
    return llvm::Error::success();
  }
};

inline llvm::Error dependencyError(const Input &input,
                                   const DependencyDeclarations &declarations) {
  if (declarations.diagnostics.empty())
    return zkc::error("source-syntax");
  const auto &d = declarations.diagnostics.front();
  const auto span = d.location.value_or(source::Span{});
  auto error = diagnostic(input.text(), input.filename(), span.offset, d.code,
                          d.message);
  llvm::Error result = llvm::Error::success();
  llvm::handleAllErrors(std::move(error),
                        [&](const SourceDiagnostic &rendered) {
                          result = llvm::make_error<SourceDiagnostic>(
                              d.code, d.message, rendered.rendered, span);
                        });
  return result;
}
} // namespace zkc::frontend::loading
#endif
