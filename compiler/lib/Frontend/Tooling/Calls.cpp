#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Protocol.h"
using namespace llvm;
namespace zkc::frontend {
namespace {
json::Array calls(const Analysis &analysis) {
  json::Array report;
  for (const auto &use : analysis.uses()) {
    if (use.kind != ResolvedUse::Kind::Call)
      continue;
    const auto *owner = analysis.declaration(use.owner);
    const auto *target = analysis.declaration(use.target);
    if (!owner || !target)
      continue;
    json::Array arguments, results, required;
    for (const auto &binding : use.bindings)
      arguments.push_back(analysis.display(binding.argument));
    for (const auto &result : use.results)
      results.push_back(json::Object{{"name", result.name},
                                     {"type", analysis.display(result.type)}});
    for (const auto &requirement : use.requirements) {
      json::Array terms;
      for (auto term : requirement.arguments)
        terms.push_back(analysis.display(term));
      required.push_back(json::Object{{"predicate", requirement.predicate},
                                      {"arguments", std::move(terms)}});
    }
    report.push_back(json::Object{
        {"owner", owner->name},
        {"site", use.site},
        {"callee", target->name},
        {"kind", !use.role.empty() ? "local"
                 : target->kind == Declaration::Kind::Function ||
                         target->kind == Declaration::Kind::Configuration
                     ? "algorithm"
                     : "operation"},
        {"static_arguments", std::move(arguments)},
        {"callee_requirements", std::move(required)},
        {"static_origin", use.writtenArguments   ? "written"
                          : use.bindings.empty() ? "none"
                                                 : "inferred"},
        {"results", std::move(results)},
        {"offset", int64_t(use.location ? use.location->offset : 0)},
        {"file", int64_t(use.location ? use.location->file : 0)}});
  }
  return report;
}
} // namespace
Expected<json::Array> inspectProtocolElaboration(StringRef text,
                                                 StringRef filename) {
  if (text.empty() || text.ltrim().starts_with("["))
    return json::Array{};
  return inspectProtocolElaboration(analyzeProtocol(text, filename));
}
Expected<json::Array> inspectProtocolElaboration(const Analysis &analysis) {
  if (!analysis.complete()) {
    auto result = analysis.lower();
    return result.takeError();
  }
  return calls(analysis);
}
} // namespace zkc::frontend
