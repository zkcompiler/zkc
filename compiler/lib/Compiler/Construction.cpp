#include "zkc/Compiler/Construction.h"
#include "../Protocol/Construction.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Resolution.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Translation/Protocol.h"
#include <set>
using namespace llvm;
namespace zkc::protocol {
namespace {
Expected<ConstructionResult> constructAlgorithms(
    const source::Module &prepared, const source::Module &original,
    const source::Construction &descriptor, mlir::MLIRContext &ctx) {
  if (descriptor.draws.size() > 32768)
    return error("construction-descriptor-limit");
  bool calls = false;
  for (const auto &fn : prepared.functions)
    if (fn.body)
      source::walk(*fn.body, [&](const source::Instruction &ins) {
        calls |= ins.get<source::AlgorithmCall>() != nullptr;
      });
  // A selector (definition, site) selects every expanded copy of that
  // definition's primitive, and a function's own name its direct site
  // (docs/spec/profiles/compiler/local-algorithms.md). A materialized
  // top-level configuration is such a copy: its origin is the definition.
  // Concrete names and logical origins may overlap in valid source; closed
  // selectors take their union. Normalized resolution checks that numbering
  // preserves each selected alias's occurrence membership before this step.
  using Selector = std::pair<std::string, std::string>;
  std::map<Selector, std::vector<Selector>> occurrences;
  std::optional<ExpandedAlgorithms> expanded;
  if (calls) {
    auto result = expandAlgorithms(prepared, ctx);
    if (!result)
      return result.takeError();
    expanded = std::move(*result);
    if (expanded->origins.size() > 1000000)
      return error("construction-analysis-limit");
    for (const auto &origin : expanded->origins)
      occurrences[{origin.definition, origin.originalSite}].emplace_back(
          origin.function, origin.site);
  } else {
    // Expansion keeps every site of a call-free module: record its
    // occurrences as expansion does, without re-serializing the module.
    size_t work = 0;
    for (const auto &fn : prepared.functions)
      if (fn.body)
        source::walk(*fn.body, [&](const source::Instruction &ins) {
          if (ins.get<source::Return>() || ins.get<source::Yield>() ||
              ++work > 1000000)
            return;
          occurrences[{fn.name, ins.site}].emplace_back(fn.name, ins.site);
          if (fn.origin && fn.origin->definition != fn.name)
            occurrences[{fn.origin->definition, ins.site}].emplace_back(
                fn.name, ins.site);
        });
    if (work > 1000000)
      return error("construction-analysis-limit");
  }
  // The descriptor selects the union of its selectors' occurrence sets, and
  // naming one selector twice is malformed
  // (docs/spec/profiles/compiler/local-algorithms.md).
  auto selected = descriptor;
  selected.draws.clear();
  std::set<Selector> selectors, chosen;
  for (const auto &selector : descriptor.draws) {
    if (!selectors.insert(selector).second)
      return error("construction-draw-selector");
    auto found = occurrences.find(selector);
    if (calls && found == occurrences.end())
      return error("construction-draw-selector");
    // A call-free module keeps its sites, so construction refuses a selector
    // without an occurrence where it checks every selector.
    const std::vector<Selector> direct{selector};
    for (const auto &copy :
         found == occurrences.end() ? direct : found->second) {
      if (!chosen.insert(copy).second)
        continue;
      if (selected.draws.size() == 32768)
        return error("construction-descriptor-limit");
      selected.draws.push_back(copy);
    }
  }
  auto preparation = prepareConstruction(
      expanded ? std::move(expanded->source) : prepared, original, selected);
  if (!preparation)
    return preparation.takeError();
  // Import the exact prepared original before analysis can consume its facts.
  auto checkedOriginal = importModule(preparation->source(), ctx);
  if (!checkedOriginal)
    return checkedOriginal.takeError();
  auto draft = std::move(*preparation).emit();
  if (!draft)
    return draft.takeError();
  auto candidate = importModule(draft->source, ctx);
  if (!candidate)
    return candidate.takeError();
  Expected<ConstructionResult> result(
      ConstructionResult{std::move(*candidate), std::move(draft->certificate)});
  if (printJson(result->certificate).size() > 1024 * 1024)
    return error("construction-byte-limit");
  // The certificate keeps the caller's selectors, which may be longer than
  // the occurrences they select.
  (*result->certificate.getAsArray())[1] = source::encode(descriptor);
  if (printJson(result->certificate).size() > 1024 * 1024)
    return error("construction-byte-limit");
  return result;
}
} // namespace
Expected<ConstructionResult> construct(const source::Module &module,
                                       const source::Construction &descriptor,
                                       mlir::MLIRContext &ctx) {
  // Programmatic records establish structure only. Validate both original
  // snapshots before resolution, preparation, or analysis can dereference them.
  if (auto e = source::checkStructure(module))
    return e;
  if (auto e = source::checkStructure(descriptor))
    return e;
  if (descriptor.identity == source::Construction::Identity::Normalized) {
    auto resolved = source::resolveProtocolSites(module);
    if (!resolved)
      return resolved.takeError();
    auto selected = resolved->descriptor(descriptor);
    if (!selected)
      return selected.takeError();
    Expected<source::Module> prepared = std::move(resolved->source);
    if (prepared->isLibrary())
      prepared = generic::prepareLibrary(*prepared);
    if (!prepared)
      return prepared.takeError();
    auto result = constructAlgorithms(*prepared, module, *selected, ctx);
    if (!result)
      return result.takeError();
    // The certificate retains the caller's original descriptor. Only the
    // executable copy uses derived occurrence coordinates.
    (*result->certificate.getAsArray())[1] = source::encode(descriptor);
    if (printJson(result->certificate).size() > 1024 * 1024)
      return error("construction-byte-limit");
    return result;
  }
  if (module.isLibrary()) {
    auto prepared = generic::prepareLibrary(module);
    if (!prepared)
      return prepared.takeError();
    return constructAlgorithms(*prepared, module, descriptor, ctx);
  }
  return constructAlgorithms(module, module, descriptor, ctx);
}
Error checkConstruction(const source::Module &source,
                        const source::Construction &descriptor,
                        const json::Value &candidate, mlir::MLIRContext &ctx) {
  auto expected = construct(source, descriptor, ctx);
  if (!expected)
    return expected.takeError();
  if (expected->certificate != candidate)
    return error("construction-candidate-mismatch");
  return Error::success();
}
} // namespace zkc::protocol
