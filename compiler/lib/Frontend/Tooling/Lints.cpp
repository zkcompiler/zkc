#include "Lints.h"
#include "Access.h"
#include <map>
#include <set>

namespace zkc::frontend::tooling {
std::vector<Diagnostic> unusedBindingWarnings(const Analysis &analysis) {
  const auto &model = semantics::AnalysisAccess::get(analysis);
  std::set<DeclId> checked;
  for (const auto &body : model.bodies)
    if (body.body)
      if (const auto *owner = analysis.declaration(body.declaration))
        if (owner->bodyState == Declaration::BodyState::Checked)
          checked.insert(owner->id);

  std::set<ValueId> used;
  for (const auto &use : analysis.valueUses())
    used.insert(use.binding);
  std::map<std::pair<ScopeId, std::string>, const LocalBinding *> names;
  for (const auto &binding : analysis.bindings())
    names.emplace(std::make_pair(binding.scope, binding.name), &binding);

  // Flattened field names and their aggregate binding have distinct IDs.
  // A use of any field counts as a use of its source aggregate, while sharing
  // SSA leaves between unrelated lexical aliases does not count as a use.
  for (const auto &binding : analysis.bindings()) {
    if (!used.count(binding.id))
      continue;
    llvm::StringRef name(binding.name);
    while (name.contains('.')) {
      name = name.rsplit('.').first;
      auto parent = names.find({binding.scope, name.str()});
      if (parent != names.end())
        used.insert(parent->second->id);
    }
  }

  std::vector<Diagnostic> warnings;
  for (const auto &binding : analysis.bindings()) {
    if (!binding.location || binding.name.empty() ||
        llvm::StringRef(binding.name).starts_with("_") ||
        llvm::StringRef(binding.name).contains('.') || used.count(binding.id) ||
        binding.scope.index >= model.scopes.size())
      continue;
    const auto &scope = model.scopes[binding.scope.index];
    if (!checked.count(scope.owner))
      continue;

    // Explicit regions rebind captured names to the same typed leaves. These
    // aliases are not new source declarations. With no binding-kind metadata,
    // conservatively omit an identical ancestor alias (including a redundant
    // shadow), rather than inventing a second unused-local warning.
    bool capturedAlias = false;
    auto parent = scope.parent;
    for (size_t depth = 0;
         parent.index < model.scopes.size() && depth < model.scopes.size();
         ++depth) {
      auto ancestor = names.find({parent, binding.name});
      if (ancestor != names.end()) {
        capturedAlias = ancestor->second->type == binding.type &&
                        ancestor->second->leaves == binding.leaves;
        break;
      }
      parent = model.scopes[parent.index].parent;
    }
    if (capturedAlias)
      continue;
    Diagnostic warning{"source-unused-binding",
                       "unused local binding '" + binding.name + "'",
                       binding.location};
    if (const auto *owner = analysis.declaration(scope.owner))
      warning.causes.push_back(
          {DiagnosticCause::Kind::Declaration, owner->identity,
           owner->displayName.empty() ? owner->name : owner->displayName,
           owner->location});
    warnings.push_back(std::move(warning));
  }
  return warnings;
}
} // namespace zkc::frontend::tooling
