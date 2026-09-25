#include "zkc/Frontend/Analysis.h"
#include "../Model/Module.h"
#include "Access.h"
#include "zkc/Frontend/Compile.h"

using namespace llvm;
namespace zkc::frontend {
Analysis::Analysis(std::shared_ptr<const model::Module> model)
    : model(std::move(model)) {}
StringRef Analysis::sourceText() const { return model->text; }
StringRef Analysis::filename() const { return model->filename; }
const ProjectInput *Analysis::project() const {
  return model->project ? &*model->project : nullptr;
}
bool Analysis::complete() const {
  return model->complete && model->diagnostics.empty();
}
AnalysisState Analysis::state() const {
  for (const auto &d : model->diagnostics)
    if (isResourceLimitDiagnostic(d.code))
      return AnalysisState::ResourceLimit;
  return model->syntaxPartial ? AnalysisState::SyntaxPartial
         : complete()         ? AnalysisState::SourceChecked
                              : AnalysisState::SemanticError;
}
bool Analysis::resolutionComplete() const { return model->resolutionComplete; }
ArrayRef<SemanticDependency> Analysis::dependencies() const {
  return model->dependencies;
}
ArrayRef<Scope> Analysis::scopes() const { return model->scopes; }
ArrayRef<Declaration> Analysis::declarations() const {
  return model->declarations;
}
ArrayRef<Type> Analysis::types() const { return model->types; }
ArrayRef<Domain> Analysis::domains() const { return model->domains; }
ArrayRef<ResolvedUse> Analysis::uses() const { return model->uses; }
ArrayRef<LocalBinding> Analysis::bindings() const { return model->bindings; }
ArrayRef<ValueUse> Analysis::valueUses() const { return model->valueUses; }
ArrayRef<Instantiation> Analysis::instantiations() const {
  return model->instantiations;
}
ArrayRef<Diagnostic> Analysis::diagnostics() const {
  return model->diagnostics;
}
const Declaration *Analysis::declaration(DeclId id) const {
  return id.index < model->declarations.size() ? &model->declarations[id.index]
                                               : nullptr;
}
const Type *Analysis::type(TypeId id) const {
  return id.index < model->types.size() ? &model->types[id.index] : nullptr;
}
const Domain *Analysis::domain(DomainId id) const {
  return id.index < model->domains.size() ? &model->domains[id.index] : nullptr;
}
std::optional<DeclId> Analysis::lookup(ScopeId scope, StringRef name) const {
  auto id = model->lookup(scope, name);
  return id.valid() ? std::optional<DeclId>(id) : std::nullopt;
}
std::string Analysis::display(TypeId id) const {
  const auto *t = type(id);
  if (!t)
    return "<unresolved>";
  if (t->kind == Type::Kind::Logical)
    return model->spelling(id);
  if (t->kind == Type::Kind::Array)
    return "Array<" + display(t->elements.front()) + ", " +
           std::to_string(t->count) + ">";
  if (t->kind == Type::Kind::Product) {
    std::string result = "(";
    for (size_t i = 0; i < t->elements.size(); ++i) {
      if (i)
        result += ", ";
      result += display(t->elements[i]);
    }
    return result + (t->elements.size() == 1 ? ",)" : ")");
  }
  const auto *d = declaration(t->declaration);
  std::string result =
      d ? (d->displayName.empty() ? d->name : d->displayName) : "<unresolved>";
  if (!t->arguments.empty()) {
    result += "<";
    for (size_t i = 0; i < t->arguments.size(); ++i) {
      if (i)
        result += ", ";
      result += display(t->arguments[i]);
    }
    result += ">";
  }
  return result;
}
std::string Analysis::display(DomainId id) const {
  return domain(id) ? model->spelling(id) : "<unresolved>";
}
Expected<CheckedModule> Analysis::checkedModule() const {
  if (!complete()) {
    if (!model->diagnostics.empty()) {
      const auto &d = model->diagnostics.front();
      if (model->project)
        return diagnostic(*model->project, d);
      return diagnostic(model->text, model->filename,
                        d.location ? d.location->offset : 0, d.code, d.message);
    }
    // Analysis marks a model incomplete only while recording why.
    report_fatal_error("an incomplete analysis carries no diagnostic");
  }
  return CheckedModule(model);
}
Expected<source::Content> Analysis::lower() const {
  auto checked = checkedModule();
  if (!checked)
    return checked.takeError();
  return frontend::lower(*checked);
}

} // namespace zkc::frontend
