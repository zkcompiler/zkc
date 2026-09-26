#ifndef ZKC_FRONTEND_MODEL_MODULE_H
#define ZKC_FRONTEND_MODEL_MODULE_H
#include "Body.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Module.h"
#include "zkc/Frontend/Work.h"
#include <map>

namespace zkc::frontend::resolution {
struct Context;
}

namespace zkc::frontend::model {
struct LibraryReport;
/// A checked definition body; call targets are scoped references, not strings
/// or positional entries in a parallel table.
struct DefinitionBody {
  bool emit = true;
  DeclId declaration;
  std::optional<model::Body> body;
  std::optional<source::LogicalOrigin> origin;
  source::Names roles, naturalParameters;
  std::vector<source::Dependency> dependencies;
};
struct Module {
  WorkUsage workUsage{};
  /// Owns the captured input for analyzed source, including partial analyses.
  /// Raw standalone model utilities may leave resolution absent.
  std::shared_ptr<const resolution::Context> resolution;
  bool resolutionComplete = false;
  std::string text, filename;
  bool syntaxPartial = false;
  std::vector<Scope> scopes;
  std::vector<Declaration> declarations;
  std::vector<Type> types;
  std::vector<Domain> domains;
  std::vector<ResolvedUse> uses;
  std::vector<LocalBinding> bindings;
  std::vector<ValueUse> valueUses;
  std::map<TypeId, std::vector<Port>> layouts;
  std::vector<Instantiation> instantiations;
  std::vector<Diagnostic> diagnostics;
  std::vector<SemanticDependency> dependencies;
  std::vector<DefinitionBody> bodies;
  /// Carrier-only metadata; callable headers and bodies are emitted from the
  /// typed declarations/plans, never recovered from these records.
  source::Module metadata;
  std::optional<source::Construction> construction;
  std::map<std::pair<ScopeId, std::string>, DeclId> names;
  std::map<std::string, DomainId> domainKeys;
  std::map<std::string, TypeId> typeKeys;
  std::shared_ptr<const model::LibraryReport> libraries = {};

  Module();
  ScopeId addScope(ScopeId parent, DeclId owner);
  DeclId add(Declaration::Kind, ScopeId, llvm::StringRef,
             std::optional<source::Span> = {});
  DeclId lookup(ScopeId, llvm::StringRef) const;
  DomainId internDomain(llvm::StringRef, ScopeId, llvm::StringRef sort = {});
  TypeId logical(llvm::StringRef, ScopeId);
  TypeId record(DeclId, llvm::ArrayRef<std::string>, ScopeId);
  TypeId product(llvm::ArrayRef<TypeId>);
  TypeId array(TypeId element, uint64_t count);
  TypeId intern(Type);
  std::string spelling(DomainId) const;
  std::string spelling(TypeId) const;
  std::vector<Port> leaves(const Port &) const;
  DomainId substitute(DomainId, const std::map<DeclId, DomainId> &);
  TypeId substitute(TypeId, const std::map<DeclId, DomainId> &);
  bool containsChecked(TypeId) const;
};
} // namespace zkc::frontend::model
#endif
