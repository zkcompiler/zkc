#ifndef ZKC_LANGUAGE_DECLARATIONINDEX_H
#define ZKC_LANGUAGE_DECLARATIONINDEX_H
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Project.h"
#include <functional>
#include <map>
namespace zkc::language {
struct SourceAccess {
  DeclarationId context;
};
/// Graph formation defers visibility until module contracts are known. The
/// binding loader excludes this import's own introduced names.
struct ImportBindingAccess {
  DeclarationId context;
  uint32_t import;
};
/// External static terms share project namespaces and permit private access.
/// Entry eligibility/short-name uniqueness is a separate selection policy.
struct ExternalSelectionAccess {};
using AccessContext =
    std::variant<SourceAccess, ImportBindingAccess, ExternalSelectionAccess>;
enum class LookupFailureKind {
  NotFound,
  Inaccessible,
  Ambiguous,
  WrongCategory,
  Cycle,
  Limit
};
struct LookupFailure {
  LookupFailureKind kind;
  std::optional<DeclarationId> selected;
  std::string segment;
  std::optional<Span> definition = {};
};
using LookupResult = std::variant<ResolvedReference, LookupFailure>;
/// Hooks allow bounded lazy import formation without a second traversal. A
/// rejected hook retains its diagnostic at the caller and terminates lookup.
struct LookupTraversal {
  std::function<bool()> charge;
  std::function<std::optional<LookupFailure>(DeclarationId, llvm::StringRef)>
      load;
};
/// The only declaration namespace owner, formed before signatures and frozen
/// after import authorization. Lexical frames remain with their lexical owner.
class DeclarationIndex {
public:
  struct NamespaceBinding {
    DeclarationId target;
    Span span;
    bool isPublic;
    std::optional<DeclarationId> provider;
    std::optional<uint32_t> import = {};
  };
  using Namespace = std::map<std::string, NamespaceBinding>;
  bool add(const Declaration &, SourceOrigin);
  Namespace &formingNamespace(DeclarationId);
  const Namespace &bindings(DeclarationId) const;
  void finish(llvm::ArrayRef<Declaration>, llvm::ArrayRef<SourceBuffer>);
  LookupResult lookup(const AccessContext &, llvm::StringRef,
                      const LookupTraversal & = {}) const;
  /// Nearest declaration/import scope only, for lexical shadowing checks.
  /// Captured roots and the prelude do not prevent a lexical binder.
  LookupResult scopeBinding(const AccessContext &, llvm::StringRef,
                            const LookupTraversal & = {}) const;
  LookupResult member(const AccessContext &, DeclarationId, llvm::StringRef,
                      const LookupTraversal & = {}) const;
  LookupResult homeMember(const AccessContext &, DeclarationId, llvm::StringRef,
                          const LookupTraversal & = {}) const;
  /// Accessible nearest bindings, including the explicit prelude adapter.
  std::map<std::string, ResolvedReference> accessible(SourceAccess) const;
  const protocol::FrontendDeclaration *association(DeclarationId) const;
  const protocol::FrontendDeclaration *ruleAssociation(DeclarationId) const;
  const protocol::ServiceMethodDeclaration *
      serviceAssociation(DeclarationId) const;
  /// Replay installed identity and ownership against the frozen namespace.
  bool matchesInstallation(llvm::ArrayRef<Declaration>,
                           llvm::ArrayRef<SourceBuffer>) const;
  std::optional<DeclarationId> home(const Type &) const;
  llvm::ArrayRef<DeclarationId> members(DeclarationId) const;
  /// Internal exact identity joins only; never source name resolution.
  std::optional<DeclarationId> canonical(llvm::StringRef) const;
  uint64_t bindingCount() const;

private:
  struct InstallationIdentity {
    std::string name, qualifiedName;
    Span span;
    bool isPublic, anonymous;
  };
  struct Node {
    std::optional<DeclarationId> parent;
    DeclarationId module;
    Declaration::Kind kind;
    ResolutionCategory category;
    SourceOrigin origin;
    std::optional<InstallationIdentity> installation;
  };
  std::vector<Node> nodes;
  std::vector<Namespace> namespaces;
  bool frozen = false;
  bool within(DeclarationId, DeclarationId) const;
  std::optional<DeclarationId> context(const AccessContext &) const;
  std::map<uint32_t, const protocol::FrontendDeclaration *> associations;
  std::map<uint32_t, const protocol::ServiceMethodDeclaration *>
      serviceAssociations;
  std::map<std::string, DeclarationId> canonicalDeclarations, roots;
  /// Only installed rows with explicit prelude membership enter this scope.
  Namespace prelude;
  std::map<std::string, DeclarationId> nominalHomes, constructorHomes;
  std::map<uint32_t, std::vector<DeclarationId>> moduleMembers;
};
} // namespace zkc::language
#endif
