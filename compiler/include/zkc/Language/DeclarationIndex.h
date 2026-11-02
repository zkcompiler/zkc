#ifndef ZKC_LANGUAGE_DECLARATIONINDEX_H
#define ZKC_LANGUAGE_DECLARATIONINDEX_H
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Project.h"
#include <map>
namespace zkc::language {
/// Frozen canonical declaration associations. Source spelling, nominal identity
/// and installed semantic constructor identity have separate lookup keys.
/// Future View/family adapters extend catalog rules and CallBinding, not a
/// second callable registry. Placement remains separate from ordinary Type.
class DeclarationIndex {
public:
  struct NamespaceBinding {
    DeclarationId declaration;
    bool isPublic;
  };
  using Namespace = std::map<std::string, NamespaceBinding>;
  DeclarationIndex(llvm::ArrayRef<Declaration>, llvm::ArrayRef<SourceBuffer>,
                   std::vector<Namespace>);
  std::optional<DeclarationId> lookup(DeclarationId context,
                                      llvm::StringRef) const;
  const protocol::FrontendDeclaration *association(DeclarationId) const;
  std::optional<DeclarationId> implicit(llvm::StringRef) const;
  std::optional<DeclarationId> home(const Type &) const;
  llvm::ArrayRef<DeclarationId> members(DeclarationId) const;
  std::optional<DeclarationId> canonical(llvm::StringRef) const;

private:
  std::vector<Namespace> namespaces;
  std::vector<std::optional<DeclarationId>> parents;
  std::map<uint32_t, const protocol::FrontendDeclaration *> associations;
  std::map<std::string, DeclarationId> implicitDeclarations,
      canonicalDeclarations;
  std::map<std::string, DeclarationId> nominalHomes, constructorHomes;
  std::map<uint32_t, std::vector<DeclarationId>> moduleMembers;
};
} // namespace zkc::language
#endif
