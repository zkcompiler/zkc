#ifndef ZKC_FRONTEND_RESOLUTION_PROJECT_H
#define ZKC_FRONTEND_RESOLUTION_PROJECT_H

#include "../Syntax/Tree.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Library.h"
#include <set>

namespace zkc::frontend::resolution {
struct Declaration {
  enum class Kind {
    Association,
    Interface,
    Component,
    Link,
    Selection,
    Constant,
    Function,
    Protocol,
    Binding,
    Bundle,
    Record,
    Enum,
    Relation,
    View,
    Configuration,
    Instance,
    Entry,
    LogicalType,
    Operation,
    Capability
  };
  library::QualifiedDecl identity;
  Kind kind;
  uint32_t owner, file;
  bool exported;
  std::string symbol, origin;
  std::optional<source::Span> location;
  // Only installed declarations carry a logical contract. A source spelling
  // or an alias cannot confer this authority.
  std::string contract = {};
};
struct Owner {
  library::LibraryId identity;
  uint32_t root;
  std::map<std::string, uint32_t> dependencies;
};
struct Context {
  struct Reference {
    std::string source, target;
    std::optional<source::Span> location;
    bool signature;
  };
  ProjectInput input;
  std::vector<Owner> owners;
  std::vector<Declaration> declarations;
  std::map<std::string, uint32_t> symbols;
  std::map<std::string, uint32_t> nominalDeclarations;
  std::map<std::string, std::string> bindingContracts;
  // Disjoint top-level declaration intervals, sorted by offset per source file.
  std::vector<std::vector<uint32_t>> intervals;
  std::vector<std::set<uint32_t>> available;
  struct SelectorName {
    std::string name;
    bool exported, module;
    std::optional<uint32_t> target;
  };
  struct SelectorScope {
    std::optional<source::Span> location;
    std::vector<SelectorName> names;
  };
  std::vector<SelectorScope> selectorScopes;
  std::map<uint32_t, std::vector<std::string>> componentMembers;
  size_t selectorWork = 0;
  bool carrier = false;
  std::set<std::string> ambiguousOrigins;
  std::vector<uint32_t> order;
  std::vector<Reference> references;
  // Modules explicitly imported or named in each source file. Installed
  // operators use this scope; merely installing a package grants no lookup.
  std::map<uint32_t, std::set<std::string>> installedModules;
  // Ordinary source operator targets retain the resolver's visibility rules.
  std::map<uint32_t, std::set<std::string>> sourceOperators;
  std::set<std::string> unavailable;
  explicit Context(ProjectInput input) : input(std::move(input)) {}
  const Declaration *lookup(llvm::StringRef) const;
  const Declaration *lookup(const library::QualifiedDecl &) const;
  const Declaration *enclosing(const source::Node &) const;
  library::Environment environment(const library::Environment &,
                                   const library::QualifiedDecl &) const;
  library::QualifiedDecl qualify(llvm::StringRef name,
                                 llvm::ArrayRef<std::string> module = {}) const;
  std::string origin(const library::QualifiedDecl &) const;
  bool operationAvailable(const source::Node &, llvm::StringRef contract) const;
  bool sourceOperatorAvailable(const source::Node &,
                               llvm::StringRef symbol) const;
};
struct Result {
  syntax::Content content;
  std::shared_ptr<const Context> context;
  std::vector<Diagnostic> diagnostics;
  bool syntaxPartial = false;
  std::optional<syntax::Content> recoverable;
};
/// Resolve captured syntax by declaration identity. Lower-level single-module
/// checkers consume injectively named AST references, never concatenated text.
/// Construction selectors are a property of a construction request, so their
/// index, bounds and ambiguities are computed only when one is being bound.
Result resolve(const ProjectInput &);
struct SelectorIndex {
  std::map<std::string, uint32_t> selectors, entrySelectors;
  std::set<std::string> ambiguousOrigins;
};
llvm::Expected<SelectorIndex> constructionSelectors(const Context &);
} // namespace zkc::frontend::resolution
#endif
