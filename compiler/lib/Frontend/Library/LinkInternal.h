#ifndef ZKC_FRONTEND_LIBRARY_LINK_INTERNAL_H
#define ZKC_FRONTEND_LIBRARY_LINK_INTERNAL_H
#include "Internal.h"

namespace zkc::frontend::library::detail {
struct Selection;
struct LinkScope {
  std::map<std::string, Selection *> components;
  Substitution arguments;
  Selection *self = nullptr;
};
struct Selection {
  Implementation implementation;
  StaticTerm selected;
  LinkScope scope;
  std::string key, artifact;
  std::string normalizedSelection, captureIdentity;
  std::vector<std::string> paths;
};
struct World {
  Environment environment;
  std::vector<std::unique_ptr<Selection>> selections;
  std::map<std::string, Selection *> byKey;
  std::set<const Implementation *> active;
  std::map<const Implementation *, Selection *> resolved;
  uint64_t layoutSteps = 0;
  std::vector<Evidence> evidence;
  std::map<std::string, CheckedBody> helpers;
  std::map<std::string, LinkedFunction> helperFunctions;
  std::map<std::string, std::string> helperSymbols;
  std::map<std::string, DependencyRecord> helperDependencies;
  std::set<std::string> activeHelpers;
  llvm::Expected<std::string> helper(const SourceCall &, const LinkScope &);
  llvm::Error merge(const Environment &);
  llvm::Expected<Selection *> select(const Binding &, const std::string &path);
  llvm::Expected<LinkScope> scope(const CheckedBody &,
                                  const std::vector<Binding> &,
                                  const Substitution &,
                                  const std::string &path);
  llvm::Error validateArguments(const Substitution &);
  llvm::Expected<StaticTerm> term(const StaticTerm &, const LinkScope &,
                                  unsigned depth = 0);
  llvm::Expected<Type> type(const Type &, const LinkScope &,
                            unsigned depth = 0);
  llvm::Expected<Type> publicType(const Type &, const LinkScope &,
                                  unsigned depth = 0);
  llvm::Expected<Permissions> publicPermissions(const Type &,
                                                const LinkScope &);
  llvm::Expected<Signature> signature(const Signature &, const LinkScope &);
  llvm::Expected<std::vector<Requirement>>
  requirements(const std::vector<Requirement> &, const LinkScope &);
  llvm::Expected<Selection *> component(const StaticTerm &, const LinkScope &);
  llvm::Expected<Layout> layout(const Type &, const LinkScope &,
                                unsigned depth = 0);
  llvm::Error conform(Selection &);
  llvm::Error bounds(const std::vector<TypeBound> &, const LinkScope &);
  llvm::Expected<LinkedFunction>
  function(const CheckedBody &, const LinkScope &, std::string symbol,
           const Signature *publicSignature = nullptr,
           const LinkScope *publicScope = nullptr);
};
std::string functionSymbol(const Selection &, llvm::StringRef member);
} // namespace zkc::frontend::library::detail
#endif
