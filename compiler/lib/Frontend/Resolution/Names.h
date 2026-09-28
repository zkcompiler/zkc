#ifndef ZKC_FRONTEND_RESOLUTION_NAMES_H
#define ZKC_FRONTEND_RESOLUTION_NAMES_H
#include "Project.h"
#include <functional>
namespace zkc::frontend::resolution {
// Authorization categories are taken from syntax, before any spelling is
// lowered into the shared string namespace. Data literals never enter here.
enum class ReferenceKind {
  Declaration,
  Value,
  Call,
  Constructor,
  Type,
  Static,
  Predicate
};
/// A resolved path: its declaration (absent for installed vocabulary words)
/// and the target recorded in syntax.
struct Resolved {
  const Declaration *declaration = nullptr;
  syntax::Target target;
};
/// The project resolver's two entry points for one module. `path` resolves
/// authored segments in one category; `exact` checks that a quoted atom names
/// installed vocabulary of that category. Both report their own diagnostics.
struct ModuleResolver {
  std::function<std::optional<Resolved>(const syntax::Path &,
                                        const source::Node &, ReferenceKind,
                                        bool signature)>
      path;
  std::function<void(llvm::StringRef, const source::Node &, ReferenceKind)>
      exact;
  /// The emitted symbol of a declaration this module defines, by its name.
  std::function<std::optional<std::string>(llvm::StringRef)> definition;
};
void qualify(syntax::Module &, const Context &, const ModuleResolver &);
} // namespace zkc::frontend::resolution
#endif
