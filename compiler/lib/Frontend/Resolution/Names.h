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
  QualifiedCall,
  Constructor,
  Type,
  Static,
  Predicate
};
using ReferenceResolver = std::function<const Declaration *(
    std::string &, const source::Node &, ReferenceKind, bool signature,
    bool quoted)>;
void qualify(syntax::Module &, const Context &, const ReferenceResolver &);
} // namespace zkc::frontend::resolution
#endif
