#ifndef ZKC_FRONTEND_SEMANTICS_PROTOCOLS_H
#define ZKC_FRONTEND_SEMANTICS_PROTOCOLS_H
#include "../Model/Module.h"
#include "../Syntax/Tree.h"
#include <functional>
namespace zkc::frontend::semantics {
/// One source type/role/requirement checker for abstract and concrete
/// protocols. This does not establish affine correctness or common PIR
/// admission.
struct CheckedPlacement {
  DeclId function;
  source::Names captures;
};
using CheckPlacement = std::function<std::optional<CheckedPlacement>(
    const syntax::Placement &, const source::Instruction &,
    llvm::ArrayRef<Port>, bool emit)>;
bool checkProtocolBody(model::Module &, const syntax::Protocol &,
                       const std::function<TypeId(const syntax::Type &)> &,
                       const CheckPlacement &,
                       source::Protocol *emitted = nullptr);
} // namespace zkc::frontend::semantics
#endif
