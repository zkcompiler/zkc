#ifndef ZKC_LANGUAGE_BODYMAPPING_H
#define ZKC_LANGUAGE_BODYMAPPING_H
#include "zkc/Language/Project.h"
#include <functional>
namespace zkc::language::detail {
/// Visit SSA references in this body only; nested regions have their own SSA.
void mapBodyValues(Body &, const std::function<ValueId(ValueId)> &);
/// Insert hidden formal inputs after authored inputs, preserving operation
/// order.
std::vector<ValueId> appendBodyInputs(Body &, llvm::ArrayRef<Value>);
} // namespace zkc::language::detail
#endif
