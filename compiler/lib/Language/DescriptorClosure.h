#ifndef ZKC_LANGUAGE_DESCRIPTORCLOSURE_H
#define ZKC_LANGUAGE_DESCRIPTORCLOSURE_H
#include "Semantics.h"
namespace zkc::language::detail {
class ValueOrigins;
struct DescriptorEnvironment {
  std::shared_ptr<const DescriptorShape> shape;
  /// SSA values in the body where this environment is consumed.
  std::vector<ValueId> operands;
};
/// Close one consumed descriptor, including every constructor in each selected
/// factory. Unrelated descriptors in the enclosing Body are not traversed.
std::optional<DescriptorEnvironment>
closeDescriptor(Semantics &, llvm::ArrayRef<Declaration>, const Body &,
                unsigned, const Substitution &,
                llvm::ArrayRef<DescriptorEnvironment>,
                ValueOrigins *cache = nullptr);
} // namespace zkc::language::detail
#endif
