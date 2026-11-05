#ifndef ZKC_LANGUAGE_DESCRIPTORFACTORIES_H
#define ZKC_LANGUAGE_DESCRIPTORFACTORIES_H
#include "Semantics.h"
namespace zkc::language::detail {
class Checker;
struct SyntaxDeclaration;
/// Structural View judgment, separate from ordinary Math purity/effects.
bool checkViewStructure(Checker &, const Declaration &,
                        const SyntaxDeclaration &);
/// The one collection-to-domain conversion. Matrices require an explicit view.
std::optional<Type> finiteDomainElement(const Type &);
std::optional<unsigned> collectionDomain(Semantics &, const Type &, ValueId,
                                         std::vector<DescriptorBinding> &,
                                         uint32_t expression, Span);
/// Retain a typed factory selection in an enclosing static environment.
/// Data operands have already been evaluated in source order by the caller.
/// Complete recipe expansion belongs to joint domain/callback specialization.
std::optional<unsigned> instantiateDescriptor(
    Semantics &, const Declaration &, const CallableReference &,
    llvm::ArrayRef<Type>, llvm::ArrayRef<ValueId>, llvm::ArrayRef<unsigned>,
    llvm::ArrayRef<unsigned>, std::vector<DescriptorBinding> &,
    uint32_t expression, Span);
struct DescriptorOperands {
  std::vector<ValueId> values;
  bool parameterized = false;
};
std::optional<DescriptorOperands>
descriptorOperands(Semantics &, const Body &, llvm::ArrayRef<unsigned>, Span);
} // namespace zkc::language::detail
#endif
