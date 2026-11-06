#ifndef ZKC_LANGUAGE_DESCRIPTORFACTORIES_H
#define ZKC_LANGUAGE_DESCRIPTORFACTORIES_H
#include "Semantics.h"
namespace zkc::language::detail {
class Checker;
struct BindingId;
struct SyntaxDeclaration;
/// Shared structural authoring judgment. Data evaluation and SSA ownership
/// stay with the enclosing checker; factory bodies use only named data ports.
std::optional<unsigned> authorDescriptorExpression(
    Checker &, Declaration &, const SyntaxDeclaration &,
    std::vector<DescriptorBinding> &, const std::map<BindingId, unsigned> &,
    const std::map<BindingId, ValueId> &, std::function<const Type *(ValueId)>,
    std::function<std::optional<ValueId>(uint32_t,
                                         const std::optional<Type> &)>,
    uint32_t, unsigned callDepth, std::optional<Type> expected = {});
/// Interpret only the existing static Natural syntax, never runtime data or
/// arbitrary calls. Normalization belongs to Checker/ NaturalArithmetic.
std::optional<Type> descriptorSelector(Checker &, const Declaration &,
                                       const SyntaxDeclaration &, uint32_t);
/// Infer only a source call's declared result from rigid argument evidence,
/// using the ordinary signature constraint solver. No body is expanded.
std::optional<Type>
descriptorCallContract(Checker &, const Declaration &,
                       const SyntaxDeclaration &, uint32_t,
                       llvm::function_ref<std::optional<Type>(uint32_t)> rigid);
/// Structural View judgment, separate from ordinary Math purity/effects.
bool checkViewStructure(Checker &, const Declaration &,
                        const SyntaxDeclaration &);
/// Pure installed Finite signature judgment; constructs no expected recipe.
bool descriptorConstructorSignature(const Declaration &,
                                    DescriptorBinding::Kind, unsigned axis);
/// The same installed leaf judgment over borrowed closed signature ports.
bool finiteConstructorSignature(
    const DescriptorContract &, DescriptorBinding::Kind, unsigned axis,
    unsigned dataCount, llvm::function_ref<const Type &(unsigned)> data,
    unsigned childCount,
    llvm::function_ref<const DescriptorContract &(unsigned)> child);
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
/// Ordinary indexed member binding and independent header admission. Witness
/// readers pass authorBody=false and never reconstruct a descriptor producer.
std::optional<SelectedViewMember>
selectDescriptorView(Checker &, const Declaration &, const SyntaxDeclaration &,
                     uint32_t, const Type &, unsigned callDepth,
                     bool authorBody);
struct DescriptorOperands {
  std::vector<ValueId> values;
  bool parameterized = false;
};
std::optional<DescriptorOperands>
descriptorOperands(Semantics &, const Body &, llvm::ArrayRef<unsigned>, Span);
} // namespace zkc::language::detail
#endif
