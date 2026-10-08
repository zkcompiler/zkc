#ifndef ZKC_LANGUAGE_SEMANTICS_H
#define ZKC_LANGUAGE_SEMANTICS_H
#include "State.h"
#include <functional>
namespace zkc::language::detail {
Type parameterType(const Parameter &);
bool valueType(const Type &);
using Substitution = std::map<std::string, Type>;

/// Semantic queries over declaration metadata. The vector object outlives this
/// view; queries never retain element pointers across specialization. Source
/// checking supplies the sole lazy-signature hook. Closed queries have none.
class Semantics {
public:
  Semantics(const std::vector<Declaration> &, Work &,
            std::function<bool(DeclarationId)> complete = {});
  void indexDeclaration(const Declaration &);
  void indexParameter(const Parameter &, DeclarationId, unsigned);
  Work &work;
  NaturalArithmetic naturals;
  std::optional<Diagnostic> diagnostic;
  struct CallSignature {
    std::vector<Type> inputs, outputs;
    Type resultType() const;
  };

  bool chargeType(const Type &, Span);
  const Parameter *parameter(llvm::StringRef) const;
  const Declaration *typeDeclaration(const Type &) const;
  bool symbolic(const Type &) const;
  Substitution substitution(const Declaration &, llvm::ArrayRef<Type>) const;
  std::optional<Type> substitute(const Type &, const Substitution &, Span,
                                 unsigned = 1);
  std::optional<Type> associated(const Type &, llvm::StringRef, Span);
  std::optional<Permissions> permissions(const Type &, Span,
                                         const Declaration *scope = nullptr,
                                         unsigned = 1);
  std::optional<std::vector<TypeField>> fields(const Type &, Span,
                                               unsigned = 1);
  std::optional<std::vector<Alternative>> alternatives(const Type &, Span,
                                                       unsigned = 1);
  bool checkArguments(const Declaration &, llvm::ArrayRef<Type>, Span,
                      const Declaration *context = nullptr,
                      const Substitution &extra = {});
  bool assumptions(const Declaration &, const NaturalBound &,
                   const Substitution &, Span);
  bool capabilityFormation(const CapabilityBound &);
  bool entails(const Declaration *, const CapabilityBound &,
               llvm::StringRef code = "source.capability");
  bool constructorAllowed(const Declaration &, const Type &) const;
  bool ingress(const Type &, Span);
  // Checks representation, not permissions: even a zero-length formal array
  // cannot become a runtime Type argument, port, region carrier or local value.
  bool executableType(const Type &, Span, unsigned = 1);
  bool mathematicalData(const Type &, Span, const Declaration * = nullptr,
                        unsigned = 1);
  std::optional<Type> projectedType(const Declaration &, Type,
                                    llvm::ArrayRef<unsigned>, Span);
  std::optional<unsigned> fieldIndex(const Declaration &, const Type &,
                                     llvm::StringRef, Span);
  std::optional<Type> selectedType(const Declaration &,
                                   const SpecificationSelector &);
  std::optional<CallSignature> kernelSignature(llvm::StringRef,
                                               llvm::ArrayRef<Type>,
                                               llvm::ArrayRef<std::string>,
                                               Span, const Declaration *);
  std::optional<CallSignature>
  intrinsicSignature(const Declaration *, llvm::StringRef, llvm::ArrayRef<Type>,
                     llvm::ArrayRef<std::string>, Span);
  bool checkProofEntry(const Declaration &, const Declaration &);
  bool relationData(const Declaration &, const Type &, Span, unsigned = 0);
  bool fail(llvm::StringRef, const llvm::Twine &, Span, std::vector<Span> = {});
  bool accept(llvm::Error);
  bool charge(uint64_t, Span);
  llvm::Error takeError();

private:
  const std::vector<Declaration> &declarations;
  std::map<std::string, DeclarationId> qualified;
  std::map<std::string, std::pair<DeclarationId, unsigned>> parameters;
  std::function<bool(DeclarationId)> complete;
  unsigned normalizationDepth = 0;
};
llvm::Error specialize(std::vector<Declaration> &, Work &, DeclarationId);
} // namespace zkc::language::detail
#endif
