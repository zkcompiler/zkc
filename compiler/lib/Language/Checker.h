#ifndef ZKC_LANGUAGE_CHECKER_H
#define ZKC_LANGUAGE_CHECKER_H
#include "Internal.h"
namespace zkc::language::detail {
Type parameterType(const Parameter &);
bool valueType(const Type &);
using Substitution = std::map<std::string, Type>;
class Checker {
public:
  Checker(std::vector<SyntaxModule>, CheckedStorage &, Work &);
  Checker(CheckedStorage &, Work &);
  llvm::Error run();
  CheckedStorage &output;
  Work &work;
  NaturalArithmetic naturals;
  std::optional<Diagnostic> diagnostic;
  std::vector<SyntaxDeclaration *> sources;
  std::vector<unsigned> bodyState, bodyHeights;
  bool fail(llvm::StringRef, const llvm::Twine &, Span, std::vector<Span> = {});
  bool accept(llvm::Error);
  bool charge(uint64_t, Span);
  bool chargeType(const Type &, Span);
  llvm::Error takeError();
  std::optional<DeclarationId> resolve(const Declaration &, llvm::StringRef,
                                       Span);
  std::optional<Type> type(const Declaration &, const SyntaxType &,
                           unsigned = 1);
  std::optional<Type> substitute(const Type &, const Substitution &, Span,
                                 unsigned = 1);
  std::optional<Permissions> permissions(const Type &, Span,
                                         const Declaration *scope = nullptr,
                                         unsigned = 1);
  std::optional<std::vector<TypeField>> fields(const Type &, Span,
                                               unsigned = 1);
  std::optional<std::vector<Alternative>> alternatives(const Type &, Span,
                                                       unsigned = 1);
  std::optional<std::vector<unsigned>> roles(const Declaration &,
                                             llvm::ArrayRef<std::string>, Span);
  std::optional<std::vector<Type>> arguments(const Declaration &,
                                             const Declaration &,
                                             llvm::ArrayRef<SyntaxType>, Span);
  bool checkArguments(const Declaration &, llvm::ArrayRef<Type>, Span,
                      const Declaration *context = nullptr,
                      const Substitution &extra = {});
  bool assumptions(const Declaration &, const NaturalBound &,
                   const Substitution &, Span);
  const Parameter *parameter(llvm::StringRef) const;
  const Declaration *typeDeclaration(const Type &) const;
  bool constructorAllowed(const Declaration &, const Type &) const;
  bool ingress(const Type &, Span);
  // Checks representation, not permissions: even a zero-length formal array
  // cannot become a runtime Type argument, port, region carrier or local value.
  bool executableType(const Type &, Span, unsigned = 1);
  bool mathematicalData(const Type &, Span, const Declaration * = nullptr,
                        unsigned = 1);
  bool bindingName(const Declaration &, llvm::StringRef, Span);
  bool body(DeclarationId, unsigned);
  bool specialize(DeclarationId);
  struct CallSignature {
    std::vector<Type> inputs, outputs;
    Type resultType() const;
  };
  std::optional<CallSignature> kernelSignature(llvm::StringRef,
                                               llvm::ArrayRef<Type>,
                                               llvm::ArrayRef<std::string>,
                                               Span);
  std::optional<CallSignature>
  intrinsicSignature(const Declaration *, llvm::StringRef, llvm::ArrayRef<Type>,
                     llvm::ArrayRef<std::string>, Span);
  bool symbolic(const Type &) const;
  Substitution substitution(const Declaration &, llvm::ArrayRef<Type>) const;
  std::optional<Type> associated(const Type &, llvm::StringRef, Span);

private:
  std::vector<SyntaxModule> syntax;
  std::map<std::string, ModuleId> modules;
  std::map<std::string, DeclarationId> qualified;
  std::vector<std::map<std::string, DeclarationId>> visible;
  std::vector<unsigned> signatureState;
  std::map<std::string, std::pair<DeclarationId, unsigned>> parameters;
  bool representations();
  bool chargeStaticSignature(const Declaration &);
  struct DeferredApplication {
    DeclarationId target;
    std::vector<Type> arguments;
    Span span;
  };
  std::set<unsigned> formingParameters;
  std::map<unsigned, std::vector<DeferredApplication>> deferredApplications;
  uint64_t typeNodes = 0;
  bool entries();
  bool collect();
  bool imports();
  bool signature(DeclarationId, unsigned = 1);
  bool conformance(DeclarationId);
  bool requirements(Declaration &);
};
} // namespace zkc::language::detail
#endif
