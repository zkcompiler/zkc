#ifndef ZKC_LANGUAGE_CHECKER_H
#define ZKC_LANGUAGE_CHECKER_H
#include "Internal.h"
#include "Semantics.h"
namespace zkc::language::detail {
class Checker {
public:
  Checker(std::vector<SyntaxModule>, CheckedStorage &, Work &);
  // Lazy signature completion captures this driver; keep its address stable.
  Checker(const Checker &) = delete;
  Checker &operator=(const Checker &) = delete;
  llvm::Error run();
  CheckedStorage &output;
  Work &work;
  Semantics types;
  std::vector<SyntaxDeclaration *> sources;
  std::vector<unsigned> bodyState, bodyHeights;

  std::optional<DeclarationId> resolve(const Declaration &, llvm::StringRef,
                                       Span, bool required = true);
  std::optional<Type> type(const Declaration &, const SyntaxType &,
                           unsigned = 1);

  std::optional<std::vector<unsigned>> roles(const Declaration &,
                                             llvm::ArrayRef<std::string>, Span);
  std::optional<std::vector<Type>> arguments(const Declaration &,
                                             const Declaration &,
                                             llvm::ArrayRef<SyntaxType>, Span);

  bool bindingName(const Declaration &, llvm::StringRef, Span);
  bool body(DeclarationId, unsigned);
  bool relation(Declaration &);

  std::map<unsigned, std::vector<SpecificationSelector>> inlineBindings;
  bool relationIdentities();
  bool specifications(Declaration &);

  std::optional<SpecificationSelector> selector(const Declaration &,
                                                const SyntaxSelector &);

  bool configureEntry(Declaration &, const Declaration &,
                      const SyntaxProofEntry &);

private:
  std::optional<Type> elaborateType(const Declaration &, const SyntaxType &,
                                    unsigned);
  std::vector<SyntaxModule> syntax;
  std::map<std::string, ModuleId> modules;
  std::map<std::string, DeclarationId> qualified;
  std::vector<std::map<std::string, DeclarationId>> visible;
  std::vector<unsigned> signatureState;
  std::set<const Declaration *> inferredContracts;
  unsigned signatureDepth = 0;
  bool representations();
  bool chargeStaticSignature(const Declaration &);
  struct DeferredApplication {
    DeclarationId target;
    std::vector<Type> arguments;
    Span span;
  };
  std::set<unsigned> formingParameters;
  std::map<unsigned, std::vector<DeferredApplication>> deferredApplications;
  bool entries();
  bool configureSetups(Declaration &, const Declaration &,
                       llvm::ArrayRef<SyntaxSetupSlot>);
  bool collect();
  bool imports();
  bool signature(DeclarationId, unsigned = 1);
  bool conformance(DeclarationId);
  bool requirements(Declaration &);
};
bool resolveBindings(Checker &, Declaration &, SyntaxDeclaration &);
} // namespace zkc::language::detail
#endif
