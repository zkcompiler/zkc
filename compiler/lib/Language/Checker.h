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
  std::vector<std::shared_ptr<const NotationEnvironment>> notationEnvironments;

  std::optional<DeclarationId> resolve(const Declaration &, llvm::StringRef,
                                       Span, bool required = true);
  std::optional<Type> type(const Declaration &, const SyntaxType &,
                           unsigned = 1);

  std::optional<std::vector<unsigned>> roles(const Declaration &,
                                             llvm::ArrayRef<std::string>, Span);
  std::optional<std::vector<Type>>
  arguments(const Declaration &, const Declaration &,
            llvm::ArrayRef<SyntaxType>, Span,
            llvm::ArrayRef<ArgumentLabel> = {});

  bool bindingName(const Declaration &, llvm::StringRef, Span);
  std::optional<CallableReference> callable(const Declaration &,
                                            llvm::StringRef, Span);
  std::optional<OperatorBinding> operatorBinding(const Declaration &,
                                                 const SyntaxOperator &);
  std::optional<std::vector<OperatorBinding>>
  operatorCandidates(const Declaration &, const SyntaxDeclaration &, uint32_t);
  std::optional<std::vector<OperatorBinding>>
  operatorWitnessFamily(const Declaration &, const SyntaxDeclaration &,
                        uint32_t);
  bool body(DeclarationId, unsigned);
  bool primitiveBody(Declaration &, Body &);
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
  std::vector<std::map<std::string, DeclarationId>> exportedNames;
  std::vector<std::map<std::string, ModuleId>> aliases, exportedAliases;
  using OperatorSite = std::pair<unsigned, unsigned>;
  std::vector<std::vector<OperatorSite>> visibleOperators, exportedOperators;
  std::map<OperatorSite, OperatorBinding> moduleOperators;
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
  std::vector<unsigned> importOrder;
  bool prepareNotationSyntax();
  bool prepareOperators();
  std::optional<DeclarationId> moduleMember(ModuleId, llvm::StringRef, Span,
                                            unsigned = 1);
  bool signature(DeclarationId, unsigned = 1);
  bool conformance(DeclarationId);
  bool requirements(Declaration &);
};
bool resolveBindings(Checker &, Declaration &, SyntaxDeclaration &);
bool elaborateExpressions(Checker &, SyntaxDeclaration &);
/// Source depth accounting follows whether the call retains a helper boundary.
bool primitiveCallIsInline(Body::Mode, llvm::StringRef identity);
} // namespace zkc::language::detail
#endif
