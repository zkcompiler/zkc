#ifndef ZKC_LANGUAGE_CHECKER_H
#define ZKC_LANGUAGE_CHECKER_H
#include "Internal.h"
#include "Semantics.h"
#include "UsagePlan.h"
#include <tuple>
namespace zkc::language::detail {
struct BodyWitnesses {
  std::vector<std::shared_ptr<ScopedSource>> sources;
  std::vector<std::shared_ptr<ScopedCallSource>> calls;
  std::vector<std::shared_ptr<ScopedInvocationSource>> invocations;
  std::map<unsigned, std::shared_ptr<NotationFamilies>> notations;
};
struct BodyPlan {
  UsagePlan usage;
  BodyWitnesses witnesses;
  struct Demand {
    Type type;
    Usage usage;
    Span span;
    std::string code, message;
  };
  std::vector<Demand> demands;
  uint64_t operations = 0;
  BodyPlan(Semantics &types, const Declaration &scope) : usage(types, scope) {}
};
class Checker {
public:
  Checker(std::vector<SyntaxDeclaration>, CheckedStorage &, Work &);
  /// Static selection over completed signatures and frozen source namespaces.
  Checker(CheckedStorage &, Work &, const NameEnvironment &);
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

  struct ModuleLookup {
    DeclarationId owner;
    std::string name;
  };
  std::optional<DeclarationId>
  resolve(const Declaration &, llvm::StringRef, Span, bool required = true,
          std::vector<ModuleLookup> *route = nullptr,
          std::optional<DeclarationId> *provider = nullptr);
  bool recordReference(const Declaration &, DeclarationId, DeclarationId,
                       llvm::StringRef, Span,
                       std::optional<std::string> abstractModule = {});
  std::optional<Type> type(const Declaration &, const SyntaxType &,
                           unsigned = 1);

  std::optional<std::vector<unsigned>> roles(const Declaration &,
                                             llvm::ArrayRef<std::string>, Span);
  std::optional<std::vector<Type>>
  arguments(const Declaration &, const Declaration &,
            llvm::ArrayRef<SyntaxType>, Span,
            llvm::ArrayRef<ArgumentLabel> = {});

  std::optional<std::vector<bool>>
  enclosingParameters(const Declaration &, const Declaration &, Span);
  bool bindingName(const Declaration &, llvm::StringRef, Span);
  std::optional<CallableReference> callable(const Declaration &,
                                            llvm::StringRef, Span);
  std::optional<OperatorBinding> operatorBinding(const Declaration &,
                                                 const SyntaxOperator &,
                                                 bool filtered = false);
  std::optional<std::vector<OperatorBinding>>
  operatorCandidates(const Declaration &, const SyntaxDeclaration &, uint32_t);
  std::optional<llvm::ArrayRef<OperatorBinding>>
  operatorWitnessFamily(const Declaration &, const SyntaxDeclaration &,
                        uint32_t);
  bool body(DeclarationId, unsigned);
  bool primitiveBody(Declaration &, Body &);
  bool finiteBody(Declaration &, Body &);
  bool domainBody(Declaration &, unsigned);
  bool domainExpression(const Declaration &, const SyntaxDeclaration &,
                        uint32_t);
  bool relation(Declaration &);

  std::map<unsigned, std::vector<SpecificationSelector>> inlineBindings;
  bool relationIdentities();
  bool specifications(Declaration &);

  std::optional<SpecificationSelector> selector(const Declaration &,
                                                const SyntaxSelector &);

  bool configureEntry(Declaration &, const Declaration &,
                      const SyntaxProofEntry &);
  bool retainNotations();
  BodyWitnesses witnesses;
  std::map<unsigned, BodyPlan *> bodyPlans;
  BodyPlan *bodyPlan(DeclarationId id) {
    auto found = bodyPlans.find(id.index);
    return found == bodyPlans.end() ? nullptr : found->second;
  }
  BodyWitnesses &bodyWitnesses(DeclarationId id) {
    auto *plan = bodyPlan(id);
    return plan ? plan->witnesses : witnesses;
  }
  bool retainScopedSources();
  std::shared_ptr<const SyntaxDeclaration> retainSyntax(DeclarationId);

private:
  bool checkBody(Declaration &, Body &, unsigned);
  bool inferUsage(Declaration &, Body::Mode, unsigned);
  bool collectUsage(const Declaration &, const Type &, Usage, Span,
                    llvm::StringRef, llvm::StringRef);
  std::optional<Type> elaborateType(const Declaration &, const SyntaxType &,
                                    unsigned);
  std::vector<SyntaxDeclaration> syntax;
  std::map<unsigned, std::shared_ptr<const SyntaxDeclaration>> retainedSyntax;
  std::map<std::string, DeclarationId> modules;
  std::vector<DeclarationId> moduleIds;
  using ScopeBinding = SourceBinding;
  bool externalSelection = false;
  std::map<std::string, std::set<uint32_t>> externalNames;
  bool checkingVisibility = false;
  std::function<bool(DeclarationId, llvm::StringRef)> loadBinding;
  std::map<std::string, DeclarationId> qualified;
  // Keep the written interface route with its binder, including inherited
  // module parameters. Canonical interfaces alone lose facade provenance.
  std::map<std::string, DeclarationId> moduleParameterProviders;
  std::vector<std::map<std::string, ScopeBinding>> visible;
  using OperatorSite = std::pair<unsigned, unsigned>;
  std::vector<std::vector<OperatorSite>> visibleOperators, exportedOperators;
  std::map<OperatorSite, OperatorBinding> moduleOperators;
  // Definition environments are fixed by resolveBindings before body checking.
  // A scope key uses (declaration, body); a module key uses (module, null).
  // Keep this cache separate from inference's candidate enumeration.
  using OperatorFamilyKey =
      std::tuple<unsigned, std::optional<uint32_t>, std::string>;
  std::map<OperatorFamilyKey, std::vector<OperatorBinding>>
      operatorWitnessFamilies;
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
  bool entry(DeclarationId, unsigned = 1);
  bool generatedSignature(Declaration &, unsigned);
  std::vector<unsigned> entryStates;
  bool constructionsReady = false;
  bool constructions();
  std::optional<DeclarationId> constructionMember(const Type &, llvm::StringRef,
                                                  Span);
  bool constructionCodec(Declaration &, const SyntaxConstruction &,
                         ConstructionDefinition &, const Substitution &);
  bool configureSetups(Declaration &, const Declaration &,
                       llvm::ArrayRef<SyntaxSetupSlot>);
  bool collect();
  bool imports();
  bool prepareNotationSyntax();
  bool prepareOperators();
  std::optional<DeclarationId> member(const Declaration &, DeclarationId,
                                      llvm::StringRef, Span);
  bool moduleContracts();
  bool retainAPI();
  bool signature(DeclarationId, unsigned = 1);
  bool conformance(DeclarationId);
  bool requirements(Declaration &);
  bool dataRequirements(Declaration &);
};
bool resolveBindings(Checker &, Declaration &, SyntaxDeclaration &);
bool elaborateExpressions(Checker &, SyntaxDeclaration &);
/// Source depth accounting follows whether the call retains a helper boundary.
bool primitiveCallIsInline(Body::Mode, llvm::StringRef identity);
} // namespace zkc::language::detail
#endif
