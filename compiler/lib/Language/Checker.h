#ifndef ZKC_LANGUAGE_CHECKER_H
#define ZKC_LANGUAGE_CHECKER_H
#include "BodySummary.h"
#include "CallResolution.h"
#include "Internal.h"
#include "ScopedWitness.h"
#include "Semantics.h"
#include "UsagePlan.h"
#include "llvm/Support/SaveAndRestore.h"
#include <tuple>
namespace zkc::language::detail {
struct BodyWitnesses {
  std::vector<std::shared_ptr<ScopedSource>> sources;
  std::vector<std::shared_ptr<ScopedCallSource>> calls;
  std::vector<std::shared_ptr<ScopedInvocationSource>> invocations;
  std::vector<std::shared_ptr<IntrinsicCallSource>> intrinsics;
  std::map<unsigned, std::shared_ptr<NotationFamilies>> notations;
  std::map<unsigned, std::shared_ptr<std::map<uint32_t, Type>>> enumTypes;
  std::map<unsigned, std::shared_ptr<std::map<uint32_t, Natural>>> repeatMaxima;
  std::map<unsigned, std::shared_ptr<SourceLiterals>> literals;
  std::map<unsigned, std::shared_ptr<SourceControlSnapshots>> controlSnapshots;
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
  Checker(CheckedStorage &, Work &, AccessContext);
  // Lazy signature completion captures this driver; keep its address stable.
  Checker(const Checker &) = delete;
  Checker &operator=(const Checker &) = delete;
  llvm::Error run();
  llvm::Expected<std::shared_ptr<const AuthoringStorage>> retainAnalysis();
  std::vector<Diagnostic> *recoveryDiagnostics = nullptr;
  bool recover(llvm::Error);
  bool namesReady = false;
  bool indexDeclarations();
  bool checkInstalledSignatures();
  /// Prepare lazy authored-signature replay in a private witness snapshot.
  /// Dependencies use the same signature cycle checks; bodies are not checked.
  bool prepareSignatureReconstruction(DeclarationId, const SyntaxDeclaration &);
  bool reconstructSignature(DeclarationId id) { return signature(id); }
  /// Replay typed View recipes with lazy dependency checking and the same
  /// authored inference policy as formation, in a private signature snapshot.
  void beginViewReconstruction();
  void prepareViewReconstruction(DeclarationId, const SyntaxDeclaration &);
  /// Eligibility is derived from authored headers, never candidate bound flags.
  bool permitsContractInference(DeclarationId id) const {
    return inferredContracts.count(&output.declarations[id.index]);
  }
  CheckedStorage &output;
  Work &work;
  Semantics types;
  BodySummaryCache bodySummaries;
  std::vector<SyntaxDeclaration *> sources;
  std::vector<unsigned> bodyState, bodyHeights;
  std::vector<std::shared_ptr<const NotationEnvironment>> notationEnvironments;

  std::optional<DeclarationId> resolve(const Declaration &, llvm::StringRef,
                                       Span, bool required = true);
  /// Resolve without recording a reference. A caller that keeps the result
  /// records its route itself; a discarded lookup records nothing.
  std::optional<DeclarationId> probe(const Declaration &, llvm::StringRef, Span,
                                     std::optional<DeclarationId> *);
  bool recordReference(const Declaration &, ReferenceRoute,
                       const ResolvedReference &, llvm::StringRef, Span,
                       uint32_t ordinal = 0);
  ReferenceSite referenceSite;
  std::map<ReferenceSite, ResolvedReference, std::owner_less<ReferenceSite>>
      typeReferences;
  std::optional<Type> associated(const Declaration &, const Type &,
                                 llvm::StringRef, Span,
                                 std::optional<ResolvedReference> = {});

  /// The neutral selection used by source consumers and immutable witnesses.
  std::optional<ResolvedReference> select(const Declaration &, llvm::StringRef,
                                          Span, bool required = true);
  bool acceptFailure(const LookupFailure &, Span, bool required);
  const DeclarationIndex &index() const {
    return output.declarationIndex ? *output.declarationIndex : *formingIndex;
  }
  AccessContext accessFor(const Declaration &context) const {
    if (std::holds_alternative<ExternalSelectionAccess>(access))
      return access;
    if (auto *import = std::get_if<ImportBindingAccess>(&access))
      return ImportBindingAccess{context.id, import->import};
    return SourceAccess{context.id};
  }
  std::optional<Type> type(const Declaration &, const SyntaxType &,
                           unsigned = 1, bool allowPlacement = false);
  std::optional<PlacedType> placedType(const Declaration &, const SyntaxType &,
                                       unsigned = 1);

  std::optional<std::vector<unsigned>> roles(const Declaration &,
                                             llvm::ArrayRef<std::string>, Span);
  /// Resolve an injective participant substitution in authored telescope order.
  /// Unlike roles(), this is not an availability set and must never be sorted.
  std::optional<std::vector<unsigned>>
  roleArguments(const Declaration &, llvm::ArrayRef<std::string>, Span);
  std::optional<std::vector<Type>>
  arguments(const Declaration &, const Declaration &,
            llvm::ArrayRef<SyntaxType>, Span,
            llvm::ArrayRef<ArgumentLabel> = {});

  std::optional<std::vector<bool>>
  enclosingParameters(const Declaration &, const Declaration &, Span);
  bool bindingName(const Declaration &, llvm::StringRef, Span);
  /// Resolve a callee. Without recording, the lookup only classifies the
  /// written name and the caller records nothing.
  std::optional<CallableReference>
  callable(const Declaration &, llvm::StringRef, Span, bool record = true);
  std::optional<CallableReference> method(const Declaration &, const Type &,
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
  bool prepareOraclePredicates();
  bool oracleSignature(Declaration &, unsigned);
  bool oraclePredicateSignature(Declaration &);
  bool oracleBody(Declaration &, Body &, unsigned);
  bool retainOraclePredicates(Declaration &, const Body &);

  std::map<unsigned, std::vector<SpecificationSelector>> inlineBindings;
  bool relationIdentities();
  bool pendingClaimRelations();
  bool specifications(Declaration &);
  bool sourceClaims();
  bool sourceClaimDomains(const Declaration &, ClaimExpression &);

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
                                    unsigned, bool allowPlacement);
  std::vector<SyntaxDeclaration> syntax;
  std::map<unsigned, std::shared_ptr<const SyntaxDeclaration>> retainedSyntax;
  std::map<unsigned, SyntaxDeclaration> reconstructedSources;
  std::shared_ptr<DeclarationIndex> formingIndex =
      std::make_shared<DeclarationIndex>();
  AccessContext access = ImportBindingAccess{{0}, UINT32_MAX};
  bool referencesReady = false;
  std::vector<DeclarationId> moduleIds;

  /// While set, references owned by this declaration are not recorded: a
  /// placement pass resolves parts of a term whose names are already recorded.
  std::optional<uint32_t> replayedOwner;
  std::map<ReferenceSite, ReferenceNodeId, std::owner_less<ReferenceSite>>
      referenceNodes;
  std::map<
      std::tuple<uint32_t, uint32_t, ReferenceRoute, std::string, uint32_t>,
      unsigned>
      recordedReferences;
  std::function<bool(DeclarationId, llvm::StringRef)> loadBinding;
  /// Asset domain declaration -> the captured asset it names.
  std::map<uint32_t, unsigned> assetDomains;
  // Keep the written interface route with its binder, including inherited
  // module parameters. Canonical interfaces alone lose facade provenance.
  struct ModuleParameterReference {
    ResolvedReference reference;
    DeclarationId owner;
    uint32_t slot;
  };
  std::map<std::string, ModuleParameterReference> moduleParameterReferences;
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
  void registerContractInference(Declaration &, const SyntaxDeclaration &);
  void installContractInference(bool signaturesOnly);
  void installAdmissionCollection(bool signaturesOnly);
  std::map<unsigned, std::map<std::pair<Boundary, std::string>, unsigned>>
      admissionIndices;
  unsigned signatureDepth = 0;
  std::optional<DeclarationId> activeBody;
  unsigned activeBodyDepth = 0;
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
  /// Select a provider's interface member and record its construction route.
  std::optional<CallableReference>
  constructionMember(const Declaration &, const Type &, llvm::StringRef, Span,
                     std::optional<ResolvedReference> = {});
  bool constructionCodec(Declaration &, const SyntaxConstruction &,
                         ConstructionDefinition &, const Substitution &);
  bool configureSetups(Declaration &, const Declaration &,
                       llvm::ArrayRef<SyntaxSetupSlot>);
  bool collect();
  bool layoutSpecifications();
  bool imports();
  bool classifyServices();
  bool prepareNotationSyntax();
  bool prepareOperators();
  std::optional<DeclarationId> member(const Declaration &, DeclarationId,
                                      llvm::StringRef, Span);

  LookupTraversal lookupTraversal(Span);
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
bool primitiveCallIsInline(Body::Mode, Declaration::Kind,
                           llvm::StringRef identity);
} // namespace zkc::language::detail
#endif
