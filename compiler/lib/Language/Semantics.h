#ifndef ZKC_LANGUAGE_SEMANTICS_H
#define ZKC_LANGUAGE_SEMANTICS_H
#include "State.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Language/Layout.h"
#include <functional>
#include <set>
namespace zkc::language::detail {
Type parameterType(const Parameter &);
bool valueType(const Type &);
using Substitution = std::map<std::string, Type>;
enum class Usage { Copy, Drop };

/// Semantic queries over declaration metadata. The vector object outlives this
/// view; queries never retain element pointers across specialization. Source
/// checking supplies lazy-signature and requirement-inference hooks. Closed
/// queries have neither.
class Semantics {
public:
  Semantics(const std::vector<Declaration> &, llvm::ArrayRef<Asset>, Work &,
            std::function<bool(DeclarationId)> complete = {});
  void indexDeclaration(const Declaration &);
  void indexParameter(const Parameter &, DeclarationId, unsigned);
  Work &work;
  NaturalArithmetic naturals;
  std::optional<Diagnostic> diagnostic;
  /// Nominal authorities of every layout this view observes, inherited by each
  /// nested Layouts. Checking and closure views keep the provisional view:
  /// their carriers classify only, and emission recomputes every published one.
  /// A Layouts over a finalized checked project sets the final view.
  AuthorityView authorities;
  /// The authority frame of one declaration path under `authorities`.
  llvm::Expected<std::optional<std::string>>
  nominalAuthority(llvm::StringRef path) const;
  /// Source checking can collect unproved open preconditions. Closed readers
  /// and conformance checks have no inference scope. Permission queries never
  /// infer resource authority.
  std::function<bool(const Declaration *, const CapabilityBound &)>
      inferCapability;
  std::function<bool(const Declaration &, const NaturalBound &)> inferNatural;
  /// Demand collection is separate from pure permission queries. The source
  /// checker installs this only while building an unpublished usage plan.
  std::function<bool(const Declaration &, const Type &, Usage, Span,
                     llvm::StringRef, llvm::StringRef)>
      collectUsage;
  std::function<bool(const Declaration &, AdmissionObligation)> recordAdmission;
  /// Checking only: finish a selected implementation before a body consumer
  /// observes it. Edges themselves are formed from headers before signatures.
  /// The second argument counts enclosing helpers in a summary traversal.
  std::function<bool(DeclarationId, unsigned enclosingCalls)>
      completeDispatchBody;
  enum class Admission { Accepted, Deferred, Rejected };
  /// Pure source authority/profile query. Deferred means an open type needs
  /// specialization; it never authorizes a boundary.
  std::optional<Admission> admission(const Type &, Boundary, Span,
                                     unsigned = 1);
  bool admit(const Type &, Boundary, Span, const Declaration * = nullptr,
             llvm::ArrayRef<Span> calls = {});
  struct CallSignature {
    std::vector<Type> inputs, outputs;
    Type resultType() const;
  };

  bool chargeType(const Type &, Span);
  bool chargeConstruction(const ConstructionDefinition &, Span);
  const Parameter *parameter(llvm::StringRef) const;
  const Declaration *typeDeclaration(const Type &) const;
  bool symbolic(const Type &) const;
  llvm::Expected<protocol::BoundType> nativeLayout(const Type &);
  /// Synchronously borrow declarations for a bounded port observation. Returned
  /// layout trees own their storage; performed work is reconciled on errors
  /// too. The caller attaches its span when accepting an error.
  llvm::Expected<ProtocolPortLayout> nativePortLayout(const Port &);
  Substitution substitution(const Declaration &, llvm::ArrayRef<Type>) const;
  std::optional<Type> substitute(const Type &, const Substitution &, Span,
                                 unsigned = 1);
  std::optional<Type> associated(const Type &, llvm::StringRef, Span);
  /// Normalize an already resolved projection without resolving its name again.
  std::optional<Type> associated(const Type &, DeclarationId, Span);
  struct Dispatch {
    DeclarationId declaration;
    std::vector<Type> arguments;
  };
  /// Select only interface-owned members. Concrete targets (including closed
  /// instances) retain their identity and arguments. Open modules retain the
  /// abstract reference; a concrete module requires its recorded exact edge.
  std::optional<Dispatch> dispatch(const std::optional<Type> &, DeclarationId,
                                   llvm::ArrayRef<Type>, Span,
                                   unsigned enclosingCalls = 0);
  bool oracleKind(const Type &, Span, const Declaration * = nullptr);
  /// A derived natural of an asset term. A closed term yields the fact of its
  /// captured asset; a symbolic term yields a projection factor that closure
  /// substitutes and inference never binds.
  std::optional<Type> assetProjection(const Type &, llvm::StringRef member,
                                      Span);
  /// The captured asset a closed asset term denotes.
  const Asset *capturedAsset(const Type &, Span);
  std::optional<Permissions> permissions(const Type &, Span,
                                         const Declaration *scope = nullptr,
                                         unsigned = 1);
  bool requireUsage(const Type &, Usage, Span, const Declaration *,
                    llvm::StringRef code, llvm::StringRef message);
  /// Reduce a demanded property to unknown generic leaves. Authored resource
  /// restrictions and native properties cannot be strengthened by inference.
  std::optional<std::vector<Type>> usageRequirements(const Type &, Usage, Span,
                                                     const Declaration &,
                                                     llvm::StringRef code,
                                                     llvm::StringRef message,
                                                     unsigned = 1);
  std::optional<std::vector<TypeField>> fields(const Type &, Span,
                                               unsigned = 1);
  /// The fields of a product type without copying a memoized declared record.
  /// The result points into `computed` or into this view's record memo and is
  /// valid until the next query.
  const std::vector<TypeField> *
  productFields(const Type &, Span, unsigned,
                std::optional<std::vector<TypeField>> &computed);
  /// Signature-only product shape. An abstract representation or open array
  /// length returns no shape and no diagnostic; it cannot select an overload.
  std::optional<std::vector<TypeField>> structuralFields(const Type &, Span);
  std::optional<std::vector<Alternative>> alternatives(const Type &, Span,
                                                       unsigned = 1);
  bool checkArguments(const Declaration &, llvm::ArrayRef<Type>, Span,
                      const Declaration *context = nullptr,
                      const Substitution &extra = {});
  /// Signature matching only. Capabilities, permissions and natural bounds
  /// are checked after resolution, never used to choose an overload.
  std::optional<Substitution> boundMemberSubstitution(const Declaration &,
                                                      const Type &module, Span);
  bool checkKnownArgumentSorts(const Declaration &,
                               llvm::ArrayRef<std::optional<Type>>, Span,
                               const Substitution &extra = {});
  bool checkArgumentSorts(const Declaration &, llvm::ArrayRef<Type>, Span,
                          const Substitution &extra = {});
  bool assumptions(const Declaration &, const NaturalBound &,
                   const Substitution &, Span);
  bool capabilityFormation(const CapabilityBound &);
  bool entails(const Declaration *, const CapabilityBound &,
               llvm::StringRef code = "source.capability");
  bool withinModule(DeclarationId context, DeclarationId owner) const;
  bool constructorAllowed(const Declaration &, const Type &) const;
  bool ingress(const Type &, Span);
  /// Setup authority is never ordinary Host data, including nested payloads.
  /// Open generic leaves are checked again after specialization.
  std::optional<bool> setupAuthority(const Type &, Span, unsigned = 1);
  bool hostData(const Type &, Span, const Declaration * = nullptr);
  // Checks representation, not permissions: even a zero-length formal array
  // cannot become a runtime Type argument, port, region carrier or local value.
  bool executableType(const Type &, Span, unsigned = 1);
  /// Logical protocol values are eliminated before native execution.
  bool protocolValue(const Type &, Span);
  /// Ordinary total shared data, excluding custody and owner-local carriers.
  bool sharedData(const Type &, Span, const Declaration *, unsigned = 1);
  bool oraclePort(const Port &);
  /// Validate a direct field's optional per-element row maximum. Symbolic
  /// kinds defer sized/unsized selection until substitution.
  bool oracleField(const TypeField &);
  /// Restricted nominal formation, cached by complete instantiated type.
  bool logicalRecord(const Type &, Span);
  /// Recompute product identities and field formulas, never edit identity text.
  std::optional<ValuePlacement> placement(const Type &, const ValuePlacement &,
                                          unsigned participants, Span,
                                          unsigned = 1);
  std::optional<PlacedType>
  substitutePlaced(const PlacedType &, const Substitution &, unsigned, Span);
  bool admitPlaced(const PlacedType &, Span, const Declaration *, unsigned = 1);
  std::optional<ValuePlacement> remapPlacement(const ValuePlacement &,
                                               llvm::ArrayRef<unsigned>,
                                               unsigned, Span);
  std::optional<ValuePlacement> projectedPlacement(const Type &,
                                                   const ValuePlacement &,
                                                   llvm::ArrayRef<unsigned>,
                                                   Span);
  bool mathematicalData(const Type &, Span, const Declaration * = nullptr,
                        unsigned = 1);
  /// Structural projection only; bounds and access are checked after inference.
  std::optional<Type> projectionType(const Type &, llvm::StringRef, Span);
  std::optional<Type> projectedType(const Declaration &, Type,
                                    llvm::ArrayRef<unsigned>, Span);
  std::optional<unsigned> fieldIndex(const Declaration &, const Type &,
                                     llvm::StringRef, Span,
                                     bool specificationRead = false);
  std::optional<Type> selectedType(const Declaration &,
                                   const SpecificationSelector &);
  /// Literal parameters are validated unless a parameter is still an open
  /// asset term; closure validates the written identities.
  std::optional<CallSignature> kernelSignature(llvm::StringRef,
                                               llvm::ArrayRef<Type>,
                                               llvm::ArrayRef<std::string>,
                                               Span, const Declaration *,
                                               bool closedParameters = true);
  std::optional<CallSignature>
  intrinsicSignature(const Declaration *, llvm::StringRef, llvm::ArrayRef<Type>,
                     llvm::ArrayRef<std::string>, Span);
  struct EntryField {
    EntryInputSelection selection;
    Type type;
    std::string name;
    bool initialized = false;
  };
  /// Source subtree roster. Closed physical selection is derived by Layouts.
  std::optional<std::vector<EntryField>>
  entryFields(const Declaration &protocol, const Declaration *entry,
              bool inputs, bool atoms = false);
  std::optional<std::vector<EntryField>>
  entryFamilyFields(const Declaration &generated,
                    llvm::ArrayRef<Type> arguments, Span);
  bool checkEntryPublic(const Declaration &, const Declaration &);
  bool checkProofEntry(const Declaration &, const Declaration &);
  /// Resolve labelled application paths against actual query/service
  /// identities. Returns the canonical source-occurrence order of the supplied
  /// selectors.
  std::optional<std::vector<unsigned>>
  proofGateOrder(const Declaration &, const ProofEntry &, llvm::ArrayRef<Type>);
  bool relationData(const Declaration &, const Type &, Span, unsigned = 0);
  bool fail(llvm::StringRef, const llvm::Twine &, Span, std::vector<Span> = {});
  bool accept(llvm::Error, std::optional<Span> fallback = {});
  bool charge(uint64_t, Span);
  llvm::Error takeError();

private:
  const std::vector<Declaration> &declarations;
  llvm::ArrayRef<Asset> assets;
  std::map<std::string, DeclarationId> qualified;
  std::map<std::string, std::pair<DeclarationId, unsigned>> parameters;
  std::function<bool(DeclarationId)> complete;
  unsigned normalizationDepth = 0;
  /// Keyed by lookup key. Like every memo below, it is confined to this view,
  /// which one checker or one Layouts owns over one immutable declaration set.
  std::set<std::string> checkedLogicalRecords;
  /// One generated Entry family's ordinary roster, walked once. Fields keep
  /// selection order; each role lists its own fields in that order. Roles are
  /// indexed by name separately; the telescope order is never sorted.
  struct FamilyRoster {
    std::vector<EntryField> fields;
    /// Per field: verifier public selection, and setup authority.
    std::vector<std::pair<bool, bool>> facts;
    std::vector<std::vector<unsigned>> byRole;
    std::map<std::string, unsigned> roles;
  };
  /// Keyed by the family target, the walked Protocol, the direction and the
  /// exact static substitution. Valid for this view's declarations.
  std::map<std::string, FamilyRoster> familyRosters;
  /// A declared record's substituted fields, keyed by its complete
  /// instantiated type. Field types, placements and spans depend only on that
  /// type and on the declaration, whose signature is complete before any type
  /// term names it. `depth` is the greatest query depth that produced them; a
  /// deeper query recomputes, so depth refusals are unchanged.
  struct DeclaredFields {
    std::vector<TypeField> fields;
    unsigned depth;
  };
  std::map<std::string, DeclaredFields> declaredFields;
};
llvm::Error specialize(std::vector<Declaration> &, llvm::ArrayRef<Asset>,
                       Work &, DeclarationId,
                       std::optional<HostInvocation::Kind> = {});
} // namespace zkc::language::detail
#endif
