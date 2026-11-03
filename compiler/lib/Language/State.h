#ifndef ZKC_LANGUAGE_STATE_H
#define ZKC_LANGUAGE_STATE_H
#include "APIRecords.h"
#include "LexicalRecords.h"
#include "NotationRecords.h"
#include "zkc/Language/DeclarationIndex.h"
#include "zkc/Language/Project.h"
#include "zkc/Syntax/Syntax.h"
#include <algorithm>
#include <map>
#include <set>
namespace zkc::language::detail {
struct CaptureStorage {
  std::vector<SourceBuffer> sources;
  std::vector<AssetBuffer> assets;
  std::string identity, format;
};
struct SyntaxDeclaration;
struct WrittenSources;
struct ScopedSource;
struct ScopedCallSource;
struct ScopedInvocationSource;
struct SourceCall;
using IntrinsicCallSource = SourceCall;
struct SourceBinding {
  DeclarationId target;
  Span span;
  bool isPublic;
  std::optional<DeclarationId> provider;
};
/// Frozen source namespaces, including resolved imports and facade bindings.
struct NameEnvironment {
  std::map<std::string, DeclarationId> modules;
  std::vector<std::map<std::string, SourceBinding>> visible;
};
struct AuthoringStorage;
/// Defining source authorities, computed once after the last checking step.
/// A unit is one captured file, named by its module path. Installation
/// sources are not units: installed declarations enter through the
/// installation identity.
struct SourceAuthorities {
  struct Unit {
    std::string module;
    SourceId source;
    /// Direct dependency units, as sorted unique indices into `units`.
    std::vector<unsigned> dependencies;
    /// Lowercase SHA-256 hex over the unit's dependency closure.
    std::string revision;
  };
  /// Sorted by module path.
  std::vector<Unit> units;
  /// The unit of each source, indexed by source; none for installation.
  std::vector<std::optional<unsigned>> sources;
  bool computed = false;
};
struct CheckedStorage {
  CheckedStorage(CapturedProject capture, std::string installation)
      : capture(std::move(capture)), installation(std::move(installation)) {}
  CapturedProject capture;
  std::vector<Asset> assets;
  std::shared_ptr<const std::vector<SourceBuffer>> sources;
  std::vector<std::vector<Token>> tokens;
  /// Immutable authored layout trees, retained before semantic elaboration.
  std::vector<std::optional<syntax::Snapshot>> layoutHeaders, layoutBodies;
  std::vector<Declaration> declarations;
  std::vector<PendingSpecification> pendingSpecifications;
  /// Fixed before declaration collection, including generated nominal families.
  const std::string installation;
  uint64_t work = 0, declarationCount = 0, operationCount = 0;
  SourceWorkObservation workObservation;
  uint64_t notationDescriptors = 0, notationHoles = 0;
  /// Written headers and parsed bodies, frozen before resolution/elaboration.
  std::shared_ptr<const WrittenSources> writtenSources;
  NotationRecords notations;
  APIRecords api;
  std::vector<LexicalResolution> lexicalResolutions;
  std::shared_ptr<const NameEnvironment> names;
  std::shared_ptr<const DeclarationIndex> declarationIndex;
  std::shared_ptr<const AuthoringStorage> authoring;
  /// Immutable authored callback and effect contracts, independent of mutable
  /// checked metadata.
  std::map<uint32_t, std::shared_ptr<const SyntaxDeclaration>> signatureSources;
  std::vector<std::shared_ptr<const ScopedSource>> scopedSources;
  std::vector<std::shared_ptr<const ScopedCallSource>> scopedCalls;
  std::vector<std::shared_ptr<const ScopedInvocationSource>> scopedInvocations;
  std::vector<std::shared_ptr<const IntrinsicCallSource>> intrinsicCalls;
  std::map<uint32_t, std::shared_ptr<const ScopedSource>> bodySources;
  SourceAuthorities authorities;
};
struct ClosedStorage {
  std::vector<Asset> assets;
  std::vector<Declaration> declarations;
  DeclarationId root;
  std::string name;
  std::optional<DeclarationId> protocol;
  std::vector<ClosedInvocation> invocations;
  std::optional<HostInvocation::Kind> invocationKind;
  uint64_t work = 0;
  SourceWorkObservation workObservation;
};
/// Editor facts are frozen separately from a CheckedProject. A declaration may
/// have a valid header without a checked signature, or a signature without a
/// checked body. This owner has no compilation or admission API.
struct AuthoringStorage {
  std::vector<Declaration> declarations;
  std::vector<bool> signatures, bodies;
  std::vector<PendingSpecification> pendingSpecifications;
  std::vector<std::optional<syntax::Snapshot>> layoutBodies;
  std::vector<LexicalResolution> lexicalResolutions;
  APIRecords api;
  std::shared_ptr<const NameEnvironment> names;
  std::shared_ptr<const DeclarationIndex> declarationIndex;
};
/// Internal immutable vector access; the project/Entry must outlive the borrow.
struct DeclarationAccess {
  static const std::vector<Declaration> &get(const CheckedProject &project) {
    return project.storage->declarations;
  }
  static const std::vector<Declaration> &get(const ClosedEntry &entry) {
    return entry.storage->declarations;
  }
};
struct AnalysisStorage {
  SourceWorkObservation workObservation;
  std::shared_ptr<const std::vector<SourceBuffer>> sources;
  std::vector<Diagnostic> diagnostics;
  std::vector<std::vector<Token>> tokens;
  std::optional<CheckedProject> checked;
  std::shared_ptr<const AuthoringStorage> authoring;
};
llvm::Error failure(llvm::StringRef code, const llvm::Twine &message,
                    std::optional<Span> span = {},
                    std::vector<Span> related = {});
std::optional<Diagnostic> diagnose(llvm::Error,
                                   std::optional<Span> fallback = {});
bool isIdentifier(llvm::StringRef);
bool isPath(llvm::StringRef, const Limits &);
bool isReserved(llvm::StringRef);
bool isUnsupported(llvm::StringRef);
std::string digest(llvm::StringRef);
void frame(std::string &, llvm::StringRef);

struct Work {
  const Limits &limits;
  uint64_t used = 0, tokens = 0, declarations = 0, operations = 0;
  uint64_t notationDescriptors = 0, notationHoles = 0;
  std::optional<source::Cancellation> cancellation = {};
  /// Optional enclosing allowance, debited immediately by every nested charge.
  uint64_t *allowance = nullptr;
  WorkLedger ledger{};
  SourceWorkPhase phase = SourceWorkPhase::Unscoped;
  /// Exclusive attribution: nested scopes replace, then restore, the phase.
  class Scope {
    Work &work;
    SourceWorkPhase previous;

  public:
    Scope(Work &work, SourceWorkPhase phase)
        : work(work), previous(work.phase) {
      enter(phase);
    }
    Scope(const Scope &) = delete;
    Scope &operator=(const Scope &) = delete;
    ~Scope() { work.phase = previous; }
    void enter(SourceWorkPhase phase) { work.phase = phase; }
  };
  /// Snapshot an independently bounded operation, including partial failure.
  class Record {
    const Work &work;
    SourceWorkPhase phase;
    std::vector<SourceWorkBudget> *output;

  public:
    Record(const Work &work, SourceWorkPhase phase,
           std::vector<SourceWorkBudget> *output)
        : work(work), phase(phase), output(output) {}
    Record(const Record &) = delete;
    Record &operator=(const Record &) = delete;
    ~Record() {
      if (output)
        output->push_back({phase, work.ledger});
    }
  };
  uint64_t remaining() const {
    auto local = limits.work - used;
    return allowance ? std::min(local, *allowance) : local;
  }
  llvm::Error charge(uint64_t amount = 1, std::optional<Span> span = {});
  llvm::Error count(uint64_t &counter, uint64_t limit, llvm::StringRef what,
                    std::optional<Span> span = {});
};

/// Bound all index setup before Semantics allocates names and parameter keys.
llvm::Error chargeSemanticIndex(const std::vector<Declaration> &, Work &);

llvm::Error closeAssets(const CheckedProject &, ClosedStorage &, Work &);

/// Compute every unit revision once, after all checking and the scoped
/// witness check. `assetDomains` maps each asset domain declaration to the
/// index of the captured asset it names.
llvm::Error computeSourceAuthorities(CheckedStorage &,
                                     const std::map<uint32_t, unsigned> &,
                                     Work &);
/// The defining source authority of a declaration path: the defining unit's
/// revision when authored, the installation identity when installed, and none
/// only for a generated declaration.
llvm::Expected<std::optional<std::string>>
definingAuthority(const CheckedStorage &, llvm::StringRef path);

} // namespace zkc::language::detail
#endif
