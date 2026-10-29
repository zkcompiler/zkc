#ifndef ZKC_LANGUAGE_STATE_H
#define ZKC_LANGUAGE_STATE_H
#include "APIRecords.h"
#include "LexicalRecords.h"
#include "NotationRecords.h"
#include "zkc/Language/Project.h"
#include "zkc/Syntax/Syntax.h"
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
struct CheckedStorage {
  explicit CheckedStorage(CapturedProject capture)
      : capture(std::move(capture)) {}
  CapturedProject capture;
  std::vector<Asset> assets;
  std::shared_ptr<const std::vector<SourceBuffer>> sources;
  std::vector<std::vector<Token>> tokens;
  /// Immutable authored layout trees, retained before semantic elaboration.
  std::vector<std::optional<syntax::Snapshot>> layoutHeaders, layoutBodies;
  std::vector<Declaration> declarations;
  std::vector<PendingSpecification> pendingSpecifications;
  std::string installation;
  uint64_t work = 0, declarationCount = 0, operationCount = 0;
  uint64_t notationDescriptors = 0, notationHoles = 0;
  /// Written headers and parsed bodies, frozen before resolution/elaboration.
  std::shared_ptr<const WrittenSources> writtenSources;
  NotationRecords notations;
  APIRecords api;
  std::vector<LexicalResolution> lexicalResolutions;
  std::shared_ptr<const NameEnvironment> names;
  /// Immutable authored callback and effect contracts, independent of mutable
  /// checked metadata.
  std::map<uint32_t, std::shared_ptr<const SyntaxDeclaration>> signatureSources;
  std::vector<std::shared_ptr<const ScopedSource>> scopedSources;
  std::vector<std::shared_ptr<const ScopedCallSource>> scopedCalls;
  std::vector<std::shared_ptr<const ScopedInvocationSource>> scopedInvocations;
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
};
struct AnalysisStorage {
  std::shared_ptr<const std::vector<SourceBuffer>> sources;
  std::vector<Diagnostic> diagnostics;
  std::vector<std::vector<Token>> tokens;
  std::optional<CheckedProject> checked;
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
  llvm::Error charge(uint64_t amount = 1, std::optional<Span> span = {});
  llvm::Error count(uint64_t &counter, uint64_t limit, llvm::StringRef what,
                    std::optional<Span> span = {});
};

llvm::Error closeAssets(const CheckedProject &, ClosedStorage &, Work &);

} // namespace zkc::language::detail
#endif
