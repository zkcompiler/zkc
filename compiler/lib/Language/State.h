#ifndef ZKC_LANGUAGE_STATE_H
#define ZKC_LANGUAGE_STATE_H
#include "NotationRecords.h"
#include "zkc/Language/Project.h"
#include <map>
#include <set>
namespace zkc::language::detail {
struct CaptureStorage {
  std::vector<SourceBuffer> sources;
  std::vector<AssetBuffer> assets;
  std::string identity, format;
};
struct CheckedStorage {
  explicit CheckedStorage(CapturedProject capture)
      : capture(std::move(capture)) {}
  CapturedProject capture;
  std::vector<Asset> assets;
  std::shared_ptr<const std::vector<SourceBuffer>> sources;
  std::vector<std::vector<Token>> tokens;
  std::vector<Declaration> declarations;
  std::string installation;
  uint64_t work = 0, declarationCount = 0, operationCount = 0;
  uint64_t notationDescriptors = 0, notationHoles = 0;
  NotationRecords notations;
};
struct ClosedStorage {
  std::vector<Asset> assets;
  std::vector<Declaration> declarations;
  DeclarationId protocol;
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
