#ifndef ZKC_SYNTAX_STORAGE_H
#define ZKC_SYNTAX_STORAGE_H
#include "zkc/Syntax/Syntax.h"

namespace zkc::syntax::detail {
struct Storage {
  source::Revision revision;
  source::SourceId sourceId;
  Status status = Status::Complete;
  bool headersOnly = false;
  std::vector<Token> tokens;
  std::vector<Node> nodes;
  std::vector<NodeId> children;
  std::vector<source::Diagnostic> diagnostics;
  NodeId root{0};
  Environment defaultEnvironment;
  Environments environments;
  Storage(source::Revision revision, source::SourceId sourceId)
      : revision(std::move(revision)), sourceId(sourceId) {}
};
class Work {
public:
  Storage &storage;
  Budget budget;
  source::Cancellation cancellation;
  uint64_t remaining, insertions = 0;
  Work(Storage &storage, Budget budget, source::Cancellation cancellation)
      : storage(storage), budget(budget), cancellation(cancellation),
        remaining(budget.work) {}
  bool stopped() const {
    return storage.status == Status::Cancelled ||
           storage.status == Status::ResourceExhausted;
  }
  bool charge(uint64_t amount, uint32_t offset);
  void error(llvm::StringRef code, llvm::StringRef message, uint32_t begin,
             uint32_t end);
  void exhaust(uint32_t offset);
};
void lex(Work &);
void layout(Work &);
} // namespace zkc::syntax::detail
#endif
