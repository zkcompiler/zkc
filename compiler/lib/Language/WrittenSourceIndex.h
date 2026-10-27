#ifndef ZKC_LANGUAGE_WRITTENSOURCEINDEX_H
#define ZKC_LANGUAGE_WRITTENSOURCEINDEX_H
#include "LexicalRecords.h"
#include "State.h"
#include "llvm/Support/JSON.h"
#include <tuple>
namespace zkc::language::detail {
struct WrittenAddress {
  std::string owner;
  std::vector<std::pair<std::string, unsigned>> path;
};
using WrittenNodeKey =
    std::tuple<uint32_t, uint32_t, uint32_t, LexicalNode::Kind, unsigned>;
inline WrittenNodeKey writtenNodeKey(Span declaration, LexicalNode node) {
  return {declaration.source.index, declaration.begin, declaration.end,
          node.kind, node.index};
}
using WrittenSpanKey = std::tuple<uint32_t, uint32_t, uint32_t>;
inline WrittenSpanKey writtenSpanKey(Span span) {
  return {span.source.index, span.begin, span.end};
}
struct WrittenIndex {
  std::map<WrittenNodeKey, std::vector<WrittenAddress>> lexical;
  std::map<WrittenSpanKey, std::vector<WrittenAddress>> spans;
  llvm::ArrayRef<WrittenAddress> at(Span declaration, LexicalNode node) const {
    auto found = lexical.find(writtenNodeKey(declaration, node));
    return found == lexical.end()
               ? llvm::ArrayRef<WrittenAddress>{}
               : llvm::ArrayRef<WrittenAddress>(found->second);
  }
  llvm::ArrayRef<WrittenAddress> at(Span span) const {
    auto found = spans.find(writtenSpanKey(span));
    return found == spans.end() ? llvm::ArrayRef<WrittenAddress>{}
                                : llvm::ArrayRef<WrittenAddress>(found->second);
  }
};
/// Reuses the AST writer's own traversal and coordinates. Its work, retained
/// path copies and the returned address encoding share the caller's budget.
llvm::Expected<WrittenIndex> indexWrittenSource(const CheckedProject &,
                                                const WrittenSources &, Work &);
llvm::Expected<llvm::json::Array>
encodeWrittenAddresses(llvm::ArrayRef<WrittenAddress>, Work &);
} // namespace zkc::language::detail
#endif
