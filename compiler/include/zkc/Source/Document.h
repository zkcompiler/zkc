#ifndef ZKC_SOURCE_DOCUMENT_H
#define ZKC_SOURCE_DOCUMENT_H

#include "zkc/Source/Model.h"
#include <memory>

namespace zkc::source {
struct File {
  std::string text, filename;
};

/// Immutable, self-contained source snapshot. Copies share owned typed data
/// and spelling. Borrowed node references live as long as a snapshot copy.
/// Constructing a document does not establish semantic admission. Source
/// origins outside the spelling are discarded, without changing its meaning.
class Document {
  struct Storage;
  std::shared_ptr<const Storage> storage;

public:
  explicit Document(Content, std::string text = {},
                    std::string filename = "<generated>");
  explicit Document(Content, std::vector<File>);
  const Content &root() const;
  const Module *module() const { return std::get_if<Module>(&root()); }
  const Participants *participants() const {
    return std::get_if<Participants>(&root());
  }
  const Construction *construction() const {
    return std::get_if<Construction>(&root());
  }
  llvm::StringRef text(uint32_t file = 0) const;
  llvm::StringRef filename(uint32_t file = 0) const;
  std::optional<Span> span(const Node *) const;
  /// One-based byte coordinates, clamped to EOF (not Unicode display columns).
  std::pair<unsigned, unsigned> lineColumn(size_t offset,
                                           uint32_t file = 0) const;
};

// Programmatic clients build Module/Function/Instruction values directly, then
// freeze them in a Document and call the same common admission entry point.
// No positional record builder or separate privileged builder checker exists.

} // namespace zkc::source
#endif
