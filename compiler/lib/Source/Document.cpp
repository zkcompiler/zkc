#include "zkc/Source/Document.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include <algorithm>
#include <limits>
#include <map>

using namespace llvm;
namespace zkc::source {
struct Document::Storage {
  Content value;
  std::vector<File> files;
  std::map<const Node *, Span> locations;
  std::vector<std::vector<size_t>> lines;

  Storage(Content value, std::vector<File> files)
      : value(std::move(value)), files(std::move(files)) {
    // A programmatic caller may have converted a mutable shared_ptr to const.
    // Freeze fresh owned payloads so later mutation through that alias cannot
    // change an admitted snapshot. Copies of Document still share this storage.
    if (auto *module = std::get_if<Module>(&this->value))
      for (auto &relation : module->relations)
        std::visit(
            [](auto &pointer) {
              using T = typename std::decay_t<decltype(pointer)>::element_type;
              if (pointer)
                pointer = std::make_shared<T>(*pointer);
            },
            relation.value);
    walk(this->value, [&](Node &node) {
      if (!node.location)
        return;
      const auto &span = *node.location;
      if (span.file >= this->files.size() ||
          span.offset > this->files[span.file].text.size() ||
          span.length > this->files[span.file].text.size() - span.offset) {
        node.location.reset();
        return;
      }
      locations.emplace(&node, span);
    });
    for (const auto &file : this->files) {
      lines.push_back({0});
      for (size_t i = 0; i < file.text.size(); ++i)
        if (file.text[i] == '\n')
          lines.back().push_back(i + 1);
    }
  }
};

Document::Document(Content value, std::string text, std::string filename)
    : Document(std::move(value),
               std::vector<File>{{std::move(text), std::move(filename)}}) {}
Document::Document(Content value, std::vector<File> files)
    : storage(std::make_shared<const Storage>(std::move(value),
                                              std::move(files))) {}
const Content &Document::root() const { return storage->value; }
StringRef Document::text(uint32_t file) const {
  return file < storage->files.size() ? StringRef(storage->files[file].text)
                                      : StringRef();
}
StringRef Document::filename(uint32_t file) const {
  return file < storage->files.size() ? StringRef(storage->files[file].filename)
                                      : StringRef("<generated>");
}
std::optional<Span> Document::span(const Node *node) const {
  auto found = storage->locations.find(node);
  return found == storage->locations.end() ? std::nullopt
                                           : std::optional(found->second);
}
std::optional<Span> Document::diagnosticSpan(const Node &node) const {
  if (!node.location)
    return std::nullopt;
  const auto &span = *node.location;
  if (span.file >= storage->files.size() ||
      span.offset > text(span.file).size() ||
      span.length > text(span.file).size() - span.offset)
    return std::nullopt;
  return span;
}
std::pair<unsigned, unsigned> Document::lineColumn(size_t offset,
                                                   uint32_t file) const {
  if (file >= storage->lines.size())
    return {1, 1};
  offset = std::min(offset, text(file).size());
  const auto &lines = storage->lines[file];
  auto next = std::upper_bound(lines.begin(), lines.end(), offset);
  auto bounded = [](size_t n) {
    return static_cast<unsigned>(
        std::min(n, size_t(std::numeric_limits<unsigned>::max())));
  };
  return {bounded(next - lines.begin()), bounded(offset - *--next + 1)};
}
} // namespace zkc::source
