#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Relation/Authoring.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
#include <algorithm>
using namespace llvm;
namespace zkc::frontend {
Input::Input(std::string text, std::string filename, Kind kind)
    : contents(std::make_shared<const Contents>(
          Contents{std::move(text), std::move(filename), kind})) {}
Input::Input(std::string text, std::string filename)
    : Input(std::move(text), std::move(filename), Kind::File) {}
Input Input::withoutFile(std::string text, std::string label) {
  return Input(std::move(text), std::move(label), Kind::Stream);
}
StringRef Input::text() const { return contents->text; }
StringRef Input::filename() const { return contents->filename; }
bool Input::file() const { return contents->kind == Kind::File; }
namespace {
constexpr size_t maxLocationPathElements = 1024 * 1024;
// Called only after portable JSON syntax has been validated. Scan the original
// spelling for array coordinates and exact spans, without another semantic
// parser or the natural-number codec's translated offsets. JSON has no
// comments.
Expected<source::SourceMap> jsonLocations(StringRef text, StringRef filename) {
  struct Frame {
    size_t start, next = 0;
    source::Path path;
  };
  std::vector<Frame> stack;
  source::SourceMap spans;
  size_t pathElements = 0;
  for (size_t i = 0; i < text.size();) {
    char ch = text[i];
    if (ch == '"') {
      ++i;
      while (i < text.size()) {
        if (text[i] == '\\')
          i += 2;
        else if (text[i++] == '"')
          break;
      }
    } else if (ch == '[') {
      source::Path path;
      if (!stack.empty()) {
        path = stack.back().path;
        path.push_back(stack.back().next);
      }
      if (path.size() > maxLocationPathElements - pathElements)
        return diagnostic(text, filename, i, "source-limit",
                          "source map exceeds coordinate budget");
      pathElements += path.size();
      stack.push_back({i++, 0, std::move(path)});
    } else if (ch == ']') {
      const auto &frame = stack.back();
      spans.emplace(frame.path, source::Span{frame.start, i + 1 - frame.start});
      stack.pop_back();
      ++i;
    } else if (ch == ',') {
      // The validated array grammar makes commas unambiguous here.
      ++stack.back().next;
      ++i;
    } else
      ++i;
  }
  return spans;
}
// Inspect only the first array item when selecting the interchange budget.
// Labels and origins elsewhere in the document cannot select a larger reader.
bool isRelationSnapshot(StringRef text) {
  auto first = text.ltrim().drop_front().ltrim();
  if (!first.starts_with("\""))
    return false;
  // Even a fully Unicode-escaped format tag fits well inside this bound.
  for (size_t i = 1; i < std::min<size_t>(first.size(), 128); ++i) {
    if (first[i] == '\\')
      ++i;
    else if (first[i] == '"') {
      auto tag = json::parse(first.take_front(i + 1));
      if (!tag) {
        consumeError(tag.takeError());
        return false;
      }
      return tag->getAsString() == StringRef("zkc.relations/1");
    }
  }
  return false;
}
} // namespace

Expected<source::Document> parseProtocolDocument(StringRef text,
                                                 StringRef filename) {
  return parseProtocolDocument(Input(text.str(), filename.str()));
}
Expected<source::Document> parseProtocolDocument(const Input &input) {
  StringRef text = input.text(), filename = input.filename();
  if (text.ltrim().starts_with("[")) {
    // The versioned relation envelope owns an independent immutable-data
    // budget. Ordinary source still passes its 1MiB structure check.
    if (isRelationSnapshot(text)) {
      auto value = relation::readSnapshotJSON(text);
      if (!value)
        return diagnostic(text, filename, 0, toString(value.takeError()),
                          "invalid relation snapshot");
      auto content = source::decode(*value);
      if (!content)
        return diagnostic(text, filename, 0, toString(content.takeError()),
                          "invalid relation source structure");
      return source::Document(std::move(*content), text.str(), filename.str());
    }
    std::optional<size_t> invalidString;
    auto value = zkc::parseJson(text, &invalidString);
    if (!value) {
      if (invalidString) {
        consumeError(value.takeError());
        return diagnostic(text, filename, *invalidString, "source-string",
                          "invalid Unicode in quoted string");
      }
      return value.takeError();
    }
    auto locations = jsonLocations(text, filename);
    if (!locations)
      return locations.takeError();
    std::optional<source::Span> failure;
    auto content = source::decode(*value, *locations, &failure);
    if (!content) {
      return diagnostic(text, filename, failure ? failure->offset : 0,
                        toString(content.takeError()),
                        "invalid source structure");
    }
    return source::Document(std::move(*content), text.str(), filename.str());
  }
  auto content = analyzeProtocol(input).lower();
  if (!content)
    return content.takeError();
  if (auto error = source::checkStructure(*content))
    return diagnostic(text, filename, 0, toString(std::move(error)),
                      "invalid source structure");
  return source::Document(std::move(*content), text.str(), filename.str());
}

} // namespace zkc::frontend
