#ifndef ZKC_LANGUAGE_AUTHORING_H
#define ZKC_LANGUAGE_AUTHORING_H

#include "zkc/Language/Project.h"
#include "zkc/Syntax/Syntax.h"

namespace zkc::language {
struct SourceSymbol {
  std::string name, detail;
  Declaration::Kind kind;
  Span span, selection;
};
struct SourceHover {
  Span span;
  std::string text;
};
struct SourceCompletion {
  std::string name, detail;
  Span definition;
};

/// Queries over one immutable analysis revision. Available signatures and
/// bodies carry separate validity; partial views cannot be promoted to
/// CheckedProject. No method reads files, emits IR or checks Lean.
class Authoring {
public:
  explicit Authoring(CheckedProject project);
  explicit Authoring(const Analysis &analysis);
  bool hasSemanticContext() const;
  std::vector<SourceSymbol> symbols(SourceId) const;
  std::optional<Span> definition(SourceId, uint32_t offset) const;
  std::optional<SourceHover> hover(SourceId, uint32_t offset) const;
  /// At most 256 visible candidates, ordered by name. Lexical candidates
  /// shadow module candidates. This is name completion, not resource admission.
  std::vector<SourceCompletion> completion(SourceId, uint32_t offset,
                                           llvm::StringRef prefix = {}) const;
  std::optional<syntax::Snapshot> syntaxTree(SourceId) const;
  syntax::FormatResult format(SourceId, source::Cancellation = {}) const;

private:
  std::shared_ptr<const detail::AuthoringStorage> view;
  void initializeSelections();
  std::string detail(const Declaration &) const;
  std::map<std::pair<uint32_t, uint32_t>, Span> selections;
  Span selection(const Declaration &) const;
};
} // namespace zkc::language
#endif
