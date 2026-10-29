#ifndef ZKC_SYNTAX_SYNTAX_H
#define ZKC_SYNTAX_SYNTAX_H

#include "zkc/Source/Source.h"
#include "zkc/Syntax/Notation.h"
#include "llvm/ADT/ArrayRef.h"
#include <map>
#include <memory>

namespace zkc::syntax {
enum class Kind {
#define KIND(name, category) name,
#include "zkc/Syntax/Kinds.def"
#undef KIND
};
enum class Category {
  Container,
  Error,
  Declaration,
  Signature,
  Contract,
  Statement,
  Expression
};
llvm::StringRef spelling(Kind);
Category category(Kind);
std::optional<Kind> declarationKind(llvm::StringRef);
enum class TokenKind {
  Word,
  Number,
  String,
  Punctuation,
  Space,
  Comment,
  Newline,
  Invalid,
  LineEnd,
  Indent,
  Dedent,
  Missing,
  End
};
struct Token {
  TokenKind kind;
  uint32_t begin, end;
  bool synthetic() const { return begin == end; }
  bool trivia() const {
    return kind == TokenKind::Space || kind == TokenKind::Comment ||
           kind == TokenKind::Newline;
  }
};
struct NodeId {
  uint32_t index;
  bool operator==(NodeId other) const { return index == other.index; }
};
struct Node {
  Kind kind;
  uint32_t firstToken, lastToken;
  uint32_t firstChild, childCount, height;
  // Exact supplied syntax environment; UINT32_MAX selects the default.
  uint32_t environmentOwner;
};
enum class Status { Complete, Partial, Cancelled, ResourceExhausted };
/// Invocation ceilings may be lowered, never raised above these defaults.
/// A stopped parse retains two sentinel tokens and one error node even at zero.
struct Budget {
  uint64_t bytes = 1048576, tokens = 1000000, tokenBytes = 4096;
  uint64_t identifierBytes = 128, nodes = 1000000, depth = 64;
  uint64_t work = 8000000, diagnostics = 100, insertions = 1024;
};
/// Only syntax facts cross this boundary, never a type or callable resolver.
struct Environment {
  std::vector<NotationDescriptor> notation;
  bool operator==(const Environment &other) const {
    return notation == other.notation;
  }
};
/// Keyed by an owning declaration's first authored byte. Entries override the
/// enclosing scope's environment. The empty map uses the supplied default.
using Environments = std::map<uint32_t, Environment>;

namespace detail {
struct Storage;
class Parser;
} // namespace detail
class Snapshot {
public:
  const source::Revision &revision() const;
  source::SourceId sourceId() const;
  Status status() const;
  bool headersOnly() const;
  llvm::ArrayRef<Token> tokens() const;
  llvm::ArrayRef<Node> nodes() const;
  llvm::ArrayRef<source::Diagnostic> diagnostics() const;
  NodeId root() const;
  const Node &node(NodeId) const;
  llvm::ArrayRef<NodeId> children(NodeId) const;
  source::Span span(NodeId) const;
  llvm::StringRef text(const Token &) const;
  llvm::StringRef text(NodeId) const;
  const Environment &environment(NodeId) const;

private:
  explicit Snapshot(std::shared_ptr<const detail::Storage> storage)
      : storage(std::move(storage)) {}
  std::shared_ptr<const detail::Storage> storage;
  friend class detail::Parser;
};
Snapshot parseHeaders(source::Revision, source::SourceId = {0}, Budget = {},
                      source::Cancellation = {});
Snapshot parseBodies(const Snapshot &, Environment = {}, Environments = {},
                     Budget = {}, source::Cancellation = {});
Snapshot parse(source::Revision, Environment = {}, Budget = {},
               source::Cancellation = {}, source::SourceId = {0});

/// Views refer to the same immutable tree; missing/error children stay
/// optional.
class View {
public:
  View(const Snapshot &snapshot, NodeId id) : snapshot(snapshot), id(id) {}
  Kind kind() const { return snapshot.node(id).kind; }
  source::Span span() const { return snapshot.span(id); }
  std::optional<View> first(Kind) const;
  std::vector<View> children(Kind) const;
  NodeId node() const { return id; }
  llvm::StringRef text() const { return snapshot.text(id); }

protected:
  const Snapshot &snapshot;
  NodeId id;
};
class ProtocolSyntax : public View {
public:
  using View::View;
  std::optional<View> name() const { return first(Kind::Name); }
  std::optional<View> parameters() const { return first(Kind::Parameters); }
  std::optional<View> body() const { return first(Kind::Suite); }
};
class SpecSyntax : public View {
public:
  using View::View;
  std::optional<View> body() const { return first(Kind::Suite); }
};
struct FormatResult {
  std::string text;
  bool complete;
  std::vector<source::Diagnostic> diagnostics;
};
FormatResult format(const Snapshot &, Budget = {}, source::Cancellation = {});
/// Ignores trivia and byte coordinates; includes authored token spelling,
/// synthetic grouping and exact ordered tree shape.
bool equivalent(const Snapshot &, const Snapshot &);
} // namespace zkc::syntax
#endif
