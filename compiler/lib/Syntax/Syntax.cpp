#include "Storage.h"
#include "zkc/Source/Names.h"
#include <algorithm>

namespace zkc::syntax {
llvm::ArrayRef<NotationDescriptor> defaultNotations() {
  using P = NotationDescriptor::Position;
  using A = NotationDescriptor::Association;
  static const NotationDescriptor fixed[] = {
#define OPERATOR(position, association, symbol, precedence, arity)             \
  {P::position, A::association, symbol, "", precedence, arity},
#include "zkc/Syntax/Operators.def"
#undef OPERATOR
  };
  return fixed;
}
bool validNotationDescriptor(const NotationDescriptor &n) {
  using P = NotationDescriptor::Position;
  using A = NotationDescriptor::Association;
  if (static_cast<unsigned>(n.position) > static_cast<unsigned>(P::Index) ||
      static_cast<unsigned>(n.association) > static_cast<unsigned>(A::Right) ||
      !n.arity || n.arity > 64 || !n.precedence)
    return false;
  if (n.position != P::Infix && n.association != A::None)
    return false;
  if (n.position == P::Index)
    return n.symbol == "[]" && n.closing == "]" && n.precedence == 100 &&
           n.arity >= 2;
  for (const auto &fixed : defaultNotations())
    if (fixed.symbol == n.symbol && fixed.position == n.position)
      return fixed == n;
  auto scalar = source::decodeSourceScalar(n.symbol, 0);
  if (n.position == P::Delimited) {
    auto close = source::decodeSourceScalar(n.closing, 0);
    return scalar && scalar->bytes == n.symbol.size() && close &&
           close->bytes == n.closing.size() && n.precedence == 100 &&
           source::matchingSourceDelimiter(scalar->value) == close->value;
  }
  if (!n.closing.empty() || n.precedence > 99 ||
      n.arity !=
          (n.position == P::Infix || n.position == P::Reduction ? 2u : 1u))
    return false;
  if (n.position == P::Reduction)
    return scalar && scalar->bytes == n.symbol.size() && scalar->value > 127 &&
           source::isMathematicalSymbol(scalar->value) && n.symbol != "∈" &&
           n.symbol != "∀" && n.symbol != "∃" && n.precedence == 67;
  if (scalar && scalar->value > 127)
    return scalar->bytes == n.symbol.size() &&
           source::isMathematicalSymbol(scalar->value) && n.symbol != "∑" &&
           n.symbol != "∏" && n.symbol != "∈" && n.symbol != "∀" &&
           n.symbol != "∃";
  // ASCII syntax is fixed even when a library binds its callable meaning.
  auto fixed = defaultNotations();
  return std::find(fixed.begin(), fixed.end(), n) != fixed.end();
}
llvm::StringRef spelling(Kind kind) {
  switch (kind) {
#define KIND(name, category)                                                   \
  case Kind::name:                                                             \
    return #name;
#include "zkc/Syntax/Kinds.def"
#undef KIND
  }
  llvm_unreachable("unknown syntax kind");
}
std::optional<Kind> declarationKind(llvm::StringRef head) {
#define HEAD(value, kind)                                                      \
  if (head == value)                                                           \
    return Kind::kind;
#include "zkc/Syntax/Heads.def"
#undef HEAD
  return std::nullopt;
}
Category category(Kind kind) {
  switch (kind) {
#define KIND(name, category)                                                   \
  case Kind::name:                                                             \
    return Category::category;
#include "zkc/Syntax/Kinds.def"
#undef KIND
  }
  llvm_unreachable("unknown syntax kind");
}
const source::Revision &Snapshot::revision() const { return storage->revision; }
source::SourceId Snapshot::sourceId() const { return storage->sourceId; }
Status Snapshot::status() const { return storage->status; }
bool Snapshot::headersOnly() const { return storage->headersOnly; }
uint64_t Snapshot::workUsed() const { return storage->workUsed; }
llvm::ArrayRef<Token> Snapshot::tokens() const { return storage->tokens; }
llvm::ArrayRef<Node> Snapshot::nodes() const { return storage->nodes; }
llvm::ArrayRef<source::Diagnostic> Snapshot::diagnostics() const {
  return storage->diagnostics;
}
NodeId Snapshot::root() const { return storage->root; }
const Node &Snapshot::node(NodeId id) const {
  return storage->nodes.at(id.index);
}
llvm::ArrayRef<NodeId> Snapshot::children(NodeId id) const {
  const auto &n = node(id);
  return llvm::ArrayRef(storage->children).slice(n.firstChild, n.childCount);
}
source::Span Snapshot::span(NodeId id) const {
  const auto &n = node(id);
  uint32_t begin = tokens()[n.firstToken].begin;
  uint32_t end =
      n.lastToken > n.firstToken ? tokens()[n.lastToken - 1].end : begin;
  return {sourceId(), begin, end};
}
llvm::StringRef Snapshot::text(const Token &token) const {
  return revision().text().slice(token.begin, token.end);
}
llvm::StringRef Snapshot::text(NodeId id) const {
  auto range = span(id);
  return revision().text().slice(range.begin, range.end);
}
const Environment &Snapshot::environment(NodeId id) const {
  // The parser records the inherited environment for each declaration/body.
  auto found = storage->environments.find(node(id).environmentOwner);
  return found == storage->environments.end() ? storage->defaultEnvironment
                                              : found->second;
}
std::optional<View> View::first(Kind kind) const {
  for (auto child : snapshot.children(id))
    if (snapshot.node(child).kind == kind)
      return View(snapshot, child);
  return std::nullopt;
}
std::vector<View> View::children(Kind kind) const {
  std::vector<View> result;
  for (auto child : snapshot.children(id))
    if (snapshot.node(child).kind == kind)
      result.emplace_back(snapshot, child);
  return result;
}
bool equivalent(const Snapshot &left, const Snapshot &right) {
  if (left.status() != right.status() ||
      left.headersOnly() != right.headersOnly())
    return false;
  auto spellings = [](const Snapshot &s) {
    std::vector<std::pair<TokenKind, std::string>> result;
    for (auto token : s.tokens())
      if (!token.trivia() || token.kind == TokenKind::Comment)
        result.emplace_back(token.kind, s.text(token).str());
    return result;
  };
  if (spellings(left) != spellings(right))
    return false;
  std::vector<std::pair<NodeId, NodeId>> pending{{left.root(), right.root()}};
  while (!pending.empty()) {
    auto [a, b] = pending.back();
    pending.pop_back();
    if (left.node(a).kind != right.node(b).kind)
      return false;
    auto ac = left.children(a), bc = right.children(b);
    if (ac.size() != bc.size())
      return false;
    for (size_t i = 0; i < ac.size(); ++i)
      pending.emplace_back(ac[i], bc[i]);
  }
  return true;
}
namespace detail {
bool Work::charge(uint64_t amount, uint32_t offset) {
  if (stopped())
    return false;
  if (cancellation.cancelled()) {
    storage.status = Status::Cancelled;
    return false;
  }
  if (amount > remaining) {
    exhaust(offset);
    return false;
  }
  remaining -= amount;
  return true;
}
void Work::error(llvm::StringRef code, llvm::StringRef message, uint32_t begin,
                 uint32_t end) {
  if (storage.status == Status::Complete)
    storage.status = Status::Partial;
  if (storage.diagnostics.size() < budget.diagnostics)
    storage.diagnostics.push_back({code.str(),
                                   message.str(),
                                   source::Span{storage.sourceId, begin, end},
                                   {}});
}
void Work::exhaust(uint32_t offset) {
  if (stopped())
    return;
  error("syntax.limit", "syntax resource limit exceeded", offset, offset);
  storage.status = Status::ResourceExhausted;
}
} // namespace detail
} // namespace zkc::syntax
