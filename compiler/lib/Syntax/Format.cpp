#include "zkc/Syntax/Syntax.h"
#include <algorithm>

namespace zkc::syntax {
FormatResult format(const Snapshot &snapshot, Budget budget,
                    source::Cancellation cancellation) {
  FormatResult result{snapshot.revision().text().str(), false, {}};
  if (snapshot.status() != Status::Complete || snapshot.headersOnly()) {
    result.diagnostics.push_back(
        {"syntax.format.partial",
         "formatting requires complete syntax and its notation environment",
         snapshot.span(snapshot.root()),
         {}});
    return result;
  }
  auto tokens = snapshot.tokens();
  // Spacing belongs to token boundaries, not text substitutions. Layout,
  // comments and all authored parentheses retain their positions.
  std::vector<int8_t> spaces(tokens.size(), -1);
  std::vector<uint32_t> next(tokens.size(), tokens.size());
  uint32_t following = tokens.size();
  for (size_t i = tokens.size(); i--;) {
    next[i] = following;
    if (!tokens[i].synthetic() && !tokens[i].trivia())
      following = i;
  }
  auto after = [&](uint32_t i, int8_t count) {
    if (i < next.size() && next[i] < spaces.size())
      spaces[next[i]] = count;
  };
  uint64_t work = budget.work;
  for (uint32_t i = 0; i < tokens.size(); ++i) {
    if (cancellation.cancelled() || !work--)
      return result;
    if (tokens[i].trivia() || tokens[i].synthetic())
      continue;
    auto value = snapshot.text(tokens[i]);
    if (value == "," || value == ";" || value == ":") {
      spaces[i] = 0;
      after(i, 1);
    } else if (value == "." || value == "::" || value == "@") {
      spaces[i] = 0;
      after(i, 0);
    } else if (value == "(" || value == "[") {
      after(i, 0);
    } else if (value == ")" || value == "]" || value == "}") {
      spaces[i] = 0;
    } else if (value == "=" || value == "<-" || value == ":=" ||
               value == "->") {
      spaces[i] = 1;
      after(i, 1);
    }
  }
  for (uint32_t i = 0; i < snapshot.nodes().size(); ++i) {
    if (cancellation.cancelled() || !work--)
      return result;
    const auto &node = snapshot.nodes()[i];
    auto children = snapshot.children({i});
    if (node.kind == Kind::Binary && children.size() == 2) {
      auto last = snapshot.node(children[0]).lastToken;
      if (last && next[last - 1] < tokens.size())
        spaces[next[last - 1]] = 1;
      spaces[snapshot.node(children[1]).firstToken] = 1;
    } else if (node.kind == Kind::StaticParameters ||
               (node.kind == Kind::Parameters &&
                snapshot.text(tokens[node.firstToken]) == "<")) {
      after(node.firstToken, 0);
      spaces[node.lastToken - 1] = 0;
    } else if ((node.kind == Kind::Call || node.kind == Kind::Index ||
                node.kind == Kind::StaticApply) &&
               children.size() == 2) {
      spaces[snapshot.node(children[1]).firstToken] = 0;
    } else if (node.kind == Kind::Prefix) {
      // Word prefixes need a separator; symbolic prefixes bind tightly.
      after(node.firstToken,
            tokens[node.firstToken].kind == TokenKind::Word ? 1 : 0);
    }
  }
  std::string formatted;
  std::map<uint32_t, uint32_t> offsets;
  bool lineStart = true;
  std::string gap;
  std::optional<Token> previous;
  for (size_t i = 0; i < tokens.size(); ++i) {
    auto token = tokens[i];
    if (cancellation.cancelled() || !work--)
      return result;
    if (token.synthetic())
      continue;
    if (token.kind == TokenKind::Space) {
      gap.append(snapshot.text(token));
      continue;
    }
    if (token.kind == TokenKind::Newline) {
      offsets.emplace(token.begin, formatted.size());
      formatted += '\n';
      gap.clear();
      lineStart = true;
      previous.reset();
      continue;
    }
    if (lineStart) {
      formatted += gap; // Legal suite and continuation indentation is retained.
    } else if (token.kind == TokenKind::Comment ||
               (previous && previous->kind == TokenKind::Comment)) {
      formatted += gap.empty() ? "" : " ";
    } else if (spaces[i] >= 0) {
      formatted.append(spaces[i], ' ');
    } else if (!gap.empty()) {
      formatted += ' ';
    }
    offsets.emplace(token.begin, formatted.size());
    formatted.append(snapshot.text(token));
    gap.clear();
    lineStart = false;
    previous = token;
  }
  if (!formatted.empty() && formatted.back() != '\n')
    formatted += '\n';
  if (formatted.size() > budget.bytes)
    return result;
  auto buffer = snapshot.revision().buffer();
  buffer.text = formatted;
  auto headers = parseHeaders(source::Revision(std::move(buffer)),
                              snapshot.sourceId(), budget, cancellation);
  Environments environments;
  for (uint32_t i = 0; i < snapshot.nodes().size(); ++i) {
    auto owner = snapshot.nodes()[i].environmentOwner;
    if (owner != UINT32_MAX) {
      auto at = offsets.find(owner);
      if (at == offsets.end())
        return result;
      environments.try_emplace(at->second, snapshot.environment({i}));
    }
  }
  auto reparsed = parseBodies(headers, snapshot.environment(snapshot.root()),
                              std::move(environments), budget, cancellation);
  if (!equivalent(snapshot, reparsed)) {
    result.diagnostics.push_back(
        {"syntax.format.equivalence",
         "formatting did not preserve syntax; source was retained",
         snapshot.span(snapshot.root()),
         {}});
    return result;
  }
  result.text = std::move(formatted);
  result.complete = true;
  return result;
}
} // namespace zkc::syntax
