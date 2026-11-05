#include "LayoutReader.h"
#include <set>
using namespace llvm;
namespace zkc::language::detail {
Expected<SyntaxScopedSignature> LayoutReader::scopedSignature(Id id) {
  if (auto error = charge(id))
    return error;
  auto nodes = parts(id, 2, 4);
  if (!nodes)
    return nodes.takeError();
  if (kind((*nodes)[0]) != K::Parameters)
    return fail(id, "scoped signature requires parameters", "source.scoped");
  SyntaxScopedSignature result;
  result.mode = head(id) == "local" ? ScopedSignature::Mode::Local
                                    : ScopedSignature::Mode::Math;
  const bool local = result.mode == ScopedSignature::Mode::Local;
  result.allowance = Effects{local, local};
  for (auto input : children((*nodes)[0])) {
    if (auto error = runtimeArgument(input))
      return error;
    auto parts = this->parts(input, 1, 2);
    if (!parts)
      return parts.takeError();
    std::string label;
    if (parts->size() == 2) {
      if (between(parts->front(), parts->back()) != ":")
        return fail(input, "callback input labels require a type annotation",
                    "source.scoped");
      if (kind(parts->front()) != K::Name)
        return fail(input, "callback input label must be a name",
                    "source.scoped");
      auto value = name(parts->front());
      if (!value)
        return value.takeError();
      label = std::move(*value);
    }
    auto value = type(parts->back());
    if (!value)
      return value.takeError();
    result.inputs.push_back(std::move(*value));
    result.inputLabels.push_back(std::move(label));
  }
  auto output = type((*nodes)[1]);
  if (!output)
    return output.takeError();
  result.result = std::move(*output);
  for (auto clause : nodes->drop_front(2)) {
    if (kind(clause) == K::Effects) {
      result.explicitAllowance = true;
      result.allowance = Effects{};
      std::set<std::string> seen;
      for (auto item : children(clause)) {
        auto inner = argument(item);
        if (!inner)
          return inner.takeError();
        if (kind(*inner) != K::Name)
          return fail(item, "callback allowance requires fixed effects",
                      "source.effect");
        auto effect = name(*inner);
        if (!effect)
          return effect.takeError();
        if (!seen.insert(*effect).second)
          return fail(item, "duplicate callback effect", "source.duplicate");
        if (*effect == "stop")
          result.allowance.mayStop = true;
        else if (*effect == "opaque")
          result.allowance.opaque = true;
        else
          return fail(item, "callback allowance requires stop or opaque",
                      "source.effect");
      }
      continue;
    }
    if (kind(clause) != K::Where)
      return fail(clause, "unsupported callback clause", "source.scoped");
    for (auto condition : children(clause)) {
      if (kind(condition) == K::Tuple && children(condition).empty())
        continue;
      if (kind(condition) != K::Call || children(condition).size() != 2)
        return fail(condition,
                    "callback where requires item_from(input, domain)",
                    "source.finite-domain");
      auto call = children(condition);
      auto callee = name(call[0]);
      if (!callee)
        return callee.takeError();
      if (kind(call[0]) != K::Name || *callee != "item_from" ||
          children(call[1]).size() != 2)
        return fail(condition,
                    "callback where requires item_from(input, domain)",
                    "source.finite-domain");
      SyntaxItemOrigin origin;
      origin.span = span(condition);
      unsigned position = 0;
      for (auto item : children(call[1])) {
        auto inner = argument(item);
        if (!inner)
          return inner.takeError();
        if (kind(*inner) != K::Name)
          return fail(item, "item_from requires named input and domain",
                      "source.finite-domain");
        auto value = name(*inner);
        if (!value)
          return value.takeError();
        (position++ == 0 ? origin.input : origin.domain) = std::move(*value);
      }
      result.itemOrigins.push_back(std::move(origin));
    }
  }
  return result;
}
} // namespace zkc::language::detail
