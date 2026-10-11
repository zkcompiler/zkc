#ifndef ZKC_CONTRACTS_CONSTRUCTION_H
#define ZKC_CONTRACTS_CONSTRUCTION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/ErrorHandling.h"
#include <initializer_list>
#include <optional>

namespace zkc::protocol {
/// Typed associations with a protocol occurrence. Bodies remain ordinary Local
/// functions; these names describe when the selected functions execute.
enum class ConstructionRuleKind {
  Start,
  Message,
  Query,
  Encode,
  Receive,
  Decode,
  Wire
};
inline llvm::StringRef constructionRuleName(ConstructionRuleKind kind) {
  switch (kind) {
  case ConstructionRuleKind::Start:
    return "start";
  case ConstructionRuleKind::Message:
    return "message";
  case ConstructionRuleKind::Query:
    return "query";
  case ConstructionRuleKind::Encode:
    return "encode";
  case ConstructionRuleKind::Receive:
    return "receive";
  case ConstructionRuleKind::Decode:
    return "decode";
  case ConstructionRuleKind::Wire:
    return "wire";
  }
  llvm_unreachable("unknown construction rule kind");
}
inline std::optional<ConstructionRuleKind>
parseConstructionRuleKind(llvm::StringRef name) {
  for (auto kind : {ConstructionRuleKind::Start, ConstructionRuleKind::Message,
                    ConstructionRuleKind::Query, ConstructionRuleKind::Encode,
                    ConstructionRuleKind::Receive, ConstructionRuleKind::Decode,
                    ConstructionRuleKind::Wire})
    if (constructionRuleName(kind) == name)
      return kind;
  return std::nullopt;
}
inline bool isCodecRule(ConstructionRuleKind kind) {
  return kind == ConstructionRuleKind::Encode ||
         kind == ConstructionRuleKind::Receive ||
         kind == ConstructionRuleKind::Decode ||
         kind == ConstructionRuleKind::Wire;
}
} // namespace zkc::protocol
#endif
