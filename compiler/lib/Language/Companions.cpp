#include "zkc/Language/Companions.h"
#include "State.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
namespace zkc::language {
StringRef spelling(ObligationRole role) {
  switch (role) {
  case ObligationRole::Postcondition:
    return "postcondition";
  case ObligationRole::Request:
    return "request";
  case ObligationRole::SourceCorrespondence:
    return "source-correspondence";
  case ObligationRole::ImplementationLaw:
    return "implementation-law";
  case ObligationRole::RealizationCorrespondence:
    return "realization-correspondence";
  case ObligationRole::StageLink:
    return "stage-link";
  }
  llvm_unreachable("unknown source obligation role");
}
Expected<std::string>
companionIdentity(StringRef owner, std::optional<StringRef> instance,
                  ObligationRole role, std::optional<StringRef> label,
                  uint64_t ordinal, const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  if (owner.empty() || (instance && instance->empty()) ||
      (label && label->empty()))
    return detail::failure("source.companion",
                           "companion identity has an empty component");
  if (!json::isUTF8(owner) || (instance && !json::isUTF8(*instance)) ||
      (label && !json::isUTF8(*label)))
    return detail::failure("source.companion",
                           "companion identity requires valid UTF-8");
  if (owner.size() > limits.moduleBytes + limits.identifierBytes + 2 ||
      (instance && instance->size() > limits.symbolBytes) ||
      (label && label->size() > limits.identifierBytes))
    return detail::failure("source.limit",
                           "companion identity component limit exceeded");
  json::Array selection{instance ? "instance" : "template"};
  if (instance)
    selection.push_back(*instance);
  json::Array key{label ? "label" : "ordinal",
                  label ? label->str() : std::to_string(ordinal)};
  json::Value value =
      json::Array{"zkc.companion/0", owner, std::move(selection),
                  spelling(role), std::move(key)};
  std::string result;
  BoundedStream out(result, limits.apiInspectionBytes);
  out << value;
  if (out.overflow())
    return detail::failure("source.limit",
                           "companion identity byte limit exceeded");
  return result;
}
} // namespace zkc::language
