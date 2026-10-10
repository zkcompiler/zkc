#include "Arguments.h"
#include "llvm/ADT/StringMap.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<unsigned>>
bindArguments(Semantics &semantics, ArrayRef<StringRef> parameters,
              unsigned count, ArrayRef<ArgumentLabel> labels, bool complete,
              Span span, StringRef diagnostic) {
  if (!semantics.charge(parameters.size() + count + 1, span))
    return {};
  if (count > parameters.size() || (complete && count != parameters.size())) {
    semantics.fail(diagnostic, "argument count differs from the declaration",
                   span);
    return {};
  }
  StringMap<unsigned> indices;
  for (unsigned i = 0; i < parameters.size(); ++i) {
    if (!semantics.charge(parameters[i].size() + 1, span))
      return {};
    indices.try_emplace(parameters[i], i);
  }
  std::vector<unsigned> result;
  std::vector<bool> assigned(parameters.size());
  unsigned label = 0;
  for (unsigned i = 0; i < count; ++i) {
    unsigned parameter = i;
    Span occurrence = span;
    if (label < labels.size() && labels[label].index == i) {
      const auto &name = labels[label++];
      occurrence = name.span;
      if (!semantics.charge(name.name.size() + 1, occurrence))
        return {};
      auto found = indices.find(name.name);
      if (found == indices.end()) {
        semantics.fail(diagnostic, "unknown argument name: " + name.name,
                       occurrence);
        return {};
      }
      parameter = found->second;
    } else if (label) {
      semantics.fail(diagnostic, "positional argument follows a named argument",
                     span);
      return {};
    }
    if (assigned[parameter]) {
      semantics.fail(diagnostic,
                     "argument supplied more than once: " +
                         parameters[parameter],
                     occurrence);
      return {};
    }
    assigned[parameter] = true;
    result.push_back(parameter);
  }
  return result;
}
std::vector<StringRef> inputNames(const Declaration &decl) {
  if (decl.kind != Declaration::Kind::Protocol)
    return argumentNames<Port>(decl.inputs);
  std::vector<StringRef> result;
  for (const auto &slot : decl.inputOrder)
    result.push_back(slot.kind == Declaration::InputSlot::Kind::Data
                         ? decl.inputs[slot.index].name
                         : decl.services[slot.index].name);
  return result;
}
} // namespace zkc::language::detail
