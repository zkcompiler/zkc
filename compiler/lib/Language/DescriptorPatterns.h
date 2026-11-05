#ifndef ZKC_LANGUAGE_DESCRIPTORPATTERNS_H
#define ZKC_LANGUAGE_DESCRIPTORPATTERNS_H
#include "Semantics.h"
namespace zkc::language::detail {
/// Relate the installed schema patterns to the existing recursive Type. This
/// owns no source expressions, payloads, expansion, or declaration resolution.
class DescriptorPatterns {
  Semantics &types;
  llvm::ArrayRef<Type> statics;
  Span span;
  bool ready = false;
  std::vector<std::optional<Type>> contracts;

public:
  std::vector<std::optional<std::optional<Type>>> extents;
  DescriptorPatterns(Semantics &types, llvm::ArrayRef<Type> statics,
                     unsigned variables, Span span)
      : types(types), statics(statics), span(span) {
    if (types.charge(variables * (sizeof(std::optional<Type>) +
                                  sizeof(std::optional<std::optional<Type>>)),
                     span)) {
      contracts.resize(variables);
      extents.resize(variables);
      ready = true;
    }
  }
  bool same(const Type &a, const Type &b) {
    return a == b || types.fail("source.descriptor-contract",
                                "installed descriptor pattern differs", span);
  }
  bool match(const protocol::PatternRef &pattern, const Type &actual) {
    if (!ready || !types.chargeType(actual, span) || !isDescriptor(actual))
      return types.diagnostic
                 ? false
                 : types.fail("source.descriptor-category",
                              "installed port requires a descriptor", span);
    if (auto *variable =
            std::get_if<protocol::ContractVariable>(&pattern->value)) {
      auto &bound = contracts[variable->variable];
      if (bound)
        return same(*bound, actual);
      bound = actual;
      return true;
    }
    if (auto *product =
            std::get_if<protocol::ProductPattern>(&pattern->value)) {
      if (actual.kind != Type::Kind::DescriptorProduct ||
          actual.arguments.size() != product->elements.size())
        return types.fail("source.descriptor-contract",
                          "installed product pattern differs", span);
      for (unsigned i = 0; i < product->elements.size(); ++i)
        if (!match(product->elements[i], actual.arguments[i]))
          return false;
      return true;
    }
    const auto &sequence = std::get<protocol::SequencePattern>(pattern->value);
    if (actual.kind != Type::Kind::DescriptorSequence ||
        !match(sequence.element, actual.arguments.front()))
      return types.diagnostic
                 ? false
                 : types.fail("source.descriptor-contract",
                              "installed sequence pattern differs", span);
    if (actual.arguments.size() == 2 &&
        !types.chargeType(actual.arguments[1], span))
      return false;
    std::optional<Type> extent = actual.arguments.size() == 2
                                     ? std::optional(actual.arguments[1])
                                     : std::nullopt;
    if (auto *variable =
            std::get_if<protocol::ExtentVariable>(&sequence.extent)) {
      auto &bound = extents[variable->variable];
      if (bound)
        return *bound == extent || types.fail("source.descriptor-contract",
                                              "sequence extents differ", span);
      bound.emplace(std::move(extent));
      return true;
    }
    if (auto *index = std::get_if<protocol::NatStatic>(&sequence.extent))
      return extent && same(*extent, statics[index->index]);
    return !extent ||
           types.fail("source.descriptor-contract",
                      "explicit extent forgetting is required", span);
  }
  std::optional<Type> instantiate(const protocol::PatternRef &pattern) {
    if (!ready || !types.charge(1, span))
      return {};
    if (auto *variable =
            std::get_if<protocol::ContractVariable>(&pattern->value)) {
      const auto &value = contracts[variable->variable];
      return value && types.chargeType(*value, span) ? value : std::nullopt;
    }
    if (auto *product =
            std::get_if<protocol::ProductPattern>(&pattern->value)) {
      if (!types.charge(product->elements.size() * sizeof(Type), span))
        return {};
      Type result(Type::Kind::DescriptorProduct);
      for (const auto &element : product->elements) {
        auto value = instantiate(element);
        if (!value)
          return {};
        result.arguments.push_back(std::move(*value));
      }
      return result;
    }
    const auto &sequence = std::get<protocol::SequencePattern>(pattern->value);
    auto element = instantiate(sequence.element);
    if (!element)
      return {};
    if (!types.charge(2 * sizeof(Type), span))
      return {};
    Type result(Type::Kind::DescriptorSequence);
    result.arguments.push_back(std::move(*element));
    if (auto *variable =
            std::get_if<protocol::ExtentVariable>(&sequence.extent)) {
      if (!extents[variable->variable])
        return {};
      if (*extents[variable->variable]) {
        if (!types.chargeType(**extents[variable->variable], span))
          return {};
        result.arguments.push_back(**extents[variable->variable]);
      }
    } else if (auto *index =
                   std::get_if<protocol::NatStatic>(&sequence.extent)) {
      if (!types.chargeType(statics[index->index], span))
        return {};
      result.arguments.push_back(statics[index->index]);
    }
    return result;
  }
};
} // namespace zkc::language::detail
#endif
