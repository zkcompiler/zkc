#include "zkc/Language/ValuePlacement.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
Error charge(uint64_t amount, uint64_t &remaining) {
  if (amount > remaining)
    return error("source.limit", "participant placement work limit exceeded");
  remaining -= amount;
  return Error::success();
}
Error roles(ArrayRef<unsigned> values, unsigned participants, bool ordered,
            uint64_t &remaining, ArrayRef<unsigned> scope = {}) {
  if (auto e = charge(values.size() + 1, remaining))
    return e;
  if (values.empty())
    return error("source.roles", "participant placement must be nonempty");
  std::set<unsigned> distinct;
  for (auto role : values) {
    if (role >= participants || !distinct.insert(role).second)
      return error("source.roles",
                   "participant placement must be distinct and in range");
    if (!scope.empty()) {
      if (auto e = charge(scope.size() + 1, remaining))
        return e;
      if (!llvm::is_contained(scope, role))
        return error("source.roles",
                     "field placement escapes its product role application");
    }
  }
  if (!ordered && !llvm::is_sorted(values))
    return error("source.roles", "participant set must be canonical");
  return Error::success();
}
Error validate(const ValuePlacement &placement, unsigned participants,
               uint64_t &remaining, unsigned depth,
               ArrayRef<unsigned> scope = {}) {
  if (!depth)
    return error("source.limit", "participant placement depth limit exceeded");
  if (auto e = charge(1, remaining))
    return e;
  if (const auto *data = std::get_if<DataPlacement>(&placement.value))
    return roles(data->roles, participants, false, remaining, scope);
  if (const auto *oracle = std::get_if<OraclePlacement>(&placement.value)) {
    if (auto e =
            roles(oracle->receivers, participants, false, remaining, scope))
      return e;
    if (auto e = roles({oracle->holder}, participants, true, remaining, scope))
      return e;
    if (llvm::is_contained(oracle->receivers, oracle->holder))
      return error("source.roles",
                   "oracle holder must be outside its receivers");
    return Error::success();
  }
  const auto &product = std::get<ProductPlacement>(placement.value);
  if (product.instance.empty())
    return error("source.placement",
                 "logical product requires nominal identity");
  if (auto e =
          charge(product.instance.size() + product.fields.size(), remaining))
    return e;
  if (auto e = roles(product.arguments, participants, true, remaining, scope))
    return e;
  for (const auto &field : product.fields)
    if (auto e = validate(field, participants, remaining, depth - 1,
                          product.arguments))
      return e;
  return Error::success();
}
Expected<ValuePlacement> substitute(const ValuePlacement &placement,
                                    ArrayRef<unsigned> mapping,
                                    uint64_t &remaining, unsigned depth) {
  if (!depth)
    return error("source.limit", "participant placement depth limit exceeded");
  if (auto e = charge(1, remaining))
    return e;
  auto remap = [&](ArrayRef<unsigned> values,
                   bool ordered) -> Expected<std::vector<unsigned>> {
    if (auto e = charge(values.size() + 1, remaining))
      return std::move(e);
    std::vector<unsigned> result;
    result.reserve(values.size());
    for (auto role : values)
      result.push_back(mapping[role]);
    if (!ordered)
      llvm::sort(result);
    return result;
  };
  if (const auto *data = std::get_if<DataPlacement>(&placement.value)) {
    auto result = remap(data->roles, false);
    if (!result)
      return result.takeError();
    return ValuePlacement(DataPlacement{std::move(*result)});
  }
  if (const auto *oracle = std::get_if<OraclePlacement>(&placement.value)) {
    auto result = remap(oracle->receivers, false);
    if (!result)
      return result.takeError();
    return ValuePlacement(
        OraclePlacement{mapping[oracle->holder], std::move(*result)});
  }
  const auto &product = std::get<ProductPlacement>(placement.value);
  if (auto e =
          charge(product.instance.size() + product.fields.size(), remaining))
    return std::move(e);
  auto arguments = remap(product.arguments, true);
  if (!arguments)
    return arguments.takeError();
  ProductPlacement result{product.instance, std::move(*arguments), {}};
  result.fields.reserve(product.fields.size());
  for (const auto &field : product.fields) {
    auto child = substitute(field, mapping, remaining, depth - 1);
    if (!child)
      return child.takeError();
    result.fields.push_back(std::move(*child));
  }
  return ValuePlacement(std::move(result));
}
} // namespace
std::vector<unsigned> placementRoles(const ValuePlacement &placement) {
  if (const auto *data = std::get_if<DataPlacement>(&placement.value))
    return data->roles;
  std::vector<unsigned> result;
  if (const auto *oracle = std::get_if<OraclePlacement>(&placement.value)) {
    result = oracle->receivers;
    result.push_back(oracle->holder);
  } else
    result = std::get<ProductPlacement>(placement.value).arguments;
  llvm::sort(result);
  return result;
}
Error validatePlacement(const ValuePlacement &placement, unsigned participants,
                        uint64_t &remaining, unsigned maximumDepth) {
  return validate(placement, participants, remaining, maximumDepth);
}
Expected<ValuePlacement> substitutePlacement(const ValuePlacement &placement,
                                             ArrayRef<unsigned> mapping,
                                             unsigned participants,
                                             uint64_t &remaining,
                                             unsigned maximumDepth) {
  if (auto e = roles(mapping, participants, true, remaining))
    return std::move(e);
  if (auto e = validate(placement, mapping.size(), remaining, maximumDepth))
    return std::move(e);
  return substitute(placement, mapping, remaining, maximumDepth);
}
} // namespace zkc::language
