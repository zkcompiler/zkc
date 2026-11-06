#ifndef ZKC_DATA_STRUCTURE_H
#define ZKC_DATA_STRUCTURE_H
#include "../../NativeTypeWork.h"
#include "mlir/IR/AttrTypeSubElements.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Diagnostics.h"
#include <algorithm>
#include <type_traits>

namespace zkc::data::detail {
// Share exact immutable structural results only within the caller's native
// work scope. Expanded local ceilings still count every occurrence. The
// cumulative debit counts actual visits, cache lookups, edges and string scans.
class ScopedStructure {
  using Summary = zkc::detail::NativeTypeWork::Structure;
  zkc::detail::NativeTypeWork &work;
  mlir::MLIRContext *context = nullptr;
  template <class Value, class Cache>
  bool read(Value value, Cache &cache, Summary &result, unsigned depth) {
    zkc::detail::NativeTypeWorkScope::charge();
    if (!value || depth >= 64 || (context && context != value.getContext()))
      return false;
    context = value.getContext();
    if (auto found = cache.find(value); found != cache.end()) {
      result = found->second;
      return depth + result.height < 64;
    }
    Summary summary{1, 0, 0};
    if constexpr (std::is_same_v<Value, mlir::Attribute>)
      if (auto text = mlir::dyn_cast<mlir::StringAttr>(value)) {
        summary.bytes = text.getValue().size();
        zkc::detail::NativeTypeWorkScope::charge(summary.bytes);
      }
    bool good = summary.bytes <= 64 * 1024 * 1024;
    auto add = [&](auto child, auto &children) {
      if (!good)
        return;
      Summary nested;
      if (!read(child, children, nested, depth + 1) ||
          nested.nodes > 200000 - summary.nodes ||
          nested.bytes > 64 * 1024 * 1024 - summary.bytes) {
        good = false;
        return;
      }
      summary.nodes += nested.nodes;
      summary.bytes += nested.bytes;
      summary.height = std::max(summary.height, 1 + nested.height);
    };
    value.walkImmediateSubElements(
        [&](mlir::Attribute child) { add(child, work.attributes); },
        [&](mlir::Type child) { add(child, work.types); });
    if (!good)
      return false;
    zkc::detail::NativeTypeWorkScope::charge();
    cache.try_emplace(value, summary);
    result = summary;
    return true;
  }

public:
  explicit ScopedStructure(zkc::detail::NativeTypeWork &work) : work(work) {}
  bool verify(llvm::ArrayRef<mlir::Attribute> attributes,
              llvm::ArrayRef<mlir::Type> types) {
    uint64_t nodes = 0, bytes = 0;
    auto include = [&](auto value, auto &cache) {
      Summary summary;
      if (!read(value, cache, summary, 0) || summary.nodes > 200000 - nodes ||
          summary.bytes > 64 * 1024 * 1024 - bytes)
        return false;
      nodes += summary.nodes;
      bytes += summary.bytes;
      return true;
    };
    for (auto value : attributes)
      if (!include(value, work.attributes))
        return false;
    for (auto value : types)
      if (!include(value, work.types))
        return false;
    return true;
  }
};
/// Count expanded occurrences, including repeated context-uniqued children.
/// This bounds structural inspection, not source or executable admission.
inline mlir::LogicalResult
verifyStructure(mlir::function_ref<mlir::InFlightDiagnostic()> emit,
                llvm::ArrayRef<mlir::Attribute> roots,
                llvm::ArrayRef<mlir::Type> leafTypes = {}) {
  if (auto *work = zkc::detail::NativeTypeWorkScope::current()) {
    if (!ScopedStructure(*work).verify(roots, leafTypes))
      return emit() << "metadata exceeds structural context, depth, node or "
                       "byte limits";
    return mlir::success();
  }
  llvm::SmallVector<std::pair<mlir::Attribute, unsigned>> attrs;
  llvm::SmallVector<std::pair<mlir::Type, unsigned>> types;
  zkc::detail::NativeTypeWorkScope::charge(roots.size() + leafTypes.size());
  for (auto root : roots)
    attrs.emplace_back(root, 0);
  for (auto type : leafTypes)
    types.emplace_back(type, 0);
  mlir::MLIRContext *context = nullptr;
  unsigned remaining = 200000;
  size_t bytes = 0;
  while (!attrs.empty() || !types.empty()) {
    zkc::detail::NativeTypeWorkScope::charge();
    if (!remaining--)
      return emit() << "metadata exceeds expanded structural work limit";
    if (!attrs.empty()) {
      auto entry = attrs.pop_back_val();
      auto attr = entry.first;
      auto depth = entry.second;
      if (!attr || depth >= 64)
        return emit() << "missing attribute or excessive structural depth";
      if (context && attr.getContext() != context)
        return emit() << "metadata crosses MLIR contexts";
      context = attr.getContext();
      if (auto string = mlir::dyn_cast<mlir::StringAttr>(attr)) {
        zkc::detail::NativeTypeWorkScope::charge(string.getValue().size());
        bytes += string.getValue().size();
        if (bytes > 64 * 1024 * 1024)
          return emit() << "metadata exceeds expanded string byte limit";
      }
      attr.walkImmediateSubElements(
          [&](mlir::Attribute child) {
            zkc::detail::NativeTypeWorkScope::charge();
            attrs.emplace_back(child, depth + 1);
          },
          [&](mlir::Type child) {
            zkc::detail::NativeTypeWorkScope::charge();
            types.emplace_back(child, depth + 1);
          });
    } else {
      auto entry = types.pop_back_val();
      auto type = entry.first;
      auto depth = entry.second;
      if (!type || depth >= 64)
        return emit() << "missing type or excessive structural depth";
      if (context && type.getContext() != context)
        return emit() << "metadata crosses MLIR contexts";
      context = type.getContext();
      type.walkImmediateSubElements(
          [&](mlir::Attribute child) {
            zkc::detail::NativeTypeWorkScope::charge();
            attrs.emplace_back(child, depth + 1);
          },
          [&](mlir::Type child) {
            zkc::detail::NativeTypeWorkScope::charge();
            types.emplace_back(child, depth + 1);
          });
    }
  }
  return mlir::success();
}
} // namespace zkc::data::detail
#endif
