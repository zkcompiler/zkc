#ifndef ZKC_DATA_STRUCTURE_H
#define ZKC_DATA_STRUCTURE_H
#include "mlir/IR/AttrTypeSubElements.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Diagnostics.h"

namespace zkc::data::detail {
/// Count expanded occurrences, including repeated context-uniqued children.
/// This bounds structural inspection, not source or executable admission.
inline mlir::LogicalResult
verifyStructure(mlir::function_ref<mlir::InFlightDiagnostic()> emit,
                llvm::ArrayRef<mlir::Attribute> roots,
                llvm::ArrayRef<mlir::Type> leafTypes = {}) {
  llvm::SmallVector<std::pair<mlir::Attribute, unsigned>> attrs;
  llvm::SmallVector<std::pair<mlir::Type, unsigned>> types;
  for (auto root : roots)
    attrs.emplace_back(root, 0);
  for (auto type : leafTypes)
    types.emplace_back(type, 0);
  unsigned remaining = 200000;
  size_t bytes = 0;
  while (!attrs.empty() || !types.empty()) {
    if (!remaining--)
      return emit() << "metadata exceeds expanded structural work limit";
    if (!attrs.empty()) {
      auto entry = attrs.pop_back_val();
      auto attr = entry.first;
      auto depth = entry.second;
      if (!attr || depth >= 64)
        return emit() << "missing attribute or excessive structural depth";
      if (auto string = mlir::dyn_cast<mlir::StringAttr>(attr)) {
        bytes += string.getValue().size();
        if (bytes > 64 * 1024 * 1024)
          return emit() << "metadata exceeds expanded string byte limit";
      }
      attr.walkImmediateSubElements(
          [&](mlir::Attribute child) { attrs.emplace_back(child, depth + 1); },
          [&](mlir::Type child) { types.emplace_back(child, depth + 1); });
    } else {
      auto entry = types.pop_back_val();
      auto type = entry.first;
      auto depth = entry.second;
      if (!type || depth >= 64)
        return emit() << "missing type or excessive structural depth";
      type.walkImmediateSubElements(
          [&](mlir::Attribute child) { attrs.emplace_back(child, depth + 1); },
          [&](mlir::Type child) { types.emplace_back(child, depth + 1); });
    }
  }
  return mlir::success();
}
} // namespace zkc::data::detail
#endif
