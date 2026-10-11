#ifndef ZKC_TRANSFORMS_REALIZATIONSUBJECT_H
#define ZKC_TRANSFORMS_REALIZATIONSUBJECT_H

#include "mlir/IR/Operation.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include <array>

namespace zkc::mathematical {
/// Copy identity before mutation. Position is relative to the nearest named
/// declaration (or root), including region and block indices at every level.
inline RealizationSubject realizationSubject(mlir::Operation *op) {
  RealizationSubject result;
  if (!op)
    return result;
  result.operation = op->getName().getStringRef().str();
  if (auto site = op->getAttrOfType<mlir::StringAttr>("site"))
    result.site = site.getValue().str();
  std::vector<std::array<unsigned, 3>> path;
  for (auto *current = op; current; current = current->getParentOp()) {
    if (auto name = mlir::SymbolTable::getSymbolName(current)) {
      result.declaration = name.getValue().str();
      if (auto origin =
              current->getAttrOfType<mlir::ArrayAttr>("logical_origin"))
        if (!origin.empty())
          if (auto definition = mlir::dyn_cast<mlir::StringAttr>(origin[0]))
            result.definition = definition.getValue().str();
      break;
    }
    auto *block = current->getBlock();
    if (!block)
      break;
    auto *region = block->getParent();
    unsigned operationIndex = 0, blockIndex = 0;
    for (auto &sibling : *block) {
      if (&sibling == current)
        break;
      ++operationIndex;
    }
    for (auto &sibling : *region) {
      if (&sibling == block)
        break;
      ++blockIndex;
    }
    path.push_back({region->getRegionNumber(), blockIndex, operationIndex});
  }
  if (!result.site.empty())
    return result;
  for (auto it = path.rbegin(); it != path.rend(); ++it)
    result.position.insert(result.position.end(), it->begin(), it->end());
  return result;
}

} // namespace zkc::mathematical
#endif
