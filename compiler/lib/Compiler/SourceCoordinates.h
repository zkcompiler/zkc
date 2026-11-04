#ifndef ZKC_LIB_COMPILER_SOURCECOORDINATES_H
#define ZKC_LIB_COMPILER_SOURCECOORDINATES_H

#include "mlir/IR/ValueRange.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include <cstdint>
#include <optional>

namespace zkc::protocol {
/// Source operands address the newest complete result tuple first, followed
/// by older results and the block arguments. Retain each value's creation
/// offset instead of rewriting every older coordinate after each operation.
class SourceCoordinates {
  struct Position {
    uint64_t created, port;
  };
  llvm::DenseMap<mlir::Value, Position> positions;
  uint64_t results = 0;

public:
  explicit SourceCoordinates(mlir::ValueRange arguments) {
    for (auto [port, value] : llvm::enumerate(arguments))
      positions.try_emplace(value, Position{0, port});
  }
  std::optional<uint64_t> lookup(mlir::Value value) const {
    auto found = positions.find(value);
    if (found == positions.end())
      return std::nullopt;
    return results - found->second.created + found->second.port;
  }
  void prepend(mlir::ValueRange values) {
    results += values.size();
    for (auto [port, value] : llvm::enumerate(values))
      positions.try_emplace(value, Position{results, port});
  }
};
} // namespace zkc::protocol

#endif
