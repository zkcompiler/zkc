#ifndef ZKC_ANALYSIS_COMMON_CONTROL_H
#define ZKC_ANALYSIS_COMMON_CONTROL_H

#include "zkc/Contracts/MathematicalFacts.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <optional>

namespace zkc {
/// One exact immutable entry component. Native ports are already flattened;
/// each path pair selects a declared variant alternative and payload ordinal.
struct CommonControlComponent {
  unsigned input = 0;
  mlir::StringAttr role;
  llvm::SmallVector<unsigned> path;
};
struct CommonControlRequirement {
  llvm::SmallVector<CommonControlComponent> components;
  mlir::Type type;
  bool tagOnly = false;
  /// Observe only this collection extent; never combined with tagOnly.
  std::optional<unsigned> extentAxis;
  /// The actual common action that first required this association.
  mlir::Operation *control = nullptr;
};
/// Derive obligations from an admitted, immutable Protocol declaration and its
/// actual acyclic helper closure. No attribute, availability set or public bit
/// supplies input agreement. A successful result is a requirement inventory,
/// not evidence that any input admission has discharged it. Borrowed operation
/// pointers expire on mutation. Every traversal and comparison debits Work.
/// Demanded loop observations use grounded base/transition equations at exact
/// invocation, slot and role identities; unrelated carries stay undemanded.
/// Tag, payload and extent observations remain separate through recurrence.
/// Refusals: common-control-provenance and common-control-capacity.
llvm::Expected<llvm::SmallVector<CommonControlRequirement>>
deriveCommonControlRequirements(protocol_ir::MathematicalOp, facts::Work &);
} // namespace zkc
#endif
