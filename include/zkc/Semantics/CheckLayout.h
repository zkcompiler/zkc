//===- CheckLayout.h - check operand segmentation ---------------*- C++ -*-===//
// The one operand-segmentation solver for check contracts
// (docs/spec/carrier.md §7): positional SSA operands are segmented into
// the contract's typed operand roles, and the restrictions on
// multiplicities (one independent capture, same_as only backward) make
// the solution unique when one exists. A counted operand — a counted
// slot or a vector challenge — contributes its declared element count
// of units to the segment consuming it; a segment consumes whole
// operands, so one vector value never splits across two roles.
//===----------------------------------------------------------------------===//

#ifndef ZKC_SEMANTICS_CHECKLAYOUT_H
#define ZKC_SEMANTICS_CHECKLAYOUT_H

#include "zkc/Registry/ProtocolVocabulary.h"
#include "mlir/IR/Value.h"
#include "mlir/IR/ValueRange.h"

#include <map>
#include <string>

namespace zkc {
namespace semantics {

struct OperandView {
  std::map<std::string, llvm::SmallVector<mlir::Value>, std::less<>> roles;
  llvm::SmallVector<std::pair<std::string, uint64_t>> positions;
};

/// The material reference a value carries in itself, or empty when it carries
/// none.
///
/// A profiled seal-stage `pir.bind` absorbs the digest of the content its
/// profile describes, so that digest *is* the value's material reference.
/// Resolving it through a `pir.material_bind` as well would spell one fact
/// twice, and two spellings can disagree — the transcript would then absorb
/// one digest while a claim's anchor named another (docs/spec/carrier.md §4).
/// Every other value carries no reference of its own and is resolved through
/// its material binding as before.
llvm::StringRef selfMaterialRef(mlir::Value value);

/// One SSA operand's element count: a counted slot or a vector
/// challenge contributes its declared count of units; every other
/// producer is one unit.
uint64_t checkOperandUnits(mlir::Value value);

/// All valid segmentations (the callers require exactly one). The
/// solver stops early after finding two — distinguishing "none" from
/// "ambiguous" needs no third.
void solveCheckLayout(const zkc::registry::CheckContract &contract,
                      mlir::ValueRange inputs,
                      llvm::SmallVectorImpl<OperandView> &answers);

} // namespace semantics
} // namespace zkc

#endif // ZKC_SEMANTICS_CHECKLAYOUT_H
