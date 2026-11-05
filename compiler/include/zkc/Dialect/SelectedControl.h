#ifndef ZKC_DIALECT_SELECTED_CONTROL_H
#define ZKC_DIALECT_SELECTED_CONTROL_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"

namespace zkc {
/// Structural access to the registered closed selected-region vocabulary.
/// Callers supply formation before borrowing these associations. This view
/// establishes neither common control, reachability, nor resource succession.
bool isSelectedControl(mlir::Operation *);
/// A selected region has one arm per alternative of its selector, at most this
/// many. The bound equals the Data type language's formation profile, so every
/// variant that forms can be selected over; a larger region refuses with
/// `selected-control-limit`.
inline constexpr size_t selectedRegionArmLimit = 512;
llvm::Expected<llvm::SmallVector<mlir::Type>>
selectedPayloadTypes(mlir::Operation *, unsigned arm);
/// Forward a capture argument to its actual outer SSA operand. Payloads have
/// no outer operand of their type and return a null value.
mlir::Value selectedCapture(mlir::BlockArgument);
mlir::LogicalResult verifySelectedControl(mlir::Operation *);
/// Refuse, with `diagnostic`, a transformation whose installed profile
/// requires unconditional Protocol regions when Protocol or participant
/// selection is in the static closure of its selected entry. Callers first
/// establish stage admission. Total Data selection is value computation and
/// does not introduce conditional protocol events; its arms and symbol uses
/// still count toward the complete traversal. `roots` are the entry definition
/// and any other definition the transformation selects to execute, such as a
/// selected construction. The closure contains every reached definition's
/// nested operations, including dormant arms, and the definitions its symbol
/// references name, transitively: applications, helper and local calls,
/// oracle and relation declarations. It is static reachability: no selector
/// is evaluated, and a declaration outside the closure, such as an uncalled
/// helper or protocol, does not change the result. Exhausting the shared
/// allowance of 100,000 operations and symbol uses also refuses. Call it before
/// any candidate mutation. Existing scoped Exec control is unaffected.
llvm::Error
requireUnconditionalProtocolControl(llvm::ArrayRef<mlir::Operation *> roots,
                                    llvm::StringRef diagnostic);
} // namespace zkc
#endif
