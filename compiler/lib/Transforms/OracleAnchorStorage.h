#ifndef ZKC_TRANSFORMS_ORACLEANCHORSTORAGE_H
#define ZKC_TRANSFORMS_ORACLEANCHORSTORAGE_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/Error.h"
#include <string>
#include <vector>
namespace zkc::protocol {
struct OracleStorageField {
  std::string name;
  mlir::Type type;
};
struct OracleRoleStorage {
  std::string role;
  std::vector<OracleStorageField> fields;
  mlir::Type record, sequence;
};
struct OracleAnchorConstructor {
  enum class Kind { Input, Send, Virtual };
  Kind constructor;
  // Instruction ordinals in the prepared entry, descending through repeats.
  // These are not JSON array paths in the original structured snapshot.
  std::vector<unsigned> path;
  protocol_ir::OracleKindAttr kind;
  std::string holder, site, declaration;
  std::vector<std::string> receivers;
  std::string scheme; // Empty for ideal tables; always empty for virtuals.
  uint64_t maximumInstances;
  std::vector<OracleRoleStorage> roles;
};
struct OracleAnchorStorage {
  std::string entry;
  std::vector<OracleAnchorConstructor> constructors;
};
// The selector runs only for root inputs and sends, never virtual anchors or
// component rebindings. Empty selects clear ideal delivery. Merkle selections
// must resolve the actual vector commitment signature for the kind's data.
using OracleStorageSelection = llvm::function_ref<llvm::Expected<std::string>(
    const OracleAnchorConstructor &)>;
// Plans ordinary, per-constructor, per-role persistent stores. A reference is
// (constructor ordinal, instance ordinal), so equal data does not merge anchors
// and recurrent virtuals need no recursive native type. This is a checked
// storage layout, not a generated body or a realization correspondence token.
// Records retain repeat indices, named dimensions, derived leaf count and
// payload; those indices must come from the actual occurrence, not its instance
// ordinal.
llvm::Expected<OracleAnchorStorage>
planOracleAnchorStorage(mlir::ModuleOp prepared, llvm::StringRef entry,
                        OracleStorageSelection select);
// Static shape erasure preserves the reference carrier. Shape belongs to the
// immutable record. No ideal oracle type escapes into the ordinary carrier.
llvm::Expected<mlir::Type>
oracleReferenceType(protocol_ir::OracleKindAttr kind);
// Producer-only helper construction in an owned candidate. The caller must
// discard a partial candidate on failure. Appending is ordered scoped
// execution; this helper neither checks oracle shapes nor authenticates data.
// Those checks belong at their original occurrences in the complete
// realization.
llvm::Expected<mlir::func::FuncOp>
emitOracleAnchorAllocator(mlir::ModuleOp candidate, const OracleAnchorStorage &,
                          unsigned constructor, unsigned role);
// Independent actual-body reader for the allocation primitive. The caller must
// separately derive the layout from the original; this check is not an oracle
// simulation or authority for a user-supplied realization record.
llvm::Error checkOracleAnchorAllocator(mlir::ModuleOp candidate,
                                       mlir::func::FuncOp actual,
                                       const OracleAnchorStorage &,
                                       unsigned constructor, unsigned role);
// Load one constructor's ordinary record through an actual reference. Verify
// its constructor tag before indexing the selected role's immutable store;
// return every recorded coordinate, dimension and payload field in order.
// The surrounding dispatcher chooses this constructor; it must not substitute
// a static possible origin for the reference's actual tag.
llvm::Expected<mlir::func::FuncOp>
emitOracleAnchorLookup(mlir::ModuleOp candidate, const OracleAnchorStorage &,
                       unsigned constructor, unsigned role);
llvm::Error checkOracleAnchorLookup(mlir::ModuleOp candidate,
                                    mlir::func::FuncOp actual,
                                    const OracleAnchorStorage &,
                                    unsigned constructor, unsigned role);
} // namespace zkc::protocol
#endif
