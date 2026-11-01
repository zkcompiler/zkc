#ifndef ZKC_DIALECT_PROTOCOL_IR_ROLEATTRIBUTES_H
#define ZKC_DIALECT_PROTOCOL_IR_ROLEATTRIBUTES_H

#include "mlir/IR/Operation.h"
#include "mlir/IR/OperationSupport.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

namespace zkc::protocol_ir {

/// How an inherent attribute holds role names. Each Protocol operation
/// declares its role-valued attributes once, in ODS, with one of these shapes;
/// the generated role attribute table is the only record of them.
enum class RoleShape {
  /// One role name.
  Role,
  /// A set of role names.
  RoleSet,
  /// One role set per input, result or carried slot.
  SlotRoleSets,
  /// A roster declaration. It binds the role names that the other attributes
  /// use, so renaming role uses never changes it.
  Roster,
};

/// One declared role-valued inherent attribute of a registered operation.
struct RoleAttribute {
  llvm::StringLiteral operation;
  llvm::StringLiteral attribute;
  RoleShape shape;
};

/// Every declared role-valued attribute, ordered by operation name and then by
/// ODS argument order.
llvm::ArrayRef<RoleAttribute> getRoleAttributeTable();

/// The declared role-valued attributes of one operation, roster declarations
/// included, in ODS argument order. Empty for every other operation.
llvm::ArrayRef<RoleAttribute> getRoleAttributes(llvm::StringRef operation);
inline llvm::ArrayRef<RoleAttribute>
getRoleAttributes(mlir::OperationName operation) {
  return getRoleAttributes(operation.getStringRef());
}

/// A role use: a present role-valued attribute that is not a roster
/// declaration.
struct RoleUse {
  llvm::StringRef attribute;
  RoleShape shape;
  mlir::Attribute value;
};

/// The role uses of `op` in ODS argument order. An absent optional attribute
/// has no use, and an attribute that merely holds a role-like name is not one.
llvm::SmallVector<RoleUse, 4> getRoleUses(mlir::Operation *op);

/// The role of an operation whose only role use is one role, such as the
/// owner of a guard or query or the role of a local call; null otherwise.
mlir::StringAttr getSoleRole(mlir::Operation *op);

/// Maps one role name to its replacement. A function that does not rename a
/// role returns it unchanged.
using RoleMap = llvm::function_ref<mlir::StringAttr(mlir::StringAttr)>;

/// Renames the role names `value` holds in `shape`. A roster declaration is
/// returned unchanged, and so is any part of `value` that does not have the
/// declared shape; operation verification refuses such values separately.
mlir::Attribute renameRoles(mlir::Attribute value, RoleShape shape,
                            RoleMap map);

/// Renames every role use among `attributes`, the attributes of an operation
/// named `operation`. Roster declarations and every other attribute, including
/// undeclared attributes that hold role-like names, are unchanged.
void renameRoleUses(llvm::StringRef operation, mlir::NamedAttrList &attributes,
                    RoleMap map);
inline void renameRoleUses(mlir::OperationName operation,
                           mlir::NamedAttrList &attributes, RoleMap map) {
  renameRoleUses(operation.getStringRef(), attributes, map);
}

/// Renames the role uses of `op` in place.
void renameRoleUses(mlir::Operation *op, RoleMap map);

} // namespace zkc::protocol_ir

#endif
