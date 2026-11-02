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
/// the generated role attribute table is the only record of them. Renaming
/// maps every element in place: it never sorts, merges or drops a name.
enum class RoleShape {
  /// One role name.
  Role,
  /// An ordered list of role names whose positions carry meaning: the actual
  /// roles of an application, in its callee roster's order, or one role per
  /// operand. Order and multiplicity are part of the value.
  RoleNames,
  /// The roles available to, or taking part in, an action or region.
  RoleSet,
  /// One role set per input, result or carried slot.
  SlotRoleSets,
  /// A roster declaration. It binds the role names that the declaring
  /// operation's other attributes, and the operations nested in it, use.
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

/// Whether an operation declares a roster. It opens a binding scope: its own
/// role uses, and those nested in it, name the roles it binds.
bool declaresRoster(llvm::StringRef operation);
inline bool declaresRoster(mlir::Operation *op) {
  return declaresRoster(op->getName().getStringRef());
}

/// The value of an operation's only role use when that use is one role; null
/// otherwise. This is a structural query over the declared role uses, not the
/// role that executes the operation: a participant send or receive names its
/// counterparty as `peer`. Use getActionOwner for ownership.
mlir::StringAttr getSoleRole(mlir::Operation *op);

/// The role that executes a single-owner Protocol action: the owner of a
/// guard, a conditional completion or a query, and the role of a local call.
/// Null for every other operation, including an exchange, whose sender and
/// receiver each execute one side, and a participant send or receive, whose
/// `peer` is the counterparty. The typed operations decide this; it is not
/// read from the role attribute table.
mlir::StringAttr getActionOwner(mlir::Operation *op);

/// Maps one role name to its replacement. A function that does not rename a
/// role returns it unchanged.
using RoleMap = llvm::function_ref<mlir::StringAttr(mlir::StringAttr)>;

/// Renames the role names `value` holds in `shape`. A roster declaration is
/// returned unchanged, and so is any part of `value` that does not have the
/// declared shape; operation verification refuses such values separately.
mlir::Attribute renameRoles(mlir::Attribute value, RoleShape shape,
                            RoleMap map);

/// Renames every role use among `attributes`, the attributes of an operation
/// named `operation`, under a substitution from an enclosing scope. Roster
/// declarations and every other attribute, including undeclared attributes
/// that hold role-like names, are unchanged. An operation that declares a
/// roster binds the names its own uses refer to, so none of its attributes
/// change.
void renameRoleUses(llvm::StringRef operation, mlir::NamedAttrList &attributes,
                    RoleMap map);
inline void renameRoleUses(mlir::OperationName operation,
                           mlir::NamedAttrList &attributes, RoleMap map) {
  renameRoleUses(operation.getStringRef(), attributes, map);
}

/// Renames the role uses of `op` in place, under the same scope rule.
void renameRoleUses(mlir::Operation *op, RoleMap map);

} // namespace zkc::protocol_ir

#endif
