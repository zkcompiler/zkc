#ifndef ZKC_DIALECT_PROTOCOL_IR_PROTOCOLDIALECT_TD
#define ZKC_DIALECT_PROTOCOL_IR_PROTOCOLDIALECT_TD

include "zkc/Dialect/Base.td"
include "mlir/IR/CommonAttrConstraints.td"

def ProtocolDialect : ZKCDialect {
  let name = "protocol";
  let cppNamespace = "::zkc::protocol_ir";
  // Oracle kinds and sequences derive their logical data carriers.
  let dependentDialects = ["::zkc::data::DataDialect"];
  let useDefaultTypePrinterParser = 1;
  let useDefaultAttributePrinterParser = 1;
  let extraClassDeclaration = ZkcStrictPropertyRegistration # [{
    void initializeAttributes();
  }];
}

// Role-valued inherent attributes. Each constraint wraps the attribute
// constraint that the operation would otherwise declare and keeps its storage
// type, return type, predicate and builders, so generated accessors and the
// textual form are those of the wrapped attribute. It adds only the shape in
// which the attribute holds role names. zkc-tblgen collects these declarations
// into the dialect's role attribute table, the one record of which attributes
// hold roles; readers enumerate and rename role uses through that table.
class ProtocolRoleAttr<Attr attr, string shape> : ConfinedAttr<attr, []> {
  string roleShape = shape;
}
// One role name.
class ProtocolRole<Attr attr> : ProtocolRoleAttr<attr, "Role">;
// An ordered list of role names whose positions carry meaning, such as an
// application's actual roles in its callee roster's order. Order and
// multiplicity are part of the value.
class ProtocolRoleNames<Attr attr> : ProtocolRoleAttr<attr, "RoleNames">;
// The roles available to, or taking part in, an action or region.
class ProtocolRoleSet<Attr attr> : ProtocolRoleAttr<attr, "RoleSet">;
// One role set per input, result or carried slot.
class ProtocolSlotRoleSets<Attr attr> : ProtocolRoleAttr<attr, "SlotRoleSets">;
// A roster declaration binds the role names that the declaring operation's
// other attributes and the operations nested in it use, rather than using
// them. A substitution from an enclosing scope changes none of them.
class ProtocolRoster<Attr attr> : ProtocolRoleAttr<attr, "Roster">;

#endif
