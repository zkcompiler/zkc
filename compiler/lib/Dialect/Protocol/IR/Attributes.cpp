#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolAttrs.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/IR/RoleAttributes.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/TypeSwitch.h"
#include <algorithm>

using namespace mlir;
#include "zkc/Dialect/Protocol/IR/protocolEnums.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolAttrs.cpp.inc"

namespace zkc::protocol_ir {
void ProtocolDialect::initializeAttributes() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Protocol/IR/protocolAttrs.cpp.inc"
      >();
}

LogicalResult ProfileAttr::verify(function_ref<InFlightDiagnostic()> emitError,
                                  Profile value) {
  if (!symbolizeProfile(static_cast<uint32_t>(value)))
    return emitError() << "unknown protocol profile";
  return success();
}
bool isMathematicalProfile(Profile profile) {
  return profile == Profile::Protocol || profile == Profile::Participant;
}
bool isExecutableProfile(Profile profile) {
  return profile == Profile::Exec || profile == Profile::Physical;
}
LogicalResult ProtocolModuleOp::verify() {
  if (!symbolizeProfile(static_cast<uint32_t>(getProfile())))
    return diagnostics::emit(emitOpError(), "protocol-profile");
  return success();
}

namespace {
// Generated from the ODS role attribute declarations.
constexpr RoleAttribute roleAttributes[] = {
#include "zkc/Dialect/Protocol/IR/protocolRoleAttributes.cpp.inc"
};
ArrayAttr renameRoleSet(ArrayAttr set, RoleMap map) {
  SmallVector<Attribute> renamed;
  renamed.reserve(set.size());
  for (Attribute role : set) {
    auto name = dyn_cast_if_present<StringAttr>(role);
    renamed.push_back(name ? Attribute(map(name)) : role);
  }
  return ArrayAttr::get(set.getContext(), renamed);
}
} // namespace

ArrayRef<RoleAttribute> getRoleAttributeTable() { return roleAttributes; }

ArrayRef<RoleAttribute> getRoleAttributes(StringRef operation) {
  ArrayRef<RoleAttribute> table(roleAttributes);
  const auto *first = llvm::partition_point(table, [&](const auto &row) {
    return StringRef(row.operation) < operation;
  });
  const auto *last =
      std::partition_point(first, table.end(), [&](const auto &row) {
        return StringRef(row.operation) == operation;
      });
  return ArrayRef<RoleAttribute>(first, last);
}

SmallVector<RoleUse, 4> getRoleUses(Operation *op) {
  SmallVector<RoleUse, 4> uses;
  for (const auto &declared : getRoleAttributes(op->getName()))
    if (declared.shape != RoleShape::Roster)
      if (auto value = op->getAttr(declared.attribute))
        uses.push_back({declared.attribute, declared.shape, value});
  return uses;
}

StringAttr getSoleRole(Operation *op) {
  auto uses = getRoleUses(op);
  if (uses.size() != 1 || uses.front().shape != RoleShape::Role)
    return {};
  return dyn_cast<StringAttr>(uses.front().value);
}

Attribute renameRoles(Attribute value, RoleShape shape, RoleMap map) {
  switch (shape) {
  case RoleShape::Role:
    if (auto role = dyn_cast_if_present<StringAttr>(value))
      return map(role);
    return value;
  case RoleShape::RoleSet:
    if (auto set = dyn_cast_if_present<ArrayAttr>(value))
      return renameRoleSet(set, map);
    return value;
  case RoleShape::SlotRoleSets:
    if (auto slots = dyn_cast_if_present<ArrayAttr>(value)) {
      SmallVector<Attribute> renamed;
      renamed.reserve(slots.size());
      for (Attribute slot : slots) {
        auto set = dyn_cast_if_present<ArrayAttr>(slot);
        renamed.push_back(set ? Attribute(renameRoleSet(set, map)) : slot);
      }
      return ArrayAttr::get(slots.getContext(), renamed);
    }
    return value;
  case RoleShape::Roster:
    return value;
  }
  llvm_unreachable("unknown role attribute shape");
}

void renameRoleUses(StringRef operation, NamedAttrList &attributes,
                    RoleMap map) {
  for (const auto &declared : getRoleAttributes(operation))
    if (declared.shape != RoleShape::Roster)
      if (auto value = attributes.get(declared.attribute))
        attributes.set(declared.attribute,
                       renameRoles(value, declared.shape, map));
}

void renameRoleUses(Operation *op, RoleMap map) {
  for (const auto &use : getRoleUses(op))
    op->setAttr(use.attribute, renameRoles(use.value, use.shape, map));
}
} // namespace zkc::protocol_ir
