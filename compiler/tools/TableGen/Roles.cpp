#include "Roles.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include "llvm/TableGen/TableGenBackend.h"
#include <map>
#include <string>
#include <utility>
#include <vector>

using namespace llvm;
namespace {
// The role shape a constraint declares, looking through wrappers such as
// OptionalAttr that keep the wrapped constraint as their base attribute.
const Record *roleConstraint(const Record *constraint) {
  while (constraint) {
    if (constraint->isSubClassOf("ProtocolRoleAttr"))
      return constraint;
    const auto *base =
        constraint->getValue("baseAttr")
            ? dyn_cast<DefInit>(constraint->getValueInit("baseAttr"))
            : nullptr;
    constraint = base ? base->getDef() : nullptr;
  }
  return nullptr;
}
} // namespace

bool emitRoleAttributes(raw_ostream &os, const RecordKeeper &records) {
  // Operation name -> (attribute, shape) in ODS argument order.
  std::map<std::string, std::vector<std::pair<std::string, std::string>>> rows;
  for (const Record *op : records.getAllDerivedDefinitions("Op")) {
    const DagInit *arguments = op->getValueAsDag("arguments");
    for (unsigned index = 0; index < arguments->getNumArgs(); ++index) {
      const auto *argument = dyn_cast<DefInit>(arguments->getArg(index));
      const Record *declared =
          argument ? roleConstraint(argument->getDef()) : nullptr;
      if (!declared)
        continue;
      StringRef shape = declared->getValueAsString("roleShape");
      if (!is_contained(
              ArrayRef<StringRef>{"Role", "RoleSet", "SlotRoleSets", "Roster"},
              shape))
        PrintFatalError(op, "unknown role attribute shape '" + shape + "'");
      StringRef attribute = arguments->getArgNameStr(index);
      if (attribute.empty())
        PrintFatalError(op, "role attributes must be named");
      std::string name =
          (op->getValueAsDef("opDialect")->getValueAsString("name") + "." +
           op->getValueAsString("opName"))
              .str();
      auto &attributes = rows[name];
      if (any_of(attributes,
                 [&](const auto &row) { return row.first == attribute; }))
        PrintFatalError(op, "duplicate role attribute '" + attribute + "'");
      attributes.emplace_back(attribute.str(), shape.str());
    }
  }
  emitSourceFileHeader("Protocol role attribute table", os, records);
  os << "// One row per role-valued inherent attribute: operation name, "
        "attribute name\n// and shape. Rows are ordered by operation name, "
        "then by ODS argument order.\n";
  for (const auto &[operation, attributes] : rows)
    for (const auto &[attribute, shape] : attributes)
      os << "{\"" << operation << "\", \"" << attribute
         << "\", ::zkc::protocol_ir::RoleShape::" << shape << "},\n";
  return false;
}
