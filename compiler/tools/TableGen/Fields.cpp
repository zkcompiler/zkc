#include "Fields.h"
#include "Roles.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include "llvm/TableGen/TableGenBackend.h"
#include <map>
#include <string>
#include <vector>

using namespace llvm;
namespace {
struct Field {
  std::string name, kind, storage, summary, presence, role, decision;
};
std::string quoted(StringRef text) {
  std::string result;
  raw_string_ostream stream(result);
  stream << '"';
  printEscapedString(text, stream);
  stream << '"';
  return result;
}
// Whether a constraint, or one it wraps, is of class `name`.
bool declares(const Record *constraint, StringRef name) {
  while (constraint) {
    if (constraint->isSubClassOf(name))
      return true;
    const RecordVal *base = constraint->getValue("baseAttr");
    const auto *def = base ? dyn_cast<DefInit>(base->getValue()) : nullptr;
    constraint = def ? def->getDef() : nullptr;
  }
  return false;
}
// A string field of a constraint, or empty when the constraint leaves it unset.
std::string text(const Record *record, StringRef field) {
  const RecordVal *value = record->getValue(field);
  const auto *string =
      value ? dyn_cast<StringInit>(value->getValue()) : nullptr;
  return string ? string->getValue().trim().str() : std::string();
}
} // namespace

// Every operation of a zkc dialect, and one row per inherent field: each
// attribute or property argument in ODS order, then the segment-size property
// that an attribute-sized trait adds. Operations without fields are listed so
// that the closed operation set is complete.
bool emitFieldInventory(raw_ostream &os, const RecordKeeper &records) {
  std::map<std::string, std::vector<Field>> operations;
  for (const Record *op : records.getAllDerivedDefinitions("Op")) {
    const Record *dialect = op->getValueAsDef("opDialect");
    if (!dialect->getValueAsString("cppNamespace").contains("zkc"))
      continue;
    std::string name = (dialect->getValueAsString("name") + "." +
                        op->getValueAsString("opName"))
                           .str();
    auto &fields = operations[name];
    const DagInit *arguments = op->getValueAsDag("arguments");
    for (unsigned index = 0; index < arguments->getNumArgs(); ++index) {
      const auto *argument = dyn_cast<DefInit>(arguments->getArg(index));
      if (!argument)
        continue;
      const Record *constraint = argument->getDef();
      if (constraint->isSubClassOf("OpVariable"))
        constraint = constraint->getValueAsDef("constraint");
      bool attribute = constraint->isSubClassOf("Attr");
      if (!attribute && !constraint->isSubClassOf("Property"))
        continue;
      StringRef field = arguments->getArgNameStr(index);
      if (field.empty())
        PrintFatalError(op, "inherent fields must be named");
      Field row{field.str(),
                attribute ? "attribute" : "property",
                text(constraint, "storageType"),
                text(constraint, "summary"),
                "required",
                "",
                declares(constraint, "CallMetadataAttr") ? "refused"
                                                         : "interpreted"};
      if (attribute) {
        std::string value = text(constraint, "defaultValue");
        if (!value.empty())
          row.presence = "default " + value;
        else if (constraint->getValueAsBit("isOptional"))
          row.presence = "optional";
      }
      if (const Record *role = roleConstraint(constraint))
        row.role = role->getValueAsString("roleShape").str();
      fields.push_back(std::move(row));
    }
    for (const Init *trait : op->getValueAsListInit("traits")->getElements()) {
      const auto *def = dyn_cast<DefInit>(trait);
      StringRef traitName = def ? def->getDef()->getName() : StringRef();
      if (traitName == "AttrSizedOperandSegments")
        fields.push_back({"operandSegmentSizes", "segments",
                          "::mlir::DenseI32ArrayAttr", "operand segment sizes",
                          "required", "", "structure"});
      else if (traitName == "AttrSizedResultSegments")
        fields.push_back({"resultSegmentSizes", "segments",
                          "::mlir::DenseI32ArrayAttr", "result segment sizes",
                          "required", "", "structure"});
    }
  }
  emitSourceFileHeader("zkc operation field inventory", os, records);
  os << "// Every operation of a zkc dialect, ordered by name, and one row "
        "per\n"
        "// inherent field in ODS order: name, kind, storage, constraint\n"
        "// summary, presence, declared role shape and reader decision.\n";
  os << "#ifdef ZKC_FIELD_OPERATION\n";
  for (const auto &[operation, fields] : operations)
    os << "ZKC_FIELD_OPERATION(" << quoted(operation) << ")\n";
  os << "#undef ZKC_FIELD_OPERATION\n#endif\n";
  os << "#ifdef ZKC_FIELD\n";
  for (const auto &[operation, fields] : operations)
    for (const auto &field : fields)
      os << "ZKC_FIELD(" << quoted(operation) << ", " << quoted(field.name)
         << ", " << quoted(field.kind) << ", " << quoted(field.storage) << ", "
         << quoted(field.summary) << ", " << quoted(field.presence) << ", "
         << quoted(field.role) << ", " << quoted(field.decision) << ")\n";
  os << "#undef ZKC_FIELD\n#endif\n";
  return false;
}
