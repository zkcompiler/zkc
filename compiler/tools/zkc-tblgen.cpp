#include "TableGen/Declarations.h"
#include "TableGen/TypeBindings.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Main.h"
#include "llvm/TableGen/Record.h"
#include <algorithm>
#include <map>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;

namespace {
enum class Action { Mappings, Declarations, Inventory, TypeBindings };
cl::opt<Action> action(
    cl::desc("Generation action (required):"), cl::Required,
    cl::values(clEnumValN(Action::TypeBindings, "gen-type-bindings",
                          "Generate native type bindings and check coverage"),
               clEnumValN(Action::Mappings, "gen-contract-mappings",
                          "Generate ODS contract associations"),
               clEnumValN(Action::Declarations, "gen-contract-declarations",
                          "Generate neutral contract descriptors"),
               clEnumValN(Action::Inventory, "dump-contract-declarations",
                          "Inspect neutral declarations as JSON")));
struct Association {
  std::string key;
  std::string operation;
  const Record *record;
};

StringRef name(const Record *record) {
  return record->getValueAsString("name");
}

const Record *parent(const Record *term) {
  auto *value = dyn_cast<DefInit>(term->getValueInit("parent"));
  return value ? value->getDef() : nullptr;
}

bool sameParameter(const Record *left, const Record *right) {
  return name(left->getValueAsDef("kind")) ==
             name(right->getValueAsDef("kind")) &&
         left->getValueAsString("sort") == right->getValueAsString("sort");
}

// Compare the ordered scope and indexed applications emitted by neutral
// declaration generation. Record identity is not signature equality: distinct
// operations normally own distinct roots and anonymous application records.
bool sameSignature(const Record *left, const Record *right) {
  auto ls = left->getValueAsListOfDefs("scope");
  auto rs = right->getValueAsListOfDefs("scope");
  auto index = [](ArrayRef<const Record *> scope, const Record *term) {
    return term ? llvm::find(scope, term) - scope.begin() : -1;
  };
  if (ls.size() != rs.size())
    return false;
  auto parameterField = [](const Record *operation) -> const Record * {
    auto *value = dyn_cast<DefInit>(operation->getValueInit("parameterField"));
    return value ? value->getDef() : nullptr;
  };
  if (index(ls, parameterField(left)) != index(rs, parameterField(right)))
    return false;
  for (auto [l, r] : zip(ls, rs)) {
    if (name(l) != name(r) ||
        !sameParameter(l->getValueAsDef("parameter"),
                       r->getValueAsDef("parameter")) ||
        index(ls, parent(l)) != index(rs, parent(r)))
      return false;
    if (l->isSubClassOf("ZKC_Apply") != r->isSubClassOf("ZKC_Apply") ||
        l->isSubClassOf("ZKC_Natural") != r->isSubClassOf("ZKC_Natural"))
      return false;
    if (l->isSubClassOf("ZKC_Natural") &&
        l->getValueAsInt("number") != r->getValueAsInt("number"))
      return false;
    if (l->isSubClassOf("ZKC_Apply")) {
      if (l->getValueAsDef("constructor") != r->getValueAsDef("constructor"))
        return false;
      auto la = l->getValueAsListOfDefs("arguments");
      auto ra = r->getValueAsListOfDefs("arguments");
      if (la.size() != ra.size())
        return false;
      for (auto [a, b] : zip(la, ra))
        if (index(ls, a) != index(rs, b))
          return false;
    }
  }
  for (StringRef field : {"inputs", "outputs", "requirements"}) {
    auto la = left->getValueAsListOfDefs(field);
    auto ra = right->getValueAsListOfDefs(field);
    if (la.size() != ra.size())
      return false;
    StringRef head = field == "requirements" ? "capability" : "constructor";
    for (auto [l, r] : zip(la, ra)) {
      if (field != "requirements" &&
          (!l->isSubClassOf("ZKC_Apply") || !r->isSubClassOf("ZKC_Apply"))) {
        if (l->isSubClassOf("ZKC_Apply") != r->isSubClassOf("ZKC_Apply") ||
            index(ls, l) != index(rs, r))
          return false;
        continue;
      }
      if (l->getValueAsDef(head) != r->getValueAsDef(head))
        return false;
      auto larg = l->getValueAsListOfDefs("arguments");
      auto rarg = r->getValueAsListOfDefs("arguments");
      if (larg.size() != rarg.size())
        return false;
      for (auto [lt, rt] : zip(larg, rarg))
        if (index(ls, lt) != index(rs, rt))
          return false;
    }
  }
  return true;
}

bool sameEnvelope(const Record *left, const Record *right) {
  const auto *lp = left->getValueAsDef("parameters");
  const auto *rp = right->getValueAsDef("parameters");
  return name(left->getValueAsDef("stage")) ==
             name(right->getValueAsDef("stage")) &&
         left->getValueAsBit("commonGeneric") ==
             right->getValueAsBit("commonGeneric") &&
         name(lp) == name(rp) &&
         lp->getValueAsInt("minimum") == rp->getValueAsInt("minimum") &&
         lp->getValueAsInt("maximum") == rp->getValueAsInt("maximum");
}

void quoted(raw_ostream &os, StringRef text) {
  os << '"';
  os.write_escaped(text);
  os << '"';
}

void validateMappedProperties(const Record *record,
                              const RecordKeeper &records) {
  const auto *dialect = record->getValueAsDef("opDialect");
  if (!dialect->isSubClassOf("ZKCDialect"))
    PrintFatalError(record, "mapped operations require a ZKCDialect");
  // ODS subclasses can replace inherited declaration text. Require the whole
  // registration hook, while allowing additional native declarations around it.
  auto hook = records.getClass("ZKCDialect")
                  ->getValueAsString("extraClassDeclaration")
                  .trim();
  if (!dialect->getValueAsString("extraClassDeclaration").contains(hook))
    PrintFatalError(record,
                    "mapped dialects must retain strict property registration");
  // Generated prop-dict parsers bypass the strict registration converter.
  if (const auto *format =
          dyn_cast<StringInit>(record->getValueInit("assemblyFormat")))
    if (format->getValue().contains("prop-dict"))
      PrintFatalError(record,
                      "mapped operations cannot use prop-dict assembly");
  const auto *arguments = record->getValueAsDag("arguments");
  for (StringRef required : {"site", "parameters", "binding"}) {
    const Record *attribute = nullptr;
    for (unsigned i = 0; i < arguments->getNumArgs(); ++i)
      if (arguments->getArgNameStr(i) == required) {
        if (attribute)
          PrintFatalError(record,
                          "duplicate mapped operation property: " + required);
        const auto *value = dyn_cast<DefInit>(arguments->getArg(i));
        attribute = value ? value->getDef() : nullptr;
      }
    bool valid =
        attribute &&
        (required == "binding"
             ? attribute->isSubClassOf("OptionalAttr") &&
                   attribute->getValueAsDef("baseAttr") ==
                       records.getDef("FlatSymbolRefAttr")
             : attribute == records.getDef(required == "site" ? "StrAttr"
                                                              : "ArrayAttr"));
    if (!valid)
      PrintFatalError(record, "invalid or missing mapped operation property: " +
                                  required);
  }
}

bool emitContractMappings(raw_ostream &os, const RecordKeeper &records) {
  for (const auto *contract : records.getAllDerivedDefinitions("ZKC_Operation"))
    if (contract->isSubClassOf("Op"))
      PrintFatalError(contract, "logical declaration must not be an Op record");
  // Reuse the neutral owner's validation (including uniqueness, scoped types,
  // predicates and facets). Do not create a second declaration checker in ODS.
  validateContractDeclarations(records);
  std::vector<Association> associations;
  std::map<std::string, const Record *> operations;
  auto operationName = [](const Record *record) {
    const auto *dialect = record->getValueAsDef("opDialect");
    return (dialect->getValueAsString("name") + "." +
            record->getValueAsString("opName"))
        .str();
  };
  // An unmapped Op with the same native name also breaks ownership of a mapped
  // Op. Inspect all native names without assigning contracts to unmapped Ops.
  for (const auto *record : records.getAllDerivedDefinitions("Op")) {
    auto operation = operationName(record);
    auto [previous, inserted] = operations.emplace(operation, record);
    if (!inserted && (record->isSubClassOf("ZKC_ContractMapping") ||
                      previous->second->isSubClassOf("ZKC_ContractMapping")))
      PrintFatalError(record, "duplicate mapped operation name: " + operation);
  }
  for (const Record *record :
       records.getAllDerivedDefinitions("ZKC_ContractMapping")) {
    if (!record->isSubClassOf("Op"))
      PrintFatalError(record, "contract mapping must belong to an Op record");
    validateMappedProperties(record, records);
    auto contracts = record->getValueAsListOfDefs("contracts");
    if (contracts.empty())
      PrintFatalError(record,
                      "contract mapping requires a logical declaration");
    auto operation = operationName(record);
    for (const auto *contract : contracts) {
      if (!sameEnvelope(contracts.front(), contract) ||
          !sameSignature(contracts.front(), contract))
        PrintFatalError(record, "incompatible mapped contract signatures: " +
                                    name(contracts.front()) + " / " +
                                    name(contract));
      associations.push_back({name(contract).str(), operation, record});
    }
  }

  llvm::sort(associations,
             [](const auto &a, const auto &b) { return a.key < b.key; });
  // Reject repeated declarations, including duplicates within one Op.
  for (size_t i = 1; i < associations.size(); ++i) {
    const auto &previous = associations[i - 1];
    const auto &current = associations[i];
    if (previous.key == current.key) {
      PrintError(previous.record,
                 "previous contract association: " + previous.key);
      PrintFatalError(current.record,
                      "conflicting contract association: " + current.key);
    }
  }

  os << "// Generated from actual ODS Op records by zkc-tblgen. Do not edit.\n"
        "// Included privately by Dialect/Bindings.cpp.\n";
  auto emitRows = [&](StringRef name, bool byOperation) {
    os << "static constexpr std::array<ContractAssociation, "
       << associations.size() << "> " << name << " = {{\n";
    for (const auto &association : associations) {
      os << "  {";
      quoted(os, byOperation ? association.operation : association.key);
      os << ", ";
      quoted(os, byOperation ? association.key : association.operation);
      os << "},\n";
    }
    os << "}};\n";
  };
  emitRows("contractAssociations", false);
  llvm::sort(associations, [](const auto &a, const auto &b) {
    return std::tie(a.operation, a.key) < std::tie(b.operation, b.key);
  });
  emitRows("operationAssociations", true);
  return false;
}
bool generate(raw_ostream &os, const RecordKeeper &records) {
  switch (action) {
  case Action::TypeBindings:
    return emitTypeBindings(os, records);
  case Action::Mappings:
    return emitContractMappings(os, records);
  case Action::Declarations:
    return emitContractDeclarations(os, records);
  case Action::Inventory:
    return emitContractInventory(os, records);
  }
  llvm_unreachable("unknown generation action");
}
} // namespace

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "zkc contract generator\n");
  return TableGenMain(argv[0], &generate);
}
