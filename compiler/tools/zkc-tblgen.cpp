#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
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
struct Association {
  std::string key;
  std::string operation;
  bool family;
  const Record *record;
};

// Accept dotted contract names, with a final dot only for family prefixes.
// Reject wildcards: a family has one explicit prefix, never a name rewrite.
bool validKey(StringRef key, bool family) {
  if (family) {
    if (!key.consume_back("."))
      return false;
  }
  if (key.empty())
    return false;
  while (!key.empty()) {
    auto [part, rest] = key.split('.');
    if (part.empty() || !llvm::all_of(part, [](char c) {
          return isAlnum(c) || c == '_' || c == '-';
        }))
      return false;
    if (rest.empty() && key.ends_with("."))
      return false;
    key = rest;
  }
  return true;
}

void quoted(raw_ostream &os, StringRef text) {
  os << '"';
  os.write_escaped(text);
  os << '"';
}

bool emitContractMappings(raw_ostream &os, const RecordKeeper &records) {
  std::vector<Association> associations;
  std::map<std::string, const Record *> operations;
  for (const Record *record :
       records.getAllDerivedDefinitions("ZKC_ContractMapping")) {
    if (!record->isSubClassOf("Op"))
      PrintFatalError(record, "contract mapping must belong to an Op record");
    auto keys = record->getValueAsListOfStrings("contractKeys");
    auto families = record->getValueAsListOfStrings("contractFamilies");
    if (keys.empty() && families.empty())
      PrintFatalError(record, "contract mapping requires a key or family");
    const auto *dialect = record->getValueAsDef("opDialect");
    std::string operation = (dialect->getValueAsString("name") + "." +
                             record->getValueAsString("opName"))
                                .str();
    if (!operations.emplace(operation, record).second)
      PrintFatalError(record, "duplicate mapped operation name: " + operation);
    auto append = [&](ArrayRef<StringRef> values, bool family) {
      for (StringRef key : values) {
        if (!validKey(key, family))
          PrintFatalError(record, "invalid contract key or family: " + key);
        associations.push_back({key.str(), operation, family, record});
      }
    };
    append(keys, false);
    append(families, true);
  }

  llvm::sort(associations,
             [](const auto &a, const auto &b) { return a.key < b.key; });
  // Reject exact duplicates, nested families, and exact keys covered by a
  // family, even on the same operation. Lookup must never choose a winner.
  for (size_t i = 1; i < associations.size(); ++i) {
    const auto &previous = associations[i - 1];
    const auto &current = associations[i];
    if (previous.key == current.key ||
        (previous.family && StringRef(current.key).starts_with(previous.key))) {
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
      os << ", " << (association.family ? "true" : "false") << "},\n";
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
} // namespace

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(argc, argv,
                              "zkc ODS contract mapping generator\n");
  return TableGenMain(argv[0], &emitContractMappings);
}
