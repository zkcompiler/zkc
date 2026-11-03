#include "zkc/Dialect/SemanticFields.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <vector>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
// Every operation of a zkc dialect, generated from ODS.
constexpr StringLiteral zkcOperations[] = {
#define ZKC_FIELD_OPERATION(NAME) NAME,
#include "zkc/Dialect/fieldInventory.cpp.inc"
};
// Each inherent field of a zkc operation, generated from ODS: an attribute or
// property is part of the operation's specified meaning, call metadata that ODS
// marks is refused, and segment sizes are structure.
constexpr FieldDecision decide(char decision) {
  return decision == 's'   ? FieldDecision::Structure
         : decision == 'r' ? FieldDecision::Refused
                           : FieldDecision::Interpreted;
}
constexpr FieldCoverage zkcFields[] = {
#define ZKC_FIELD(OPERATION, FIELD, KIND, STORAGE, SUMMARY, PRESENCE, ROLE,    \
                  DECISION)                                                    \
  {OPERATION, FIELD, decide(DECISION[0])},
#include "zkc/Dialect/fieldInventory.cpp.inc"
};

bool neutralOverflow(Attribute value) {
  auto flags = dyn_cast<arith::IntegerOverflowFlagsAttr>(value);
  return flags && flags.getValue() == arith::IntegerOverflowFlags::none;
}
// The upstream operations that semantic readers dispatch on, each with every
// field of its registered definition. A coverage test compares these adapters
// with the registered definitions, so an upstream change needs a decision.
constexpr StringLiteral upstreamOperations[] = {
    "arith.addi", "arith.andi",   "arith.cmpi", "arith.constant",
    "arith.ori",  "arith.select", "arith.xori", "cf.br",
    "cf.cond_br", "func.call",    "func.func",  "func.return"};
constexpr FieldCoverage upstreamFields[] = {
    {"arith.addi", "overflowFlags", FieldDecision::Restricted, neutralOverflow},
    {"arith.cmpi", "predicate", FieldDecision::Interpreted},
    {"arith.constant", "value", FieldDecision::Interpreted},
    {"cf.cond_br", "branch_weights", FieldDecision::Refused},
    {"cf.cond_br", "operandSegmentSizes", FieldDecision::Structure},
    {"func.call", "arg_attrs", FieldDecision::Refused},
    {"func.call", "callee", FieldDecision::Interpreted},
    {"func.call", "no_inline", FieldDecision::Refused},
    {"func.call", "res_attrs", FieldDecision::Refused},
    {"func.func", "arg_attrs", FieldDecision::Refused},
    {"func.func", "function_type", FieldDecision::Interpreted},
    {"func.func", "no_inline", FieldDecision::Refused},
    {"func.func", "res_attrs", FieldDecision::Refused},
    {"func.func", "sym_name", FieldDecision::Interpreted},
    {"func.func", "sym_visibility", FieldDecision::Interpreted},
};

ArrayRef<FieldCoverage> rowsOf(ArrayRef<FieldCoverage> table,
                               StringRef operation) {
  const auto *first = partition_point(table, [&](const auto &row) {
    return StringRef(row.operation) < operation;
  });
  const auto *last =
      std::partition_point(first, table.end(), [&](const auto &row) {
        return StringRef(row.operation) == operation;
      });
  return ArrayRef<FieldCoverage>(first, last);
}
bool contains(ArrayRef<StringLiteral> operations, StringRef operation) {
  return std::binary_search(operations.begin(), operations.end(), operation,
                            [](StringRef a, StringRef b) { return a < b; });
}
} // namespace

ArrayRef<StringLiteral> getSemanticOperations() {
  static const std::vector<StringLiteral> operations = [] {
    std::vector<StringLiteral> result(std::begin(zkcOperations),
                                      std::end(zkcOperations));
    result.insert(result.end(), std::begin(upstreamOperations),
                  std::end(upstreamOperations));
    llvm::sort(result, [](StringRef a, StringRef b) { return a < b; });
    return result;
  }();
  return operations;
}

ArrayRef<FieldCoverage> getFieldCoverage(StringRef operation) {
  auto rows = rowsOf(zkcFields, operation);
  return rows.empty() ? rowsOf(upstreamFields, operation) : rows;
}

bool isSemanticOperation(StringRef operation) {
  return contains(zkcOperations, operation) ||
         contains(upstreamOperations, operation);
}

bool admitsField(Operation *op, NamedAttribute attribute,
                 ArrayRef<StringRef> named) {
  StringRef name = attribute.getName().getValue();
  if (is_contained(named, name))
    return true;
  StringRef operation = op->getName().getStringRef();
  if (!op->isRegistered() || !isSemanticOperation(operation))
    return false;
  for (const auto &row : getFieldCoverage(operation)) {
    if (row.field != name)
      continue;
    switch (row.decision) {
    case FieldDecision::Interpreted:
    case FieldDecision::Structure:
      return true;
    case FieldDecision::Restricted:
      return row.supported && row.supported(attribute.getValue());
    case FieldDecision::Refused:
      return false;
    }
  }
  return false;
}

bool admitsFields(Operation *op, ArrayRef<StringRef> named) {
  return op->isRegistered() &&
         isSemanticOperation(op->getName().getStringRef()) &&
         all_of(op->getAttrs(), [&](NamedAttribute attribute) {
           return admitsField(op, attribute, named);
         });
}
} // namespace zkc
