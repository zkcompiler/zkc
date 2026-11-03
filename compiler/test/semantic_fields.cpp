#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/SemanticFields.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include <set>
#include <string>
#include <vector>

// Coverage of the semantic field decisions. ODS records each operation's
// structure; semantic readers admit a field only through a decision. These
// cases check that the generated inventory names exactly the registered fields
// of every zkc operation, including properties that are not attributes, that
// every upstream adapter names exactly its registered fields, and that the
// complete set of decisions equals the reviewed copy in
// fixtures/semantic-fields/inventory.txt. Adding or changing an inherent field,
// in ODS or upstream, therefore fails here until the reviewed copy records a
// decision, after every semantic reader of that operation has been checked to
// interpret, restrict or refuse the field. Run this test with `--write` to
// print the current decisions into that file.

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
struct Row {
  StringRef operation, field, kind, storage, summary, presence, role, decision;
};
// The generated inventory, read here independently of the admission code.
constexpr Row inventory[] = {
#define ZKC_FIELD(OPERATION, FIELD, KIND, STORAGE, SUMMARY, PRESENCE, ROLE,    \
                  DECISION)                                                    \
  {OPERATION, FIELD, KIND, STORAGE, SUMMARY, PRESENCE, ROLE, DECISION},
#include "zkc/Dialect/fieldInventory.cpp.inc"
};
constexpr StringLiteral zkcOperations[] = {
#define ZKC_FIELD_OPERATION(NAME) NAME,
#include "zkc/Dialect/fieldInventory.cpp.inc"
};
bool isZkcOperation(StringRef name) {
  return is_contained(zkcOperations, name);
}
StringRef decisionName(FieldDecision decision) {
  switch (decision) {
  case FieldDecision::Interpreted:
    return "interpreted";
  case FieldDecision::Restricted:
    return "restricted";
  case FieldDecision::Structure:
    return "structure";
  case FieldDecision::Refused:
    return "refused";
  }
  llvm_unreachable("unknown field decision");
}
// One reviewed line per decided field, and one per operation without fields.
std::vector<std::string> decisions() {
  std::vector<std::string> lines;
  for (StringRef operation : getSemanticOperations()) {
    std::vector<std::string> fields;
    if (isZkcOperation(operation)) {
      for (const auto &row : inventory)
        if (row.operation == operation)
          fields.push_back((row.operation + " | " + row.field + " | " +
                            row.kind + " | " + row.storage + " | " +
                            row.summary + " | " + row.presence + " | " +
                            (row.role.empty() ? "-" : row.role) + " | " +
                            row.decision)
                               .str());
    } else {
      for (const auto &row : getFieldCoverage(operation))
        fields.push_back((operation + " | " + row.field + " | upstream | " +
                          decisionName(row.decision))
                             .str());
    }
    if (fields.empty())
      fields.push_back((operation + " | -").str());
    lines.insert(lines.end(), fields.begin(), fields.end());
  }
  return lines;
}
// The registered fields of an operation: its inherent attribute names and the
// properties of an instance, which include properties that are not attributes.
std::set<std::string> registered(Builder &builder,
                                 RegisteredOperationName name) {
  std::set<std::string> result;
  for (auto attribute : name.getAttributeNames())
    result.insert(attribute.str());
  auto *op = Operation::create(OperationState(builder.getUnknownLoc(), name));
  if (auto properties =
          dyn_cast_if_present<DictionaryAttr>(op->getPropertiesAsAttribute()))
    for (auto property : properties)
      result.insert(property.getName().str());
  op->destroy();
  return result;
}
Operation *instance(Builder &builder, StringRef name,
                    ArrayRef<NamedAttribute> attributes) {
  OperationState state(builder.getUnknownLoc(), name);
  state.addAttributes(attributes);
  return Operation::create(state);
}
} // namespace

int main(int argc, char **argv) {
  require(argc == 2 || (argc == 3 && StringRef(argv[2]) == "--write"),
          "usage: zkc-semantic_fields-test <reviewed inventory> [--write]");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  context.allowUnregisteredDialects();
  Builder builder(&context);
  if (argc == 3) {
    std::error_code error;
    raw_fd_ostream output(argv[1], error, sys::fs::OF_Text);
    require(!error, "cannot write the reviewed inventory");
    for (const auto &line : decisions())
      output << line << '\n';
    return 0;
  }
  Cases cases;

  cases.run("the inventory names every registered zkc field", [&] {
    llvm::StringSet<> dialects;
    for (StringRef operation : zkcOperations)
      dialects.insert(operation.split('.').first);
    unsigned covered = 0;
    for (auto name : context.getRegisteredOperations()) {
      if (!dialects.contains(name.getDialectNamespace()))
        continue;
      require(isZkcOperation(name.getStringRef()),
              name.getStringRef() + " is not inventoried");
      std::set<std::string> inventoried;
      for (const auto &row : inventory)
        if (row.operation == name.getStringRef())
          inventoried.insert(row.field.str());
      require(registered(builder, name) == inventoried,
              name.getStringRef() + ": inventoried fields differ");
      ++covered;
    }
    require(covered == std::size(zkcOperations),
            "an inventoried operation is not registered");
  });
  cases.run("every upstream adapter names its registered fields", [&] {
    for (StringRef operation : getSemanticOperations()) {
      if (isZkcOperation(operation))
        continue;
      auto name = RegisteredOperationName::lookup(operation, &context);
      require(name.has_value(), operation + " is not registered");
      std::set<std::string> decided;
      for (const auto &row : getFieldCoverage(operation))
        decided.insert(StringRef(row.field).str());
      require(registered(builder, *name) == decided,
              operation + ": the adapter does not decide every field");
    }
  });
  cases.run("decisions match the reviewed inventory", [&] {
    auto file = MemoryBuffer::getFile(argv[1]);
    require(bool(file), "cannot read the reviewed inventory");
    SmallVector<StringRef> reviewed;
    (*file)->getBuffer().split(reviewed, '\n', -1, false);
    auto current = decisions();
    std::set<std::string> before(reviewed.begin(), reviewed.end()),
        after(current.begin(), current.end());
    std::string changes;
    for (const auto &line : before)
      if (!after.count(line))
        changes += "\n  reviewed only: " + line;
    for (const auto &line : after)
      if (!before.count(line))
        changes += "\n  current only:  " + line;
    require(changes.empty() && reviewed.size() == current.size(),
            "inherent fields changed without a reviewed decision; check "
            "every semantic reader of these operations, then rerun with "
            "--write:" +
                changes);
  });

  cases.run("admission follows the decisions", [&] {
    auto text = [&](StringRef value) { return builder.getStringAttr(value); };
    auto admitted = [&](Operation *op, ArrayRef<StringRef> named = {}) {
      bool result = admitsFields(op, named);
      op->destroy();
      return result;
    };
    // A zkc operation's interpreted fields; a discardable attribute only
    // where a reader names it.
    SmallVector<NamedAttribute> exchange{
        builder.getNamedAttr("site", text("s")),
        builder.getNamedAttr("sender", text("P")),
        builder.getNamedAttr("receiver", text("V"))};
    require(admitted(instance(builder, "protocol.exchange", exchange)),
            "interpreted fields were refused");
    exchange.push_back(builder.getNamedAttr("extra", builder.getUnitAttr()));
    require(!admitted(instance(builder, "protocol.exchange", exchange)),
            "a discardable attribute was admitted");
    require(
        admitted(instance(builder, "protocol.exchange", exchange), {"extra"}),
        "a named discardable attribute was refused");
    // Call metadata that ODS marks on a zkc operation.
    auto metadata = builder.getNamedAttr(
        "arg_attrs", builder.getArrayAttr({builder.getDictionaryAttr({})}));
    require(!admitted(instance(builder, "runtime.binding", {metadata})),
            "binding call metadata was admitted");
    require(admitted(instance(builder, "runtime.binding", {metadata}),
                     {"arg_attrs"}),
            "named binding call metadata was refused");
    // Upstream adapters.
    auto overflow = [&](arith::IntegerOverflowFlags flags) {
      return builder.getNamedAttr(
          "overflowFlags",
          arith::IntegerOverflowFlagsAttr::get(&context, flags));
    };
    require(admitted(instance(builder, "arith.addi",
                              {overflow(arith::IntegerOverflowFlags::none)})),
            "the neutral overflow flag was refused");
    require(!admitted(instance(builder, "arith.addi",
                               {overflow(arith::IntegerOverflowFlags::nsw)})),
            "an overflow assumption was admitted");
    require(!admitted(instance(
                builder, "cf.cond_br",
                {builder.getNamedAttr("branch_weights",
                                      builder.getDenseI32ArrayAttr({1, 2}))})),
            "branch weights were admitted");
    require(!admitted(instance(
                builder, "func.call",
                {builder.getNamedAttr("no_inline", builder.getUnitAttr())})),
            "an inlining directive was admitted");
    require(admitted(instance(builder, "func.call",
                              {builder.getNamedAttr("no_inline",
                                                    builder.getUnitAttr())}),
                     {"no_inline"}),
            "a named inlining directive was refused");
    // An upstream operation without an adapter, and an unregistered one,
    // are outside the closed profile even without attributes.
    require(!admitted(instance(builder, "arith.muli", {})),
            "an operation without an adapter was admitted");
    require(!admitted(instance(builder, "test.unregistered", {})),
            "an unregistered operation was admitted");
  });
  return cases.result();
}
