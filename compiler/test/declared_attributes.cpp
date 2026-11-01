#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/IR/RoleAttributes.h"
#include <memory>
#include <string>

// Declared attribute facts. Protocol operations declare their role-valued
// attributes once, in ODS; every reader enumerates and renames role uses
// through the generated table (the application expander renames copies in
// place; correspondence, value correspondence and application-map comparison
// rename attribute dictionaries; the active-role check, the action-owner
// lookups and expansion costs enumerate uses). This test applies a role
// renaming to every registered Protocol operation through each of those entry
// points and requires exactly the declared role uses to change.
//
// Mathematical formation admits the inherent attributes that the registered
// operation's ODS definition declares and refuses discardable ones and
// upstream call metadata (argument and result dictionaries and inlining).

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using protocol_ir::RoleShape;

namespace {
// Builds a value holding role names in a declared shape.
Attribute shaped(Builder &builder, RoleShape shape, StringRef first,
                 StringRef second) {
  switch (shape) {
  case RoleShape::Role:
    return builder.getStringAttr(first);
  case RoleShape::RoleSet:
  case RoleShape::Roster:
    return builder.getStrArrayAttr({first, second});
  case RoleShape::SlotRoleSets:
    return builder.getArrayAttr({builder.getStrArrayAttr({first}),
                                 builder.getStrArrayAttr({first, second})});
  }
  llvm_unreachable("unknown role shape");
}
// Candidate values for an inherent attribute, role-like ones first. The first
// candidate that the operation's property storage keeps is used.
SmallVector<Attribute> candidates(Builder &builder) {
  return {builder.getStringAttr("A"),
          builder.getStrArrayAttr({"A", "B"}),
          shaped(builder, RoleShape::SlotRoleSets, "A", "B"),
          FlatSymbolRefAttr::get(builder.getContext(), "A"),
          builder.getDictionaryAttr(
              {builder.getNamedAttr("A", builder.getStringAttr("B"))}),
          builder.getI64IntegerAttr(1),
          builder.getBoolAttr(true),
          builder.getUnitAttr(),
          builder.getDenseI64ArrayAttr({1}),
          TypeAttr::get(builder.getFunctionType({}, {}))};
}
bool keep(Operation *op, StringRef name, Attribute value) {
  op->setAttr(name, value);
  if (op->getAttr(name) == value)
    return true;
  op->removeAttr(name);
  return false;
}
// Sets every inherent attribute of an unverified instance. Declared role
// attributes hold roles A and B in their declared shape; every other attribute
// holds role-like names where its storage admits them. Role attribute names
// that the operation does not declare are added as discardable attributes.
void fill(Builder &builder, Operation *op,
          ArrayRef<std::pair<StringRef, RoleShape>> roleNames) {
  auto name = *op->getRegisteredInfo();
  auto declared = protocol_ir::getRoleAttributes(name);
  for (auto attribute : name.getAttributeNames()) {
    auto row = llvm::find_if(declared, [&](const auto &row) {
      return row.attribute == attribute.getValue();
    });
    if (row != declared.end()) {
      bool kept = keep(op, attribute, shaped(builder, row->shape, "A", "B"));
      // A roster may also be one role, such as the role a participant plays.
      if (!kept && row->shape == RoleShape::Roster)
        kept = keep(op, attribute, builder.getStringAttr("A"));
      require(kept, name.getStringRef() + ": declared role attribute '" +
                        attribute.getValue() + "' rejects its shape");
      continue;
    }
    for (auto candidate : candidates(builder))
      if (keep(op, attribute, candidate))
        break;
  }
  // Upstream call metadata is inherent too, but is admitted only where a
  // reader names it; formation names none.
  if (auto ports = dyn_cast<ArgAndResultAttrsOpInterface>(op)) {
    ports.removeArgAttrsAttr();
    ports.removeResAttrsAttr();
  }
  if (auto call = dyn_cast<func::CallOp>(op))
    call.removeNoInlineAttr();
  for (auto [attribute, shape] : roleNames)
    if (!llvm::is_contained(name.getAttributeNames(), attribute))
      op->setDiscardableAttr(attribute, shaped(builder, shape, "A", "B"));
}
// An unverified instance without operands, results or regions.
struct Instance {
  Operation *op;
  Instance(Builder &builder, OperationName name)
      : op(Operation::create(OperationState(builder.getUnknownLoc(), name))) {}
  Instance(const Instance &) = delete;
  ~Instance() { op->destroy(); }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  Cases cases;
  auto table = protocol_ir::getRoleAttributeTable();
  // Every attribute name that some operation declares as role-valued, with a
  // shape it is declared in, so other operations can carry look-alikes.
  SmallVector<std::pair<StringRef, RoleShape>> roleNames;
  for (const auto &row : table)
    if (llvm::none_of(roleNames, [&](const auto &item) {
          return item.first == row.attribute;
        }))
      roleNames.push_back({row.attribute, row.shape});
  auto rename = [&](StringAttr role) {
    return role.getValue() == "A"   ? builder.getStringAttr("X")
           : role.getValue() == "B" ? builder.getStringAttr("Y")
                                    : role;
  };

  cases.run("the table names registered inherent attributes in order", [&] {
    require(!table.empty(), "no declared role attributes");
    for (size_t index = 0; index < table.size(); ++index) {
      const auto &row = table[index];
      auto name = RegisteredOperationName::lookup(row.operation, &context);
      require(name.has_value(), row.operation + " is not registered");
      require(llvm::is_contained(name->getAttributeNames(),
                                 StringAttr::get(&context, row.attribute)),
              row.operation + ": '" + row.attribute + "' is not inherent");
      if (index)
        require(StringRef(table[index - 1].operation) <= row.operation,
                "table rows are not ordered by operation");
      auto rows = protocol_ir::getRoleAttributes(*name);
      require(rows.data() <= &row && &row < rows.data() + rows.size() &&
                  llvm::all_of(
                      rows,
                      [&](const auto &item) {
                        return item.operation == row.operation;
                      }),
              row.operation + ": lookup differs from the table");
    }
  });

  unsigned operations = 0, renamed = 0, untouched = 0;
  for (auto name : context.getRegisteredOperations()) {
    if (name.getDialectNamespace() != "protocol")
      continue;
    ++operations;
    cases.run(name.getStringRef() + " renames exactly its role uses", [&] {
      Instance owned(builder, name);
      auto *op = owned.op;
      fill(builder, op, roleNames);
      auto before = op->getAttrDictionary();
      // Expected uses: present declared attributes that are not rosters.
      SmallVector<protocol_ir::RoleAttribute> expected;
      for (const auto &row : protocol_ir::getRoleAttributes(name))
        if (row.shape != RoleShape::Roster && before.get(row.attribute))
          expected.push_back(row);
      auto uses = protocol_ir::getRoleUses(op);
      require(uses.size() == expected.size(), "role use count differs");
      for (auto [use, row] : llvm::zip(uses, expected))
        require(use.attribute == row.attribute && use.shape == row.shape &&
                    use.value == before.get(row.attribute),
                "role use differs from its declaration");
      auto sole = protocol_ir::getSoleRole(op);
      bool single =
          expected.size() == 1 && expected[0].shape == RoleShape::Role;
      require(single ? sole && sole.getValue() == "A" : !sole,
              "sole role differs from the declared uses");
      // The renamed value of each attribute, independently of the table.
      auto check = [&](DictionaryAttr after) {
        require(after.size() == before.size(), "attribute inventory changed");
        for (auto attribute : before) {
          auto row = llvm::find_if(expected, [&](const auto &row) {
            return row.attribute == attribute.getName().getValue();
          });
          auto value = after.get(attribute.getName());
          if (row == expected.end()) {
            require(value == attribute.getValue(),
                    "'" + attribute.getName().getValue() +
                        "' is not a role use but changed");
            continue;
          }
          require(value == shaped(builder, row->shape, "X", "Y"),
                  "role use '" + attribute.getName().getValue() +
                      "' was not renamed");
        }
      };
      NamedAttrList attributes(before);
      protocol_ir::renameRoleUses(op->getName(), attributes, rename);
      check(attributes.getDictionary(&context));
      protocol_ir::renameRoleUses(op, rename);
      check(op->getAttrDictionary());
      renamed += expected.size();
      untouched += before.size() - expected.size();
    });
  }

  cases.run("values outside the declared shape are left unchanged", [&] {
    auto mixed = builder.getArrayAttr(
        {builder.getStringAttr("A"), builder.getI64IntegerAttr(1)});
    require(protocol_ir::renameRoles(mixed, RoleShape::RoleSet, rename) ==
                builder.getArrayAttr(
                    {builder.getStringAttr("X"), builder.getI64IntegerAttr(1)}),
            "role set element handling differs");
    auto flat = builder.getStrArrayAttr({"A", "B"});
    require(protocol_ir::renameRoles(flat, RoleShape::SlotRoleSets, rename) ==
                flat,
            "slot role sets renamed a non-set slot");
    auto number = builder.getI64IntegerAttr(1);
    require(protocol_ir::renameRoles(number, RoleShape::Role, rename) == number,
            "a non-role value changed");
    require(protocol_ir::renameRoles(flat, RoleShape::Roster, rename) == flat,
            "a roster declaration changed");
  });

  cases.run("application expansion charges every role use", [&] {
    // One copied role set larger than the expansion's whole index budget.
    SmallVector<Attribute> receivers(1000001, builder.getStringAttr("A"));
    OperationState moduleState(builder.getUnknownLoc(), "protocol.module");
    moduleState.addRegion()->push_back(new Block);
    std::unique_ptr<Operation, void (*)(Operation *)> module(
        Operation::create(moduleState), [](Operation *op) { op->destroy(); });
    OperationState functionState(builder.getUnknownLoc(), "protocol.func");
    functionState.addRegion()->push_back(new Block);
    auto *function = Operation::create(functionState);
    module->getRegion(0).front().push_back(function);
    OperationState viewState(builder.getUnknownLoc(),
                             "protocol.oracle_components");
    viewState.addAttribute("holder", builder.getStringAttr("A"));
    viewState.addAttribute("receivers", builder.getArrayAttr(receivers));
    function->getRegion(0).front().push_back(Operation::create(viewState));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyApplications(
                cast<protocol_ir::ProtocolModuleOp>(module.get()))),
            "an over-budget role set was admitted");
  });

  unsigned admitted = 0;
  for (auto name : context.getRegisteredOperations()) {
    Instance owned(builder, name);
    auto meaning = mathematical::classify(owned.op);
    if (!meaning)
      continue;
    ++admitted;
    auto contextBit = meaning->contexts & (~meaning->contexts + 1);
    auto formation = static_cast<mathematical::Context>(contextBit);
    cases.run(name.getStringRef() + " admits its ODS attributes only", [&] {
      fill(builder, owned.op, {});
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      // Without operands, results or regions, only attribute admission can
      // refuse an instance in an admitted context.
      require(succeeded(mathematical::verifyOperation(owned.op, formation)),
              "an ODS attribute was refused: " + diagnostic);
      diagnostic.clear();
      owned.op->setDiscardableAttr("unexpected", builder.getUnitAttr());
      require(failed(mathematical::verifyOperation(owned.op, formation)) &&
                  StringRef(diagnostic)
                      .contains("unsupported mathematical operation attribute"),
              "a discardable attribute was admitted: " + diagnostic);
    });
  }
  cases.run("formation admits the registered operations", [&] {
    require(admitted > 0, "no admitted mathematical operations");
  });
  cases.run("helper calls admit no call metadata", [&] {
    auto refused = [&](llvm::function_ref<void(func::CallOp)> annotate) {
      Instance call(builder, OperationName("func.call", &context));
      fill(builder, call.op, {});
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(succeeded(
                  mathematical::verifyOperation(call.op, mathematical::Helper)),
              "a plain helper call was refused");
      annotate(cast<func::CallOp>(call.op));
      return failed(
          mathematical::verifyOperation(call.op, mathematical::Helper));
    };
    auto empty = builder.getArrayAttr({builder.getDictionaryAttr({})});
    require(refused([&](func::CallOp call) { call.setNoInline(true); }),
            "an inlining directive was admitted");
    require(refused([&](func::CallOp call) { call.setResAttrsAttr(empty); }),
            "result dictionaries were admitted");
    require(
        refused([&](func::CallOp call) {
          call.setArgAttrsAttr(builder.getArrayAttr({builder.getDictionaryAttr(
              {builder.getNamedAttr("annotation", builder.getUnitAttr())})}));
        }),
        "an argument annotation was admitted");
  });

  llvm::outs() << operations << " Protocol operations, " << renamed
               << " role uses renamed, " << untouched
               << " other attributes unchanged; " << admitted
               << " admitted mathematical operations\n";
  return cases.result();
}
