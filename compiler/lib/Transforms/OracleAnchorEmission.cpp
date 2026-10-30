#include "OracleAnchorStorage.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<func::FuncOp>
emitOracleAnchorAllocator(ModuleOp candidate, const OracleAnchorStorage &plan,
                          unsigned constructor, unsigned role) {
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()) ||
      constructor >= plan.constructors.size() ||
      role >= plan.constructors[constructor].roles.size())
    return error("oracle-storage-allocator");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("oracle-storage-allocator");
  const auto &layout = plan.constructors[constructor];
  const auto &storage = layout.roles[role];
  auto reference = oracleReferenceType(layout.kind);
  if (!reference)
    return reference.takeError();
  OpBuilder builder(candidate.getContext());
  builder.setInsertionPointToEnd(&unit.getBody().front());
  SmallVector<Type> arguments{runtime::ScopeType::get(candidate.getContext()),
                              storage.sequence};
  for (const auto &field : storage.fields)
    arguments.push_back(field.type);
  SmallVector<Type> outputs{*reference, storage.sequence};
  auto outcome = exec::OutcomeType::get(candidate.getContext(), outputs);
  std::string prefix = "_oracle_allocate_" + std::to_string(constructor) + "_" +
                       std::to_string(role);
  std::string name = prefix;
  for (unsigned n = 0; SymbolTable::lookupSymbolIn(unit, name); ++n)
    name = prefix + "_" + std::to_string(n);
  auto helper =
      func::FuncOp::create(builder, candidate.getLoc(), name,
                           builder.getFunctionType(arguments, outcome));
  helper.setPrivate();
  helper.setNoInline(true);
  helper->setAttr("runtime.origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(helper.addEntryBlock());
  mathematical::RealizationEmitter bindings(unit, "_oracle_storage_binding_");
  exec::ScopedExecutionBuilder control(builder, helper);
  auto apply = [&](StringRef contract, ArrayRef<Attribute> statics, Type output,
                   ValueRange inputs, StringRef site,
                   ArrayRef<Attribute> parameters = {}) {
    auto binding =
        bindings.binding(builder, helper.getLoc(),
                         {contract.str(), SmallVector<Attribute>(statics), ""});
    return control
        .invoke("exec.apply", output, control.scoped(inputs),
                {builder.getNamedAttr("binding", binding),
                 builder.getNamedAttr("parameters",
                                      builder.getArrayAttr(parameters)),
                 builder.getNamedAttr("site", builder.getStringAttr(site))})
        .front();
  };
  auto pack = [&](Type type, ValueRange inputs, StringRef site) {
    return control
        .invoke("exec.variant", type, control.scoped(inputs),
                {builder.getNamedAttr("alternative",
                                      builder.getStringAttr("Record")),
                 builder.getNamedAttr("site", builder.getStringAttr(site))})
        .front();
  };
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  auto tag = apply("index.constant", {}, index, {}, "constructor",
                   {builder.getIntegerAttr(index, constructor)});
  auto length = apply("sequence.length", {TypeAttr::get(storage.record)}, index,
                      helper.getArgument(1), "length");
  auto value =
      pack(storage.record, helper.getArguments().drop_front(2), "record");
  auto next = apply("sequence.append", {TypeAttr::get(storage.record)},
                    storage.sequence, {helper.getArgument(1), value}, "append");
  auto handle = pack(*reference, {tag, length}, "reference");
  control.returned({handle, next});
  return helper;
}
Expected<func::FuncOp> emitOracleAnchorLookup(ModuleOp candidate,
                                              const OracleAnchorStorage &plan,
                                              unsigned constructor,
                                              unsigned role) {
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()) ||
      constructor >= plan.constructors.size() ||
      role >= plan.constructors[constructor].roles.size())
    return error("oracle-storage-lookup");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("oracle-storage-lookup");
  const auto &layout = plan.constructors[constructor];
  const auto &storage = layout.roles[role];
  auto reference = oracleReferenceType(layout.kind);
  if (!reference)
    return reference.takeError();
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  SmallVector<Type> fields;
  for (const auto &field : storage.fields)
    fields.push_back(field.type);
  auto outcome = exec::OutcomeType::get(candidate.getContext(), fields);
  auto function = [&](StringRef suffix, TypeRange inputs, bool region) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string prefix = "_oracle_lookup_" + std::to_string(constructor) + "_" +
                         std::to_string(role) + "_" + suffix.str();
    std::string name = prefix;
    for (unsigned n = 0; SymbolTable::lookupSymbolIn(unit, name); ++n)
      name = prefix + "_" + std::to_string(n);
    SmallVector<Type> arguments{
        runtime::ScopeType::get(candidate.getContext())};
    append_range(arguments, inputs);
    auto result = func::FuncOp::create(
        builder, loc, name, builder.getFunctionType(arguments, outcome));
    result.setPrivate();
    result.setNoInline(true);
    if (region)
      result->setAttr("runtime.region", builder.getUnitAttr());
    else
      result->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    result.addEntryBlock();
    return result;
  };
  auto helper =
      function("record", TypeRange{*reference, storage.sequence}, false);
  mathematical::RealizationEmitter bindings(unit, "_oracle_lookup_binding_");
  builder.setInsertionPointToEnd(&helper.getBody().front());
  exec::ScopedExecutionBuilder control(builder, helper);
  auto loaded = control.match(
      helper.getArgument(1), helper.getArgument(2), fields, {"Record"},
      "reference", [&](unsigned) {
        auto selected = function(
            "reference", TypeRange{index, index, storage.sequence}, true);
        builder.setInsertionPointToEnd(&selected.getBody().front());
        exec::ScopedExecutionBuilder body(builder, selected);
        auto apply = [&](StringRef contract, ArrayRef<Attribute> arguments,
                         TypeRange outputs, ValueRange inputs, StringRef site,
                         ArrayRef<Attribute> parameters = {}) {
          auto binding = bindings.binding(
              builder, loc,
              {contract.str(), SmallVector<Attribute>(arguments), ""});
          return body.invoke(
              "exec.apply", outputs, body.scoped(inputs),
              {builder.getNamedAttr("binding", binding),
               builder.getNamedAttr("parameters",
                                    builder.getArrayAttr(parameters)),
               builder.getNamedAttr("site", builder.getStringAttr(site))});
        };
        auto expected = apply("index.constant", {}, index, {}, "constructor",
                              {builder.getIntegerAttr(index, constructor)})
                            .front();
        auto matches = apply("index.equal", {}, builder.getI1Type(),
                             {selected.getArgument(1), expected}, "belongs_to")
                           .front();
        apply("control.require", {}, {}, matches, "admit_reference");
        auto value =
            apply("sequence.at", {TypeAttr::get(storage.record)},
                  storage.record,
                  {selected.getArgument(3), selected.getArgument(2)}, "lookup")
                .front();
        auto values =
            body.match(value, {}, fields, {"Record"}, "record", [&](unsigned) {
              auto unpacked = function("fields", fields, true);
              builder.setInsertionPointToEnd(&unpacked.getBody().front());
              exec::ScopedExecutionBuilder unpack(builder, unpacked);
              unpack.complete(unpacked.getArguments().drop_front());
              return unpacked;
            });
        body.complete(values);
        return selected;
      });
  control.returned(loaded);
  return helper;
}
} // namespace zkc::protocol
