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
  auto record = encodeBoundType(storage.record, false);
  if (!record)
    return record.takeError();
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
  auto apply = [&](StringRef contract, ArrayRef<std::string> statics,
                   Type output, ValueRange inputs, StringRef site,
                   ArrayRef<std::string> parameters = {}) {
    auto binding = bindings.binding(
        builder, helper.getLoc(),
        {contract.str(),
         std::vector<std::string>(statics.begin(), statics.end()), ""});
    SmallVector<Attribute> attrs;
    for (const auto &parameter : parameters)
      attrs.push_back(builder.getStringAttr(parameter));
    return control
        .invoke(
            "exec.apply", output, control.scoped(inputs),
            {builder.getNamedAttr("binding", binding),
             builder.getNamedAttr("parameters", builder.getArrayAttr(attrs)),
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
                   {std::to_string(constructor)});
  auto length = apply("sequence.length", {record->spelling()}, index,
                      helper.getArgument(1), "length");
  auto value =
      pack(storage.record, helper.getArguments().drop_front(2), "record");
  auto next = apply("sequence.append", {record->spelling()}, storage.sequence,
                    {helper.getArgument(1), value}, "append");
  auto handle = pack(*reference, {tag, length}, "reference");
  control.returned({handle, next});
  return helper;
}
} // namespace zkc::protocol
