#include "OracleTableRead.h"
#include "CollectionRealization.h"
#include "OracleEmissionAccounting.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<func::FuncOp> emitOracleTableRead(ModuleOp candidate,
                                           protocol_ir::OracleKindAttr kind) {
  OracleNativeWork common;
  return emitOracleTableReadWithWork(candidate, kind, common);
}
Expected<func::FuncOp>
emitOracleTableReadWithWork(ModuleOp candidate,
                            protocol_ir::OracleKindAttr kind,
                            OracleNativeWork &common) {
  return oracleExpectedWithWork(common, [&]() -> Expected<func::FuncOp> {
    if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()) ||
        !kind || kind.getContext() != candidate.getContext() ||
        kind.getIdentity() != "table" ||
        failed(protocol_ir::OracleKindAttr::verify(
            [&]() { return emitError(candidate.getLoc()); }, kind.getIdentity(),
            kind.getArguments())))
      return error("oracle-table-read");
    auto unit =
        dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
    if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
      return error("oracle-table-read");
    auto collection = mathematical::collectionRealization(kind.getDataType());
    if (!collection || collection->rank != 1 || !collection->get ||
        collection->element != kind.getAnswerType())
      return error("oracle-table-read");
    auto *session = common.emission;
    bool owned = session && session->ownsCandidate(unit);
    if (owned)
      if (auto function = session->findTableRead(kind))
        return function;
    OracleEmissionListener emission(common);
    OpBuilder builder(candidate.getContext(), &emission);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto index =
        IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
    SmallVector<Type> inputs{runtime::ScopeType::get(candidate.getContext()),
                             kind.getDataType(), index, index};
    auto outcome =
        exec::OutcomeType::get(candidate.getContext(), kind.getAnswerType());
    std::string name = "_oracle_table_read";
    for (unsigned i = 0; lookupOracleEmissionSymbol(unit, name, common); ++i)
      name = "_oracle_table_read_" + std::to_string(i);
    auto helper =
        func::FuncOp::create(builder, candidate.getLoc(), name,
                             builder.getFunctionType(inputs, outcome));
    helper.setPrivate();
    helper.setNoInline(true);
    helper->setAttr("runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr(name),
                                          builder.getArrayAttr({})}));
    reserveOracleEmission(common, 1 + helper.getNumArguments());
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    OracleBindingEmitter bindings(unit, "_oracle_read_binding_", common);
    exec::ScopedExecutionBuilder control(builder, helper);
    auto call = [&](StringRef contract, ArrayRef<Attribute> arguments,
                    TypeRange outputs, ValueRange inputs, StringRef site) {
      auto binding = bindings.binding(
          builder, helper.getLoc(),
          {contract.str(), SmallVector<Attribute>(arguments), ""});
      return control.invoke(
          "exec.apply", outputs, control.scoped(inputs),
          {builder.getNamedAttr("binding", binding),
           builder.getNamedAttr("parameters", builder.getArrayAttr({})),
           builder.getNamedAttr("site", builder.getStringAttr(site))});
    };
    auto valid = call("index.less", {}, builder.getI1Type(),
                      {helper.getArgument(3), helper.getArgument(2)}, "domain")
                     .front();
    call("control.require", {}, {}, valid, "admit");
    auto value = call(collection->get->contract, collection->get->arguments,
                      kind.getAnswerType(),
                      {helper.getArgument(1), helper.getArgument(3)}, "read")
                     .front();
    control.returned(value);
    if (owned)
      session->rememberTableRead(kind, helper);
    return helper;
  });
}
} // namespace zkc::protocol
