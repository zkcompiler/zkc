#include "OracleCommonPlan.h"
#include "OracleEmissionAccounting.h"
#include "OracleNativeCommon.h"
#include "OracleOwnedRealization.h"
#include "OraclePublication.h"
#include "OracleQuerySchedule.h"
#include "RealizationEmission.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace pir = protocol_ir;
Expected<func::FuncOp> emitOracleLocalHelper(pir::ProtocolModuleOp unit,
                                             const OracleLocalRecipe &recipe,
                                             OracleNativeWork &work) {
  std::unique_ptr<mathematical::RealizationEmitter> bindings;
  return emitOracleLocalHelper(unit, recipe, work, bindings);
}
Expected<func::FuncOp> emitOracleLocalHelper(
    pir::ProtocolModuleOp unit, const OracleLocalRecipe &recipe,
    OracleNativeWork &work,
    std::unique_ptr<mathematical::RealizationEmitter> &bindings) {
  return oracleExpectedWithWork(work, [&]() -> Expected<func::FuncOp> {
    if (!work.charge(recipe.name.size() + recipe.inputs.size() +
                     recipe.outputs.size() + recipe.instructions.size() +
                     recipe.results.size()))
      return error("oracle-common-limit");
    OracleEmissionListener emission(work);
    OpBuilder builder(unit.getContext(), &emission);
    auto loc = unit.getLoc();
    builder.setInsertionPointToEnd(&unit.getBody().front());
    SmallVector<Type> inputs{runtime::ScopeType::get(unit.getContext())};
    append_range(inputs, recipe.inputs);
    auto helper = func::FuncOp::create(
        builder, loc, recipe.name,
        builder.getFunctionType(
            inputs, exec::OutcomeType::get(unit.getContext(), recipe.outputs)));
    helper.setPrivate();
    helper.setNoInline(true);
    helper->setAttr("runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr(recipe.name),
                                          builder.getArrayAttr({})}));
    reserveOracleEmission(work, 1 + helper.getNumArguments());
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    exec::ScopedExecutionBuilder control(builder, helper);
    constexpr StringLiteral bindingPrefix = "_oracle_common_binding_";
    // One emitter owns only its exact generated bindings across local helpers.
    // Construct it lazily after the other primitive setup. Its initial
    // inventory is charged once; every new spelling still uses a charged LIVE
    // lookup.
    if (!work.emission && !bindings) {
      if (!work.charge(bindingPrefix.size()))
        return error("oracle-common-limit");
      for (auto &declaration : unit.getBody().front()) {
        if (!work.charge(2) ||
            !work.chargeProduct(2, declaration.getAttrDictionary().size()))
          return error("oracle-common-limit");
        if (auto name = SymbolTable::getSymbolName(&declaration))
          if (!work.charge(name.getValue().size()))
            return error("oracle-common-limit");
      }
      bindings = std::make_unique<mathematical::RealizationEmitter>(
          unit, bindingPrefix);
    }
    SmallVector<Value> values(helper.getArguments().drop_front());
    for (auto [i, instruction] : enumerate(recipe.instructions)) {
      if (!work.charge(instruction.inputs.size() + instruction.types.size() +
                       instruction.parameters.size() +
                       instruction.outputs.size() +
                       instruction.binding.arguments.size()))
        return error("oracle-common-limit");
      SmallVector<Value> operands;
      for (unsigned input : instruction.inputs)
        operands.push_back(values[input]);
      auto &emitter = work.emission ? work.emission->get(unit) : *bindings;
      auto binding = emitter.bindingWithWork(
          builder, loc, instruction.binding,
          [&](uint64_t amount) { return work.charge(amount); });
      if (failed(binding))
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-body");
      auto outputs = control.invoke(
          "exec.apply", instruction.types, control.scoped(operands),
          {builder.getNamedAttr("binding", *binding),
           builder.getNamedAttr("parameters",
                                builder.getArrayAttr(instruction.parameters)),
           builder.getNamedAttr(
               "site", builder.getStringAttr("step_" + std::to_string(i)))});
      append_range(values, outputs);
    }
    SmallVector<Value> outputs;
    for (unsigned result : recipe.results)
      outputs.push_back(values[result]);
    control.returned(outputs);
    return helper;
  });
}
Expected<OracleCommonRealization>
emitOracleRealization(ModuleOp prepared,
                      const OracleRealizationPolicy &policy) {
  OracleNativeWork commonWork;
  return emitOracleRealizationWithWork(prepared, policy, commonWork);
}
Expected<OracleCommonRealization>
emitOracleRealizationWithWork(ModuleOp prepared,
                              const OracleRealizationPolicy &policy,
                              OracleNativeWork &commonWork) {
  auto owned = OracleOwnedRealization::create(prepared, policy, commonWork);
  if (!owned)
    return owned.takeError();
  return std::move(owned->actual);
}
Expected<OracleOwnedRealization>
OracleOwnedRealization::create(ModuleOp prepared,
                               const OracleRealizationPolicy &policy,
                               OracleNativeWork &commonWork) {

  return oracleExpectedWithWork(
      commonWork, [&]() -> Expected<OracleOwnedRealization> {
        auto sourcePreflight =
            OracleNativeSourcePreflight::read(prepared, commonWork);
        if (!sourcePreflight)
          return sourcePreflight.takeError();

        // This bounded traversal pays for the exact source clone before it is
        // allocated. Admission and entry discovery run once on that retained
        // immutable copy, which is the source used by every later consumer.
        OracleCommonRealization result;
        if (!sourcePreflight->reserveTraversal(prepared))
          return error("oracle-common-limit");
        result.original =
            OwningOpRef<ModuleOp>(cast<ModuleOp>(prepared->clone()));
        prepared = *result.original;
        // This second borrow names the retained clone, never the caller's
        // module.
        auto originalPreflight =
            OracleNativeSourcePreflight::read(prepared, commonWork);
        if (!originalPreflight)
          return originalPreflight.takeError();
        auto entries =
            oracleEntries(prepared, &commonWork, &*originalPreflight);
        if (!entries)
          return entries.takeError();
        auto sourceUnit =
            cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
        for (const auto &entry : *entries) {
          auto program = cast<pir::MathematicalOp>(
              SymbolTable::lookupSymbolIn(sourceUnit, entry));
          if (auto e = checkOracleNativeSource(prepared, program, &commonWork,
                                               &*originalPreflight))
            return std::move(e);
        }

        auto selections = resolveOracleRealizationSelectionWithWork(
            prepared, policy, commonWork, *originalPreflight);
        if (!selections)
          return selections.takeError();
        if (!originalPreflight->reserveTraversal(prepared))
          return error("oracle-common-limit");
        result.module =
            OwningOpRef<ModuleOp>(cast<ModuleOp>(prepared->clone()));
        auto unit =
            cast<pir::ProtocolModuleOp>(result.module->getBody()->front());

        OracleEmissionSession emissionSession(commonWork, unit);
        emissionSession.own();
        std::vector<OracleCommonPlan> plans;
        OracleVirtualFunctionWork work;
        work.common = &commonWork;
        work.scratch = *result.module;
        work.source = &*originalPreflight;
        std::unique_ptr<mathematical::RealizationEmitter> localBindings;
        // Build every helper while the complete admitted source inventory
        // remains intact. A sibling's original signature or shared virtual
        // declaration must not disappear while another entry's primitive is
        // being constructed.
        for (const auto &entry : *entries) {
          auto requirements = oracleRequirements(
              prepared, entry, *selections, &commonWork, &*originalPreflight);
          if (!requirements)
            return requirements.takeError();
          OracleCommonEntryRealization item;
          item.entry = entry;

          for (auto [ordinal, constructor] :
               enumerate(requirements->storage.constructors)) {
            OracleMerkleFunctions functions;
            if (!constructor.scheme.empty()) {
              const auto &choice = requirements->realizations[ordinal];
              auto emitted = emitOracleMerkleWithWork(
                  *result.module, constructor.kind, choice.scheme,
                  choice.grouping, choice.order, commonWork);
              if (!emitted)
                return emitted.takeError();
              functions = *emitted;
            }
            item.merkle.push_back(functions);
          }

          for (const auto &[role, kind, access] : requirements->controllers) {
            auto controller = emitOracleQueryController(
                *result.module, prepared, requirements->storage, role, kind,
                requirements->capacity, work, access);
            if (!controller)
              return controller.takeError();
            item.controllers.push_back(
                {role, kind, access, std::move(*controller)});
          }

          for (auto [ordinal, constructor] :
               enumerate(requirements->storage.constructors)) {
            std::vector<func::FuncOp> allocators;
            for (unsigned role = 0; role < constructor.roles.size(); ++role) {
              auto allocator = emitOracleAnchorAllocatorWithWork(
                  *result.module, requirements->storage, ordinal, role,
                  commonWork);
              if (!allocator)
                return allocator.takeError();
              allocators.push_back(*allocator);
            }
            item.allocators.push_back(std::move(allocators));
          }

          auto schedule = planOracleQueryScheduleWithWork(
              prepared, entry, *requirements, item.controllers, item.merkle,
              policy.authentication, commonWork, *originalPreflight);
          if (!schedule)
            return schedule.takeError();

          for (const auto &remote : schedule->remotes) {
            const auto &receiver = item.controllers[remote.receiver];
            auto demand =
                emitOracleQueryDemand(*result.module, requirements->storage,
                                      receiver.body, receiver.kind, work);
            if (!demand)
              return demand.takeError();
            auto response =
                emitOracleQueryResponse(*result.module, remote.exchange, work);
            if (!response)
              return response.takeError();
            OracleExchangeRecipe recipe;
            unsigned suffix = 0;
            do {
              recipe.name = "_oracle_query_open_" + std::to_string(suffix++);
            } while (lookupOracleEmissionSymbol(unit, recipe.name, commonWork));
            recipe.action = OracleExchangeAction::Open;
            recipe.exchange =
                std::make_shared<const OracleQueryExchange>(remote.exchange);
            recipe.inputs.push_back(remote.exchange.request);
            append_range(recipe.inputs, remote.exchange.holderStores);
            recipe.outputs.push_back(remote.exchange.response);
            auto open = emitOracleQueryExchangeWithWork(*result.module, recipe,
                                                        commonWork);
            if (!open)
              return open.takeError();
            auto packet = emitOracleQueryPacket(*result.module, remote.exchange,
                                                *response, *open, item.merkle,
                                                schedule->capacity, work);
            if (!packet)
              return packet.takeError();
            auto window = emitOracleQueryWindow(
                *result.module, receiver.body, *demand, remote.exchange,
                *response, schedule->capacity, work);
            if (!window)
              return window.takeError();
            item.remotes.push_back({remote.receiver, remote.holder,
                                    std::move(*demand), std::move(*response),
                                    *open, std::move(*packet),
                                    std::move(*window)});
          }

          for (const auto &batch : schedule->batches) {
            SmallVector<OracleQueryBatchRoot> roots;
            for (unsigned index : batch.remotes) {
              const auto &remote = item.remotes[index];
              roots.push_back({&item.controllers[remote.receiver].body,
                               &remote.demand, &remote.window});
            }
            auto emitted = emitOracleQueryBatch(*result.module, roots, work);
            if (!emitted)
              return emitted.takeError();
            item.batches.push_back({batch.remotes, std::move(*emitted)});
          }

          auto plan = materializeOracleCommon(
              prepared, entry, *requirements, item.controllers, item.allocators,
              item.merkle, policy.authentication, item.remotes, item.batches,
              &commonWork, &*originalPreflight);
          if (!plan)
            return plan.takeError();

          for (const auto &recipe : plan->locals) {
            auto helper =
                emitOracleLocalHelper(unit, recipe, commonWork, localBindings);
            if (!helper)
              return helper.takeError();
            item.locals.push_back(*helper);
          }
          item.inputShapes = std::move(plan->inputShapes);
          item.resultStores = std::move(plan->resultStores);
          item.resultReferences = std::move(plan->resultReferences);
          plans.push_back(std::move(*plan));
          result.entries.push_back(std::move(item));
        }
        emissionSession.finish();
        for (auto [entry, plan] : zip(*entries, plans)) {
          auto original = cast<pir::MathematicalOp>(
              SymbolTable::lookupSymbolIn(unit, entry));
          // setAttrs updates supplied inherent properties; an omitted optional
          // property on the cloned operation must be cleared explicitly.
          original.removeContractsAttr();
          original->setAttrs(plan.attributes);
          original.getBody().getBlocks().clear();
          original.getBody().push_back(plan.body.release());
        }
        for (auto declaration : llvm::make_early_inc_range(
                 unit.getBody().front().getOps<pir::OracleDefinitionOp>()))
          declaration.erase();
        // The actual candidate cannot be admitted in isolation: its generated
        // counts refer to two private stores. Finish the whole paired check
        // before returning it, using the emission allowance without resetting
        // it.

        auto candidatePreflight =
            OracleNativeSourcePreflight::read(result.module.get(), commonWork);
        if (!candidatePreflight)
          return candidatePreflight.takeError();
        std::vector<OracleCommonAnalysis> analyses;

        auto checked = checkOracleRealizationWithWork(
            prepared, result, policy, commonWork, &*originalPreflight,
            &*candidatePreflight, &analyses);

        if (!checked)
          return checked.takeError();
        if (!reserveOraclePolicy(policy, commonWork))
          return error("oracle-common-limit");
        return OracleOwnedRealization(
            std::move(result), std::move(*checked), std::move(analyses), policy,
            std::move(*selections), std::move(*originalPreflight),
            std::move(*candidatePreflight));
      });
}
} // namespace zkc::protocol
