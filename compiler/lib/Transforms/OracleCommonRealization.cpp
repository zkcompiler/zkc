#include "OracleCommonPlan.h"
#include "RealizationEmission.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
func::FuncOp local(pir::ProtocolModuleOp unit,
                   const OracleLocalRecipe &recipe) {
  OpBuilder builder(unit.getContext());
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
  builder.setInsertionPointToEnd(helper.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, helper);
  mathematical::RealizationEmitter bindings(unit, "_oracle_common_binding_");
  SmallVector<Value> values(helper.getArguments().drop_front());
  for (auto [i, instruction] : enumerate(recipe.instructions)) {
    SmallVector<Value> operands;
    for (unsigned input : instruction.inputs)
      operands.push_back(values[input]);
    auto binding = bindings.binding(builder, loc, instruction.binding);
    auto outputs = control.invoke(
        "exec.apply", instruction.types, control.scoped(operands),
        {builder.getNamedAttr("binding", binding),
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
}
func::FuncOp local(pir::ProtocolModuleOp unit,
                   const OraclePacketRecipe &recipe) {
  OpBuilder builder(unit.getContext());
  auto make = [&](StringRef name, TypeRange inputs, TypeRange outputs,
                  bool region) {
    builder.setInsertionPointToEnd(&unit.getBody().front());
    SmallVector<Type> formals{runtime::ScopeType::get(unit.getContext())};
    append_range(formals, inputs);
    auto helper = func::FuncOp::create(
        builder, unit.getLoc(), name,
        builder.getFunctionType(
            formals, exec::OutcomeType::get(unit.getContext(),
                                            SmallVector<Type>(outputs))));
    helper.setPrivate();
    helper.setNoInline(true);
    if (region)
      helper->setAttr("runtime.region", builder.getUnitAttr());
    else
      helper->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    return helper;
  };
  auto helper = make(recipe.name, recipe.inputs, recipe.outputs, false);
  exec::ScopedExecutionBuilder control(builder, helper);
  auto inputs = helper.getArguments().drop_front();
  if (recipe.pack) {
    control.returned(control.invoke(
        "exec.variant", recipe.outputs, control.scoped(inputs),
        {builder.getNamedAttr("alternative", builder.getStringAttr("Record")),
         builder.getNamedAttr("site", builder.getStringAttr("packet"))}));
  } else {
    control.returned(control.match(
        inputs.front(), {}, recipe.outputs, {"Record"}, "packet",
        [&](unsigned) {
          unsigned suffix = 0;
          std::string name;
          do {
            name = recipe.name + "_fields_" + std::to_string(suffix++);
          } while (SymbolTable::lookupSymbolIn(unit, name));
          auto fields = make(name, recipe.outputs, recipe.outputs, true);
          exec::ScopedExecutionBuilder region(builder, fields);
          region.complete(fields.getArguments().drop_front());
          return fields;
        }));
  }
  return helper;
}
void body(OpBuilder &builder, Location loc, const OracleCommonBlock &plan,
          Block &block) {
  llvm::DenseMap<unsigned, Value> environment;
  for (auto [i, type] : enumerate(plan.types))
    environment[plan.arguments[i]] = block.addArgument(type, loc);
  for (const auto &instruction : plan.instructions) {
    builder.setInsertionPointToEnd(&block);
    OperationState state(loc, instruction.name);
    state.addAttributes(instruction.attributes.getValue());
    state.addTypes(instruction.types);
    for (unsigned input : instruction.inputs)
      state.addOperands(environment.lookup(input));
    if (instruction.region)
      state.addRegion();
    auto *op = builder.create(state);
    if (instruction.region) {
      auto *nested = new Block;
      op->getRegion(0).push_back(nested);
      body(builder, loc, *instruction.region, *nested);
    }
    for (auto [id, value] : zip(instruction.outputs, op->getResults()))
      environment[id] = value;
  }
}
} // namespace
Expected<OracleCommonRealization>
emitOracleRealization(ModuleOp prepared,
                      const OracleRealizationPolicy &policy) {
  auto selections = resolveOracleRealizationSelection(prepared, policy);
  if (!selections)
    return selections.takeError();
  auto entries = oracleEntries(prepared);
  if (!entries)
    return entries.takeError();
  OracleCommonRealization result;
  result.module = OwningOpRef<ModuleOp>(cast<ModuleOp>(prepared->clone()));
  auto unit = cast<pir::ProtocolModuleOp>(result.module->getBody()->front());
  std::vector<OracleCommonPlan> plans;
  OracleVirtualFunctionWork work;
  // Build every helper while the complete admitted source inventory remains
  // intact. A sibling's original signature or shared virtual declaration must
  // not disappear while another entry's primitive is being constructed.
  for (const auto &entry : *entries) {
    auto requirements = oracleRequirements(prepared, entry, *selections);
    if (!requirements)
      return requirements.takeError();
    OracleCommonEntryRealization item;
    item.entry = entry;
    for (auto [ordinal, constructor] :
         enumerate(requirements->storage.constructors)) {
      OracleMerkleFunctions functions;
      if (!constructor.scheme.empty()) {
        const auto &choice = requirements->realizations[ordinal];
        auto emitted =
            emitOracleMerkle(*result.module, constructor.kind, choice.scheme,
                             choice.grouping, choice.order);
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
      item.controllers.push_back({role, kind, access, std::move(*controller)});
    }
    for (auto [ordinal, constructor] :
         enumerate(requirements->storage.constructors)) {
      std::vector<func::FuncOp> allocators;
      for (unsigned role = 0; role < constructor.roles.size(); ++role) {
        auto allocator = emitOracleAnchorAllocator(
            *result.module, requirements->storage, ordinal, role);
        if (!allocator)
          return allocator.takeError();
        allocators.push_back(*allocator);
      }
      item.allocators.push_back(std::move(allocators));
    }
    auto plan =
        planOracleCommon(prepared, entry, *requirements, item.controllers,
                         item.allocators, item.merkle, policy.authentication);
    if (!plan)
      return plan.takeError();
    for (const auto &recipe : plan->locals)
      item.locals.push_back(std::visit(
          [&](const auto &body) -> func::FuncOp {
            if constexpr (std::is_same_v<std::decay_t<decltype(body)>,
                                         OracleLocalRecipe> ||
                          std::is_same_v<std::decay_t<decltype(body)>,
                                         OraclePacketRecipe>)
              return local(unit, body);
            else
              return emitOracleQueryExchange(*result.module, body);
          },
          recipe));
    item.inputShapes = plan->inputShapes;
    item.resultStores = plan->resultStores;
    item.resultReferences = plan->resultReferences;
    plans.push_back(std::move(*plan));
    result.entries.push_back(std::move(item));
  }
  for (auto [entry, plan] : zip(*entries, plans)) {
    auto original =
        cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, entry));
    // setAttrs updates supplied inherent properties; an omitted optional
    // property on the cloned operation must be cleared explicitly.
    original.removeContractsAttr();
    original->setAttrs(plan.attributes);
    original.getBody().getBlocks().clear();
    auto *block = new Block;
    original.getBody().push_back(block);
    OpBuilder builder(prepared.getContext());
    body(builder, original.getLoc(), plan.body, *block);
  }
  for (auto declaration : llvm::make_early_inc_range(
           unit.getBody().front().getOps<pir::OracleDefinitionOp>()))
    declaration.erase();
  if (failed(zkc::admitStage(*result.module)))
    return error("oracle-common-formation");
  return result;
}
} // namespace zkc::protocol
