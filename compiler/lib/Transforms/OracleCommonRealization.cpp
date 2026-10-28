#include "OracleCommonPlan.h"
#include "RealizationEmission.h"
#include "mlir/IR/Verifier.h"
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
    SmallVector<StringRef> parameters;
    for (const auto &parameter : instruction.parameters)
      parameters.push_back(parameter);
    auto outputs = control.invoke(
        "exec.apply", instruction.types, control.scoped(operands),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters",
                              builder.getStrArrayAttr(parameters)),
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
Expected<OracleCommonRealization> emitIdealOracleRealization(ModuleOp prepared,
                                                             StringRef entry) {
  auto requirements = idealOracleRequirements(prepared, entry);
  if (!requirements)
    return requirements.takeError();
  OracleCommonRealization result;
  result.module = OwningOpRef<ModuleOp>(cast<ModuleOp>(prepared->clone()));
  auto unit = cast<pir::ProtocolModuleOp>(result.module->getBody()->front());
  auto original =
      cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, entry));
  // Keep the admitted source function while building helpers: helper readers
  // require a formed protocol unit. Replace it only once the common plan
  // exists.
  OracleVirtualFunctionWork work;
  for (const auto &[role, kind] : requirements->controllers) {
    auto controller = emitOracleQueryController(
        *result.module, prepared, requirements->storage, role, kind,
        requirements->capacity, work);
    if (!controller)
      return controller.takeError();
    result.controllers.push_back({role, kind, std::move(*controller)});
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
    result.allocators.push_back(std::move(allocators));
  }
  auto plan = planIdealOracleCommon(prepared, entry, *requirements,
                                    result.controllers, result.allocators);
  if (!plan)
    return plan.takeError();
  for (const auto &recipe : plan->locals)
    result.locals.push_back(local(unit, recipe));
  original->setAttrs(plan->attributes);
  original.getBody().getBlocks().clear();
  auto *block = new Block;
  original.getBody().push_back(block);
  OpBuilder builder(prepared.getContext());
  body(builder, original.getLoc(), plan->body, *block);
  for (auto declaration : llvm::make_early_inc_range(
           unit.getBody().front().getOps<pir::OracleDefinitionOp>()))
    declaration.erase();
  if (failed(verify(*result.module)))
    return error("oracle-common-formation");
  return result;
}
} // namespace zkc::protocol
