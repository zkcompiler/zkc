#include "PhysicalPlan.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Selection.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
#include <set>

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
std::string structure(ModuleOp module) {
  std::string result;
  raw_string_ostream out(result);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return result;
}
SmallVector<const void *> identities(ModuleOp module) {
  SmallVector<const void *> result;
  module->walk<WalkOrder::PreOrder>([&](Operation *op) {
    result.push_back(op);
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        result.push_back(&block);
        for (auto arg : block.getArguments())
          result.push_back(arg.getAsOpaquePointer());
      }
    for (auto value : op->getResults())
      result.push_back(value.getAsOpaquePointer());
  });
  return result;
}
} // namespace
struct InputSnapshot {
  ModuleOp subject;
  std::string contents;
  SmallVector<const void *> addresses;
  source::Assignments selections;
  bool linearContractions;
  Error check(ModuleOp module) const {
    // Compare only fresh live IR against opaque saved addresses. Never walk or
    // dereference a saved operation/value, including after erasure/replacement.
    if (module != subject || identities(module) != addresses ||
        structure(module) != contents)
      return error("binding-stale-selection");
    return Error::success();
  }
};
SmallVector<Operation *> physicalPlanOperations(ModuleOp module) {
  SmallVector<Operation *> result;
  module->walk<WalkOrder::PreOrder>(
      [&](Operation *op) { result.push_back(op); });
  return result;
}
Error CheckedPhysicalPlan::checkInput(ModuleOp module) const {
  return plan.input->check(module);
}
namespace {
void locate(Location *failureLocation, Operation *op) {
  if (failureLocation)
    *failureLocation = op->getLoc();
}
Expected<Type> defaultPort(Type type) {
  auto logical = encodeBoundType(type, false);
  if (!logical)
    return logical.takeError();
  auto physical = defaultRepresentation(*logical);
  if (!physical)
    return physical.takeError();
  auto decoded = decodeBoundType(type.getContext(), *physical);
  if (!decoded)
    return createStringError(
        "physical conversion requires loaded zkc dialects");
  return decoded;
}
Expected<SmallVector<Type>> defaultPorts(TypeRange types) {
  SmallVector<Type> result;
  for (auto type : types) {
    auto port = defaultPort(type);
    if (!port)
      return port.takeError();
    result.push_back(*port);
  }
  return result;
}
Expected<SmallVector<Type>> decodePorts(MLIRContext *context,
                                        ArrayRef<BoundType> types) {
  SmallVector<Type> result;
  for (const auto &type : types) {
    auto decoded = decodeBoundType(context, type);
    if (!decoded)
      return createStringError(
          "physical conversion requires loaded zkc dialects");
    result.push_back(decoded);
  }
  return result;
}
bool sameApplication(const BindingApplication &a, const BindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments &&
         a.implementation == b.implementation;
}
bool sameLogical(const BindingApplication &a, const BindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments;
}
bool interfaceOperation(Operation *op) {
  return isa<func::ReturnOp, HaltOp, VariantInjectOp, LocalMatchOp, LocalIfOp,
             LocalForOp, LocalYieldOp>(op);
}
using Indices = llvm::DenseMap<Operation *, OperationIndex>;
Indices indexOperations(ArrayRef<Operation *> operations) {
  Indices indices;
  for (auto [index, op] : enumerate(operations))
    indices[op] = index;
  return indices;
}
// Resolve one actual SSA definition through its own recorded ports. This is
// deliberately not a Type -> Type conversion map.
Type valuePort(Value value, const PhysicalPlan &plan, const Indices &indices) {
  if (auto result = dyn_cast<OpResult>(value))
    return plan.operations[indices.lookup(result.getOwner())]
        .outputs[result.getResultNumber()];
  auto arg = cast<BlockArgument>(value);
  auto *owner = arg.getOwner()->getParentOp();
  size_t blockIndex = 0;
  for (auto &region : owner->getRegions())
    for (auto &block : region) {
      if (&block == arg.getOwner())
        return plan.operations[indices.lookup(owner)]
            .blockArguments[blockIndex][arg.getArgNumber()];
      ++blockIndex;
    }
  llvm_unreachable("block argument belongs to its parent");
}
std::string fresh(std::set<std::string> &used, StringRef prefix,
                  unsigned &next) {
  std::string result;
  do {
    result = prefix.str() + std::to_string(next++);
  } while (!used.insert(result).second);
  return result;
}
Expected<ImplementationChoice> choose(const BindingApplication &application,
                                      std::optional<StringRef> request,
                                      const CandidateCatalog &catalog) {
  if (request || !application.implementation.empty())
    return selectImplementation(application, request);
  auto candidates = catalog.implementations(application);
  if (!candidates)
    return candidates.takeError();
  for (const auto &implementation : *candidates) {
    auto selected = application;
    selected.implementation = implementation;
    auto installed = resolveBinding(selected, true);
    if (!installed) {
      consumeError(installed.takeError());
      continue;
    }
    return ImplementationChoice{std::move(selected), false};
  }
  return error("binding-implementation");
}
Expected<BindingApplication> chooseConversion(Type from, Type to,
                                              const CandidateCatalog &catalog) {
  auto source = encodeBoundType(from, true);
  if (!source)
    return source.takeError();
  auto target = encodeBoundType(to, true);
  if (!target)
    return target.takeError();
  for (auto candidate : catalog.conversions(*source, *target)) {
    if (auto e = checkDirectConversion(candidate, *source, *target)) {
      consumeError(std::move(e));
      continue;
    }
    return candidate;
  }
  return error("binding-no-conversion");
}

class Proposer {
  ModuleOp module;
  ProtocolModuleOp root;
  const CandidateCatalog &catalog;
  SmallVector<Operation *> operations;
  Indices indices;
  Location *failureLocation;
  SmallVector<BindingDecision> originals;
  std::map<std::string, BindingIndex> names;
  SmallVector<LinearContractionGroup> eligible;
  std::set<std::string> symbols;

  Error ports(PhysicalPlan &plan) {
    // Record every definition first; nested interface uses can refer to their
    // parent's outputs. Every operation has exactly one preorder entry.
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      for (auto &region : op->getRegions())
        for (auto &block : region) {
          auto ports = defaultPorts(block.getArgumentTypes());
          if (!ports)
            return ports.takeError();
          decision.blockArguments.push_back(std::move(*ports));
        }
      if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
        auto functionType = cast<FunctionType>(signature.getValue());
        auto inputs = defaultPorts(functionType.getInputs());
        if (!inputs)
          return inputs.takeError();
        auto outputs = defaultPorts(functionType.getResults());
        if (!outputs)
          return outputs.takeError();
        decision.functionType =
            FunctionType::get(module.getContext(), *inputs, *outputs);
      }
      if (decision.binding) {
        auto signature = resolveBinding(
            plan.bindings[*decision.binding].binding.application, true);
        if (!signature)
          return signature.takeError();
        auto inputs = decodePorts(module.getContext(), signature->inputs);
        if (!inputs)
          return inputs.takeError();
        auto outputs = decodePorts(module.getContext(), signature->outputs);
        if (!outputs)
          return outputs.takeError();
        decision.inputs = std::move(*inputs);
        decision.outputs = std::move(*outputs);
      } else {
        auto outputs = defaultPorts(op->getResultTypes());
        if (!outputs)
          return outputs.takeError();
        decision.outputs = std::move(*outputs);
      }
    }
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      if (decision.binding)
        continue;
      if (isa<func::ReturnOp>(op)) {
        auto function = op->getParentOfType<func::FuncOp>();
        append_range(decision.inputs, plan.operations[indices.lookup(function)]
                                          .functionType.getResults());
      } else if (isa<LocalIfOp>(op)) {
        auto condition = defaultPort(IntegerType::get(module.getContext(), 1));
        if (!condition)
          return condition.takeError();
        decision.inputs.push_back(*condition);
        append_range(decision.inputs, decision.blockArguments[0]);
      } else if (isa<LocalForOp>(op)) {
        decision.inputs.push_back(decision.blockArguments[0][0]);
        append_range(decision.inputs, decision.blockArguments[0]);
      } else if (isa<LocalYieldOp>(op)) {
        auto *parent = op->getParentOp();
        append_range(decision.inputs,
                     plan.operations[indices.lookup(parent)].outputs);
        if (isa<LocalForOp>(parent))
          append_range(
              decision.inputs,
              ArrayRef(
                  plan.operations[indices.lookup(parent)].blockArguments[0])
                  .drop_front(1 + parent->getNumResults()));
      } else {
        auto inputs = defaultPorts(op->getOperandTypes());
        if (!inputs)
          return inputs.takeError();
        decision.inputs = std::move(*inputs);
      }
      if (decision.inputs.size() != op->getNumOperands())
        return error("binding-operation-signature");
    }
    return Error::success();
  }

public:
  Proposer(ModuleOp module, const CandidateCatalog &catalog,
           Location *failureLocation)
      : module(module),
        root(cast<ProtocolModuleOp>(&module.getBody()->front())),
        catalog(catalog), operations(physicalPlanOperations(module)),
        indices(indexOperations(operations)), failureLocation(failureLocation) {
  }

  Error initialize(ArrayRef<std::pair<std::string, std::string>> requests,
                   bool contractions) {
    std::map<std::string, std::string> choices;
    for (const auto &[key, implementation] : requests)
      if (!choices.emplace(key, implementation).second)
        return error("binding-duplicate-selection");
    for (auto &op : root.getBody().front()) {
      locate(failureLocation, &op);
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        symbols.insert(name.getValue().str());
      if (!isa<OperationBindingOp>(op))
        continue;
      auto binding = readBinding(&op);
      if (!binding)
        return binding.takeError();
      auto request = choices.find(binding->name);
      auto selected = choose(binding->application,
                             request == choices.end()
                                 ? std::nullopt
                                 : std::optional<StringRef>(request->second),
                             catalog);
      if (!selected)
        return selected.takeError();
      binding->application = std::move(selected->application);
      names.emplace(binding->name, originals.size());
      originals.push_back({std::move(*binding), BindingPurpose::Original,
                           indices.lookup(&op), selected->fixed,
                           indices.lookup(&op)});
      if (request != choices.end())
        choices.erase(request);
    }
    locate(failureLocation, root);
    if (!choices.empty())
      return error("binding-unknown-selection");
    if (contractions) {
      LinearContractionStats ignored;
      for (auto function : root.getBody().front().getOps<func::FuncOp>())
        append_range(eligible, findLinearContractions(function, ignored));
    }
    return Error::success();
  }

  Error populate(PhysicalPlan &plan, size_t groupLimit) {
    plan.bindings = originals;
    plan.operations.clear();
    plan.contractions.clear();
    auto used = symbols;
    unsigned next = 0;
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      OperationDecision decision;
      decision.operation = index;
      if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding")) {
        auto found = names.find(ref.getValue().str());
        if (found == names.end())
          return error("binding-reference");
        decision.binding = found->second;
      } else if (op->getParentOfType<func::FuncOp>() && !interfaceOperation(op))
        return error("binding-reference");
      plan.operations.push_back(std::move(decision));
    }
    for (const auto &group : eligible) {
      if (plan.contractions.size() >= groupLimit)
        break;
      SmallVector<std::pair<OperationIndex, BindingDecision>> pending;
      auto prepare = [&](Operation *op) {
        auto index = indices.lookup(op);
        auto binding = plan.operations[index].binding;
        if (!binding || plan.bindings[*binding].fixed)
          return false;
        auto clone = plan.bindings[*binding];
        bool available = false;
        for (const auto &implementation :
             catalog.diagonalImplementations(clone.binding.application)) {
          auto candidate = clone.binding.application;
          candidate.implementation = implementation;
          auto installed = resolveDiagonalImplementation(candidate);
          if (!installed) {
            consumeError(installed.takeError());
            continue;
          }
          clone.binding.application = std::move(candidate);
          available = true;
          break;
        }
        if (!available)
          return false;
        clone.purpose = BindingPurpose::Contraction;
        clone.declaration.reset();
        clone.location = index;
        pending.emplace_back(index, std::move(clone));
        return true;
      };
      if (plan.bindings.size() + 1 + group.uses.size() > 4096 ||
          !prepare(group.producer))
        continue;
      bool available = true;
      for (const auto &use : group.uses)
        if (!prepare(use.consumer)) {
          available = false;
          break;
        }
      if (!available)
        continue;
      ContractionDecision selected{indices.lookup(group.producer), {}};
      for (const auto &use : group.uses)
        selected.consumers.push_back(indices.lookup(use.consumer));
      for (auto &[index, binding] : pending) {
        binding.binding.name = fresh(used, "diagonal_", next);
        plan.operations[index].binding = plan.bindings.size();
        plan.bindings.push_back(std::move(binding));
      }
      plan.contractions.push_back(std::move(selected));
    }
    if (auto e = ports(plan))
      return e;
    std::map<Operation *, std::set<std::string>> sites;
    for (auto *op : operations)
      if (auto function = op->getParentOfType<func::FuncOp>())
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          sites[function].insert(site.getValue().str());
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      for (auto [operand, value] : enumerate(op->getOperands())) {
        Type from = valuePort(value, plan, indices);
        Type to = decision.inputs[operand];
        if (from == to)
          continue;
        auto application = chooseConversion(from, to, catalog);
        if (!application)
          return application.takeError();
        BindingIndex binding = plan.bindings.size();
        // Reuse declarations, never conversion instructions or their results.
        for (auto [i, candidate] : enumerate(plan.bindings))
          if (candidate.purpose == BindingPurpose::Conversion &&
              sameApplication(candidate.binding.application, *application))
            binding = i;
        if (binding == plan.bindings.size()) {
          source::OperationBinding declaration{
              {}, fresh(used, "layout_", next), std::move(*application)};
          plan.bindings.push_back({std::move(declaration),
                                   BindingPurpose::Conversion,
                                   {},
                                   false,
                                   index});
        }
        auto function = op->getParentOfType<func::FuncOp>();
        if (!function)
          return error("binding-no-conversion");
        decision.conversions.push_back(
            {unsigned(operand), binding, from, to,
             fresh(sites[function], "layout_", next)});
      }
    }
    return Error::success();
  }
};
} // namespace

Expected<PhysicalPlan>
proposePhysical(ModuleOp module, const CandidateCatalog &catalog,
                ArrayRef<std::pair<std::string, std::string>> selections,
                bool linearContractions, Location *failureLocation) {
  locate(failureLocation, module);
  if (failed(verify(module)) || module.getBody()->empty() ||
      !isa<ProtocolModuleOp>(module.getBody()->front()))
    return error("binding-operation");
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  if (root.getStage() != "logical")
    return error("interactive-physical-stage");
  PhysicalPlan plan;
  plan.input = std::make_shared<InputSnapshot>(
      InputSnapshot{module, structure(module), identities(module),
                    source::Assignments(selections.begin(), selections.end()),
                    linearContractions});
  Proposer proposer(module, catalog, failureLocation);
  if (auto e = proposer.initialize(selections, linearContractions))
    return e;
  size_t groupLimit = 4096;
  for (;;) {
    if (auto e = proposer.populate(plan, groupLimit))
      return e;
    if (plan.bindings.size() <= 4096)
      return plan;
    // Reserve space for real conversions as well as clones. Drop the last
    // selected atomic group deterministically, retaining dense execution.
    locate(failureLocation, root);
    if (plan.contractions.empty())
      return error("binding-declaration-limit");
    groupLimit = plan.contractions.size() - 1;
  }
}

namespace {
Error checkFixed(const BindingApplication &source,
                 const BindingApplication &selected,
                 std::optional<StringRef> request, bool recordedFixed) {
  if (!sameLogical(source, selected))
    return error("binding-operation");
  const bool fixed = request.has_value() || !source.implementation.empty();
  if (fixed != recordedFixed ||
      (!source.implementation.empty() &&
       selected.implementation != source.implementation) ||
      (request && selected.implementation != *request))
    return error("binding-selection-conflict");
  return Error::success();
}
Error checkDefaultPorts(TypeRange logical, ArrayRef<Type> recorded) {
  if (logical.size() != recorded.size())
    return error("binding-operation-signature");
  for (auto [source, selected] : zip(logical, recorded)) {
    auto expected = defaultPort(source);
    if (!expected)
      return expected.takeError();
    if (*expected != selected)
      return error("binding-operation-signature");
  }
  return Error::success();
}
Error checkInstalledPorts(TypeRange recorded, ArrayRef<BoundType> installed) {
  if (recorded.size() != installed.size())
    return error("binding-operation-signature");
  for (auto [type, expected] : zip(recorded, installed)) {
    if (!type)
      return error("binding-operation-signature");
    auto actual = encodeBoundType(type, true);
    if (!actual)
      return actual.takeError();
    if (!(*actual == expected))
      return error("binding-operation-signature");
  }
  return Error::success();
}

// This traversal checks all *actual* SSA operand uses. It neither calls the
// opportunity finder nor enumerates uses supplied by a proposed group.
Expected<SmallVector<OperationIndex>> checkAllUses(Operation *op,
                                                   const PhysicalPlan &plan,
                                                   const Indices &indices,
                                                   Location *failureLocation) {
  locate(failureLocation, op);
  auto function = op->getParentOfType<func::FuncOp>();
  auto producer = dyn_cast<DiagonalProducerInterface>(op);
  if (!function || function.isDeclaration() ||
      !hasSingleElement(function.getBody()) ||
      op->getParentOp() != function.getOperation() || !producer)
    return error("binding-contraction");
  auto production = producer.getDiagonalProducerRoles();
  if (!production || production->result >= op->getNumResults() ||
      production->factorsOperand >= op->getNumOperands() ||
      production->valuesOperand >= op->getNumOperands() ||
      production->factorsOperand == production->valuesOperand)
    return error("binding-contraction");
  const auto &decision = plan.operations[indices.lookup(op)];
  if (!decision.binding)
    return error("binding-contraction");
  const auto &application =
      plan.bindings[*decision.binding].binding.application;
  // Admission is independent of the catalog's candidate-name derivation.
  // Resolve the full selected contract instance, then inspect its role ports.
  auto installed = resolveBinding(application, true);
  if (!installed)
    return installed.takeError();
  const auto *facts = operationContracts(application.contract);
  if (!facts || !facts->diagonalMap ||
      facts->diagonalMap->factorsOperand != production->factorsOperand ||
      facts->diagonalMap->valuesOperand != production->valuesOperand ||
      facts->diagonalMap->result != production->result)
    return error("binding-contraction");
  // Complete recorded ports were checked before this traversal. Requiring
  // the exact installed role and view port also excludes a dense contract
  // masquerading as a contraction group with internally consistent ports.
  const auto &view = installed->outputs[production->result];
  if (!isDiagonalRepresentation(view.representation))
    return error("binding-contraction");
  auto result = op->getResult(production->result);
  if (result.use_empty() ||
      op->getOperand(production->valuesOperand).getType() != result.getType())
    return error("binding-contraction");
  SmallVector<OperationIndex> consumers;
  for (OpOperand &use : result.getUses()) {
    auto *user = use.getOwner();
    locate(failureLocation, user);
    auto consumer = dyn_cast<DiagonalContractionInterface>(user);
    if (!consumer || user->getBlock() != op->getBlock() ||
        user->getParentOp() != function.getOperation() ||
        !op->isBeforeInBlock(user))
      return error("binding-contraction");
    auto contraction = consumer.getDiagonalContractionRoles();
    if (!contraction || use.getOperandNumber() != contraction->valuesOperand ||
        contraction->coefficientsOperand >= user->getNumOperands() ||
        contraction->coefficientsOperand == contraction->valuesOperand ||
        op->getOperand(production->factorsOperand).getType() !=
            user->getOperand(contraction->coefficientsOperand).getType())
      return error("binding-contraction");
    auto index = indices.lookup(user);
    const auto &selected = plan.operations[index];
    if (!selected.binding || selected.inputs[use.getOperandNumber()] !=
                                 decision.outputs[production->result])
      return error("binding-contraction");
    const auto &consumerApplication =
        plan.bindings[*selected.binding].binding.application;
    auto consumerInstalled = resolveBinding(consumerApplication, true);
    if (!consumerInstalled)
      return consumerInstalled.takeError();
    const auto *consumerFacts =
        operationContracts(consumerApplication.contract);
    if (!consumerFacts || !consumerFacts->linearContraction ||
        consumerFacts->linearContraction->coefficientsOperand !=
            contraction->coefficientsOperand ||
        consumerFacts->linearContraction->valuesOperand !=
            contraction->valuesOperand ||
        !(consumerInstalled->inputs[contraction->valuesOperand] == view))
      return error("binding-contraction");
    consumers.push_back(index);
  }
  llvm::sort(consumers);
  return consumers;
}
} // namespace

Expected<CheckedPhysicalPlan> validatePhysical(ModuleOp module,
                                               const PhysicalPlan &plan,
                                               const CandidateCatalog &catalog,
                                               Location *failureLocation) {
  locate(failureLocation, module);
  if (!plan.input)
    return error("binding-stale-selection");
  if (auto e = plan.input->check(module))
    return e;
  // Verify the unchanged logical subject, not a mutated physical candidate.
  if (failed(verify(module)))
    return error("binding-operation");
  auto root = cast<ProtocolModuleOp>(&module.getBody()->front());
  auto operations = physicalPlanOperations(module);
  auto indices = indexOperations(operations);
  if (plan.operations.size() != operations.size())
    return error("binding-plan-coverage");
  if (plan.bindings.size() > 4096)
    return error("binding-declaration-limit");
  for (auto [i, decision] : enumerate(plan.operations))
    if (decision.operation != i ||
        (decision.binding && *decision.binding >= plan.bindings.size()))
      return error("binding-plan-coverage");

  std::map<std::string, std::string> requests;
  for (const auto &[key, implementation] : plan.input->selections)
    if (!requests.emplace(key, implementation).second)
      return error("binding-duplicate-selection");
  std::set<std::string> symbols;
  for (auto &op : root.getBody().front())
    if (!isa<OperationBindingOp>(op))
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        symbols.insert(name.getValue().str());
  std::map<std::string, BindingIndex> originals;
  size_t declarationIndex = 0;
  for (auto declaration : root.getBody().front().getOps<OperationBindingOp>()) {
    locate(failureLocation, declaration);
    if (declarationIndex >= plan.bindings.size())
      return error("binding-plan-coverage");
    const auto &decision = plan.bindings[declarationIndex];
    auto source = readBinding(declaration);
    if (!source)
      return source.takeError();
    if (decision.purpose != BindingPurpose::Original ||
        decision.declaration != indices.lookup(declaration) ||
        decision.binding.name != source->name ||
        decision.location != indices.lookup(declaration))
      return error("binding-plan-coverage");
    auto request = requests.find(source->name);
    if (auto e = checkFixed(source->application, decision.binding.application,
                            request == requests.end()
                                ? std::nullopt
                                : std::optional<StringRef>(request->second),
                            decision.fixed))
      return e;
    if (!decision.fixed) {
      auto candidates = catalog.implementations(source->application);
      if (!candidates)
        return candidates.takeError();
      if (!is_contained(*candidates,
                        decision.binding.application.implementation))
        return error("binding-implementation");
    }
    if (request != requests.end())
      requests.erase(request);
    originals.emplace(source->name, declarationIndex++);
  }
  if (!requests.empty())
    return error("binding-unknown-selection");
  for (auto [i, decision] : enumerate(plan.bindings)) {
    locate(failureLocation, root);
    if (decision.location >= operations.size())
      return error("binding-plan-coverage");
    locate(failureLocation, operations[decision.location]);
    if (i >= declarationIndex &&
        (decision.purpose == BindingPurpose::Original || decision.declaration ||
         decision.fixed))
      return error("binding-plan-coverage");
    if (!symbols.insert(decision.binding.name).second)
      return error("binding-plan-coverage");
    if (auto e = checkBindingDeclaration(decision.binding.name,
                                         decision.binding.application, true))
      return e;
  }

  // Check complete definition and use signatures before consulting any ports
  // by SSA index. This makes malformed proposal vectors ordinary refusals.
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.inputs.size() != op->getNumOperands() ||
        decision.outputs.size() != op->getNumResults())
      return error("binding-operation-signature");
    size_t blockIndex = 0;
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        if (blockIndex >= decision.blockArguments.size())
          return error("binding-operation-signature");
        if (auto e = checkDefaultPorts(block.getArgumentTypes(),
                                       decision.blockArguments[blockIndex++]))
          return e;
      }
    if (blockIndex != decision.blockArguments.size())
      return error("binding-operation-signature");
    if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
      auto functionType = cast<FunctionType>(signature.getValue());
      if (!decision.functionType)
        return error("binding-operation-signature");
      if (auto e = checkDefaultPorts(functionType.getInputs(),
                                     decision.functionType.getInputs()))
        return e;
      if (auto e = checkDefaultPorts(functionType.getResults(),
                                     decision.functionType.getResults()))
        return e;
    } else if (decision.functionType)
      return error("binding-operation-signature");

    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    if (ref) {
      if (!decision.binding)
        return error("binding-plan-coverage");
      auto original = originals.find(ref.getValue().str());
      if (original == originals.end())
        return error("binding-reference");
      const auto &binding = plan.bindings[*decision.binding];
      const auto &base = plan.bindings[original->second];
      // Exact contract AND arguments, not merely physical signature equality.
      // The source verifier also checks its ODS association and parameters.
      if (failed(verifyBoundOperation(op, false)))
        return error("binding-operation");
      if (!sameLogical(binding.binding.application, base.binding.application))
        return error("binding-operation");
      if (*decision.binding != original->second &&
          (binding.purpose != BindingPurpose::Contraction || base.fixed))
        return error(base.fixed ? "binding-selection-conflict"
                                : "binding-plan-coverage");
      if (binding.purpose == BindingPurpose::Contraction &&
          !is_contained(
              catalog.diagonalImplementations(base.binding.application),
              binding.binding.application.implementation))
        return error("binding-implementation");
      auto installed = resolveBinding(binding.binding.application, true);
      if (!installed)
        return installed.takeError();
      if (auto e = checkInstalledPorts(decision.inputs, installed->inputs))
        return e;
      if (auto e = checkInstalledPorts(decision.outputs, installed->outputs))
        return e;
    } else {
      if (decision.binding ||
          (op->getParentOfType<func::FuncOp>() && !interfaceOperation(op)))
        return error("binding-plan-coverage");
      if (auto e = checkDefaultPorts(op->getOperandTypes(), decision.inputs))
        return e;
      if (auto e = checkDefaultPorts(op->getResultTypes(), decision.outputs))
        return e;
    }
  }

  // Original preorder and operand order determine every instruction position.
  // No sharing, hoisting, path search, or inferred purity is permitted here.
  std::map<Operation *, std::set<std::string>> sites;
  for (auto *op : operations)
    if (auto function = op->getParentOfType<func::FuncOp>())
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        sites[function].insert(site.getValue().str());
  SmallVector<unsigned> references(plan.bindings.size(), 0);
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.binding)
      ++references[*decision.binding];
    size_t crossing = 0;
    for (auto [operand, value] : enumerate(op->getOperands())) {
      auto from = valuePort(value, plan, indices);
      auto to = decision.inputs[operand];
      if (from == to)
        continue;
      if (crossing >= decision.conversions.size())
        return error("binding-no-conversion");
      const auto &conversion = decision.conversions[crossing++];
      if (conversion.operand != operand || conversion.from != from ||
          conversion.to != to || conversion.binding >= plan.bindings.size())
        return error("binding-no-conversion");
      const auto &binding = plan.bindings[conversion.binding];
      auto source = encodeBoundType(from, true);
      if (!source)
        return source.takeError();
      auto target = encodeBoundType(to, true);
      if (!target)
        return target.takeError();
      if (binding.purpose != BindingPurpose::Conversion)
        return error("binding-no-conversion");
      if (auto e = checkDirectConversion(binding.binding.application, *source,
                                         *target))
        return e;
      auto available = catalog.conversions(*source, *target);
      if (none_of(available, [&](const auto &candidate) {
            return sameApplication(candidate, binding.binding.application);
          }))
        return error("binding-no-conversion");
      auto function = op->getParentOfType<func::FuncOp>();
      StringRef site = conversion.site;
      const bool validSite =
          !site.empty() && site.size() <= 512 &&
          (isAlpha(site.front()) || site.front() == '_') &&
          all_of(site, [](char c) {
            return isAlnum(c) || c == '_' || c == '.' || c == '-';
          });
      if (!function || !validSite ||
          !sites[function].insert(conversion.site).second)
        return error("binding-plan-coverage");
      if (references[conversion.binding] == 0 && binding.location != i)
        return error("binding-plan-coverage");
      ++references[conversion.binding];
    }
    if (crossing != decision.conversions.size())
      return error("binding-no-conversion");
  }

  std::set<OperationIndex> grouped;
  OperationIndex previous = 0;
  LinearContractionStats stats;
  for (const auto &group : plan.contractions) {
    locate(failureLocation, root);
    if (!plan.input->linearContractions ||
        group.producer >= operations.size() || group.producer <= previous ||
        group.consumers.empty())
      return error("binding-contraction");
    previous = group.producer;
    auto actual = checkAllUses(operations[group.producer], plan, indices,
                               failureLocation);
    if (!actual)
      return actual.takeError();
    if (*actual != group.consumers)
      return error("binding-contraction");
    SmallVector<OperationIndex> members{group.producer};
    append_range(members, *actual);
    for (auto index : members) {
      const auto &decision = plan.operations[index];
      if (!grouped.insert(index).second || !decision.binding ||
          plan.bindings[*decision.binding].purpose !=
              BindingPurpose::Contraction ||
          references[*decision.binding] != 1 ||
          plan.bindings[*decision.binding].location != index)
        return error("binding-contraction");
    }
    ++stats.selectedProducers;
    stats.selectedPairs += actual->size();
  }
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.binding &&
        plan.bindings[*decision.binding].purpose ==
            BindingPurpose::Contraction &&
        !grouped.count(i))
      return error("binding-contraction");
    // Explicit diagonal implementations also require all-uses preflight; they
    // do not have to be automatic, freshly cloned contraction groups.
    for (auto type : decision.outputs)
      if (auto physical = dyn_cast<DataType>(type))
        if (isDiagonalRepresentation(physical.getRepresentation())) {
          auto uses = checkAllUses(op, plan, indices, failureLocation);
          if (!uses)
            return uses.takeError();
        }
  }
  for (auto [i, binding] : enumerate(plan.bindings))
    if (binding.purpose != BindingPurpose::Original && references[i] == 0)
      return error("binding-plan-coverage");
  // Statistics use the existing opportunity analysis, never as the validator's
  // all-uses or group-completeness oracle above.
  if (plan.input->linearContractions)
    for (auto function : root.getBody().front().getOps<func::FuncOp>())
      (void)findLinearContractions(function, stats);
  return CheckedPhysicalPlan(plan, stats);
}
} // namespace zkc::target
