#include "Bindings.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Builders.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/LinearContraction.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include <set>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class Planner {
  ModuleOp module;
  ProtocolModuleOp root;
  OpBuilder b;
  Location location;
  std::map<std::string, source::OperationBinding> bindings;
  std::set<std::string> symbols;
  unsigned next = 0;

  Expected<Type> port(Type logical) {
    auto type = encodeBoundType(logical, false);
    if (!type)
      return type.takeError();
    auto physical = defaultRepresentation(*type);
    if (!physical)
      return physical.takeError();
    return decodeBoundType(b.getContext(), *physical);
  }

  std::string fresh(std::set<std::string> &used, StringRef prefix) {
    std::string result;
    do {
      result = prefix.str() + std::to_string(next++);
    } while (!used.insert(result).second);
    return result;
  }

  void declaration(const source::OperationBinding &binding, Location location) {
    OpBuilder::InsertionGuard guard(b);
    b.setInsertionPointToStart(&root.getBody().front());
    SmallVector<Attribute> arguments;
    for (const auto &a : binding.application.arguments)
      arguments.push_back(text(b, a));
    operation(b, "pir.operation_binding", {}, {},
              {named(b, "sym_name", binding.name),
               named(b, "contract", binding.application.contract),
               named(b, "arguments", b.getArrayAttr(arguments)),
               named(b, "implementation", binding.application.implementation)},
              0, location);
  }

  Expected<mlir::Value> convert(mlir::Value input, Type target,
                                std::set<std::string> &sites,
                                Location location) {
    if (input.getType() == target)
      return input;
    auto from = encodeBoundType(input.getType(), true);
    if (!from)
      return from.takeError();
    auto to = encodeBoundType(target, true);
    if (!to)
      return to.takeError();
    if (from->kind != "table" || to->kind != "table" ||
        from->identity != to->identity)
      return error("binding-no-conversion");
    std::vector<std::string> args{from->identity, from->representation,
                                  to->representation};
    std::string key;
    for (const auto &[name, binding] : bindings)
      if (binding.application.contract == "table.relayout" &&
          binding.application.arguments == args)
        key = name;
    if (key.empty()) {
      key = fresh(symbols, "layout_");
      source::OperationBinding binding{
          {},
          key,
          {"table.relayout", std::move(args), "arkworks/table.relayout"}};
      auto installed = resolveBinding(binding.application, true);
      if (!installed)
        return installed.takeError();
      declaration(binding, location);
      bindings.emplace(key, std::move(binding));
    }
    // Conversion is an actual ordered instruction. It is neither a type cast
    // nor metadata, and cannot be moved across a source action by this pass.
    auto *conversion = operation(
        b, "plan.kernel", input, target,
        {named(b, "site", fresh(sites, "layout_")),
         named(b, "binding", FlatSymbolRefAttr::get(b.getContext(), key)),
         named(b, "kernel", "arkworks/table.relayout"),
         named(b, "parameters", b.getArrayAttr({}))},
        0, location);
    return conversion->getResult(0);
  }

public:
  explicit Planner(ModuleOp module)
      : module(module),
        root(cast<ProtocolModuleOp>(&module.getBody()->front())),
        b(module.getContext()), location(root.getLoc()) {}

  Location failureLocation() const { return location; }

  Error run(ArrayRef<std::pair<std::string, std::string>> requests,
            bool linearContractions, LinearContractionStats &stats) {
    std::set<std::string> fixed;
    std::map<std::string, std::string> choices;
    for (const auto &[key, impl] : requests)
      if (!choices.emplace(key, impl).second)
        return error("binding-duplicate-selection");
    for (auto &op : root.getBody().front()) {
      symbols.insert(attr(&op, "sym_name").str());
      if (!isa<OperationBindingOp>(op))
        continue;
      location = op.getLoc();
      auto binding = readBinding(&op);
      if (!binding)
        return binding.takeError();
      auto choice = choices.find(binding->name);
      auto selected = target::selectImplementation(
          binding->application, choice == choices.end()
                                    ? std::nullopt
                                    : std::optional<StringRef>(choice->second));
      if (!selected)
        return selected.takeError();
      if (selected->fixed)
        fixed.insert(binding->name);
      binding->application = std::move(selected->application);
      if (choice != choices.end())
        choices.erase(choice);
      bindings.emplace(binding->name, std::move(*binding));
    }
    location = root.getLoc();
    if (!choices.empty())
      return error("binding-unknown-selection");

    if (linearContractions) {
      for (auto function : root.getBody().front().getOps<func::FuncOp>()) {
        for (const auto &group : findLinearContractions(function, stats)) {
          // Preflight the entire producer/use set. A fixed consumer or lack of
          // space for even one clone leaves the whole group materialized.
          SmallVector<std::pair<Operation *, source::OperationBinding>> pending;
          auto prepare = [&](Operation *op, StringRef implementation) {
            auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
            if (!ref || fixed.count(ref.getValue().str()))
              return false;
            auto found = bindings.find(ref.getValue().str());
            if (found == bindings.end())
              return false;
            auto binding = found->second;
            binding.application.implementation = implementation.str();
            auto installed = resolveBinding(binding.application, true);
            if (!installed) {
              consumeError(installed.takeError());
              return false;
            }
            pending.emplace_back(op, std::move(binding));
            return true;
          };
          if (bindings.size() + 1 + group.uses.size() > 4096 ||
              !prepare(group.producer, group.production.implementation))
            continue;
          bool available = true;
          for (const auto &use : group.uses)
            if (!prepare(use.consumer, use.contraction.implementation)) {
              available = false;
              break;
            }
          if (!available)
            continue;
          // One clone per operation, including one producer shared by all uses.
          for (auto &[op, binding] : pending) {
            binding.name = fresh(symbols, "diagonal_");
            declaration(binding, op->getLoc());
            op->setAttr("binding",
                        FlatSymbolRefAttr::get(b.getContext(), binding.name));
            bindings.emplace(binding.name, std::move(binding));
          }
          ++stats.selectedProducers;
          stats.selectedPairs += group.uses.size();
        }
      }
    }

    // Callable/control interfaces receive explicit physical ports. Kernel
    // outputs below instead receive their selected implementation's ports;
    // consequently one logical type can have several live representations.
    Error failure = Error::success();
    auto assign = [&](Type type) -> Type {
      auto selected = port(type);
      if (!selected) {
        if (!failure)
          failure = selected.takeError();
        else
          consumeError(selected.takeError());
        return type;
      }
      return *selected;
    };
    root->walk([&](Operation *op) {
      if (failure)
        return;
      location = op->getLoc();
      for (auto &region : op->getRegions())
        for (auto &block : region)
          for (auto arg : block.getArguments())
            arg.setType(assign(arg.getType()));
      if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
        auto ft = cast<FunctionType>(signature.getValue());
        SmallVector<Type> inputs, outputs;
        for (auto type : ft.getInputs())
          inputs.push_back(assign(type));
        for (auto type : ft.getResults())
          outputs.push_back(assign(type));
        op->setAttr("function_type",
                    TypeAttr::get(b.getFunctionType(inputs, outputs)));
      }
      if (!op->hasAttr("binding"))
        for (auto value : op->getResults())
          value.setType(assign(value.getType()));
    });
    if (failure)
      return failure;

    for (auto function : root.getBody().front().getOps<func::FuncOp>()) {
      std::set<std::string> sites;
      SmallVector<Operation *> work;
      function.walk<WalkOrder::PreOrder>([&](Operation *op) {
        if (op != function.getOperation()) {
          sites.insert(attr(op, "site").str());
          work.push_back(op);
        }
      });
      for (auto *op : work) {
        location = op->getLoc();
        b.setInsertionPoint(op);
        SmallVector<Type> inputs, outputs;
        const source::OperationBinding *binding = nullptr;
        if (isa<func::ReturnOp>(op)) {
          inputs.append(function.getFunctionType().getResults().begin(),
                        function.getFunctionType().getResults().end());
        } else if (isa<HaltOp>(op)) {
          continue;
        } else if (isa<VariantInjectOp, LocalMatchOp>(op)) {
          for (auto type : op->getOperandTypes()) {
            if (auto physical = dyn_cast<DataType>(type))
              type = physical.getLogical();
            auto selected = port(type);
            if (!selected)
              return selected.takeError();
            inputs.push_back(*selected);
          }
        } else if (isa<LocalIfOp>(op)) {
          auto condition = port(IntegerType::get(b.getContext(), 1));
          if (!condition)
            return condition.takeError();
          inputs.push_back(*condition);
          llvm::append_range(inputs,
                             op->getRegion(0).front().getArgumentTypes());
        } else if (isa<LocalForOp>(op)) {
          auto &block = op->getRegion(0).front();
          inputs.push_back(block.getArgument(0).getType());
          inputs.push_back(block.getArgument(0).getType());
          llvm::append_range(
              inputs, ValueRange(block.getArguments()).drop_front().getTypes());
        } else if (isa<LocalYieldOp>(op)) {
          auto *parent = op->getParentOp();
          llvm::append_range(inputs, parent->getResultTypes());
          if (isa<LocalForOp>(parent))
            llvm::append_range(inputs,
                               ValueRange(op->getBlock()->getArguments())
                                   .drop_front(1 + parent->getNumResults())
                                   .getTypes());
        } else {
          auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
          if (!ref || !bindings.count(ref.getValue().str()))
            return error("binding-reference");
          binding = &bindings.at(ref.getValue().str());
          auto selected = resolveBinding(binding->application, true);
          if (!selected)
            return selected.takeError();
          for (const auto &t : selected->inputs)
            inputs.push_back(decodeBoundType(b.getContext(), t));
          for (const auto &t : selected->outputs)
            outputs.push_back(decodeBoundType(b.getContext(), t));
        }
        if (inputs.size() != op->getNumOperands())
          return error("binding-operation-signature");
        SmallVector<mlir::Value> operands;
        for (auto [value, type] : zip(op->getOperands(), inputs)) {
          auto converted = convert(value, type, sites, op->getLoc());
          if (!converted)
            return converted.takeError();
          operands.push_back(*converted);
        }
        if (!binding) {
          op->setOperands(operands);
          continue;
        }
        auto *physical =
            operation(b, "plan.kernel", operands, outputs,
                      {named(b, "site", op->getAttr("site")),
                       named(b, "binding", op->getAttr("binding")),
                       named(b, "kernel", binding->application.implementation),
                       named(b, "parameters", op->getAttr("parameters"))},
                      0, op->getLoc());
        op->replaceAllUsesWith(physical->getResults());
        op->erase();
      }
    }
    for (auto declaration : root.getBody().front().getOps<OperationBindingOp>())
      declaration.setImplementation(bindings.at(declaration.getSymName().str())
                                        .application.implementation);
    root.setStage("physical");
    return Error::success();
  }
};
} // namespace

LogicalResult
lowerBoundPhysical(ModuleOp original,
                   ArrayRef<std::pair<std::string, std::string>> selections,
                   bool linearContractions, LinearContractionStats *stats) {
  // Planning failures leave the caller's logical artifact intact.
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(original->clone()));
  Planner planner(*candidate);
  LinearContractionStats result;
  if (auto e = planner.run(selections, linearContractions, result)) {
    diagnostics::emit(emitError(planner.failureLocation()), std::move(e));
    return failure();
  }
  if (failed(verify(*candidate)))
    return failure();
  original.getBodyRegion().takeBody(candidate->getBodyRegion());
  if (stats)
    *stats = result;
  return success();
}
} // namespace zkc::protocol
