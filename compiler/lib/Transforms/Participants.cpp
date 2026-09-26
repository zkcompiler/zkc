#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/DenseMap.h"
#include <set>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
std::map<std::string, std::string> bindings(ArrayAttr array,
                                            bool refs = false) {
  std::map<std::string, std::string> result;
  for (auto a : array) {
    auto p = cast<ArrayAttr>(a);
    result.emplace(cast<StringAttr>(p[0]).str(),
                   refs ? cast<FlatSymbolRefAttr>(p[1]).getValue().str()
                        : cast<StringAttr>(p[1]).str());
  }
  return result;
}
template <typename Map>
typename Map::mapped_type *lookup(Map &map, const typename Map::key_type &key) {
  auto found = map.find(key);
  return found == map.end() ? nullptr : &found->second;
}
Error missingBinding(Operation *op) {
  diagnostics::emit(op->emitOpError(), "interactive-projection-binding");
  return error("interactive-projection-binding");
}
class Projector {
  OpBuilder b;
  ProtocolModuleOp source;
  std::map<std::string, ProtocolOp> definitions;
  std::map<std::string, InstanceOp> instances;
  std::map<std::pair<std::string, std::string>, std::string> symbols;
  using Owners = llvm::DenseMap<mlir::Value, std::string>;
  Error body(Block &block, Owners owners, IRMapping values, InstanceOp instance,
             StringRef role, StringRef actual) {
    auto roles = bindings(instance.getRoles());
    auto deps = bindings(instance.getDependencies(), true);
    std::map<std::string, Attribute> params;
    for (auto a : instance.getParameters()) {
      auto pair = cast<ArrayAttr>(a);
      params.emplace(cast<StringAttr>(pair[0]).str(), pair[1]);
    }
    auto owned = [&](mlir::Value v) { return owners.lookup(v) == role; };
    auto inputs = [&](ValueRange range) {
      SmallVector<mlir::Value> out;
      for (auto v : range)
        if (owned(v))
          out.push_back(values.lookup(v));
      return out;
    };
    for (auto &item : block) {
      Operation *op = &item;
      if (auto local = dyn_cast<LocalCallOp>(op)) {
        for (auto v : op->getResults())
          owners[v] = local.getRoleAttr().getValue().str();
        if (local.getRoleAttr().getValue() != role)
          continue;
        SmallVector<Type> types;
        for (auto v : op->getResults())
          types.push_back(v.getType());
        auto copy = LocalCallOp::create(
            b, op->getLoc(), types, inputs(op->getOperands()),
            local.getCalleeAttr(), local.getSiteAttr(), StringAttr());
        for (auto [old, value] : zip(op->getResults(), copy->getResults()))
          values.map(old, value);
      } else if (auto message = dyn_cast<MessageOp>(op)) {
        owners[message.getOutput()] = message.getReceiver().str();
        auto *sender = lookup(roles, message.getSender().str());
        auto *receiver = lookup(roles, message.getReceiver().str());
        if (!sender || !receiver)
          return missingBinding(op);
        if (message.getSender() == role)
          EmitOp::create(b, op->getLoc(), values.lookup(message.getInput()),
                         message.getSite(), message.getSchema(), *receiver);
        else if (message.getReceiver() == role) {
          auto copy =
              AwaitOp::create(b, op->getLoc(), message.getOutput().getType(),
                              message.getSite(), message.getSchema(), *sender);
          values.map(message.getOutput(), copy->getResult(0));
        }
      } else if (auto call = dyn_cast<ProtocolCallOp>(op)) {
        auto *binding = lookup(deps, call.getDependency().str());
        auto *selected = binding ? lookup(instances, *binding) : nullptr;
        auto *decl = selected
                         ? lookup(definitions, selected->getProtocol().str())
                         : nullptr;
        if (!selected || !decl)
          return missingBinding(op);
        InstanceOp child = *selected;
        ProtocolOp childDef = *decl;
        for (auto [value, r] : zip(op->getResults(), childDef.getOutputRoles()))
          owners[value] = cast<StringAttr>(r).str();
        auto childRoles = bindings(child.getRoles());
        if (!childRoles.count(role.str()))
          continue;
        SmallVector<Type> outputTypes;
        for (auto v : op->getResults())
          if (owned(v))
            outputTypes.push_back(v.getType());
        auto *callee =
            lookup(symbols, {child.getSymName().str(), actual.str()});
        if (!callee)
          return missingBinding(op);
        auto copy = ParticipantCallOp::create(b, op->getLoc(), outputTypes,
                                              inputs(op->getOperands()),
                                              call.getSite(), *callee);
        unsigned i = 0;
        for (auto v : op->getResults())
          if (owned(v))
            values.map(v, copy->getResult(i++));
      } else if (auto loop = dyn_cast<ProtocolLoopOp>(op)) {
        unsigned carried = loop.getCarried();
        for (unsigned i = 0; i < carried; ++i)
          owners[op->getResult(i)] = owners.lookup(op->getOperand(i));
        SmallVector<Type> types;
        for (auto v : op->getResults())
          if (owned(v))
            types.push_back(v.getType());
        StringRef count = loop.getCount();
        bool symbolic = false;
        if (loop.getParameter()) {
          auto *bound = lookup(params, count.str());
          if (!bound)
            return missingBinding(op);
          symbolic = isa<ArrayAttr>(*bound);
          if (!symbolic)
            count = cast<StringAttr>(*bound).getValue();
        }
        auto copy = ProtocolLoopOp::create(
            b, op->getLoc(), types, inputs(op->getOperands()), loop.getSite(),
            types.size(), count, symbolic);
        auto *target = new Block();
        copy->getRegion(0).push_back(target);
        Owners innerOwners;
        IRMapping innerValues;
        auto &inner = loop.getBody().front();
        for (auto [arg, input] : zip(inner.getArguments(), op->getOperands())) {
          innerOwners[arg] = owners.lookup(input);
          if (owned(input))
            innerValues.map(arg,
                            target->addArgument(arg.getType(), arg.getLoc()));
        }
        {
          OpBuilder::InsertionGuard guard(b);
          b.setInsertionPointToEnd(target);
          if (auto e = body(inner, std::move(innerOwners),
                            std::move(innerValues), instance, role, actual))
            return e;
        }
        unsigned i = 0;
        for (auto v : op->getResults())
          if (owned(v))
            values.map(v, copy->getResult(i++));
      } else if (isa<FinishOp>(op)) {
        FinishOp::create(b, op->getLoc(), inputs(op->getOperands()));
      } else if (isa<ProtocolYieldOp>(op)) {
        ProtocolYieldOp::create(b, op->getLoc(), inputs(op->getOperands()));
      } else if (auto halt = dyn_cast<HaltOp>(op)) {
        if (halt.getRoleAttr().getValue() == role)
          HaltOp::create(b, op->getLoc(), halt.getSite(), halt.getReason(),
                         StringAttr());
        else
          IncompleteOp::create(b, op->getLoc(), halt.getSite());
      }
    }
    return Error::success();
  }

public:
  explicit Projector(ProtocolModuleOp source)
      : b(source.getContext()), source(source) {}
  Expected<OwningOpRef<ModuleOp>> run() {
    OwningOpRef<ModuleOp> module(ModuleOp::create(source.getLoc()));
    b.setInsertionPointToEnd(module->getBody());
    auto root = ProtocolModuleOp::create(b, source.getLoc(), "logical");
    auto *block = new Block();
    root->getRegion(0).push_back(block);
    b.setInsertionPointToEnd(block);
    for (auto &op : source.getBody().front()) {
      if (auto d = dyn_cast<ProtocolOp>(op))
        definitions.emplace(d.getSymName().str(), d);
      if (auto i = dyn_cast<InstanceOp>(op))
        instances.emplace(i.getSymName().str(), i);
    }
    // Validate the whole source, but emit only the union of entry closures.
    // Unused instances remain legal library declarations, not extra endpoints.
    std::vector<std::string> pending;
    for (auto &op : source.getBody().front())
      if (auto entry = dyn_cast<ProtocolEntryOp>(op))
        pending.push_back(
            cast<FlatSymbolRefAttr>(entry.getTargets()[0]).getValue().str());
    std::set<std::string> reachable;
    while (!pending.empty()) {
      auto name = std::move(pending.back());
      pending.pop_back();
      if (!reachable.insert(name).second)
        continue;
      auto *instance = lookup(instances, name);
      if (!instance)
        return missingBinding(source);
      for (const auto &[alias, child] :
           bindings(instance->getDependencies(), true))
        pending.push_back(child);
    }
    for (auto it = instances.begin(); it != instances.end();)
      if (!reachable.count(it->first))
        it = instances.erase(it);
      else
        ++it;
    std::set<std::string> used;
    for (auto &op : source.getBody().front())
      used.insert(attr(&op, "sym_name").str());
    for (auto &[name, instance] : instances)
      for (const auto &[formal, actual] : bindings(instance.getRoles())) {
        std::string symbol =
            "r" + std::to_string(name.size()) + "_" + name + "_" + actual;
        while (used.count(symbol))
          symbol = "_" + symbol;
        used.insert(symbol);
        symbols[{name, actual}] = std::move(symbol);
      }
    for (auto &op : source.getBody().front())
      if (isa<func::FuncOp, OperationBindingOp>(op)) {
        auto *copy = b.clone(op);
        // Source relation ownership was checked before this explicit lowering
        // boundary. Exact matrix checks remain ordinary executable operations.
        copy->removeAttr("relation");
        copy->removeAttr("relation_view");
      }
    for (auto &[name, instance] : instances) {
      auto *decl = lookup(definitions, instance.getProtocol().str());
      if (!decl)
        return missingBinding(instance);
      ProtocolOp definition = *decl;
      auto ft = definition.getFunctionType();
      auto roles = bindings(instance.getRoles());
      for (auto roleAttr : definition.getRoles()) {
        StringRef role = cast<StringAttr>(roleAttr).getValue();
        auto *actualRole = lookup(roles, role.str());
        if (!actualRole)
          return missingBinding(instance);
        const std::string &actual = *actualRole;
        auto *symbol = lookup(symbols, {name, actual});
        if (!symbol)
          return missingBinding(instance);
        SmallVector<Type> inputs, outputs;
        SmallVector<Attribute> argumentNames;
        auto sourceNames =
            definition->getAttrOfType<ArrayAttr>("argument_names");
        if (sourceNames)
          for (auto [n, r] : zip(sourceNames, definition.getInputRoles()))
            if (cast<StringAttr>(r).getValue() == role)
              argumentNames.push_back(n);
        for (auto [type, r] : zip(ft.getInputs(), definition.getInputRoles()))
          if (cast<StringAttr>(r).getValue() == role)
            inputs.push_back(type);
        for (auto [type, r] : zip(ft.getResults(), definition.getOutputRoles()))
          if (cast<StringAttr>(r).getValue() == role)
            outputs.push_back(type);
        auto op = ParticipantOp::create(
            b,
            FusedLoc::get(b.getContext(),
                          {definition.getLoc(), instance.getLoc()}),
            *symbol, b.getFunctionType(inputs, outputs), name, actual,
            instance.getParameters(),
            sourceNames ? b.getArrayAttr(argumentNames) : ArrayAttr());
        auto *bodyBlock = new Block();
        op->getRegion(0).push_back(bodyBlock);
        Owners owners;
        IRMapping values;
        for (auto [arg, r] : zip(definition.getBody().front().getArguments(),
                                 definition.getInputRoles())) {
          owners[arg] = cast<StringAttr>(r).str();
          if (cast<StringAttr>(r).getValue() == role)
            values.map(arg,
                       bodyBlock->addArgument(arg.getType(), arg.getLoc()));
        }
        OpBuilder::InsertionGuard guard(b);
        b.setInsertionPointToEnd(bodyBlock);
        if (auto e = body(definition.getBody().front(), std::move(owners),
                          std::move(values), instance, role, actual))
          return e;
      }
    }
    for (auto &op : source.getBody().front())
      if (auto e = dyn_cast<ProtocolEntryOp>(op)) {
        std::string instance =
            cast<FlatSymbolRefAttr>(e.getTargets()[0]).getValue().str();
        SmallVector<Attribute> targets;
        auto *selected = lookup(instances, instance);
        auto *decl = selected
                         ? lookup(definitions, selected->getProtocol().str())
                         : nullptr;
        if (!selected || !decl)
          return missingBinding(e);
        auto roles = bindings(selected->getRoles());
        for (auto r : decl->getRoles()) {
          auto *actual = lookup(roles, cast<StringAttr>(r).str());
          auto *symbol =
              actual ? lookup(symbols, {instance, *actual}) : nullptr;
          if (!actual || !symbol)
            return missingBinding(e);
          targets.push_back(b.getArrayAttr(
              {text(b, *actual),
               FlatSymbolRefAttr::get(b.getContext(), *symbol)}));
        }
        ProtocolEntryOp::create(b, e.getLoc(), e.getSymName(),
                                b.getArrayAttr(targets));
      }
    return module;
  }
};
struct ProjectionPass : PassWrapper<ProjectionPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(ProjectionPass)
  StringRef getArgument() const final { return "zkc-project-participants"; }
  StringRef getDescription() const final {
    return "Project admitted common protocols to independently callable roles";
  }
  void runOnOperation() final {
    auto target = project(getOperation());
    if (!target) {
      diagnostics::emit(getOperation().emitError(), target.takeError());
      return signalPassFailure();
    }
    getOperation().getBodyRegion().takeBody((*target)->getBodyRegion());
  }
};
} // namespace
Expected<OwningOpRef<ModuleOp>> project(ModuleOp module) {
  if (failed(verify(module)))
    return error("interactive-projection-verification");
  auto source = exportSource(module);
  if (!source)
    return source.takeError();
  if (auto e = admit(*source, true))
    return e;
  auto root = dyn_cast<ProtocolModuleOp>(&module.getBody()->front());
  if (!root || root.getStage() != "common")
    return error("interactive-projection-stage");
  // Expand on a private copy; projection does not mutate its input.
  OwningOpRef<ModuleOp> expanded(cast<ModuleOp>(module->clone()));
  if (failed(expandAlgorithms(*expanded)))
    return error("algorithm-expansion-failed");
  root = cast<ProtocolModuleOp>(&expanded->getBody()->front());
  auto target = Projector(root).run();
  if (!target)
    return target.takeError();
  if (failed(verify(**target)))
    return error("interactive-projection-verification");
  return target;
}
std::unique_ptr<Pass> createProjectParticipantsPass() {
  return std::make_unique<ProjectionPass>();
}
} // namespace zkc::protocol
