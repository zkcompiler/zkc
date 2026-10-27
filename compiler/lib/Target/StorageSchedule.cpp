#include "StorageSchedule.h"
#include "ExecutionPorts.h"
#include "PhysicalPlan.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <map>

using namespace llvm;
using namespace mlir;
namespace zkc::target {
namespace {
constexpr size_t storageWorkLimit = 1000000;
enum class Use { Ordinary, Escape, Release };
struct Permission {
  bool discardable, affine;
};
struct Definition {
  Block *block;
  Permission permission;
};

// A borrowed index over the real blocks, with coordinate interpretation only.
// In particular, this view never stores last-use answers or liveness sets.
class StorageView {
  ModuleOp module;
  std::optional<ExecutionPorts> execution;
  ArrayRef<OperationDecision> ports;
  SmallVector<Operation *> operations;
  SmallVector<std::pair<Block *, StoragePoint>> blocks;
  llvm::DenseMap<Value, StorageValue> coordinates;
  llvm::DenseMap<Type, Permission> permissions;
  Location *failureLocation;
  size_t remaining = storageWorkLimit;

  Error charge(size_t work = 1) {
    if (work > remaining)
      return error("storage-schedule-limit");
    remaining -= work;
    return Error::success();
  }
  Expected<Permission> permission(Type type) {
    if (!type)
      return error("storage-schedule-coordinate");
    auto found = permissions.find(type);
    if (found != permissions.end())
      return found->second;
    auto encoded = protocol::encodeBoundType(type, true);
    if (!encoded)
      return encoded.takeError();
    Permission result{protocol::discardable(*encoded),
                      protocol::affine(encoded->spelling())};
    permissions[type] = result;
    return result;
  }
  Error add(StorageValue coordinate, Block *block, Type type) {
    if (auto e = charge())
      return e;
    auto properties = permission(type);
    if (!properties)
      return properties.takeError();
    definitions.emplace(coordinate, Definition{block, *properties});
    return Error::success();
  }

public:
  std::map<StorageValue, Definition> definitions;
  StorageView(ModuleOp module, ArrayRef<OperationDecision> ports,
              Location *failureLocation)
      : module(module), ports(ports), failureLocation(failureLocation) {}

  Error initialize() {
    if (!hasSingleElement(*module.getBody()))
      return error("storage-schedule-context");
    auto root =
        dyn_cast<protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
    if (!root ||
        (ports.empty() ? root.getProfile() != protocol_ir::Profile::Physical
                       : root.getProfile() != protocol_ir::Profile::Exec))
      return error("storage-schedule-context");
    auto admitted = ExecutionPorts::read(module);
    if (!admitted)
      return admitted.takeError();
    execution = std::move(*admitted);
    append_range(operations, execution->operations());
    if (!ports.empty() && ports.size() != operations.size())
      return error("storage-schedule-coordinate");
    for (auto [index, op] : enumerate(operations)) {
      if (auto e = charge())
        return e;
      const auto &node = execution->get(op);
      if (!ports.empty() && ports[index].outputs.size() != node.outputs.size())
        return error("storage-schedule-coordinate");
      if (failureLocation)
        *failureLocation = op->getLoc();
      if (!node.scoped)
        continue;
      unsigned blockIndex = 0;
      for (auto *entry : node.bodies) {
        const auto &body = execution->body(entry);
        if (body.owner != op)
          continue;
        if (auto e = charge())
          return e;
        blocks.emplace_back(
            entry, StoragePoint{StoragePoint::BlockEntry, index, blockIndex});
        if (!ports.empty() &&
            (blockIndex >= ports[index].blockArguments.size() ||
             ports[index].blockArguments[blockIndex].size() !=
                 body.arguments.size()))
          return error("storage-schedule-coordinate");
        for (auto [argumentIndex, argument] : enumerate(body.arguments)) {
          StorageValue coordinate{StorageValue::BlockArgument, index,
                                  unsigned(argumentIndex), blockIndex};
          coordinates.insert({argument, coordinate});
          Type type =
              ports.empty()
                  ? argument.getType()
                  : ports[index].blockArguments[blockIndex][argumentIndex];
          if (auto e = add(coordinate, entry, type))
            return e;
        }
        ++blockIndex;
      }
      if (!ports.empty() && ports[index].blockArguments.size() != blockIndex)
        return error("storage-schedule-coordinate");
      if (!node.step)
        continue;
      auto *body = execution->enclosingBody(op);
      if (!body)
        return error("storage-schedule-context");
      for (auto [resultIndex, result] : enumerate(node.outputs)) {
        StorageValue coordinate{StorageValue::OperationResult, index,
                                unsigned(resultIndex)};
        coordinates.insert({result, coordinate});
        Type type = ports.empty() ? result.getType()
                                  : ports[index].outputs[resultIndex];
        if (auto e = add(coordinate, body, type))
          return e;
      }
      if (!ports.empty())
        for (auto [crossing, conversion] : enumerate(ports[index].conversions))
          if (auto e = add(
                  {StorageValue::ConversionResult, index, unsigned(crossing)},
                  body, conversion.to))
            return e;
    }
    return Error::success();
  }

  Error
  walk(llvm::function_ref<Error(StorageValue, StoragePoint)> define,
       llvm::function_ref<Error(StorageValue, Block *, Use, StoragePoint)> use,
       llvm::function_ref<Error(StoragePoint, Block *)> point) {
    llvm::DenseMap<Operation *, size_t> indices;
    for (auto [index, op] : enumerate(operations))
      indices[op] = index;
    for (auto [block, entry] : blocks) {
      for (Value argument : execution->body(block).arguments)
        if (auto e = define(coordinates.find(argument)->second, entry))
          return e;
      if (auto e = point(entry, block))
        return e;
      for (Operation *op : execution->body(block).instructions) {
        if (failureLocation)
          *failureLocation = op->getLoc();
        if (auto e = charge(execution->inputs(op).size() + 1))
          return e;
        size_t index = indices.lookup(op);
        SmallVector<StorageValue> operands;
        for (Value operand : execution->inputs(op)) {
          auto found = coordinates.find(operand);
          if (found == coordinates.end())
            return error("storage-schedule-context");
          operands.push_back(found->second);
        }
        if (!ports.empty())
          for (auto [crossing, conversion] :
               enumerate(ports[index].conversions)) {
            if (auto e = charge())
              return e;
            if (conversion.operand >= operands.size())
              return error("storage-schedule-coordinate");
            StoragePoint at{StoragePoint::AfterConversion, index,
                            static_cast<unsigned>(crossing)};
            if (auto e =
                    use(operands[conversion.operand], block, Use::Ordinary, at))
              return e;
            StorageValue value{StorageValue::ConversionResult, index,
                               static_cast<unsigned>(crossing)};
            if (auto e = define(value, at))
              return e;
            operands[conversion.operand] = value;
            if (auto e = point(at, block))
              return e;
          }
        Use kind = isa<runtime::ReleaseBindingsOp>(op)         ? Use::Release
                   : isa<exec::ReturnOp, exec::CompleteOp>(op) ? Use::Escape
                                                               : Use::Ordinary;
        StoragePoint at{StoragePoint::AfterOperation, index};
        for (auto operand : operands)
          if (auto e = use(operand, block, kind, at))
            return e;
        for (Value result : execution->outputs(op))
          if (auto e = define(coordinates.find(result)->second, at))
            return e;
        if (!isa<exec::ReturnOp, exec::CompleteOp, exec::RejectOp>(op))
          if (auto e = point(at, block))
            return e;
      }
    }
    return Error::success();
  }
};
} // namespace

Expected<SmallVector<StorageRelease>>
proposeStorage(ModuleOp module, ArrayRef<OperationDecision> ports,
               Location *failureLocation) {
  StorageView view(module, ports, failureLocation);
  if (auto e = view.initialize())
    return e;
  struct Lifetime {
    StoragePoint end;
    bool used = false, excluded = false;
  };
  std::map<StorageValue, Lifetime> lifetimes;
  SmallVector<StorageValue> order;
  // The producer computes last uses in actual conversion/instruction order.
  if (auto e = view.walk(
          [&](StorageValue value, StoragePoint at) -> Error {
            order.push_back(value);
            lifetimes.emplace(value, Lifetime{at});
            return Error::success();
          },
          [&](StorageValue value, Block *block, Use kind,
              StoragePoint at) -> Error {
            auto found = lifetimes.find(value);
            if (found == lifetimes.end() ||
                view.definitions.at(value).block != block)
              return error("storage-schedule-context");
            found->second.used = true;
            found->second.excluded |= kind != Use::Ordinary;
            found->second.end = at;
            return Error::success();
          },
          [&](StoragePoint, Block *) { return Error::success(); }))
    return e;
  std::map<StoragePoint, SmallVector<StorageValue>> after;
  for (auto value : order) {
    const auto &lifetime = lifetimes.at(value);
    const auto &permission = view.definitions.at(value).permission;
    if (!permission.discardable || lifetime.excluded ||
        (permission.affine && lifetime.used))
      continue;
    after[lifetime.end].push_back(value);
  }
  SmallVector<StorageRelease> releases;
  for (const auto &[point, values] : after) {
    ArrayRef<StorageValue> remaining = values;
    while (!remaining.empty()) {
      auto chunk = remaining.take_front(1024);
      releases.push_back({point, SmallVector<StorageValue>(chunk)});
      remaining = remaining.drop_front(chunk.size());
    }
  }
  return releases;
}

Error validateStorage(ModuleOp module, ArrayRef<OperationDecision> ports,
                      ArrayRef<StorageRelease> releases,
                      Location *failureLocation) {
  if (releases.empty())
    return Error::success();
  StorageView view(module, ports, failureLocation);
  if (auto e = view.initialize())
    return e;
  std::map<StoragePoint, SmallVector<const StorageRelease *>> points;
  size_t work = 0;
  for (const auto &release : releases) {
    if (release.values.empty() || release.values.size() > 1024)
      return error("storage-schedule-coordinate");
    work += release.values.size() + 1;
    if (work > storageWorkLimit)
      return error("storage-schedule-limit");
    points[release.point].push_back(&release);
  }
  struct State {
    bool used = false, escaped = false, released = false;
  };
  std::map<StorageValue, State> states;
  size_t checked = 0;
  // The checker simulates definition/use/release legality. It never computes
  // last uses and accepts any safe delayed point in the same block.
  if (auto e = view.walk(
          [&](StorageValue value, StoragePoint) -> Error {
            if (!states.emplace(value, State{}).second)
              return error("storage-schedule-coordinate");
            return Error::success();
          },
          [&](StorageValue value, Block *block, Use kind,
              StoragePoint) -> Error {
            auto found = states.find(value);
            if (found == states.end() ||
                view.definitions.at(value).block != block ||
                found->second.released)
              return error("storage-schedule-lifetime");
            auto &state = found->second;
            auto permission = view.definitions.at(value).permission;
            if (permission.affine && state.used)
              return error("storage-schedule-lifetime");
            state.used = true;
            state.escaped |= kind == Use::Escape;
            if (kind == Use::Release) {
              if (!permission.discardable)
                return error("storage-schedule-permission");
              state.released = true;
            }
            return Error::success();
          },
          [&](StoragePoint at, Block *block) -> Error {
            auto found = points.find(at);
            if (found == points.end())
              return Error::success();
            for (auto *release : found->second) {
              ++checked;
              for (auto value : release->values) {
                auto state = states.find(value);
                if (state == states.end())
                  return error("storage-schedule-coordinate");
                const auto &definition = view.definitions.at(value);
                if (definition.block != block || state->second.released ||
                    state->second.escaped)
                  return error("storage-schedule-lifetime");
                if (!definition.permission.discardable ||
                    (definition.permission.affine && state->second.used))
                  return error("storage-schedule-permission");
                state->second.released = true;
              }
            }
            return Error::success();
          }))
    return e;
  if (checked != releases.size())
    return error("storage-schedule-coordinate");
  return Error::success();
}
} // namespace zkc::target
