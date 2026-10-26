#include "../ScopedCandidate.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using mathematical::CandidatePorts;
using mathematical::ScopedCandidate;
FailureOr<Values> mapped(ValueRange inputs, const IRMapping &mapping) {
  Values result;
  for (Value input : inputs) {
    auto value = mapping.lookupOrNull(input);
    if (!value)
      return failure();
    result.push_back(value);
  }
  return result;
}
bool bound(Operation *op) {
  auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding = reference
                     ? dyn_cast_or_null<runtime::BindingOp>(
                           SymbolTable::lookupNearestSymbolFrom(op, reference))
                     : runtime::BindingOp();
  return binding && protocol::operationSupportsContract(
                        op->getName().getStringRef(), binding.getContract());
}
struct Captures {
  Values unique;
  SmallVector<unsigned> positions;
  explicit Captures(ValueRange inputs) {
    llvm::DenseMap<Value, unsigned> seen;
    for (Value input : inputs) {
      auto [at, inserted] = seen.try_emplace(input, unique.size());
      positions.push_back(at->second);
      if (inserted)
        unique.push_back(input);
    }
  }
};

class Consumer {
  protocol_ir::ProtocolModuleOp owner;
  OpBuilder builder;
  SymbolTable symbols;
  uint64_t &remaining;
  std::optional<CapacityCause> *capacity;
  unsigned nextRegion = 0;
  bool valid = true;

  bool charge(uint64_t cost) {
    if (!valid)
      return false;
    if (cost > remaining) {
      if (capacity)
        *capacity =
            CapacityCause{WorkOwner::AlgorithmExpansion, cost, remaining};
      valid = false;
      return false;
    }
    remaining -= cost;
    return true;
  }
  func::FuncOp function(StringRef name, TypeRange inputs, TypeRange outputs,
                        bool region, Attribute origin = {}) {
    if (!charge(16 + inputs.size() + outputs.size()))
      return {};
    OpBuilder::InsertionGuard restore(builder);
    builder.setInsertionPointToEnd(&owner.getBody().front());
    Types scoped{runtime::ScopeType::get(builder.getContext())};
    append_range(scoped, inputs);
    auto result = func::FuncOp::create(
        builder, owner.getLoc(), name,
        builder.getFunctionType(
            scoped,
            {exec::OutcomeType::get(builder.getContext(), Types(outputs))}));
    result.setPrivate();
    result.setNoInline(true);
    if (region)
      result->setAttr("runtime.region", builder.getUnitAttr());
    else
      result->setAttr("runtime.origin", origin);
    symbols.insert(result);
    result.addEntryBlock();
    return result;
  }
  func::FuncOp outline(Block &source, ValueRange arguments, unsigned prefix,
                       const Captures &captures, TypeRange outputs,
                       bool scheduled, unsigned depth) {
    OpBuilder::InsertionGuard restore(builder);
    Types types(arguments.take_front(prefix).getTypes());
    append_range(types, ValueRange(captures.unique).getTypes());
    std::string name;
    do {
      name = "_numerical_region_" + std::to_string(nextRegion++);
    } while (symbols.lookup(name));
    auto result = function(name, types, outputs, true);
    if (!result)
      return {};
    IRMapping values;
    values.map(arguments.take_front(prefix),
               result.getArguments().slice(1, prefix));
    for (auto [index, position] : enumerate(captures.positions))
      values.map(arguments[prefix + index],
                 result.getArgument(1 + prefix + position));
    if (failed(block(source, result, values, outputs.size(), scheduled, depth)))
      return {};
    return result;
  }
  LogicalResult block(Block &source, func::FuncOp target, IRMapping values,
                      unsigned returned, bool scheduled, unsigned depth) {
    if (depth > 64)
      return failure();
    builder.setInsertionPointToEnd(&target.front());
    exec::ScopedExecutionBuilder control(builder, target);
    auto *cursor = source.empty() ? nullptr : &source.front();
    if (scheduled)
      cursor = cursor->getNextNode();
    while (cursor) {
      auto *after = cursor;
      auto parsed = readScheduledLoop(after, remaining);
      if (failed(parsed)) {
        if (capacity)
          *capacity = CapacityCause{WorkOwner::AlgorithmExpansion};
        return failure();
      }
      Operation *op = *parsed ? parsed->value().loop.getOperation() : cursor;
      if (!charge(48 +
                  8 * (uint64_t(op->getNumOperands()) + op->getNumResults())))
        return failure();
      if (!*parsed &&
          isa<scf::ForOp, UnrealizedConversionCastOp, arith::ConstantOp>(op))
        return failure();
      auto inputs = mapped(*parsed ? ValueRange(parsed->value().inputs)
                                   : op->getOperands(),
                           values);
      if (failed(inputs))
        return failure();
      if (isa<func::ReturnOp, local::LocalYieldOp, local::LocalConditionOp,
              scf::YieldOp>(op)) {
        if (cursor->getNextNode() || inputs->size() < returned)
          return failure();
        if (isa<func::ReturnOp>(op))
          control.returned(*inputs);
        else
          control.complete(ArrayRef(*inputs).take_front(returned));
        return success();
      }
      if (auto stop = dyn_cast<local::StopOp>(op)) {
        control.reject(stop.getReason(), stop.getSite());
        return success();
      }
      Values outputs;
      auto resultTypes = Types(op->getResultTypes());
      auto site = op->getAttrOfType<StringAttr>("site");
      if (!site)
        return failure();
      if (*parsed ||
          isa<local::LocalForOp, local::LocalIfOp, local::LocalMatchOp>(op)) {
        bool loop = *parsed || isa<local::LocalForOp>(op);
        unsigned count = *parsed ? parsed->value().states : op->getNumResults();
        resultTypes.resize(count);
        unsigned offset = loop ? 2 + count : 1;
        if (inputs->size() < offset)
          return failure();
        Captures captures(ArrayRef(*inputs).drop_front(offset));
        bool conditional =
            loop && !*parsed &&
            isa<local::LocalConditionOp>(op->getRegion(0).front().back());
        auto outlineBody = [&](unsigned index) {
          Block &body = op->getRegion(index).front();
          auto arguments =
              *parsed ? parsed->value().arguments : Values(body.getArguments());
          if (arguments.size() < captures.positions.size()) {
            valid = false;
            return func::FuncOp();
          }
          unsigned prefix = arguments.size() - captures.positions.size();
          Types results(resultTypes);
          if (conditional)
            results.insert(results.begin(), builder.getI1Type());
          return outline(body, arguments, prefix, captures, results,
                         bool(*parsed), depth + 1);
        };
        if (loop)
          outputs = control.loop((*inputs)[0], (*inputs)[1],
                                 ArrayRef(*inputs).slice(2, count),
                                 captures.unique, resultTypes, conditional,
                                 site.getValue(), outlineBody);
        else if (isa<local::LocalIfOp>(op))
          outputs =
              control.conditional(inputs->front(), captures.unique, resultTypes,
                                  site.getValue(), outlineBody);
        else {
          SmallVector<std::string> alternatives;
          for (Attribute item : op->getAttrOfType<ArrayAttr>("alternatives"))
            alternatives.push_back(cast<StringAttr>(item).str());
          outputs = control.match(inputs->front(), captures.unique, resultTypes,
                                  alternatives, site.getValue(), outlineBody);
        }
      } else {
        StringRef name;
        if (bound(op))
          name = exec::ApplyOp::getOperationName();
        else if (isa<local::BoolConstantOp>(op))
          name = exec::BooleanOp::getOperationName();
        else if (isa<local::VariantInjectOp>(op))
          name = exec::VariantOp::getOperationName();
        else
          return failure();
        outputs = control.invoke(name, resultTypes, control.scoped(*inputs),
                                 op->getAttrs());
      }
      if (!valid || outputs.size() != resultTypes.size())
        return failure();
      values.map(op->getResults().take_front(outputs.size()), outputs);
      cursor = *parsed ? after : cursor->getNextNode();
    }
    return failure();
  }

public:
  Consumer(protocol_ir::ProtocolModuleOp owner, uint64_t &remaining,
           std::optional<CapacityCause> *capacity)
      : owner(owner), builder(owner.getContext()), symbols(owner),
        remaining(remaining), capacity(capacity) {}
  LogicalResult run(func::FuncOp source) {
    auto target = function(source.getSymName(), source.getArgumentTypes(),
                           source.getResultTypes(), false,
                           source->getAttr("logical_origin"));
    if (!target)
      return failure();
    IRMapping values;
    values.map(source.getArguments(), target.getArguments().drop_front());
    return block(source.front(), target, values, source.getNumResults(), false,
                 0);
  }
};

// Separate actual-candidate reader. It does not call Consumer, copy candidate
// instructions, regenerate CFG, or obtain body mappings from the producer.
class Reader {
  const ScopedCandidate &candidate;
  CandidatePorts ports;
  uint64_t &remaining;
  bool capacity = false;
  llvm::DenseSet<Block *> visited;
  bool charge(uint64_t cost) {
    if (cost > remaining) {
      capacity = true;
      remaining = 0;
      return false;
    }
    remaining -= cost;
    return true;
  }

public:
  Reader(const ScopedCandidate &candidate, uint64_t &remaining)
      : candidate(candidate), ports(&candidate), remaining(remaining) {}
  bool exhausted() const { return capacity; }
  unsigned bodies() const { return visited.size(); }
  bool block(Block &source, Block &target, IRMapping values, unsigned returned,
             bool scheduled = false, unsigned depth = 0) {
    if (depth > 64 || !visited.insert(&target).second)
      return false;
    auto *at = &source.front();
    auto *actual = ports.first(&target);
    if (scheduled)
      at = at->getNextNode();
    while (at) {
      if (!actual || !charge(1 + at->getNumOperands() + at->getNumResults()))
        return false;
      auto *after = at;
      auto parsed = readScheduledLoop(after, remaining);
      if (failed(parsed)) {
        capacity = true;
        return false;
      }
      Operation *op = *parsed ? parsed->value().loop.getOperation() : at;
      if (!*parsed &&
          isa<scf::ForOp, UnrealizedConversionCastOp, arith::ConstantOp>(op))
        return false;
      auto inputs = mapped(*parsed ? ValueRange(parsed->value().inputs)
                                   : op->getOperands(),
                           values);
      if (failed(inputs))
        return false;
      if (isa<func::ReturnOp, local::LocalYieldOp, local::LocalConditionOp,
              scf::YieldOp>(op)) {
        bool root = isa<func::ReturnOp>(op);
        if ((root ? !isa<exec::ReturnOp>(actual)
                  : !isa<exec::CompleteOp>(actual)) ||
            !actual->getAttrs().empty() || inputs->size() < returned ||
            ports.inputs(actual) !=
                ValueRange(ArrayRef(*inputs).take_front(returned)) ||
            !ports.outputs(actual).empty() || ports.bodies(actual) ||
            ports.next(actual) || at->getNextNode())
          return false;
        return true;
      }
      auto site = op->getAttrOfType<StringAttr>("site");
      if (!site || actual->getAttr("site") != site)
        return false;
      if (auto stop = dyn_cast<local::StopOp>(op))
        return isa<exec::RejectOp>(actual) &&
               actual->getAttrDictionary() == stop->getAttrDictionary() &&
               ports.inputs(actual).empty() && ports.outputs(actual).empty() &&
               !ports.next(actual) && !at->getNextNode();
      unsigned count = *parsed ? parsed->value().states : op->getNumResults();
      if (ports.outputs(actual).getTypes() !=
          op->getResults().take_front(count).getTypes())
        return false;
      if (*parsed ||
          isa<local::LocalForOp, local::LocalIfOp, local::LocalMatchOp>(op)) {
        bool loop = *parsed || isa<local::LocalForOp>(op);
        if ((loop && !isa<exec::RangeOp>(actual)) ||
            (isa<local::LocalIfOp>(op) && !isa<exec::TestOp>(actual)) ||
            (isa<local::LocalMatchOp>(op) && !isa<exec::MatchOp>(actual)))
          return false;
        unsigned offset = loop ? 2 + count : 1;
        if (inputs->size() < offset)
          return false;
        Captures captures(ArrayRef(*inputs).drop_front(offset));
        Values expected(ArrayRef(*inputs).take_front(offset));
        append_range(expected, captures.unique);
        auto *step = candidate.get(actual);
        bool conditional =
            loop && !*parsed &&
            isa<local::LocalConditionOp>(op->getRegion(0).front().back());
        if (!step || step->conditional != conditional ||
            ports.inputs(actual) != ValueRange(expected) ||
            ports.bodies(actual) != op->getNumRegions())
          return false;
        if (isa<local::LocalMatchOp>(op) &&
            actual->getAttr("alternatives") != op->getAttr("alternatives"))
          return false;
        for (unsigned index = 0; index != op->getNumRegions(); ++index) {
          auto &body = op->getRegion(index).front();
          Values args =
              *parsed ? parsed->value().arguments : Values(body.getArguments());
          if (args.size() < captures.positions.size())
            return false;
          unsigned prefix = args.size() - captures.positions.size();
          auto *out = ports.body(actual, index);
          auto formals = ports.arguments(out);
          Types types(ValueRange(args).take_front(prefix).getTypes());
          append_range(types, ValueRange(captures.unique).getTypes());
          if (formals.getTypes() != TypeRange(types))
            return false;
          IRMapping nested;
          nested.map(ValueRange(args).take_front(prefix),
                     formals.take_front(prefix));
          for (auto [position, selected] : enumerate(captures.positions))
            nested.map(args[prefix + position], formals[prefix + selected]);
          if (!block(body, *out, nested, count + unsigned(conditional),
                     bool(*parsed), depth + 1))
            return false;
        }
      } else {
        bool primitive = bound(op);
        if ((primitive && !isa<exec::ApplyOp>(actual)) ||
            (isa<local::BoolConstantOp>(op) && !isa<exec::BooleanOp>(actual)) ||
            (isa<local::VariantInjectOp>(op) &&
             !isa<exec::VariantOp>(actual)) ||
            (!primitive &&
             !isa<local::BoolConstantOp, local::VariantInjectOp>(op)) ||
            ports.inputs(actual) != ValueRange(*inputs) ||
            ports.bodies(actual) ||
            actual->getAttrDictionary() != op->getAttrDictionary())
          return false;
      }
      values.map(op->getResults().take_front(count), ports.outputs(actual));
      at = *parsed ? after : at->getNextNode();
      actual = ports.next(actual);
    }
    return false;
  }
};
} // namespace

OwningOpRef<mlir::ModuleOp>
consumeSchedule(mlir::ModuleOp source, uint64_t &remaining,
                std::optional<CapacityCause> *capacity) {
  auto function = readScheduledFunction(source);
  if (!function || !chargeCopy(source, remaining, capacity))
    return {};
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(result->getBody(), result->getBody()->end());
  auto owner = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(), protocol_ir::Profile::Exec);
  owner.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&owner.getBody().front());
  for (auto binding : source.getBody()->getOps<runtime::BindingOp>())
    builder.clone(*binding.getOperation());
  if (failed(Consumer(owner, remaining, capacity).run(function)) ||
      failed(verifyRecipeOutput(*result)))
    return {};
  return result;
}

LogicalResult verifyScheduleLowering(mlir::ModuleOp schedule,
                                     mlir::ModuleOp candidate, uint64_t *shared,
                                     finite::VerificationResult *reported) {
  if (reported)
    *reported = {finite::VerificationStatus::Mismatch,
                 "schedule lowering differs"};
  auto function = readScheduledFunction(schedule);
  if (!function || failed(verifyRecipeOutput(candidate)))
    return failure();
  auto owner =
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  auto target = SymbolTable(owner).lookup<func::FuncOp>(function.getSymName());
  if (!target ||
      target->getAttr("runtime.origin") !=
          function->getAttr("logical_origin") ||
      target->hasAttr("runtime.region") ||
      target.getNumArguments() != function.getNumArguments() + 1 ||
      target.getArgumentTypes().drop_front() != function.getArgumentTypes() ||
      cast<exec::OutcomeType>(target.getResultTypes().front()).getPayload() !=
          function.getResultTypes())
    return failure();
  auto before = schedule.getBody()->getOps<runtime::BindingOp>();
  auto after = owner.getBody().front().getOps<runtime::BindingOp>();
  if (std::distance(before.begin(), before.end()) !=
      std::distance(after.begin(), after.end()))
    return failure();
  for (auto [a, b] : zip(before, after))
    if (!OperationEquivalence::isEquivalentTo(
            a, b, OperationEquivalence::IgnoreLocations))
      return failure();
  for (auto function : owner.getBody().front().getOps<func::FuncOp>())
    if (function != target && !function->hasAttr("runtime.region"))
      return failure();
  auto view = ScopedCandidate::read(owner);
  if (!view) {
    consumeError(view.takeError());
    return failure();
  }
  IRMapping values;
  values.map(function.getArguments(), target.getArguments().drop_front());
  uint64_t standalone = 1000000;
  Reader reader(**view, shared ? *shared : standalone);
  bool valid = reader.block(function.front(), target.front(), values,
                            function.getNumResults()) &&
               reader.bodies() == (*view)->size();
  if (reported) {
    if (valid)
      *reported = {finite::VerificationStatus::Verified, {}};
    else if (reader.exhausted())
      *reported = {finite::VerificationStatus::RequiredCapacity,
                   "schedule checking capacity",
                   CapacityCause{WorkOwner::AlgorithmChecking}};
  }
  return success(valid);
}
} // namespace zkc::kernel
