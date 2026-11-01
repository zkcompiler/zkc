#include "FrontierVerification.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(),
                           "computation-frontier-correspondence", reason);
}
class CheckingWork {
  uint64_t &remaining;
  std::optional<CapacityCause> &capacity;

public:
  CheckingWork(uint64_t &remaining, std::optional<CapacityCause> &capacity)
      : remaining(remaining), capacity(capacity) {
    capacity.reset();
  }
  bool exhausted() const { return capacity.has_value(); }
  bool charge(uint64_t cost) {
    if (exhausted())
      return false;
    if (cost > remaining) {
      capacity = CapacityCause{WorkOwner::AlgorithmChecking, cost, remaining};
      return false;
    }
    remaining -= cost;
    return true;
  }
  bool charge(Operation *op) {
    return charge(1 + uint64_t(op->getNumOperands()) + op->getNumResults() +
                  op->getAttrs().size() + op->getNumRegions());
  }
  bool withinDepth(unsigned depth) {
    if (exhausted())
      return false;
    if (depth <= 64)
      return true;
    // A depth refusal is not a failed request against the work allowance.
    capacity = CapacityCause{WorkOwner::AlgorithmChecking};
    return false;
  }
};
bool prefix(TypeRange before, TypeRange after) {
  return before.size() <= after.size() &&
         llvm::equal(before, after.take_front(before.size()));
}

bool outcomePrefix(TypeRange before, TypeRange after) {
  if (before.size() != 1 || after.size() != 1)
    return false;
  auto a = dyn_cast<exec::OutcomeType>(before.front());
  auto b = dyn_cast<exec::OutcomeType>(after.front());
  return a && b && prefix(a.getPayload(), b.getPayload());
}
Block *payloadBlock(exec::ComputeOp call) {
  if (!call || !call.getOutcome().hasOneUse())
    return nullptr;
  auto dispatch =
      dyn_cast<exec::DispatchOp>(*call.getOutcome().getUsers().begin());
  if (!dispatch || dispatch->getPrevNode() != call.getOperation() ||
      dispatch.getReturned() == dispatch.getStopped() ||
      dispatch.getReturned()->getParent() != call->getParentRegion() ||
      dispatch.getReturned()->getSinglePredecessor() != call->getBlock() ||
      dispatch.getReturned()->getArgumentTypes() !=
          call.getOutcome().getType().getPayload())
    return nullptr;
  return dispatch.getReturned();
}

// The same ordered structural pattern as AlgorithmVerification::unchanged,
// with narrow, explicitly enumerated exceptions. Locations are not semantic.
class ContextReader {
  CheckingWork &work;

public:
  llvm::DenseMap<Operation *, Operation *> pairs;
  llvm::DenseSet<Operation *> flexibleFunctions, flexibleCalls, flexibleReturns;
  llvm::DenseSet<Operation *> skipBodies, appendedDeclarations,
      flexibleOutcomes;
  llvm::DenseSet<Block *> flexibleBlocks;
  llvm::DenseMap<Operation *, Attribute> callees;

  explicit ContextReader(CheckingWork &work) : work(work) {}
  LogicalResult operation(Operation *before, Operation *after, IRMapping values,
                          unsigned depth = 0) {
    if (!work.withinDepth(depth) || !work.charge(before) || !work.charge(after))
      return refuse(after, "context inspection limit");
    if (before->getName() != after->getName() ||
        before->getNumRegions() != after->getNumRegions() ||
        before->getNumSuccessors() != after->getNumSuccessors())
      return refuse(after, "operation identity or structured control changed");
    for (auto [source, target] :
         zip(before->getSuccessors(), after->getSuccessors()))
      if (values.lookupOrNull(source) != target)
        return refuse(after, "ordered control successor changed");
    pairs[before] = after;
    NamedAttrList expected(before->getAttrs()), actual(after->getAttrs());
    if (auto replacement = callees.find(before); replacement != callees.end())
      expected.set("callee", replacement->second);
    bool function = flexibleFunctions.contains(before);
    if (function) {
      auto a = before->getAttrOfType<TypeAttr>("function_type");
      auto b = after->getAttrOfType<TypeAttr>("function_type");
      auto x = a ? dyn_cast<FunctionType>(a.getValue()) : FunctionType();
      auto y = b ? dyn_cast<FunctionType>(b.getValue()) : FunctionType();
      if (!x || !y)
        return refuse(after, "missing function interface");
      uint64_t cost = uint64_t(x.getNumInputs()) + x.getNumResults() +
                      y.getNumInputs() + y.getNumResults();
      if (!work.charge(cost))
        return refuse(after, "function interface inspection limit");
      if (!prefix(x.getInputs(), y.getInputs()) ||
          !(prefix(x.getResults(), y.getResults()) ||
            outcomePrefix(x.getResults(), y.getResults())))
        return refuse(after, "original function interface changed");
      expected.erase("function_type");
      actual.erase("function_type");
    }
    bool call = flexibleCalls.contains(before);
    if (expected.getDictionary(before->getContext()) !=
        actual.getDictionary(after->getContext()))
      return refuse(after, "attributes, guard, declaration or site changed");
    bool returned = flexibleReturns.contains(before);
    if ((call || returned)
            ? before->getNumOperands() > after->getNumOperands()
            : before->getNumOperands() != after->getNumOperands())
      return refuse(after, "original operand interface changed");
    for (auto [operand, candidate] :
         zip(before->getOperands(), after->getOperands()))
      if (values.lookupOrNull(operand) != candidate)
        return refuse(after, "ordered operand or original return changed");
    if (flexibleOutcomes.contains(before)
            ? !outcomePrefix(before->getResultTypes(), after->getResultTypes())
            : (call ? !prefix(before->getResultTypes(), after->getResultTypes())
                    : before->getResultTypes() != after->getResultTypes()))
      return refuse(after, "original result interface changed");
    if (flexibleOutcomes.contains(before) &&
        isa<exec::ReturnOp, exec::FailureOp>(after)) {
      auto parent = after->getParentOfType<func::FuncOp>();
      if (!parent || after->getResultTypes() != parent.getResultTypes())
        return refuse(after,
                      "scoped completion type differs from its function");
    }
    if (skipBodies.contains(before))
      return success();
    for (auto [source, target] :
         zip(before->getRegions(), after->getRegions())) {
      if (source.getBlocks().size() != target.getBlocks().size())
        return refuse(after, "region shape changed");
      // CFG block order need not be dominance order. Establish the complete
      // positional correspondence before checking any operation, including
      // successor operands, failure continuations and loop backedges. This
      // grants no rewrite: every paired definition is checked below.
      IRMapping inner(values);
      for (auto [a, b] : zip(source, target)) {
        uint64_t cost = 1 + uint64_t(a.getNumArguments()) + b.getNumArguments();
        if (!work.charge(cost))
          return refuse(after, "block interface inspection limit");
        bool extensible = flexibleBlocks.contains(&a);
        if (extensible ? !prefix(a.getArgumentTypes(), b.getArgumentTypes())
                       : a.getArgumentTypes() != b.getArgumentTypes())
          return refuse(after, "block interface changed");
        inner.map(&a, &b);
        inner.map(a.getArguments(),
                  b.getArguments().take_front(a.getNumArguments()));
        auto cursor = b.begin();
        for (auto &op : a) {
          if (cursor == b.end() || op.getNumResults() > cursor->getNumResults())
            return refuse(after, "missing ordered definition");
          uint64_t cost = 1 + uint64_t(op.getNumResults());
          if (!work.charge(cost))
            return refuse(after, "definition correspondence inspection limit");
          inner.map(op.getResults(),
                    cursor->getResults().take_front(op.getNumResults()));
          ++cursor;
        }
      }
      for (auto [a, b] : zip(source, target)) {
        auto cursor = b.begin();
        for (auto &op : a) {
          if (cursor == b.end())
            return refuse(after, "missing ordered operation");
          auto *candidate = &*cursor++;
          if (failed(operation(&op, candidate, inner, depth + 1)))
            return failure();
        }
        // Normalization may append only the explicitly checked fresh units,
        // in the protocol module's declaration block.
        for (; cursor != b.end(); ++cursor)
          if (!work.charge(&*cursor) || !appendedDeclarations.erase(&*cursor))
            return refuse(&*cursor, "extra ordered operation or declaration");
      }
    }
    return success();
  }
};

struct Step {
  func::FuncOp wrapper;
  protocol_ir::LocalCallOp invocation;
  exec::ComputeOp call;
  exec::ReturnOp returned;
  func::FuncOp entry;
  llvm::DenseSet<Operation *> generated;
};
struct Producer {
  Operation *operation;
  SmallVector<uint64_t> inputs, outputs;
  Operation *cut;
};
size_t fingerprint(Operation *op, ArrayRef<uint64_t> inputs) {
  return hash_combine(
      op->getName().getStringRef(), op->getAttrDictionary(),
      hash_combine_range(op->result_type_begin(), op->result_type_end()),
      hash_combine_range(inputs.begin(), inputs.end()));
}
struct BlockFrontier {
  llvm::DenseMap<Value, uint64_t> outer;
  SmallVector<Producer> producers;
  llvm::DenseMap<size_t, SmallVector<size_t>> producerIndex;
  llvm::DenseMap<uint64_t, SmallVector<uint64_t>> packs;
};

class FrontierReader {
  mlir::ModuleOp before, after;
  CheckingWork &work;
  ContextReader context;
  SmallVector<Step> steps;
  llvm::DenseMap<Block *, BlockFrontier> frontiers;
  llvm::DenseSet<uint64_t> generatedValues, projectedValues, extraValues;
  uint64_t nextValue = 1;

  uint64_t anchor(Value value, BlockFrontier &frontier) {
    auto [found, inserted] = frontier.outer.try_emplace(value, 0);
    if (inserted)
      found->second = nextValue++;
    return found->second;
  }
  bool signature(Operation *source, Operation *target,
                 ArrayRef<uint64_t> expected, ArrayRef<uint64_t> actual) {
    return source->getName() == target->getName() &&
           source->getAttrDictionary() == target->getAttrDictionary() &&
           source->getResultTypes() == target->getResultTypes() &&
           expected == actual && !target->getNumRegions() &&
           !target->getNumSuccessors();
  }
  FailureOr<SmallVector<uint64_t>>
  operands(Operation *op, const llvm::DenseMap<Value, uint64_t> &values) {
    if (!work.charge(op))
      return failure();
    SmallVector<uint64_t> result;
    for (Value value : op->getOperands()) {
      auto found = values.find(value);
      if (found == values.end())
        return failure();
      result.push_back(found->second);
    }
    return result;
  }
  // A generated instruction and a concrete occurrence can have identical
  // signatures. Greedily consuming the concrete occurrence as generated work
  // would reject a valid deletion. Explore only that local ambiguity, charging
  // copied state and every attempted instruction; never replay an IR producer.
  bool body(Step &source, protocol_ir::LocalCallOp invocation,
            Block::iterator position, Block::iterator cursor,
            func::ReturnOp sourceReturn, func::ReturnOp actualReturn,
            llvm::DenseMap<Value, uint64_t> &original,
            llvm::DenseMap<Value, uint64_t> &actual, BlockFrontier &frontier,
            unsigned depth = 0) {
    if (!work.withinDepth(depth))
      return false;
    for (; &*position != sourceReturn.getOperation(); ++position) {
      auto &op = *position;
      if (op.getNumRegions() || op.getNumSuccessors())
        return false;
      auto inputs = operands(&op, original);
      if (failed(inputs))
        return false;
      SmallVector<uint64_t> reused;
      auto bucket = frontier.producerIndex.find(fingerprint(&op, *inputs));
      if (source.generated.contains(&op) &&
          bucket != frontier.producerIndex.end())
        for (auto index : bucket->second) {
          auto &producer = frontier.producers[index];
          if (!work.charge(producer.operation))
            return false;
          if (producer.cut != invocation.getOperation() &&
              signature(&op, producer.operation, *inputs, producer.inputs)) {
            reused = producer.outputs;
            break;
          }
        }
      // A checked polynomial projection may use the exact coordinate of an
      // already retained pack. This forwards an existing scalar; it never
      // deletes or coalesces its concrete producer or the pack itself.
      if (auto projection = dyn_cast<data::ArrayAtOp>(op);
          projection && source.generated.contains(&op)) {
        auto found = frontier.packs.find(inputs->front());
        auto index = projection.getIndexAttr().getInt();
        if (found != frontier.packs.end() && index >= 0 &&
            uint64_t(index) < found->second.size()) {
          reused = {found->second[index]};
          projectedValues.insert(reused.front());
        }
      }
      auto *target = &*cursor;
      bool retained = false;
      if (target != actualReturn.getOperation()) {
        auto targetInputs = operands(target, actual);
        if (work.exhausted())
          return false;
        retained = succeeded(targetInputs) &&
                   signature(&op, target, *inputs, *targetInputs);
      }
      auto retain = [&] {
        SmallVector<uint64_t> outputs;
        for (auto [a, b] : zip(op.getResults(), target->getResults())) {
          auto id = nextValue++;
          original[a] = id;
          actual[b] = id;
          outputs.push_back(id);
        }
        if (isa<data::ArrayFromElementsOp>(op))
          frontier.packs[outputs.front()] = *inputs;
        if (source.generated.contains(&op)) {
          frontier.producerIndex[fingerprint(target, *inputs)].push_back(
              frontier.producers.size());
          frontier.producers.push_back({target, *inputs, outputs, invocation});
          for (auto id : outputs)
            generatedValues.insert(id);
        }
      };
      if (retained && !reused.empty()) {
        uint64_t cost = 1 + uint64_t(original.size()) + actual.size() +
                        projectedValues.size();
        for (const auto &pack : frontier.packs)
          cost += 1 + pack.second.size();
        if (!work.charge(cost))
          return false;
        auto savedOriginal = original, savedActual = actual;
        auto savedProducers = frontier.producers.size();
        auto savedPacks = frontier.packs;
        auto savedProjected = projectedValues;
        retain();
        if (body(source, invocation, std::next(position), std::next(cursor),
                 sourceReturn, actualReturn, original, actual, frontier,
                 depth + 1))
          return true;
        // Capacity is terminal, including in a speculative retention branch.
        // Do not probe another path or replace the first failed request.
        if (work.exhausted())
          return false;
        for (auto &producer : ArrayRef<Producer>(frontier.producers)
                                  .drop_front(savedProducers)) {
          frontier
              .producerIndex[fingerprint(producer.operation, producer.inputs)]
              .pop_back();
          for (auto id : producer.outputs)
            generatedValues.erase(id);
        }
        frontier.producers.resize(savedProducers);
        frontier.packs = std::move(savedPacks);
        projectedValues = std::move(savedProjected);
        original = std::move(savedOriginal);
        actual = std::move(savedActual);
      } else if (retained) {
        retain();
        ++cursor;
        continue;
      }
      if (reused.size() != op.getNumResults() || reused.empty())
        return false; // Concrete instructions always require exact retention.
      for (auto [result, id] : zip(op.getResults(), reused))
        original[result] = id;
    }
    if (&*cursor != actualReturn.getOperation())
      return false;
    auto expected = operands(sourceReturn, original);
    if (failed(expected))
      return false;
    auto returned = operands(actualReturn, actual);
    return succeeded(returned) && expected->size() <= returned->size() &&
           llvm::equal(*expected, ArrayRef<uint64_t>(*returned).take_front(
                                      expected->size()));
  }
  LogicalResult step(Step source) {
    auto wrapper =
        dyn_cast_or_null<func::FuncOp>(context.pairs.lookup(source.wrapper));
    auto invocation = dyn_cast_or_null<protocol_ir::LocalCallOp>(
        context.pairs.lookup(source.invocation));
    auto call =
        dyn_cast_or_null<exec::ComputeOp>(context.pairs.lookup(source.call));
    auto entry =
        dyn_cast_or_null<func::FuncOp>(context.pairs.lookup(source.entry));
    auto signature =
        wrapper ? protocol::scopedDataSignature(wrapper) : FunctionType();
    auto *payload = payloadBlock(call);
    if (!signature || !invocation || !entry || !payload ||
        !entry.getBody().hasOneBlock() || entry.front().empty() ||
        !llvm::equal(signature.getInputs(), invocation.getOperandTypes()) ||
        !llvm::equal(signature.getResults(), invocation.getResultTypes()) ||
        wrapper.front().getArgumentTypes() != wrapper.getArgumentTypes() ||
        !llvm::equal(entry.getArgumentTypes(), call.getInputs().getTypes()) ||
        !llvm::equal(entry.getResultTypes(), payload->getArgumentTypes()) ||
        entry.front().getArgumentTypes() != entry.getArgumentTypes())
      return refuse(after,
                    "actual wrapper or entry interface differs from call");
    SymbolTableCollection symbols;
    if (call.resolveCallee(symbols) != entry)
      return refuse(call, "actual numerical callee changed");
    auto &frontier = frontiers[source.invocation->getBlock()];
    llvm::DenseMap<Value, uint64_t> original, actual;
    // Read both boundaries. Original inner operands need not be identity
    // forwarding, but their actual original prefix must remain exact.
    auto input = [&](Value value) -> uint64_t {
      auto argument = dyn_cast<BlockArgument>(value);
      if (!argument || argument.getOwner() != &wrapper.getBody().front() ||
          !argument.getArgNumber() ||
          argument.getArgNumber() > invocation.getNumOperands())
        return 0;
      return anchor(invocation.getOperand(argument.getArgNumber() - 1),
                    frontier);
    };
    for (auto [argument, value] : zip(entry.getArguments(), call.getInputs())) {
      auto id = input(value);
      if (!id)
        return refuse(call, "actual inner input is not a wrapper port");
      actual[argument] = id;
      if (argument.getArgNumber() >= source.entry.getNumArguments() &&
          argument.use_empty())
        return refuse(call, "unused appended numerical input");
    }
    for (auto [argument, value] :
         zip(source.entry.getArguments(), source.call.getInputs())) {
      auto mapped = dyn_cast<BlockArgument>(value);
      if (!mapped || mapped.getOwner() != &source.wrapper.getBody().front() ||
          !mapped.getArgNumber() ||
          mapped.getArgNumber() > source.invocation.getNumOperands())
        return refuse(source.call, "source inner input is not a wrapper port");
      original[argument] =
          anchor(invocation.getOperand(mapped.getArgNumber() - 1), frontier);
    }
    for (unsigned i = source.invocation.getNumOperands();
         i < invocation.getNumOperands(); ++i) {
      auto result = dyn_cast<OpResult>(invocation.getOperand(i));
      if (!result || result.getOwner()->getBlock() != invocation->getBlock() ||
          !result.getOwner()->isBeforeInBlock(invocation) ||
          !frontier.outer.lookup(result))
        return refuse(invocation,
                      "appended import is not an exact earlier output");
      extraValues.insert(frontier.outer.lookup(result));
      if (wrapper.getArgument(i + 1).use_empty())
        return refuse(invocation, "unused appended import");
    }
    auto sourceReturn = dyn_cast<func::ReturnOp>(source.entry.front().back());
    auto actualReturn = dyn_cast<func::ReturnOp>(entry.front().back());
    if (!sourceReturn || !actualReturn ||
        sourceReturn->getAttrDictionary() !=
            actualReturn->getAttrDictionary() ||
        actualReturn.getOperandTypes() != entry.getResultTypes())
      return refuse(entry, "numerical return interface changed");
    if (!body(source, invocation, source.entry.front().begin(),
              entry.front().begin(), sourceReturn, actualReturn, original,
              actual, frontier)) {
      return refuse(entry, "numerical occurrence, exact reuse, return identity "
                           "or inspection limit");
    }
    auto expected = operands(sourceReturn, original);
    if (failed(expected))
      return refuse(entry, "original numerical return identity changed");
    auto returned = operands(actualReturn, actual);
    if (failed(returned) || expected->size() > returned->size() ||
        !llvm::equal(*expected, ArrayRef<uint64_t>(*returned).take_front(
                                    expected->size())))
      return refuse(entry, "original numerical return identity changed");
    for (auto id : ArrayRef<uint64_t>(*returned).drop_front(expected->size()))
      extraValues.insert(id);
    auto wrapperReturn =
        dyn_cast_or_null<exec::ReturnOp>(context.pairs.lookup(source.returned));
    if (!wrapperReturn ||
        wrapperReturn.getOperandTypes() != signature.getResults())
      return refuse(wrapper, "actual wrapper return interface changed");
    for (auto [value, result] :
         zip(wrapperReturn.getValues(), invocation.getResults())) {
      // Preserve the distinction between a wrapper input and a numerical
      // result coordinate. ContextReader already fixes every original return
      // operand, including duplicate aliases and the order of mixed returns.
      uint64_t id = input(value);
      if (auto coordinate = dyn_cast<BlockArgument>(value);
          coordinate && coordinate.getOwner() == payload &&
          coordinate.getArgNumber() < returned->size())
        id = (*returned)[coordinate.getArgNumber()];
      if (!id)
        return refuse(wrapper,
                      "actual wrapper return is not a wrapper input or "
                      "numerical coordinate");
      if (result.getResultNumber() >= source.invocation.getNumResults())
        extraValues.insert(id);
      frontier.outer[result] = id;
    }
    return success();
  }

public:
  FrontierReader(mlir::ModuleOp before, mlir::ModuleOp after,
                 CheckingWork &work)
      : before(before), after(after), work(work), context(work) {}
  LogicalResult run(ArrayRef<FrontierNormalizationOrigin> origins) {
    if (!hasSingleElement(*before.getBody()) ||
        !hasSingleElement(*after.getBody()))
      return refuse(after, "module shape changed");
    auto owner =
        dyn_cast<protocol_ir::ProtocolModuleOp>(before.getBody()->front());
    if (!owner || !owner.getBody().hasOneBlock())
      return refuse(after, "expected one protocol owner");
    llvm::DenseMap<Operation *, llvm::DenseSet<Operation *>> generated;
    for (auto origin : origins) {
      auto unit =
          origin.entry
              ? dyn_cast_or_null<mlir::ModuleOp>(origin.entry->getParentOp())
              : mlir::ModuleOp();
      if (!unit || unit->getParentOp() != owner.getOperation() ||
          !origin.entry.getBody().hasOneBlock() || !work.charge(origin.entry) ||
          !generated.try_emplace(origin.entry).second)
        return refuse(after,
                      "invalid or duplicate checked normalization entry");
      auto &membership = generated[origin.entry];
      for (auto *op : origin.polynomialGenerated)
        if (!op || !work.charge(op) ||
            op->getBlock() != &origin.entry.front() ||
            op->hasTrait<OpTrait::IsTerminator>() || op->getNumRegions() ||
            op->getNumSuccessors() || !op->getNumResults() ||
            !mathematical::isTotal(op) || isa<func::CallOp>(op) ||
            !membership.insert(op).second)
          return refuse(after, "invalid checked generated occurrence");
    }
    llvm::DenseSet<Attribute> wrappers;
    llvm::DenseMap<Attribute, std::pair<Attribute, Attribute>> wrapperOrigins;
    for (auto record :
         owner.getBody().front().getOps<protocol_ir::ProjectionOp>())
      for (auto item : record.getCalculations()) {
        if (!work.charge(uint64_t(1)))
          return refuse(after, "projection inspection limit");
        auto dictionary = dyn_cast<DictionaryAttr>(item);
        auto callee = dictionary ? dictionary.get("callee") : Attribute();
        auto participant =
            dictionary ? dictionary.getAs<FlatSymbolRefAttr>("participant")
                       : FlatSymbolRefAttr();
        auto site =
            dictionary ? dictionary.getAs<StringAttr>("site") : StringAttr();
        if (!isa_and_nonnull<FlatSymbolRefAttr>(callee) || !participant ||
            !site ||
            !wrapperOrigins
                 .try_emplace(callee, std::make_pair(participant, site))
                 .second)
          return refuse(after, "invalid calculation wrapper reference");
        wrappers.insert(callee);
      }
    llvm::DenseMap<Attribute, unsigned> uses;
    llvm::DenseMap<Operation *, unsigned> entryUses, wrapperCalls;
    SmallVector<protocol_ir::LocalCallOp> invocations;
    SymbolTableCollection symbols;
    auto walk = owner.walk([&](Operation *op) {
      if (!work.charge(op))
        return WalkResult::interrupt();
      if (auto invocation = dyn_cast<protocol_ir::LocalCallOp>(op)) {
        ++uses[invocation.getCalleeAttr()];
        invocations.push_back(invocation);
      }
      if (auto call = dyn_cast<exec::ComputeOp>(op)) {
        if (auto function = call->getParentOfType<func::FuncOp>())
          ++wrapperCalls[function];
        if (auto entry = call.resolveCallee(symbols))
          ++entryUses[entry];
      }
      return WalkResult::advance();
    });
    if (walk.wasInterrupted())
      return refuse(after, "selection inspection limit");
    SymbolTable declarations(owner);
    llvm::DenseSet<Operation *> selectedEntries;
    for (auto invocation : invocations) {
      if (!wrappers.contains(invocation.getCalleeAttr()))
        continue;
      auto wrapper = declarations.lookup<func::FuncOp>(invocation.getCallee());
      auto participant =
          invocation->getParentOfType<protocol_ir::ParticipantOp>();
      auto recorded = wrapperOrigins.lookup(invocation.getCalleeAttr());
      if (!wrapper || wrapper.empty() ||
          uses.lookup(invocation.getCalleeAttr()) != 1 || !participant ||
          recorded.first !=
              FlatSymbolRefAttr::get(participant.getSymNameAttr()) ||
          recorded.second != invocation.getSiteAttr())
        return refuse(
            after, "calculation wrapper is not uniquely participant-invoked");
      if (wrapper.getBody().front().empty())
        return refuse(after, "empty calculation wrapper");
      auto call = dyn_cast<exec::ComputeOp>(wrapper.front().front());
      if (!call)
        continue; // Guard-only wrappers remain exactly unchanged.
      auto entry = call.resolveCallee(symbols);
      auto signature = protocol::scopedDataSignature(wrapper);
      auto *payload = payloadBlock(call);
      if (!signature || !payload || !entry || !generated.count(entry) ||
          entryUses.lookup(entry) != 1 || wrapperCalls.lookup(wrapper) != 1 ||
          entry.front().empty() ||
          !llvm::equal(signature.getInputs(), invocation.getOperandTypes()) ||
          !llvm::equal(signature.getResults(), invocation.getResultTypes()) ||
          !llvm::equal(entry.getArgumentTypes(), call.getInputs().getTypes()) ||
          !llvm::equal(entry.getResultTypes(), payload->getArgumentTypes()) ||
          !selectedEntries.insert(entry).second)
        return refuse(after,
                      "missing checked origin or nonunique numerical entry");
      exec::ReturnOp returned;
      for (auto &block : wrapper.getBody())
        for (auto &op : block) {
          if (!work.charge(&op))
            return refuse(after, "wrapper packaging inspection limit");
          if (auto result = dyn_cast<exec::ReturnOp>(op)) {
            if (returned)
              return refuse(after, "calculation wrapper has multiple returns");
            returned = result;
          }
          if (isa<exec::ReturnOp, exec::FailureOp>(op))
            context.flexibleOutcomes.insert(&op);
        }
      if (!returned)
        return refuse(after, "calculation wrapper has no return");
      steps.push_back({wrapper, invocation, call, returned, entry,
                       generated.lookup(entry)});
      context.flexibleFunctions.insert(wrapper);
      context.flexibleFunctions.insert(entry);
      context.flexibleBlocks.insert(&wrapper.front());
      context.flexibleBlocks.insert(&entry.front());
      context.flexibleBlocks.insert(payload);
      context.flexibleCalls.insert(invocation);
      context.flexibleCalls.insert(call);
      context.flexibleOutcomes.insert(call);
      context.flexibleReturns.insert(returned);
      context.skipBodies.insert(entry);
    }
    // Evidence for dormant/authored entries cannot enable interface changes.
    if (failed(context.operation(before, after, {})))
      return failure();
    for (const auto &item : steps)
      if (failed(step(item)))
        return failure();
    for (auto id : extraValues)
      if (!generatedValues.contains(id) && !projectedValues.contains(id))
        return refuse(after, "extra port has no checked normalization use");
    return success();
  }
};
} // namespace

LogicalResult verifyComputationFrontier(
    mlir::ModuleOp normalizedBefore, mlir::ModuleOp actualAfter,
    ArrayRef<FrontierNormalizationOrigin> checkedOrigins, uint64_t &remaining,
    std::optional<CapacityCause> *capacity) {
  std::optional<CapacityCause> localCapacity;
  CheckingWork work(remaining, capacity ? *capacity : localCapacity);
  return FrontierReader(normalizedBefore, actualAfter, work)
      .run(checkedOrigins);
}

LogicalResult verifyComputationNormalizationContext(
    mlir::ModuleOp source, mlir::ModuleOp normalized,
    ArrayRef<ComputationNormalizationRewrite> checkedRewrites,
    uint64_t &remaining, std::optional<CapacityCause> *capacity) {
  std::optional<CapacityCause> localCapacity;
  CheckingWork work(remaining, capacity ? *capacity : localCapacity);
  ContextReader context(work);
  llvm::DenseSet<Operation *> targets;
  if (!hasSingleElement(*source.getBody()) ||
      !hasSingleElement(*normalized.getBody()))
    return refuse(normalized, "normalization module shape changed");
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  auto proposal =
      dyn_cast<protocol_ir::ProtocolModuleOp>(normalized.getBody()->front());
  if (!owner || !proposal || !owner.getBody().hasOneBlock() ||
      !proposal.getBody().hasOneBlock())
    return refuse(normalized, "normalization protocol owner missing");
  SymbolTable declarations(owner);
  SymbolTableCollection symbols;
  for (auto rewrite : checkedRewrites) {
    auto a = rewrite.sourceCall;
    auto b = rewrite.normalizedCall;
    auto unit = rewrite.normalizedUnit;
    if (!a || !b || !unit || !work.charge(a) ||
        a->getParentOfType<mlir::ModuleOp>() != source ||
        b->getParentOfType<mlir::ModuleOp>() != normalized ||
        unit->getParentOp() != proposal.getOperation() ||
        declarations.lookup(SymbolTable::getSymbolName(unit)) ||
        !targets.insert(b).second ||
        !context.appendedDeclarations.insert(unit).second ||
        !context.callees
             .try_emplace(a, b->getAttrOfType<SymbolRefAttr>("callee"))
             .second)
      return refuse(normalized, "invalid or duplicate checked callee rewrite");
    auto raw = resolveInvocation(a, symbols),
         entry = resolveInvocation(b, symbols);
    if (!raw || !entry || entry->getParentOp() != unit.getOperation() ||
        raw.getFunctionType() != entry.getFunctionType())
      return refuse(normalized,
                    "normalization changed original call interface");
    NamedAttrList expected(raw->getAttrs()), actual(entry->getAttrs());
    for (StringRef name : {"sym_name", "sym_visibility"}) {
      expected.erase(name);
      actual.erase(name);
    }
    if (expected.getDictionary(source.getContext()) !=
        actual.getDictionary(normalized.getContext()))
      return refuse(normalized,
                    "normalized entry declaration attributes changed");
  }
  if (failed(context.operation(source, normalized, {})) ||
      !context.appendedDeclarations.empty())
    return refuse(normalized, "normalization changed source context");
  for (auto rewrite : checkedRewrites)
    if (context.pairs.lookup(rewrite.sourceCall) != rewrite.normalizedCall)
      return refuse(normalized,
                    "normalization rewrote a different ordered call");
  return success();
}
} // namespace zkc::computation
