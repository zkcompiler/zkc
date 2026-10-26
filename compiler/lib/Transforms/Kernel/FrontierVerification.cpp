#include "FrontierVerification.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "kernel-frontier-correspondence",
                           reason);
}
bool charge(Operation *op, uint64_t &remaining) {
  uint64_t cost = 1 + op->getNumOperands() + op->getNumResults() +
                  op->getAttrs().size() + op->getNumRegions();
  if (cost > remaining)
    return false;
  remaining -= cost;
  return true;
}
bool prefix(TypeRange before, TypeRange after) {
  return before.size() <= after.size() &&
         llvm::equal(before, after.take_front(before.size()));
}

// The same ordered structural pattern as AlgorithmVerification::unchanged,
// with narrow, explicitly enumerated exceptions. Locations are not semantic.
class ContextReader {
  uint64_t &remaining;

  bool portAttributes(Operation *before, Operation *after,
                      NamedAttrList &expected, NamedAttrList &actual) {
    for (auto name : {"arg_attrs", "res_attrs"}) {
      auto a = expected.get(name), b = actual.get(name);
      if (bool(a) != bool(b))
        return false;
      if (!a)
        continue;
      for (auto [op, raw] : {std::pair{before, a}, std::pair{after, b}}) {
        auto attributes = dyn_cast<ArrayAttr>(raw);
        auto count = StringRef(name) == "arg_attrs" ? op->getNumOperands()
                                                    : op->getNumResults();
        if (!attributes || attributes.size() != count || count > remaining)
          return false;
        remaining -= count;
        if (!llvm::all_of(attributes, [](Attribute value) {
              auto dictionary = dyn_cast<DictionaryAttr>(value);
              return dictionary && dictionary.empty();
            }))
          return false;
      }
      expected.erase(name);
      actual.erase(name);
    }
    return true;
  }

public:
  llvm::DenseMap<Operation *, Operation *> pairs;
  llvm::DenseSet<Operation *> flexibleFunctions, flexibleCalls, flexibleReturns;
  llvm::DenseSet<Operation *> skipBodies, appendedDeclarations;
  llvm::DenseMap<Operation *, Attribute> callees;

  explicit ContextReader(uint64_t &remaining) : remaining(remaining) {}
  LogicalResult operation(Operation *before, Operation *after, IRMapping values,
                          unsigned depth = 0) {
    if (depth > 64 || !charge(before, remaining) || !charge(after, remaining))
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
      if (cost > remaining)
        return refuse(after, "function interface inspection limit");
      remaining -= cost;
      if (!prefix(x.getInputs(), y.getInputs()) ||
          !prefix(x.getResults(), y.getResults()))
        return refuse(after, "original function interface changed");
      expected.erase("function_type");
      actual.erase("function_type");
    }
    bool call = flexibleCalls.contains(before);
    if (call && isa<CallOp>(before) &&
        !portAttributes(before, after, expected, actual))
      return refuse(after, "numerical call port attributes changed");
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
    if (call ? !prefix(before->getResultTypes(), after->getResultTypes())
             : before->getResultTypes() != after->getResultTypes())
      return refuse(after, "original result interface changed");
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
        if (cost > remaining)
          return refuse(after, "block interface inspection limit");
        remaining -= cost;
        if (function ? !prefix(a.getArgumentTypes(), b.getArgumentTypes())
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
          if (cost > remaining)
            return refuse(after, "definition correspondence inspection limit");
          remaining -= cost;
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
          if (!charge(&*cursor, remaining) ||
              !appendedDeclarations.erase(&*cursor))
            return refuse(&*cursor, "extra ordered operation or declaration");
      }
    }
    return success();
  }
};

struct Step {
  local::FuncOp wrapper;
  local::CallOp invocation;
  CallOp call;
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
  uint64_t &remaining;
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
    if (!charge(op, remaining))
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
  bool body(Step &source, local::CallOp invocation, Block::iterator position,
            Block::iterator cursor, func::ReturnOp sourceReturn,
            func::ReturnOp actualReturn,
            llvm::DenseMap<Value, uint64_t> &original,
            llvm::DenseMap<Value, uint64_t> &actual, BlockFrontier &frontier,
            unsigned depth = 0) {
    if (depth > 64)
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
          if (!charge(producer.operation, remaining))
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
      if (auto projection = dyn_cast<algebra::ArrayAtOp>(op);
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
        if (isa<algebra::ArrayFromElementsOp>(op))
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
        if (cost > remaining)
          return false;
        remaining -= cost;
        auto savedOriginal = original, savedActual = actual;
        auto savedProducers = frontier.producers.size();
        auto savedPacks = frontier.packs;
        auto savedProjected = projectedValues;
        retain();
        if (body(source, invocation, std::next(position), std::next(cursor),
                 sourceReturn, actualReturn, original, actual, frontier,
                 depth + 1))
          return true;
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
    auto returned = operands(actualReturn, actual);
    return succeeded(expected) && succeeded(returned) &&
           expected->size() <= returned->size() &&
           llvm::equal(*expected, ArrayRef<uint64_t>(*returned).take_front(
                                      expected->size()));
  }
  LogicalResult step(Step source) {
    auto wrapper =
        dyn_cast_or_null<local::FuncOp>(context.pairs.lookup(source.wrapper));
    auto invocation = dyn_cast_or_null<local::CallOp>(
        context.pairs.lookup(source.invocation));
    auto call = dyn_cast_or_null<CallOp>(context.pairs.lookup(source.call));
    auto entry =
        dyn_cast_or_null<func::FuncOp>(context.pairs.lookup(source.entry));
    if (!wrapper || !invocation || !call || !entry ||
        !wrapper.getBody().hasOneBlock() || !entry.getBody().hasOneBlock() ||
        entry.front().empty() ||
        !llvm::equal(wrapper.getArgumentTypes(),
                     invocation.getOperandTypes()) ||
        !llvm::equal(wrapper.getResultTypes(), invocation.getResultTypes()) ||
        wrapper.getBody().front().getArgumentTypes() !=
            wrapper.getArgumentTypes() ||
        !llvm::equal(entry.getArgumentTypes(), call.getOperandTypes()) ||
        !llvm::equal(entry.getResultTypes(), call.getResultTypes()) ||
        entry.front().getArgumentTypes() != entry.getArgumentTypes())
      return refuse(after,
                    "actual wrapper or entry interface differs from call");
    SymbolTableCollection symbols;
    if (resolve(call, symbols) != entry)
      return refuse(call, "actual numerical callee changed");
    auto &frontier = frontiers[source.invocation->getBlock()];
    llvm::DenseMap<Value, uint64_t> original, actual;
    // Read both boundaries. Original inner operands need not be identity
    // forwarding, but their actual original prefix must remain exact.
    auto input = [&](Value value) -> uint64_t {
      auto argument = dyn_cast<BlockArgument>(value);
      if (!argument || argument.getOwner() != &wrapper.getBody().front() ||
          argument.getArgNumber() >= invocation.getNumOperands())
        return 0;
      return anchor(invocation.getOperand(argument.getArgNumber()), frontier);
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
          mapped.getArgNumber() >= source.invocation.getNumOperands())
        return refuse(source.call, "source inner input is not a wrapper port");
      original[argument] =
          anchor(invocation.getOperand(mapped.getArgNumber()), frontier);
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
      if (wrapper.getArgument(i).use_empty())
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
    auto returned = operands(actualReturn, actual);
    if (failed(expected) || failed(returned) ||
        expected->size() > returned->size() ||
        !llvm::equal(*expected, ArrayRef<uint64_t>(*returned).take_front(
                                    expected->size())))
      return refuse(entry, "original numerical return identity changed");
    for (auto id : ArrayRef<uint64_t>(*returned).drop_front(expected->size()))
      extraValues.insert(id);
    auto wrapperReturn =
        dyn_cast<local::ReturnOp>(wrapper.getBody().front().back());
    if (!wrapperReturn ||
        wrapperReturn.getOperandTypes() != wrapper.getResultTypes())
      return refuse(wrapper, "actual wrapper return interface changed");
    for (auto [value, result] :
         zip(wrapperReturn.getInputs(), invocation.getResults())) {
      // Preserve the distinction between a wrapper input and a numerical
      // result coordinate. ContextReader already fixes every original return
      // operand, including duplicate aliases and the order of mixed returns.
      uint64_t id = input(value);
      if (auto coordinate = dyn_cast<OpResult>(value);
          coordinate && coordinate.getOwner() == call.getOperation() &&
          coordinate.getResultNumber() < returned->size())
        id = (*returned)[coordinate.getResultNumber()];
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
                 uint64_t &remaining)
      : before(before), after(after), remaining(remaining), context(remaining) {
  }
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
          !origin.entry.getBody().hasOneBlock() ||
          !charge(origin.entry, remaining) ||
          !generated.try_emplace(origin.entry).second)
        return refuse(after,
                      "invalid or duplicate checked normalization entry");
      auto &membership = generated[origin.entry];
      for (auto *op : origin.polynomialGenerated)
        if (!op || !charge(op, remaining) ||
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
        if (!remaining)
          return refuse(after, "projection inspection limit");
        --remaining;
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
    SmallVector<local::CallOp> invocations;
    SymbolTableCollection symbols;
    auto walk = owner.walk([&](Operation *op) {
      if (!charge(op, remaining))
        return WalkResult::interrupt();
      if (auto invocation = dyn_cast<local::CallOp>(op)) {
        ++uses[invocation.getCalleeAttr()];
        invocations.push_back(invocation);
      }
      if (auto call = dyn_cast<CallOp>(op)) {
        if (auto function = call->getParentOfType<local::FuncOp>())
          ++wrapperCalls[function];
        if (auto entry = resolve(call, symbols))
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
      auto wrapper = declarations.lookup<local::FuncOp>(invocation.getCallee());
      auto participant =
          invocation->getParentOfType<protocol_ir::ParticipantOp>();
      auto recorded = wrapperOrigins.lookup(invocation.getCalleeAttr());
      if (!wrapper || !wrapper.getBody().hasOneBlock() ||
          uses.lookup(invocation.getCalleeAttr()) != 1 || !participant ||
          recorded.first !=
              FlatSymbolRefAttr::get(participant.getSymNameAttr()) ||
          recorded.second != invocation.getSiteAttr())
        return refuse(
            after, "calculation wrapper is not uniquely participant-invoked");
      if (wrapper.getBody().front().empty())
        return refuse(after, "empty calculation wrapper");
      auto call = dyn_cast<CallOp>(wrapper.getBody().front().front());
      if (!call)
        continue; // Guard-only wrappers remain exactly unchanged.
      auto entry = resolve(call, symbols);
      if (!entry || !generated.count(entry) || entryUses.lookup(entry) != 1 ||
          wrapperCalls.lookup(wrapper) != 1 || entry.front().empty() ||
          !llvm::equal(wrapper.getArgumentTypes(),
                       invocation.getOperandTypes()) ||
          !llvm::equal(wrapper.getResultTypes(), invocation.getResultTypes()) ||
          !llvm::equal(entry.getArgumentTypes(), call.getOperandTypes()) ||
          !llvm::equal(entry.getResultTypes(), call.getResultTypes()) ||
          !selectedEntries.insert(entry).second)
        return refuse(after,
                      "missing checked origin or nonunique numerical entry");
      auto returned =
          dyn_cast<local::ReturnOp>(wrapper.getBody().front().back());
      if (!returned)
        return refuse(after, "calculation wrapper has no return");
      steps.push_back(
          {wrapper, invocation, call, entry, generated.lookup(entry)});
      context.flexibleFunctions.insert(wrapper);
      context.flexibleFunctions.insert(entry);
      context.flexibleCalls.insert(invocation);
      context.flexibleCalls.insert(call);
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

LogicalResult verifyKernelFrontier(
    mlir::ModuleOp normalizedBefore, mlir::ModuleOp actualAfter,
    ArrayRef<FrontierNormalizationOrigin> checkedOrigins, uint64_t &remaining) {
  return FrontierReader(normalizedBefore, actualAfter, remaining)
      .run(checkedOrigins);
}

LogicalResult verifyKernelNormalizationContext(
    mlir::ModuleOp source, mlir::ModuleOp normalized,
    ArrayRef<KernelNormalizationRewrite> checkedRewrites, uint64_t &remaining) {
  ContextReader context(remaining);
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
    if (!a || !b || !unit || !charge(a, remaining) ||
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
} // namespace zkc::kernel
