#include "FrontierVerification.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/TimeProfiler.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "computation-frontier", detail);
}
struct Step {
  func::FuncOp wrapper;
  protocol_ir::LocalCallOp invocation;
  exec::ComputeOp call;
  exec::ReturnOp returned;
  Block *payload;
  func::FuncOp entry;
  unsigned originalArguments = 0, originalResults = 0;
  unsigned originalComputationArguments = 0, originalComputationResults = 0;
};
// Every key describes an actual typed instruction over already available SSA
// values. Only polynomial-created instructions enter the table. Concrete source
// instructions always get a fresh identity, even when their expression matches.
struct Instruction {
  Operation *operation;
  SmallVector<unsigned> inputs, outputs;
  unsigned step;
};
class Frontier {
  SmallVector<Step> &steps;
  llvm::DenseSet<Operation *> &shareable;
  uint64_t &remaining;
  std::optional<CapacityCause> *capacity;
  unsigned nextValue = 1;
  llvm::DenseMap<Value, unsigned> callerValues;
  struct Available {
    unsigned step;
    Value value;
  };
  llvm::DenseMap<unsigned, Available> available;
  llvm::DenseMap<unsigned, SmallVector<unsigned>> packedArrays;
  SmallVector<Instruction> instructions;
  llvm::DenseMap<size_t, SmallVector<unsigned>> buckets;
  // (earlier cut, normalized value) -> its actual appended call output.
  llvm::DenseMap<std::pair<unsigned, Value>, Value> exports;

  bool charge(uint64_t amount = 1) {
    if (amount > remaining) {
      if (capacity)
        *capacity =
            CapacityCause{WorkOwner::AlgorithmExpansion, amount, remaining};
      return false;
    }
    remaining -= amount;
    return true;
  }
  unsigned anchor(Value value) {
    auto found = callerValues.find(value);
    if (found != callerValues.end())
      return found->second;
    auto id = nextValue++;
    callerValues[value] = id;
    return id;
  }
  Value wrapperInput(Step &step, Value value) {
    auto argument = dyn_cast<BlockArgument>(value);
    if (!argument || argument.getOwner() != &step.wrapper.getBody().front() ||
        !argument.getArgNumber() ||
        argument.getArgNumber() > step.invocation.getNumOperands())
      return {};
    return step.invocation.getOperand(argument.getArgNumber() - 1);
  }
  Value numericalReturn(Step &step, Value value) {
    auto result = dyn_cast<BlockArgument>(value);
    auto returned = cast<func::ReturnOp>(step.entry.front().back());
    if (!result || result.getOwner() != step.payload ||
        result.getArgNumber() >= returned.getNumOperands())
      return {};
    return returned.getOperand(result.getArgNumber());
  }
  bool wrapperOutputs(Step &step, TypeRange outputs) {
    auto outcome = exec::OutcomeType::get(step.wrapper.getContext(),
                                          llvm::to_vector(outputs));
    // Only packaging changes. The active scope, failure continuation, guard
    // bodies and success path are retained exactly.
    for (auto &block : step.wrapper.getBody())
      for (auto &op : block) {
        if (!charge())
          return false;
        if (isa<exec::ReturnOp, exec::FailureOp>(op))
          op.getResult(0).setType(outcome);
      }
    step.wrapper.setFunctionType(FunctionType::get(
        step.wrapper.getContext(), step.wrapper.getArgumentTypes(), outcome));
    return true;
  }
  protocol_ir::LocalCallOp replaceInvocation(Step &step, TypeRange types) {
    OpBuilder builder(step.invocation);
    OperationState state(step.invocation.getLoc(),
                         protocol_ir::LocalCallOp::getOperationName());
    state.addOperands(step.invocation.getInputs());
    state.addTypes(types);
    state.addAttributes(step.invocation->getAttrs());
    return cast<protocol_ir::LocalCallOp>(builder.create(state));
  }
  Value exportValue(unsigned producer, Value value) {
    auto key = std::make_pair(producer, value);
    if (auto found = exports.find(key); found != exports.end())
      return found->second;
    auto &step = steps[producer];
    auto returned = cast<func::ReturnOp>(step.entry.front().back());
    // Reuse an existing result port when it already exports this exact SSA.
    auto wrapperReturn = step.returned;
    for (auto [index, output] : enumerate(wrapperReturn.getValues())) {
      if (!charge())
        return {};
      // A forwarding return names a wrapper input, not a computation result
      // coordinate. Reuse it only for the corresponding exact entry argument.
      auto argument = dyn_cast<BlockArgument>(value);
      bool forwarded = wrapperInput(step, output) && argument &&
                       argument.getOwner() == &step.entry.front() &&
                       argument.getArgNumber() < step.call.getInputs().size() &&
                       step.call.getInputs()[argument.getArgNumber()] == output;
      if (forwarded || numericalReturn(step, output) == value) {
        auto result = step.invocation.getResult(index);
        exports.try_emplace(key, result);
        return result;
      }
    }
    if (!charge(32 + step.invocation.getNumResults() +
                step.payload->getNumArguments() +
                step.wrapper.getNumArguments()))
      return {};
    returned->insertOperands(returned.getNumOperands(), value);
    SmallVector<Type> computationTypes(step.entry.getResultTypes());
    computationTypes.push_back(value.getType());
    OpBuilder builder(step.wrapper.getContext());
    step.entry.setFunctionType(builder.getFunctionType(
        step.entry.getArgumentTypes(), computationTypes));
    step.call.getOutcome().setType(
        exec::OutcomeType::get(builder.getContext(), computationTypes));
    auto payload = step.payload->addArgument(value.getType(), value.getLoc());
    wrapperReturn->insertOperands(wrapperReturn.getNumOperands(), payload);
    SmallVector<Type> types(step.invocation.getResultTypes());
    types.push_back(value.getType());
    if (!wrapperOutputs(step, types))
      return {};
    auto replacement = replaceInvocation(step, types);
    step.invocation->replaceAllUsesWith(
        replacement.getResults().take_front(step.invocation.getNumResults()));
    // Keep canonical identities when replacing an existing invocation handle.
    for (auto [old, actual] :
         zip(step.invocation.getResults(), replacement.getResults()))
      if (auto found = callerValues.find(old); found != callerValues.end()) {
        auto id = found->second;
        callerValues.erase(old);
        callerValues[actual] = id;
      }
    for (auto &item : exports)
      if (auto result = dyn_cast<OpResult>(item.second);
          result && result.getOwner() == step.invocation.getOperation())
        item.second = replacement.getResult(result.getResultNumber());
    step.invocation.erase();
    step.invocation = replacement;
    auto result = replacement.getResults().back();
    exports.try_emplace(key, result);
    return result;
  }
  Value importValue(unsigned consumer, unsigned producer, Value value,
                    unsigned id) {
    auto input = exportValue(producer, value);
    if (!input)
      return {};
    callerValues[input] = id;
    auto &step = steps[consumer];
    for (auto [argument, operand] :
         zip(step.entry.getArguments(), step.call.getInputs())) {
      if (!charge())
        return {};
      if (wrapperInput(step, operand) == input)
        return argument;
    }
    if (!charge(16 + step.entry.getNumArguments()))
      return {};
    auto entryIndex = step.entry.getNumArguments();
    auto wrapperIndex = step.wrapper.getNumArguments();
    if (failed(step.entry.insertArgument(entryIndex, value.getType(), {},
                                         value.getLoc())) ||
        failed(step.wrapper.insertArgument(wrapperIndex, value.getType(), {},
                                           value.getLoc())))
      return {};
    auto argument = step.entry.getArgument(entryIndex);
    auto wrapperArgument = step.wrapper.getArgument(wrapperIndex);
    step.invocation->insertOperands(step.invocation.getNumOperands(), input);
    step.call->insertOperands(step.call.getNumOperands(), wrapperArgument);
    return argument;
  }

public:
  Frontier(SmallVector<Step> &steps, llvm::DenseSet<Operation *> &shareable,
           uint64_t &remaining, std::optional<CapacityCause> *capacity)
      : steps(steps), shareable(shareable), remaining(remaining),
        capacity(capacity) {}
  LogicalResult run() {
    for (auto [position, step] : enumerate(steps)) {
      llvm::DenseMap<Value, unsigned> values;
      for (auto [argument, operand] :
           zip(step.entry.getArguments(), step.call.getInputs())) {
        if (!charge())
          return refuse(step.entry, "normalization frontier input work limit");
        auto input = wrapperInput(step, operand);
        if (!input)
          return refuse(step.wrapper, "numerical input is not a wrapper port");
        auto id = anchor(input);
        values[argument] = id;
        available.try_emplace(id, Available{unsigned(position), argument});
      }
      for (auto &op :
           make_early_inc_range(step.entry.front().without_terminator())) {
        if (!charge())
          return refuse(step.entry, "normalization frontier work limit");
        SmallVector<unsigned> inputs;
        for (Value operand : op.getOperands()) {
          auto id = values.lookup(operand);
          if (!id)
            return refuse(step.entry, "normalization frontier lost an operand");
          inputs.push_back(id);
        }
        // The earlier cut can expose a concrete pack while polynomial
        // normalization at that cut had used its scalar elements directly.
        // Reconstructing its descriptor later introduces array_at operations.
        // Resolve only these polynomial-created projections by the existing
        // exact pack-coordinate law, so coefficient/evaluation memoization is
        // not lost merely because the concrete pack crossed a native port.
        if (auto projection = dyn_cast<data::ArrayAtOp>(op);
            projection && shareable.contains(&op)) {
          auto packed = packedArrays.find(inputs.front());
          if (packed != packedArrays.end()) {
            auto index = projection.getIndexAttr().getInt();
            if (index < 0 || uint64_t(index) >= packed->second.size())
              return refuse(step.wrapper, "invalid packed frontier coordinate");
            auto id = packed->second[index];
            auto found = available.find(id);
            if (found == available.end() ||
                found->second.value.getType() !=
                    projection.getResult().getType())
              return refuse(step.wrapper, "lost packed frontier element");
            if (!projection.getResult().use_empty()) {
              auto replacement = found->second.step == position
                                     ? found->second.value
                                     : importValue(position, found->second.step,
                                                   found->second.value, id);
              if (!replacement)
                return refuse(step.wrapper, "packed frontier port work limit");
              values[replacement] = id;
              projection.getResult().replaceAllUsesWith(replacement);
            }
            shareable.erase(&op);
            op.erase();
            continue;
          }
        }
        NamedAttrList attributes(op.getAttrs());
        attributes.erase("site");
        auto dictionary = attributes.getDictionary(op.getContext());
        size_t hash =
            hash_combine(op.getName(), dictionary,
                         hash_combine_range(inputs.begin(), inputs.end()));
        Instruction *prior = nullptr;
        if (shareable.contains(&op)) {
          for (auto index : buckets[hash]) {
            if (!charge())
              return refuse(step.entry, "frontier signature comparison limit");
            auto &candidate = instructions[index];
            if (candidate.step == position)
              continue; // Keep the original normalization within each call.
            NamedAttrList candidateAttrs(candidate.operation->getAttrs());
            candidateAttrs.erase("site");
            if (candidate.inputs == inputs &&
                candidate.operation->getName() == op.getName() &&
                candidate.operation->getResultTypes() == op.getResultTypes() &&
                candidateAttrs.getDictionary(op.getContext()) == dictionary) {
              prior = &candidate;
              break;
            }
          }
        }
        if (prior) {
          for (auto [coordinate, result] : enumerate(op.getResults())) {
            if (result.use_empty())
              continue;
            Value earlier = prior->operation->getResult(coordinate);
            auto replacement = prior->step == position
                                   ? earlier
                                   : importValue(position, prior->step, earlier,
                                                 prior->outputs[coordinate]);
            if (!replacement)
              return refuse(step.wrapper,
                            "concrete port construction work limit");
            values[replacement] = prior->outputs[coordinate];
            result.replaceAllUsesWith(replacement);
          }
          shareable.erase(&op);
          op.erase();
          continue;
        }
        SmallVector<unsigned> outputs;
        for (Value result : op.getResults()) {
          auto id = nextValue++;
          values[result] = id;
          available.try_emplace(id, Available{unsigned(position), result});
          outputs.push_back(id);
        }
        if (isa<data::ArrayFromElementsOp>(op))
          packedArrays[outputs.front()] = inputs;
        if (shareable.contains(&op)) {
          buckets[hash].push_back(instructions.size());
          instructions.push_back({&op, inputs, outputs, unsigned(position)});
        }
      }
      auto wrapperReturn = step.returned;
      for (auto [value, result] :
           zip(wrapperReturn.getValues(), step.invocation.getResults())) {
        if (!charge())
          return refuse(step.wrapper,
                        "normalization frontier return work limit");
        auto input = wrapperInput(step, value);
        auto id =
            input ? anchor(input) : values.lookup(numericalReturn(step, value));
        if (!id)
          return refuse(step.wrapper, "normalization frontier lost a return");
        callerValues[result] = id;
      }
    }
    // A later shared expression may make an earlier speculative import dead.
    // Trim ports backwards through the acyclic cut sequence; source interfaces
    // and every retained instruction remain fixed. No work is moved or erased.
    for (auto &step : reverse(steps)) {
      OpBuilder builder(step.wrapper.getContext());
      auto wrapperReturn = step.returned;
      BitVector unused(step.invocation.getNumResults());
      SmallVector<Type> outputs;
      for (auto [index, result] : enumerate(step.invocation.getResults())) {
        if (index >= step.originalResults && result.use_empty())
          unused.set(index);
        else
          outputs.push_back(result.getType());
      }
      if (unused.any()) {
        wrapperReturn->eraseOperands(unused);
        if (!wrapperOutputs(step, outputs))
          return refuse(step.wrapper, "wrapper output trimming work limit");
        auto replacement = replaceInvocation(step, outputs);
        unsigned coordinate = 0;
        for (auto [index, result] : enumerate(step.invocation.getResults()))
          if (!unused[index])
            result.replaceAllUsesWith(replacement.getResult(coordinate++));
        step.invocation.erase();
        step.invocation = replacement;
      }
      auto returned = cast<func::ReturnOp>(step.entry.front().back());
      unused.resize(step.payload->getNumArguments());
      unused.reset();
      outputs.clear();
      for (auto [index, result] : enumerate(step.payload->getArguments())) {
        if (index >= step.originalComputationResults && result.use_empty())
          unused.set(index);
        else
          outputs.push_back(result.getType());
      }
      if (unused.any()) {
        returned->eraseOperands(unused);
        step.entry.setFunctionType(
            builder.getFunctionType(step.entry.getArgumentTypes(), outputs));
        step.payload->eraseArguments(unused);
        step.call.getOutcome().setType(
            exec::OutcomeType::get(builder.getContext(), outputs));
      }
      // Numerical inputs and wrapper ports have independent coordinates. A
      // wrapper argument can be omitted, repeated or forwarded only by return.
      for (unsigned index = step.entry.getNumArguments();
           index-- > step.originalComputationArguments;)
        if (step.entry.getArgument(index).use_empty()) {
          if (failed(step.entry.eraseArgument(index)))
            return refuse(step.entry, "cannot trim appended numerical input");
          step.call->eraseOperand(index + 1);
        }
      for (unsigned index = step.wrapper.getNumArguments();
           index-- > step.originalArguments;)
        if (step.wrapper.getArgument(index).use_empty()) {
          if (failed(step.wrapper.eraseArgument(index)))
            return refuse(step.wrapper, "cannot trim appended wrapper input");
          step.invocation->eraseOperand(index - 1);
        }
    }
    return success();
  }
};
} // namespace

// The returned subject is temporary checked mathematics, never an executable
// proposal regenerated by a verifier. Independent readers check normalization
// provenance, unchanged ordered context and actual port rewrites before any
// recipe is selected. Public verification reads actual candidate instructions.
OwningOpRef<mlir::ModuleOp> prepareComputationRealization(
    mlir::ModuleOp source, uint64_t &remaining,
    mathematical::RealizationWork &work, std::optional<CapacityCause> *capacity,
    mathematical::NumericalSelection *selection, bool deferContext) {
  llvm::TimeTraceScope timing("zkc.numerical-normalization");
  if (capacity)
    capacity->reset();
  if (!chargeCopy(source, remaining, capacity))
    return {};
  IRMapping sourceMapping;
  OwningOpRef<mlir::ModuleOp> proposal(
      cast<mlir::ModuleOp>(source->clone(sourceMapping)));
  auto inherit = [&] {
    if (selection)
      source.walk([&](Operation *op) {
        for (auto id : selection->owners(op))
          selection->record(sourceMapping.lookup(op), id);
      });
  };
  auto owner =
      cast<protocol_ir::ProtocolModuleOp>(proposal->getBody()->front());
  llvm::DenseSet<Operation *> shareable;
  SymbolTableCollection symbols;
  SmallVector<ComputationNormalizationRewrite> rewrites;
  SmallVector<Operation *> calls;
  source.walk([&](Operation *op) {
    if (isa<exec::ComputeOp>(op))
      calls.push_back(op);
  });
  // One immutable unit can have several actual invocations. Give each proposal
  // a private normalized entry so sharing never changes another invocation.
  SymbolTable outer(owner);
  for (auto sourceCall : calls) {
    auto *call = sourceMapping.lookup(sourceCall);
    auto raw = resolveInvocation(call, symbols);
    if (!raw)
      return {};
    auto unit = dyn_cast<mlir::ModuleOp>(raw->getParentOp());
    OwningOpRef<mlir::ModuleOp> closed;
    if (!unit || !mathematical::isComputationUnit(unit)) {
      closed = closeComputation(raw, remaining);
      if (!closed)
        return {};
      unit = *closed;
    }
    llvm::DenseSet<Operation *> generated;
    auto normalized = normalizeUnit(unit, remaining, generated, capacity);
    if (!normalized)
      return {};
    // Adopt the checked computation subject without copying its body or
    // replacing its standard entry. SymbolTable owns collision avoidance;
    // insertion preserves every independently tracked generated operation
    // identity.
    SymbolTable::setSymbolName(*normalized, "_normalized_computation");
    auto fresh = normalized.release();
    auto name = outer.insert(fresh, owner.getBody().front().end());
    call->setAttr("callee",
                  SymbolRefAttr::get(
                      name, {FlatSymbolRefAttr::get(raw.getSymNameAttr())}));
    shareable.insert(generated.begin(), generated.end());
    rewrites.push_back({sourceCall, call, fresh});
  }
  // Only checked polynomial-generated operations can change a frontier. With
  // none, the checked normalized subject is already final: there is no port
  // rewrite to propose or independently compare, and no snapshot to copy.
  if ((!deferContext || !shareable.empty()) &&
      failed(verifyComputationNormalizationContext(
          source, *proposal, rewrites, work.numericalContextChecking,
          capacity)))
    return {};
  if (shareable.empty()) {
    inherit();
    return proposal;
  }
  // Preserve the actual normalized subject and checked origins before any
  // port rewrite. The independent reader consumes this immutable snapshot.
  if (!chargeCopy(proposal->getOperation(), remaining, capacity))
    return {};
  IRMapping normalizedMapping;
  OwningOpRef<mlir::ModuleOp> normalizedBefore(
      cast<mlir::ModuleOp>(proposal->getOperation()->clone(normalizedMapping)));
  SmallVector<FrontierNormalizationOrigin> origins;
  for (const auto &rewrite : rewrites) {
    auto entry = mathematical::getComputationEntry(rewrite.normalizedUnit);
    FrontierNormalizationOrigin origin{
        cast<func::FuncOp>(normalizedMapping.lookup(entry.getOperation())), {}};
    for (auto &op : entry.front().without_terminator())
      if (shareable.contains(&op))
        origin.polynomialGenerated.push_back(normalizedMapping.lookup(&op));
    origins.push_back(std::move(origin));
  }
  // Only calculation wrappers explicitly attributed by the projection record
  // may acquire ports. Authored scoped interfaces are fixed, including dormant
  // authored definitions. Each selected wrapper has one actual invocation.
  llvm::DenseSet<Attribute> generatedWrappers;
  for (auto record :
       owner.getBody().front().getOps<protocol_ir::ProjectionOp>())
    for (auto item : record.getCalculations())
      generatedWrappers.insert(cast<DictionaryAttr>(item).get("callee"));
  llvm::DenseMap<Operation *, unsigned> uses;
  owner.walk([&](protocol_ir::LocalCallOp call) {
    if (generatedWrappers.contains(call.getCalleeAttr()))
      if (auto *definition = outer.lookup(call.getCallee()))
        ++uses[definition];
  });
  SmallVector<Block *> blocks;
  owner.walk([&](protocol_ir::ParticipantOp participant) {
    participant.walk([&](Operation *op) {
      for (auto &region : op->getRegions())
        for (auto &block : region)
          blocks.push_back(&block);
    });
  });
  for (auto *block : blocks) {
    SmallVector<Step> steps;
    for (auto invocation : block->getOps<protocol_ir::LocalCallOp>()) {
      if (!generatedWrappers.contains(invocation.getCalleeAttr()))
        continue;
      auto wrapper = outer.lookup<func::FuncOp>(invocation.getCallee());
      if (!wrapper || uses.lookup(wrapper) != 1 || wrapper.empty())
        return {};
      auto call = dyn_cast<exec::ComputeOp>(wrapper.front().front());
      if (!call)
        continue; // A guard-only wrapper has no numerical work.
      SymbolTableCollection localSymbols;
      auto entry = call.resolveCallee(localSymbols);
      if (!entry)
        return {};
      // Resolve actual wrapper ports in run(); their order and multiplicity
      // need not match the numerical entry's argument coordinates.
      exec::ReturnOp returned;
      auto walk = wrapper.walk([&](Operation *op) {
        if (!remaining) {
          if (capacity)
            *capacity = CapacityCause{WorkOwner::AlgorithmExpansion, 1, 0};
          return WalkResult::interrupt();
        }
        --remaining;
        if (auto result = dyn_cast<exec::ReturnOp>(op)) {
          if (returned)
            return WalkResult::interrupt();
          returned = result;
        }
        return WalkResult::advance();
      });
      if (walk.wasInterrupted() || !returned || !call.getOutcome().hasOneUse())
        return {};
      auto dispatch =
          dyn_cast<exec::DispatchOp>(*call.getOutcome().getUsers().begin());
      if (!dispatch || dispatch->getPrevNode() != call.getOperation())
        return {};
      auto *payload = dispatch.getReturned();
      steps.push_back({wrapper, invocation, call, returned, payload, entry,
                       wrapper.getNumArguments(), invocation.getNumResults(),
                       unsigned(call.getInputs().size()),
                       payload->getNumArguments()});
    }
    if (steps.empty())
      continue;
    if (failed(Frontier(steps, shareable, remaining, capacity).run()))
      return {};
  }
  if (failed(verifyComputationFrontier(*normalizedBefore, *proposal, origins,
                                       work.numericalContextChecking,
                                       capacity)))
    return {};
  inherit();
  return proposal;
}
OwningOpRef<mlir::ModuleOp>
prepareComputationRealization(mlir::ModuleOp source) {
  uint64_t remainingCopy = 4000000;
  mathematical::RealizationWork work;
  return prepareComputationRealization(source, remainingCopy, work);
}
} // namespace zkc::computation
