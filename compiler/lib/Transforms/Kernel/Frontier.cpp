#include "FrontierVerification.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SetVector.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "kernel-frontier", detail);
}
struct Step {
  local::FuncOp wrapper;
  local::CallOp invocation;
  CallOp call;
  func::FuncOp entry;
  unsigned originalArguments = 0, originalResults = 0;
  unsigned originalKernelResults = 0;
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
    if (amount > remaining)
      return false;
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
  Value exportValue(unsigned producer, Value value) {
    auto key = std::make_pair(producer, value);
    if (auto found = exports.find(key); found != exports.end())
      return found->second;
    auto &step = steps[producer];
    auto returned = cast<func::ReturnOp>(step.entry.front().back());
    // Reuse an existing result port when it already exports this exact SSA.
    auto wrapperReturn =
        cast<local::ReturnOp>(step.wrapper.getBody().front().back());
    for (auto [index, output] : enumerate(wrapperReturn.getInputs())) {
      if (!charge())
        return {};
      auto coordinate = cast<OpResult>(output).getResultNumber();
      if (returned.getOperand(coordinate) == value) {
        auto result = step.invocation.getResult(index);
        exports.try_emplace(key, result);
        return result;
      }
    }
    if (!charge(32 + step.invocation.getNumResults() +
                step.call.getNumResults() + step.wrapper.getNumArguments()))
      return {};
    returned->insertOperands(returned.getNumOperands(), value);
    SmallVector<Type> kernelTypes(step.entry.getResultTypes());
    kernelTypes.push_back(value.getType());
    OpBuilder builder(step.wrapper.getContext());
    step.entry.setFunctionType(
        builder.getFunctionType(step.entry.getArgumentTypes(), kernelTypes));
    builder.setInsertionPoint(step.call);
    OperationState callState(step.call.getLoc(), CallOp::getOperationName());
    callState.addOperands(step.call.getInputs());
    callState.addTypes(kernelTypes);
    callState.addAttributes(step.call->getAttrs());
    auto call = cast<CallOp>(builder.create(callState));
    step.call->replaceAllUsesWith(
        call.getResults().take_front(step.call.getNumResults()));
    step.call.erase();
    step.call = call;
    wrapperReturn->insertOperands(wrapperReturn.getNumOperands(),
                                  call.getResults().back());
    SmallVector<Type> types(step.wrapper.getResultTypes());
    types.push_back(value.getType());
    step.wrapper.setFunctionType(
        builder.getFunctionType(step.wrapper.getArgumentTypes(), types));
    builder.setInsertionPoint(step.invocation);
    auto replacement = local::CallOp::create(
        builder, step.invocation.getLoc(), types, step.invocation.getInputs(),
        step.invocation.getCalleeAttr(), step.invocation.getSiteAttr());
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
    for (auto [index, operand] : enumerate(step.invocation.getInputs())) {
      if (!charge())
        return {};
      if (operand == input)
        return step.entry.getArgument(index);
    }
    if (!charge(16 + step.entry.getNumArguments()))
      return {};
    auto argument =
        step.entry.front().addArgument(value.getType(), value.getLoc());
    auto wrapperArgument = step.wrapper.getBody().front().addArgument(
        value.getType(), value.getLoc());
    step.invocation->insertOperands(step.invocation.getNumOperands(), input);
    step.call->insertOperands(step.call.getNumOperands(), wrapperArgument);
    OpBuilder builder(step.wrapper.getContext());
    step.entry.setFunctionType(builder.getFunctionType(
        step.entry.front().getArgumentTypes(), step.entry.getResultTypes()));
    step.wrapper.setFunctionType(builder.getFunctionType(
        step.wrapper.getBody().front().getArgumentTypes(),
        step.wrapper.getResultTypes()));
    return argument;
  }

public:
  Frontier(SmallVector<Step> &steps, llvm::DenseSet<Operation *> &shareable,
           uint64_t &remaining)
      : steps(steps), shareable(shareable), remaining(remaining) {}
  LogicalResult run() {
    for (auto [position, step] : enumerate(steps)) {
      llvm::DenseMap<Value, unsigned> values;
      for (auto [argument, input] :
           zip(step.entry.getArguments(), step.invocation.getInputs())) {
        auto id = anchor(input);
        values[argument] = id;
        available.try_emplace(id, Available{unsigned(position), argument});
      }
      for (auto &op :
           make_early_inc_range(step.entry.front().without_terminator())) {
        if (!remaining)
          return refuse(step.entry, "normalization frontier work limit");
        --remaining;
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
        if (auto projection = dyn_cast<algebra::ArrayAtOp>(op);
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
            if (!remaining)
              return refuse(step.entry, "frontier signature comparison limit");
            --remaining;
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
        if (isa<algebra::ArrayFromElementsOp>(op))
          packedArrays[outputs.front()] = inputs;
        if (shareable.contains(&op)) {
          buckets[hash].push_back(instructions.size());
          instructions.push_back({&op, inputs, outputs, unsigned(position)});
        }
      }
      auto returned = cast<func::ReturnOp>(step.entry.front().back());
      auto wrapperReturn =
          cast<local::ReturnOp>(step.wrapper.getBody().front().back());
      for (auto [value, result] :
           zip(wrapperReturn.getInputs(), step.invocation.getResults())) {
        auto coordinate = cast<OpResult>(value).getResultNumber();
        auto id = values.lookup(returned.getOperand(coordinate));
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
      auto wrapperReturn =
          cast<local::ReturnOp>(step.wrapper.getBody().front().back());
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
        step.wrapper.setFunctionType(
            builder.getFunctionType(step.wrapper.getArgumentTypes(), outputs));
        builder.setInsertionPoint(step.invocation);
        auto replacement = local::CallOp::create(
            builder, step.invocation.getLoc(), outputs,
            step.invocation.getInputs(), step.invocation.getCalleeAttr(),
            step.invocation.getSiteAttr());
        unsigned coordinate = 0;
        for (auto [index, result] : enumerate(step.invocation.getResults()))
          if (!unused[index])
            result.replaceAllUsesWith(replacement.getResult(coordinate++));
        step.invocation.erase();
        step.invocation = replacement;
      }
      auto returned = cast<func::ReturnOp>(step.entry.front().back());
      unused.resize(step.call.getNumResults());
      unused.reset();
      outputs.clear();
      for (auto [index, result] : enumerate(step.call.getResults())) {
        if (index >= step.originalKernelResults && result.use_empty())
          unused.set(index);
        else
          outputs.push_back(result.getType());
      }
      if (unused.any()) {
        returned->eraseOperands(unused);
        step.entry.setFunctionType(
            builder.getFunctionType(step.entry.getArgumentTypes(), outputs));
        builder.setInsertionPoint(step.call);
        OperationState state(step.call.getLoc(), CallOp::getOperationName());
        state.addOperands(step.call.getInputs());
        state.addTypes(outputs);
        state.addAttributes(step.call->getAttrs());
        auto replacement = cast<CallOp>(builder.create(state));
        unsigned coordinate = 0;
        for (auto [index, result] : enumerate(step.call.getResults()))
          if (!unused[index])
            result.replaceAllUsesWith(replacement.getResult(coordinate++));
        step.call.erase();
        step.call = replacement;
      }
      for (unsigned index = step.entry.getNumArguments();
           index-- > step.originalArguments;)
        if (step.entry.getArgument(index).use_empty()) {
          step.entry.front().eraseArgument(index);
          step.call->eraseOperand(index);
          step.wrapper.getBody().front().eraseArgument(index);
          step.invocation->eraseOperand(index);
        }
      step.entry.setFunctionType(builder.getFunctionType(
          step.entry.front().getArgumentTypes(), step.entry.getResultTypes()));
      step.wrapper.setFunctionType(builder.getFunctionType(
          step.wrapper.getBody().front().getArgumentTypes(),
          step.wrapper.getResultTypes()));
      // CallOpInterface metadata follows the final port counts. Kernel
      // admission permits only empty dictionaries, with no per-port premise.
      auto empty = builder.getDictionaryAttr({});
      if (step.call.getArgAttrsAttr())
        step.call.setArgAttrsAttr(builder.getArrayAttr(
            SmallVector<Attribute>(step.call.getNumOperands(), empty)));
      if (step.call.getResAttrsAttr())
        step.call.setResAttrsAttr(builder.getArrayAttr(
            SmallVector<Attribute>(step.call.getNumResults(), empty)));
    }
    return success();
  }
};
} // namespace

// The returned subject is temporary checked mathematics, never an executable
// proposal regenerated by a verifier. Independent readers check normalization
// provenance, unchanged ordered context and actual port rewrites before any
// recipe is selected. Public verification reads actual candidate instructions.
OwningOpRef<mlir::ModuleOp> prepareKernelLowering(mlir::ModuleOp source) {
  IRMapping sourceMapping;
  OwningOpRef<mlir::ModuleOp> proposal(
      cast<mlir::ModuleOp>(source->clone(sourceMapping)));
  auto owner =
      cast<protocol_ir::ProtocolModuleOp>(proposal->getBody()->front());
  llvm::DenseSet<Operation *> shareable;
  uint64_t remaining = 1000000;
  SymbolTableCollection symbols;
  SmallVector<KernelNormalizationRewrite> rewrites;
  SmallVector<CallOp> calls;
  source.walk([&](CallOp call) { calls.push_back(call); });
  // One immutable unit can have several actual invocations. Give each proposal
  // a private normalized entry so sharing never changes another invocation.
  SymbolTable outer(owner);
  unsigned next = 0;
  for (auto sourceCall : calls) {
    auto call = cast<CallOp>(sourceMapping.lookup(sourceCall.getOperation()));
    auto raw = resolve(call, symbols);
    if (!raw)
      return {};
    auto unit = cast<ModuleOp>(raw->getParentOp());
    local::FuncOp normalized;
    llvm::DenseSet<Operation *> generated;
    auto scratch =
        normalizationWorkspace(unit, normalized, remaining, generated);
    if (!scratch)
      return {};
    if (!chargeCopy(*scratch, remaining))
      return {};
    OpBuilder builder(unit.getContext());
    builder.setInsertionPointToEnd(&owner.getBody().front());
    std::string name;
    do {
      name = "_normalized_kernel_" + std::to_string(next++);
    } while (outer.lookup(name));
    auto fresh = ModuleOp::create(builder, unit.getLoc(), name);
    fresh.getBody().emplaceBlock();
    builder.setInsertionPointToEnd(&fresh.getBody().front());
    for (auto &declaration : scratch->getBody().front()) {
      if (&declaration != normalized.getOperation())
        builder.clone(declaration);
    }
    auto entry = func::FuncOp::create(builder, raw.getLoc(), raw.getSymName(),
                                      normalized.getFunctionType());
    for (auto attribute : raw->getAttrs())
      if (attribute.getName() != "sym_name" &&
          attribute.getName() != "sym_visibility")
        entry->setAttr(attribute.getName(), attribute.getValue());
    auto *block = entry.addEntryBlock();
    builder.setInsertionPointToEnd(block);
    IRMapping mapping;
    mapping.map(normalized.getArguments(), block->getArguments());
    for (auto &op : normalized.getBody().front().without_terminator()) {
      auto *copy = builder.clone(op, mapping);
      copy->removeAttr("site");
      if (generated.contains(&op))
        shareable.insert(copy);
    }
    SmallVector<Value> outputs;
    for (Value value : normalized.getBody().front().back().getOperands())
      outputs.push_back(mapping.lookup(value));
    func::ReturnOp::create(builder, raw.getLoc(), outputs);
    call->setAttr(
        "callee",
        SymbolRefAttr::get(builder.getContext(), name,
                           {FlatSymbolRefAttr::get(raw.getSymNameAttr())}));
    outer.insert(fresh);
    rewrites.push_back({sourceCall, call, fresh});
  }
  if (failed(verifyKernelNormalizationContext(source, *proposal, rewrites,
                                              remaining)))
    return {};
  // Preserve the actual normalized subject and checked origins before any
  // port rewrite. The independent reader consumes this immutable snapshot.
  if (!chargeCopy(proposal->getOperation(), remaining))
    return {};
  IRMapping normalizedMapping;
  OwningOpRef<mlir::ModuleOp> normalizedBefore(
      cast<mlir::ModuleOp>(proposal->getOperation()->clone(normalizedMapping)));
  SmallVector<FrontierNormalizationOrigin> origins;
  for (const auto &rewrite : rewrites) {
    auto entry = getEntry(rewrite.normalizedUnit);
    FrontierNormalizationOrigin origin{
        cast<func::FuncOp>(normalizedMapping.lookup(entry.getOperation())), {}};
    for (auto &op : entry.front().without_terminator())
      if (shareable.contains(&op))
        origin.polynomialGenerated.push_back(normalizedMapping.lookup(&op));
    origins.push_back(std::move(origin));
  }
  // Only calculation wrappers explicitly attributed by the projection record
  // may acquire ports. Authored Local interfaces are fixed, including dormant
  // authored definitions. Each selected wrapper has one actual invocation.
  llvm::DenseSet<Attribute> generatedWrappers;
  for (auto record :
       owner.getBody().front().getOps<protocol_ir::ProjectionOp>())
    for (auto item : record.getCalculations())
      generatedWrappers.insert(cast<DictionaryAttr>(item).get("callee"));
  llvm::DenseMap<Operation *, unsigned> uses;
  owner.walk([&](local::CallOp call) {
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
    for (auto invocation : block->getOps<local::CallOp>()) {
      if (!generatedWrappers.contains(invocation.getCalleeAttr()))
        continue;
      auto wrapper = outer.lookup<local::FuncOp>(invocation.getCallee());
      if (!wrapper || uses.lookup(wrapper) != 1 ||
          !wrapper.getBody().hasOneBlock())
        return {};
      auto call = dyn_cast<CallOp>(wrapper.getBody().front().front());
      if (!call)
        continue; // A guard-only wrapper has no numerical work.
      SymbolTableCollection localSymbols;
      auto entry = resolve(call, localSymbols);
      if (!entry || call.getInputs() != wrapper.getArguments())
        return {};
      steps.push_back({wrapper, invocation, call, entry,
                       wrapper.getNumArguments(), wrapper.getNumResults(),
                       call.getNumResults()});
    }
    if (steps.empty())
      continue;
    if (failed(Frontier(steps, shareable, remaining).run()))
      return {};
  }
  if (failed(verifyKernelFrontier(*normalizedBefore, *proposal, origins,
                                  remaining)))
    return {};
  return proposal;
}
} // namespace zkc::kernel
