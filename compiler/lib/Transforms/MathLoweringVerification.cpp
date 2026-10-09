#include "MathematicalSupport.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// This checks the compiler's closed schedule and recipes, not arbitrary
// equivalent executable programs. Walk source dependencies iteratively; match
// each recipe in execution order. There is no second expression graph and no
// recursive expansion of calls or SSA chains.
class LoweringVerifier {
  protocol_ir::ProtocolModuleOp before, after;
  llvm::DenseSet<Operation *> generated, invoked;
  SymbolTable sourceSymbols, symbols;
  size_t remaining = 1000000;

  LogicalResult refuse(Operation *op, StringRef detail) {
    return diagnostics::emit(op->emitOpError(),
                             "mathematical-lowering-preservation", detail);
  }
  bool charge(size_t amount = 1) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
  // Sites are allocated by lowering and checked for uniqueness by the profile.
  // The resolved contract, arguments, implementation and parameters determine
  // the executable primitive; matching its operation name alone is
  // insufficient.
  bool primitive(Operation *op, StringRef contract, ValueRange inputs,
                 ArrayRef<StringRef> arguments = {},
                 ArrayRef<StringRef> expectedParameters = {}) {
    if (!op ||
        op->getName().getStringRef() !=
            protocol::boundOperationName(contract) ||
        op->getNumResults() != 1 || op->getNumRegions() != 0 ||
        op->getOperands() != inputs || !charge(1 + inputs.size()))
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding = reference ? dyn_cast_or_null<local::OperationBindingOp>(
                                   symbols.lookup(reference.getValue()))
                             : local::OperationBindingOp();
    auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() || !parameters ||
        parameters.size() != expectedParameters.size() ||
        binding.getArguments().size() != arguments.size())
      return false;
    for (auto [item, expected] : zip(parameters, expectedParameters))
      if (auto parameter = dyn_cast<StringAttr>(item);
          !parameter || parameter.getValue() != expected)
        return false;
    for (auto [item, expected] : zip(binding.getArguments(), arguments))
      if (auto argument = dyn_cast<StringAttr>(item);
          !argument || argument.getValue() != expected)
        return false;
    return true;
  }

  Value recipe(Operation *source, Operation *&cursor, ValueRange inputs) {
    auto take = [&](StringRef contract, ValueRange operands,
                    ArrayRef<StringRef> arguments = {},
                    ArrayRef<StringRef> parameters = {}) -> Value {
      if (!primitive(cursor, contract, operands, arguments, parameters))
        return {};
      auto value = cursor->getResult(0);
      cursor = cursor->getNextNode();
      return value;
    };
    if (isa<data::SequenceEmptyOp, data::SequenceAppendOp,
            data::SequenceLengthOp>(source)) {
      auto sequence = cast<data::SequenceType>(
          isa<data::SequenceEmptyOp>(source) ? source->getResult(0).getType()
                                             : source->getOperand(0).getType());
      auto element =
          protocol::encodeBoundType(sequence.getElementType(), false);
      if (!element) {
        consumeError(element.takeError());
        return {};
      }
      auto spelling = element->spelling();
      return take(isa<data::SequenceEmptyOp>(source)    ? "sequence.empty"
                  : isa<data::SequenceAppendOp>(source) ? "sequence.append"
                                                        : "sequence.length",
                  inputs, {spelling});
    }
    if (auto dim = dyn_cast<data::DimOp>(source)) {
      auto tensor = dim.getInput().getType();
      auto axis = dim.getAxisAttr().getInt();
      if (!tensor.isDynamicDim(axis)) {
        auto length = std::to_string(tensor.getDimSize(axis));
        return take("index.constant", {}, {}, {length});
      }
      if (auto field = dyn_cast<algebra::FieldType>(tensor.getElementType())) {
        if (tensor.getRank() == 1)
          return take("vector.length", inputs, {field.getDomain()});
        auto coordinate = std::to_string(axis);
        return take("matrix.dimension", inputs, {field.getDomain()},
                    {coordinate});
      }
      if (auto group = dyn_cast<algebra::GroupType>(tensor.getElementType()))
        return take("curve.length", inputs, {group.getDomain()});
      return take("indices.length", inputs);
    }
    if (auto constant = dyn_cast<data::IndexOp>(source))
      return take("index.constant", {}, {}, {constant.getValue()});
    if (isa<data::EqualOp, data::LessOp>(source))
      return take(isa<data::EqualOp>(source) ? "index.equal" : "index.less",
                  inputs);
    if (auto make = dyn_cast<data::MakeOp>(source)) {
      auto target = dyn_cast_or_null<local::VariantInjectOp>(cursor);
      if (!target || target.getOperands() != inputs ||
          target.getAlternative() != make.getAlternative())
        return {};
      cursor = cursor->getNextNode();
      return target.getOutput();
    }
    if (isa<data::GetOp, data::IsOp>(source)) {
      auto target = dyn_cast_or_null<local::LocalMatchOp>(cursor);
      auto descriptor = protocol::decodeVariant(
          cast<local::VariantType>(source->getOperand(0).getType())
              .getDescriptor());
      if (!target || !descriptor || target.getOperands() != inputs ||
          target.getNumRegions() != descriptor->alternatives.size() ||
          target.getAlternatives().size() != descriptor->alternatives.size() ||
          target.getNumResults() != 1)
        return {};
      for (auto [i, arm] : enumerate(descriptor->alternatives)) {
        if (target.getAlternatives()[i] !=
                StringAttr::get(source->getContext(), arm.label) ||
            !hasSingleElement(target->getRegion(i)))
          return {};
        auto &body = target->getRegion(i).front();
        if (body.getNumArguments() != arm.payload.size())
          return {};
        for (auto [argument, spelling] :
             zip(body.getArguments(), arm.payload)) {
          auto bound = protocol::encodeBoundType(argument.getType(), false);
          if (!bound) {
            consumeError(bound.takeError());
            return {};
          }
          if (bound->spelling() != spelling)
            return {};
        }
        Value expected;
        if (auto get = dyn_cast<data::GetOp>(source)) {
          if (!hasSingleElement(body))
            return {};
          expected = body.getArgument(get.getIndexAttr().getInt());
        } else {
          if (body.getOperations().size() != 2)
            return {};
          auto value = dyn_cast<local::BoolConstantOp>(body.front());
          if (!value ||
              value.getValue() !=
                  (arm.label == cast<data::IsOp>(source).getAlternative()))
            return {};
          expected = value.getOutput();
        }
        auto yield = dyn_cast<local::LocalYieldOp>(body.back());
        if (!yield || yield.getInputs() != ValueRange{expected})
          return {};
      }
      cursor = cursor->getNextNode();
      return target.getResult(0);
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(source)) {
      auto target = dyn_cast_or_null<local::BoolConstantOp>(cursor);
      auto value = dyn_cast<IntegerAttr>(constant.getValue());
      if (!target || !value || !value.getType().isSignlessInteger(1) ||
          !constant.getType().isSignlessInteger(1) ||
          target.getValue() != value.getValue().getBoolValue())
        return {};
      cursor = cursor->getNextNode();
      return target.getOutput();
    }
    if (isa<arith::SelectOp>(source)) {
      auto target = dyn_cast_or_null<local::LocalIfOp>(cursor);
      if (!target || target.getNumResults() != 1 ||
          target.getNumOperands() < 2 || target.getNumOperands() > 3 ||
          target.getInputs()[0] != inputs[0])
        return {};
      llvm::DenseSet<Value> captures;
      for (auto value : target.getInputs().drop_front())
        if ((value != inputs[1] && value != inputs[2]) ||
            !captures.insert(value).second)
          return {};
      for (auto [index, region] : enumerate(target->getRegions())) {
        if (!hasSingleElement(region))
          return {};
        auto &block = region.front();
        if (!hasSingleElement(block))
          return {};
        auto yield = dyn_cast<local::LocalYieldOp>(block.back());
        if (!yield || yield.getNumOperands() != 1)
          return {};
        auto selected = dyn_cast<BlockArgument>(yield.getInputs()[0]);
        if (!selected || selected.getOwner() != &block ||
            selected.getArgNumber() + 1 >= target.getNumOperands() ||
            target.getInputs()[selected.getArgNumber() + 1] !=
                inputs[index + 1])
          return {};
      }
      cursor = cursor->getNextNode();
      return target.getResult(0);
    }
    if (isa<arith::AndIOp, arith::OrIOp>(source))
      return take(isa<arith::AndIOp>(source) ? "bool.and" : "bool.or", inputs);
    if (isa<arith::XOrIOp, arith::CmpIOp>(source)) {
      if (auto cmp = dyn_cast<arith::CmpIOp>(source);
          cmp && cmp.getPredicate() != arith::CmpIPredicate::eq &&
          cmp.getPredicate() != arith::CmpIPredicate::ne)
        return {};
      auto disjunction = take("bool.or", inputs);
      auto conjunction = take("bool.and", inputs);
      if (!disjunction || !conjunction)
        return {};
      auto inverse = take("bool.not", ValueRange{conjunction});
      if (!inverse)
        return {};
      auto result = take("bool.and", ValueRange{disjunction, inverse});
      if (!result)
        return {};
      if (auto cmp = dyn_cast<arith::CmpIOp>(source);
          cmp && cmp.getPredicate() == arith::CmpIPredicate::eq) {
        if (!result.hasOneUse())
          return {};
        result = take("bool.not", ValueRange{result});
      }
      // Intermediate work belongs exclusively to this recipe.
      if (!disjunction.hasOneUse() || !conjunction.hasOneUse() ||
          !inverse.hasOneUse())
        return {};
      return result;
    }
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(source))
      return take("field.constant", {},
                  {constant.getResult().getType().getDomain()},
                  {constant.getValue()});
    if (auto at = dyn_cast<algebra::ArrayAtOp>(source)) {
      auto array = at.getArray().getType();
      auto field = cast<algebra::FieldType>(array.getElementType()).getDomain();
      auto length = std::to_string(array.getDimSize(0));
      auto index = std::to_string(at.getIndexAttr().getInt());
      return take("field_array.at", inputs, {field, length}, {index});
    }
    if (isa<tensor::FromElementsOp>(source)) {
      auto array = cast<RankedTensorType>(source->getResult(0).getType());
      auto field = cast<algebra::FieldType>(array.getElementType()).getDomain();
      auto length = std::to_string(array.getDimSize(0));
      auto vector = take("vector.empty", {}, {field});
      for (auto element : inputs) {
        if (!vector || !vector.hasOneUse())
          return {};
        vector = take("vector.append", ValueRange{vector, element}, {field});
      }
      if (!vector || !vector.hasOneUse())
        return {};
      return take("field_array.from_vector", ValueRange{vector},
                  {field, length});
    }
    if (isa<algebra::PairingOp>(source)) {
      auto group = cast<algebra::GroupType>(source->getOperand(0).getType());
      auto field = protocol::installedDomains().associatedIdentity(
          group.getDomain(), "Scalar");
      return take("pairing.apply", inputs, {field});
    }
    StringRef contract, domain;
    if (isa<algebra::SubtractFieldOp>(source))
      contract = "field.sub";
    if (isa<algebra::FieldAddOp>(source))
      contract = "field.add";
    if (isa<algebra::FieldMultiplyOp>(source))
      contract = "field.mul";
    if (isa<algebra::FieldEqualOp>(source))
      contract = "field.equal";
    if (isa<algebra::GroupAddOp>(source))
      contract = "curve.add";
    if (isa<algebra::GroupScaleOp>(source))
      contract = "curve.scale";
    if (isa<algebra::GroupEqualOp>(source))
      contract = "curve.equal";
    if (contract.empty())
      return {};
    if (auto type =
            dyn_cast<algebra::FieldType>(source->getOperand(0).getType()))
      domain = type.getDomain();
    if (auto type =
            dyn_cast<algebra::GroupType>(source->getOperand(0).getType()))
      domain = type.getDomain();
    return take(contract, inputs, {domain});
  }

  bool guard(local::GuardOp source, Operation *&cursor, Value condition) {
    auto branch = dyn_cast_or_null<local::LocalIfOp>(cursor);
    if (!branch || branch.getNumResults() ||
        branch.getInputs() != ValueRange{condition})
      return false;
    if (!hasSingleElement(branch.getThenRegion()) ||
        !hasSingleElement(branch.getElseRegion()))
      return false;
    auto &yes = branch.getThenRegion().front();
    auto &no = branch.getElseRegion().front();
    if (!hasSingleElement(yes) || !hasSingleElement(no))
      return false;
    auto yield = dyn_cast<local::LocalYieldOp>(yes.back());
    auto stop = dyn_cast<local::StopOp>(no.back());
    if (!yield || yield.getNumOperands() || !stop ||
        stop.getReason() != "reject" || stop.getSite() != source.getSite())
      return false;
    cursor = cursor->getNextNode();
    return true;
  }

  LogicalResult participant(protocol_ir::ParticipantOp source,
                            protocol_ir::ParticipantOp target) {
    if (source->getAttrDictionary() != target->getAttrDictionary())
      return refuse(target, "lowering changed the participant interface");
    return block(source.getBody().front(), target.getBody().front(), target);
  }
  LogicalResult block(Block &original, Block &candidate, Operation *target) {
    if (original.getArgumentTypes() != candidate.getArgumentTypes() ||
        original.empty() || candidate.empty())
      return refuse(target, "lowering changed a region interface");
    llvm::DenseMap<Value, Value> participantValues;
    llvm::DenseMap<Value, Value> sourceValues;
    for (auto [a, b] : zip(original.getArguments(), candidate.getArguments())) {
      participantValues[a] = b;
      sourceValues[b] = a;
    }
    llvm::DenseMap<Operation *, unsigned> order;
    llvm::DenseSet<Operation *> realized;
    unsigned index = 0;
    for (auto &op : original)
      order[&op] = index++;
    auto *cursor = &candidate.front();
    for (auto &action : original) {
      if (isTotal(&action))
        continue;
      // Stop at operations realized at an earlier cut, even when an internal
      // result was not exported. A later demand for that result must then fail
      // capture matching, rather than silently permit recomputation.
      SmallVector<Value> pending(action.getOperands());
      SmallVector<Operation *> needed;
      llvm::DenseSet<Operation *> visited;
      while (!pending.empty()) {
        auto value = pending.pop_back_val();
        if (!charge())
          return refuse(target, "lowering comparison work limit exceeded");
        auto *definition = value.getDefiningOp();
        if (!definition || !isTotal(definition) ||
            realized.contains(definition) || !visited.insert(definition).second)
          continue;
        needed.push_back(definition);
        append_range(pending, definition->getOperands());
      }
      llvm::sort(needed, [&](Operation *a, Operation *b) {
        return order[a] < order[b];
      });
      auto sourceGuard = dyn_cast<local::GuardOp>(action);
      if (!needed.empty() || sourceGuard) {
        auto call = dyn_cast_or_null<local::CallOp>(cursor);
        auto function = call ? dyn_cast_or_null<local::FuncOp>(
                                   symbols.lookup(call.getCallee()))
                             : local::FuncOp();
        if (!function || !generated.contains(function) ||
            !invoked.insert(function).second)
          return refuse(target,
                        "missing or reused calculation at its first demand");
        // Diagnose the existing one-calculation policy at the demand boundary.
        // Splitting a valid calculation changes local invocations and finite
        // costs.
        if (!sourceGuard) {
          auto next = dyn_cast_or_null<local::CallOp>(call->getNextNode());
          auto nextFunction = next ? dyn_cast_or_null<local::FuncOp>(
                                         symbols.lookup(next.getCallee()))
                                   : local::FuncOp();
          if (nextFunction && generated.contains(nextFunction))
            return refuse(call, "multiple calculations at one cut");
        }
        if (sourceGuard && call.getSite() != sourceGuard.getSite())
          return refuse(call, "guard invocation changed its occurrence");
        llvm::DenseMap<Value, Value> localValues;
        llvm::DenseSet<Value> usedCaptures;
        for (auto [input, argument] :
             zip(call.getInputs(), function.getArguments())) {
          auto value = sourceValues.lookup(input);
          if (!value || !localValues.try_emplace(value, argument).second)
            return refuse(call, "calculation changed or duplicated a capture");
        }
        auto lookup = [&](Value value) -> Value {
          auto mapped = localValues.lookup(value);
          if (mapped && isa<BlockArgument>(mapped))
            usedCaptures.insert(mapped);
          return mapped;
        };
        auto *instruction = &function.getBody().front().front();
        for (auto *op : needed) {
          if (op->getNumResults() != 1)
            return refuse(call, "recipe requires one result");
          auto dependencies = operandDependencies(op, 0);
          if (failed(dependencies) ||
              dependencies->size() != op->getNumOperands())
            return refuse(call,
                          "recipe requires complete operand dependencies");
          for (auto [index, operand] : enumerate(*dependencies))
            if (index != operand)
              return refuse(call, "recipe dependency ordering changed");
          SmallVector<Value> inputs;
          for (auto operand : op->getOperands()) {
            auto value = lookup(operand);
            if (!value)
              return refuse(call, "calculation lost a mathematical dependency");
            inputs.push_back(value);
          }
          auto value = recipe(op, instruction, inputs);
          if (!value || op->getNumResults() != 1 ||
              value.getType() != op->getResult(0).getType())
            return refuse(call,
                          "calculation changed an execution recipe or operand");
          localValues[op->getResult(0)] = value;
          realized.insert(op);
        }
        if (sourceGuard && !guard(sourceGuard, instruction,
                                  lookup(sourceGuard.getCondition())))
          return refuse(call,
                        "calculation changed the guard condition or rejection");
        auto returned = dyn_cast_or_null<local::ReturnOp>(instruction);
        if (!returned || instruction->getNextNode() ||
            usedCaptures.size() != call.getNumOperands())
          return refuse(call,
                        "calculation contains extra work or unused captures");
        llvm::DenseMap<Value, Value> results;
        for (auto *op : needed)
          results[localValues.lookup(op->getResult(0))] = op->getResult(0);
        llvm::DenseSet<Value> exported;
        for (auto [value, output] :
             zip(returned.getInputs(), call.getResults())) {
          auto originalValue = results.lookup(value);
          if (!originalValue || !exported.insert(originalValue).second ||
              output.use_empty())
            return refuse(call, "calculation changed or duplicated a result");
          participantValues[originalValue] = output;
          sourceValues[output] = originalValue;
        }
        cursor = cursor->getNextNode();
      }
      if (sourceGuard)
        continue;
      if (!cursor || cursor->getName() != action.getName() ||
          cursor->getAttrDictionary() != action.getAttrDictionary() ||
          cursor->getOperandTypes() != action.getOperandTypes() ||
          cursor->getResultTypes() != action.getResultTypes())
        return refuse(target, "lowering changed ordered participant actions");
      for (auto [a, b] : zip(action.getOperands(), cursor->getOperands()))
        if (participantValues.lookup(a) != b)
          return refuse(cursor, "lowering changed an action operand");
      if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(action)) {
        auto lowered = cast<protocol_ir::ProtocolLoopOp>(cursor);
        if (failed(block(loop.getBody().front(), lowered.getBody().front(),
                         cursor)))
          return failure();
      }
      for (auto [a, b] : zip(action.getResults(), cursor->getResults())) {
        participantValues[a] = b;
        sourceValues[b] = a;
      }
      cursor = cursor->getNextNode();
    }
    return cursor ? refuse(target, "lowering added a participant action")
                  : success();
  }

public:
  LoweringVerifier(protocol_ir::ProtocolModuleOp before,
                   protocol_ir::ProtocolModuleOp after)
      : before(before), after(after), sourceSymbols(before), symbols(after) {}
  LogicalResult calculations(ArrayRef<local::FuncOp> functions) {
    for (auto target : functions) {
      auto source = sourceSymbols.lookup<local::FuncOp>(target.getSymName());
      if (!source ||
          source->getAttrDictionary() != target->getAttrDictionary() ||
          !hasSingleElement(source.getBody()) ||
          !hasSingleElement(target.getBody()))
        return refuse(target, "realized calculation interface changed");
      llvm::DenseMap<Value, Value> values;
      for (auto [a, b] : zip(source.getArguments(), target.getArguments()))
        values[a] = b;
      auto *cursor = &target.getBody().front().front();
      for (auto &op : source.getBody().front()) {
        if (!charge(1 + op.getNumOperands() + op.getNumResults()))
          return refuse(target, "lowering comparison work limit exceeded");
        SmallVector<Value> inputs;
        for (auto operand : op.getOperands()) {
          auto value = values.lookup(operand);
          if (!value)
            return refuse(target, "realized calculation lost a dependency");
          inputs.push_back(value);
        }
        if (isa<local::ReturnOp>(op)) {
          auto returned = dyn_cast_or_null<local::ReturnOp>(cursor);
          if (!returned || cursor->getNextNode() ||
              returned.getInputs() != ValueRange(inputs))
            return refuse(target, "realized calculation changed its return");
          cursor = nullptr;
          continue;
        }
        if (!isTotal(&op) || op.getNumResults() != 1)
          return refuse(target, "unexpected realized mathematical operation");
        auto value = recipe(&op, cursor, inputs);
        if (!value || value.getType() != op.getResult(0).getType() ||
            value.use_empty())
          return refuse(
              target,
              "realized calculation changed a recipe, operand or liveness");
        values[op.getResult(0)] = value;
      }
      if (cursor)
        return refuse(target, "realized calculation contains extra work");
    }
    return success();
  }
  LogicalResult run() {
    if (before.getProfile() != protocol_ir::Profile::Participant ||
        after.getProfile() != protocol_ir::Profile::Exec)
      return refuse(after, "expected 'participant' to 'exec' profiles");
    // Formation already bounded types, attributes and regions. Account for
    // operations and operand edges across the whole pair before inspecting it.
    for (auto unit : {before, after}) {
      auto walk = unit.walk([&](Operation *op) {
        return charge(1 + op->getNumOperands() + op->getNumResults())
                   ? WalkResult::advance()
                   : WalkResult::interrupt();
      });
      if (walk.wasInterrupted())
        return refuse(after, "lowering comparison work limit exceeded");
    }
    auto records = after.getBody().front().getOps<protocol_ir::ProjectionOp>();
    if (!hasSingleElement(records))
      return refuse(after, "lowering requires one projection record");
    auto record = *records.begin();
    // Module verification already ties every (participant, callee, site) record
    // to exactly one invocation. This check owns the frozen-source recipe.
    for (auto item : record.getCalculations()) {
      auto ref = cast<DictionaryAttr>(item).getAs<FlatSymbolRefAttr>("callee");
      auto *function = symbols.lookup(ref.getValue());
      if (!function || !generated.insert(function).second)
        return refuse(record, "calculation callee is not unique");
      if (sourceSymbols.lookup(ref.getValue()))
        return refuse(record, "calculation callee must be fresh");
      auto local = dyn_cast<local::FuncOp>(function);
      if (!local || !hasSingleElement(local.getBody()))
        return refuse(record, "calculation must have one local body");
      Builder builder(after.getContext());
      auto origin = builder.getArrayAttr(
          {builder.getStringAttr(ref.getValue()), builder.getArrayAttr({})});
      const StringRef identityAttributes[] = {"sym_name", "function_type",
                                              "logical_origin"};
      if (function->getAttrs().size() != std::size(identityAttributes) ||
          !all_of(function->getAttrs(),
                  [&](NamedAttribute attribute) {
                    return is_contained(identityAttributes,
                                        attribute.getName().getValue());
                  }) ||
          function->getAttr("logical_origin") != origin)
        return refuse(function, "calculation changed its generated identity");
    }
    unsigned count = 0;
    for (auto original :
         before.getBody().front().getOps<protocol_ir::ParticipantOp>()) {
      auto candidate = dyn_cast_or_null<protocol_ir::ParticipantOp>(
          symbols.lookup(original.getSymName()));
      if (!candidate)
        return refuse(after, "lowering lost a participant");
      if (failed(participant(original, candidate)))
        return failure();
      ++count;
    }
    if (count !=
            llvm::range_size(
                after.getBody().front().getOps<protocol_ir::ParticipantOp>()) ||
        generated.size() != invoked.size())
      return refuse(after,
                    "lowering added participants or unused calculations");
    // Only outlined functions and bindings used by their recipes may extend
    // the frozen symbol table. Even unused executable declarations affect
    // later admission and exported artifacts.
    llvm::DenseSet<Operation *> recipeBindings;
    for (auto *function : generated)
      function->walk([&](Operation *op) {
        if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
          recipeBindings.insert(symbols.lookup(reference.getValue()));
      });
    for (auto &definition : after.getBody().front()) {
      auto name = SymbolTable::getSymbolName(&definition);
      if (name && !sourceSymbols.lookup(name) &&
          !generated.contains(&definition) &&
          !recipeBindings.contains(&definition))
        return refuse(&definition, "lowering added an untracked declaration");
    }
    llvm::DenseMap<Operation *, unsigned> uses;
    after.walk([&](local::CallOp call) {
      auto *callee = symbols.lookup(call.getCallee());
      if (generated.contains(callee))
        ++uses[callee];
    });
    for (auto *function : generated)
      if (uses.lookup(function) != 1)
        return refuse(function, "calculation must have exactly one invocation");
    return success();
  }
};
} // namespace
LogicalResult verifyCalculationRecipes(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate,
                                       ArrayRef<local::FuncOp> functions) {
  return LoweringVerifier(original, candidate).calculations(functions);
}
LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                 protocol_ir::ProtocolModuleOp candidate) {
  return LoweringVerifier(original, candidate).run();
}
} // namespace zkc::mathematical
