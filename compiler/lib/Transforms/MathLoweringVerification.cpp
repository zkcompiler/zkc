#include "CollectionInterpretation.h"
#include "HelperNormalization.h"
#include "MathematicalSupport.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Transforms/Finite.h"
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
  const CheckedHelperNormalizations &helpers;
  size_t remaining = 1000000;
  finite::VerificationLimits finiteLimits;
  finite::VerificationResult finiteOutcome{finite::VerificationStatus::Mismatch,
                                           {}};
  finite::VerificationResult *reportedOutcome = nullptr;

  LogicalResult refuse(Operation *op, StringRef detail) {
    if (finiteOutcome.status == finite::VerificationStatus::OptionalCapacity ||
        finiteOutcome.status == finite::VerificationStatus::RequiredCapacity) {
      if (reportedOutcome) {
        *reportedOutcome = finiteOutcome;
        return failure();
      }
      return diagnostics::emit(op->emitOpError(),
                               "finite-verification-capacity",
                               finiteOutcome.detail);
    }
    return diagnostics::emit(op->emitOpError(),
                             "mathematical-lowering-preservation", detail);
  }
  bool charge(size_t amount = 1) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
  // Generated instructions belong to the source occurrence that introduced
  // their recipe. Global admission separately checks uniqueness. Suffix
  // allocation is deliberately not used as mathematical evidence.
  bool occurrences(Operation *begin, Operation *end, StringRef root,
                   bool finite) {
    auto prefix = (root + (finite ? "_finite_" : "_recipe_")).str();
    for (auto *op = begin; op != end; op = op->getNextNode()) {
      if (!op)
        return false;
      auto walk = op->walk([&](Operation *nested) {
        if (!charge())
          return WalkResult::interrupt();
        auto site = nested->getAttrOfType<StringAttr>("site");
        if (site && site.getValue() != root &&
            !site.getValue().starts_with(prefix))
          return WalkResult::interrupt();
        return WalkResult::advance();
      });
      if (walk.wasInterrupted())
        return false;
    }
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
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() || !site ||
        site.getValue().empty() || op->getAttrs().size() != 3 || !parameters ||
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

  FailureOr<SmallVector<Value>>
  finiteRecipe(Operation *source, Operation *&cursor, ValueRange inputs) {
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto result = finite::verifyExpression(
        source, inputs, cursor,
        [&](Operation *helper, ValueRange args,
            Operation *&at) -> FailureOr<SmallVector<Value>> {
          // Only independently checked proposals are available here. Lookup
          // is read-only: this verifier cannot run either normalizer.
          auto normalized = helpers.lookup(helper);
          if (!normalized || normalized.getNumArguments() != args.size())
            return failure();
          auto &body = normalized.front();
          llvm::DenseMap<Value, Value> values;
          for (auto [a, b] : zip(body.getArguments(), args)) {
            if (a.getType() != b.getType())
              return failure();
            values[a] = b;
          }
          for (auto &op : body.without_terminator()) {
            if (!charge(1 + op.getNumOperands() + op.getNumResults()))
              return failure();
            SmallVector<Value> operands;
            for (Value v : op.getOperands()) {
              auto value = values.lookup(v);
              if (!value)
                return failure();
              operands.push_back(value);
            }
            if (finite::isComputation(&op)) {
              auto results = finiteRecipe(&op, at, operands);
              if (failed(results) || results->size() != op.getNumResults())
                return failure();
              for (auto [a, b] : zip(op.getResults(), *results))
                values[a] = b;
            } else {
              auto value = recipe(&op, at, operands);
              if (!value || op.getNumResults() != 1 ||
                  value.getType() != op.getResult(0).getType())
                return failure();
              values[op.getResult(0)] = value;
            }
          }
          SmallVector<Value> results;
          for (Value v : body.back().getOperands()) {
            auto value = values.lookup(v);
            if (!value)
              return failure();
            results.push_back(value);
          }
          return results;
        },
        before, finiteLimits, outcome);
    // A recursive finite callback may already have reported capacity; its
    // enclosing ordered reader must not replace that cause with a mismatch.
    if (failed(result) &&
        finiteOutcome.status == finite::VerificationStatus::Mismatch)
      finiteOutcome = outcome;
    return result;
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
    if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(source)) {
      auto col = interpretCollection(inputs[0].getType());
      SmallVector<StringRef> args;
      for (auto &arg : col.arguments)
        args.push_back(arg);
      return take(col.access, inputs, args);
    }
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
      auto collection = cast<CollectionTypeInterface>(dim.getInput().getType());
      auto axis = dim.getAxisAttr().getInt();
      if (auto extent = collection.getStaticExtent(axis)) {
        auto length = std::to_string(*extent);
        return take("index.constant", {}, {}, {length});
      }
      if (auto field =
              dyn_cast<algebra::FieldType>(collection.getElementType())) {
        if (collection.getRank() == 1)
          return take("vector.length", inputs, {field.getDomain()});
        auto coordinate = std::to_string(axis);
        return take("matrix.dimension", inputs, {field.getDomain()},
                    {coordinate});
      }
      if (auto group =
              dyn_cast<algebra::GroupType>(collection.getElementType()))
        return take("curve.length", inputs, {group.getDomain()});
      return take(collection.getCollectionKind() == CollectionKind::Bytes
                      ? "bytes.length"
                      : "indices.length",
                  inputs);
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
      auto length = std::to_string(array.getLength());
      auto index = std::to_string(at.getIndexAttr().getInt());
      return take("field_array.at", inputs, {field, length}, {index});
    }
    if (isa<algebra::ArrayFromElementsOp>(source)) {
      auto array =
          cast<algebra::FieldArrayType>(source->getResult(0).getType());
      auto field = cast<algebra::FieldType>(array.getElementType()).getDomain();
      auto length = std::to_string(array.getLength());
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
    if (auto identity = dyn_cast<algebra::GroupIdentityOp>(source))
      return take("curve.identity", {},
                  {identity.getResult().getType().getDomain()});
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
          if (op->getNumResults() != 1 && !finite::isComputation(op))
            return refuse(call,
                          "recipe requires one result or a finite state list");
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
          if (finite::isComputation(op)) {
            auto results = finiteRecipe(op, instruction, inputs);
            if (failed(results) || results->size() != op->getNumResults())
              return refuse(call, "finite recipe result arity");
            for (auto [a, b] : zip(op->getResults(), *results)) {
              if (!b || a.getType() != b.getType())
                return refuse(call, "finite recipe result type");
              localValues[a] = b;
            }
            realized.insert(op);
            continue;
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
          for (Value result : op->getResults())
            results[localValues.lookup(result)] = result;
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
                   protocol_ir::ProtocolModuleOp after,
                   const CheckedHelperNormalizations &helpers,
                   finite::VerificationLimits finiteLimits = {},
                   finite::VerificationResult *outcome = nullptr)
      : before(before), after(after), sourceSymbols(before), symbols(after),
        helpers(helpers), finiteLimits(finiteLimits), reportedOutcome(outcome) {
  }
  LogicalResult calculations(ArrayRef<local::FuncOp> functions,
                             bool realization = false) {
    for (auto target : functions) {
      Block *sourceBody = nullptr;
      if (realization) {
        auto declaration =
            sourceSymbols.lookup<local::RealizeOp>(target.getSymName());
        auto helper =
            declaration
                ? sourceSymbols.lookup<func::FuncOp>(declaration.getHelper())
                : func::FuncOp();
        auto normalized =
            helper ? helpers.lookup(helper, true) : func::FuncOp();
        if (normalized &&
            normalized.getFunctionType() == target.getFunctionType())
          sourceBody = &normalized.front();
      } else {
        auto source = sourceSymbols.lookup<local::FuncOp>(target.getSymName());
        if (source &&
            source->getAttrDictionary() == target->getAttrDictionary() &&
            source.getBody().hasOneBlock())
          sourceBody = &source.getBody().front();
      }
      if (!sourceBody || !hasSingleElement(target.getBody()) ||
          !llvm::equal(sourceBody->getArgumentTypes(),
                       target.getArgumentTypes()))
        return refuse(target, "realized calculation interface changed");
      llvm::DenseMap<Value, Value> values;
      for (auto [a, b] : zip(sourceBody->getArguments(), target.getArguments()))
        values[a] = b;
      auto *cursor = &target.getBody().front().front();
      unsigned occurrence = 0;
      for (auto &op : *sourceBody) {
        if (!charge(1 + op.getNumOperands() + op.getNumResults()))
          return refuse(target, "lowering comparison work limit exceeded");
        SmallVector<Value> inputs;
        for (auto operand : op.getOperands()) {
          auto value = values.lookup(operand);
          if (!value)
            return refuse(target, "realized calculation lost a dependency");
          inputs.push_back(value);
        }
        if (isa<local::ReturnOp, func::ReturnOp>(op)) {
          auto returned = dyn_cast_or_null<local::ReturnOp>(cursor);
          if (!returned || cursor->getNextNode() ||
              returned.getInputs() != ValueRange(inputs))
            return refuse(target, "realized calculation changed its return");
          cursor = nullptr;
          continue;
        }
        if (auto sourceGuard = dyn_cast<local::GuardOp>(op)) {
          // Participant outlining includes the guard at its demand boundary.
          // It has no result, but its condition and rejection remain part of
          // the independently checked calculation.
          if (realization || inputs.size() != 1 ||
              !guard(sourceGuard, cursor, inputs.front()))
            return refuse(target, "realized calculation changed its guard");
          continue;
        }
        if (finite::isComputation(&op)) {
          auto *begin = cursor;
          auto results = finiteRecipe(&op, cursor, inputs);
          if (failed(results) || results->size() != op.getNumResults())
            return refuse(target, "finite multi-result recipe changed");
          for (auto [a, b] : zip(op.getResults(), *results))
            values[a] = b;
          if (realization &&
              !occurrences(begin, cursor, "value_" + std::to_string(occurrence),
                           true))
            return refuse(target, "finite recipe changed its occurrence");
          ++occurrence;
          continue;
        }
        if (!isTotal(&op) || op.getNumResults() != 1)
          return refuse(target, "unexpected realized mathematical operation");
        auto *begin = cursor;
        auto value = recipe(&op, cursor, inputs);
        // A checked finite realization may discard an ignored capture in an
        // outlined participant calculation. Its eagerly computed primitive
        // still has to match exactly, even when it is no longer used.
        if (!value || value.getType() != op.getResult(0).getType() ||
            (realization && value.use_empty()))
          return refuse(
              target,
              "realized calculation changed a recipe, operand or liveness");
        // The complete local.realize path assigns these root occurrences
        // before lowering; expanded recipe intermediates have their own sites.
        if (realization) {
          auto root = "value_" + std::to_string(occurrence);
          auto site = value.getDefiningOp()->getAttrOfType<StringAttr>("site");
          if (!site || site.getValue() != root ||
              !occurrences(begin, cursor, root, false))
            return refuse(target,
                          "realized calculation changed its occurrence");
        }
        ++occurrence;
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
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch, {}};
  auto result =
      verifyCalculationRecipes(original, candidate, functions, {}, outcome);
  if (failed(result) &&
      (outcome.status == finite::VerificationStatus::OptionalCapacity ||
       outcome.status == finite::VerificationStatus::RequiredCapacity))
    return diagnostics::emit(candidate.emitError(),
                             "finite-verification-capacity", outcome.detail);
  return result;
}
LogicalResult verifyCalculationRecipes(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate,
                                       ArrayRef<local::FuncOp> functions,
                                       finite::VerificationLimits limits,
                                       finite::VerificationResult &outcome) {
  outcome = {finite::VerificationStatus::Mismatch,
             "calculation recipes differ"};
  CheckedHelperNormalizations helpers(original);
  SymbolTable symbols(original);
  for (auto function : functions) {
    auto source = symbols.lookup<local::FuncOp>(function.getSymName());
    if (!source || failed(helpers.prepare(source)))
      return failure();
  }
  auto result = LoweringVerifier(original, candidate, helpers, limits, &outcome)
                    .calculations(functions);
  if (succeeded(result))
    outcome = {finite::VerificationStatus::Verified, {}};
  return result;
}
LogicalResult
verifyRealizedHelperRecipes(protocol_ir::ProtocolModuleOp original,
                            protocol_ir::ProtocolModuleOp candidate,
                            ArrayRef<local::FuncOp> functions) {
  CheckedHelperNormalizations helpers(original);
  SymbolTable symbols(original);
  for (auto function : functions) {
    auto declaration = symbols.lookup<local::RealizeOp>(function.getSymName());
    auto helper = declaration
                      ? symbols.lookup<func::FuncOp>(declaration.getHelper())
                      : func::FuncOp();
    if (!helper || failed(helpers.prepareRealization(helper)))
      return failure();
  }
  return verifyRealizedHelperRecipes(original, candidate, functions, helpers);
}
LogicalResult
verifyRealizedHelperRecipes(protocol_ir::ProtocolModuleOp original,
                            protocol_ir::ProtocolModuleOp candidate,
                            ArrayRef<local::FuncOp> functions,
                            const CheckedHelperNormalizations &helpers) {
  return LoweringVerifier(original, candidate, helpers)
      .calculations(functions, true);
}
LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                 protocol_ir::ProtocolModuleOp candidate) {
  CheckedHelperNormalizations helpers(original);
  for (auto participant :
       original.getBody().front().getOps<protocol_ir::ParticipantOp>())
    if (failed(helpers.prepare(participant)))
      return failure();
  return LoweringVerifier(original, candidate, helpers).run();
}
} // namespace zkc::mathematical
