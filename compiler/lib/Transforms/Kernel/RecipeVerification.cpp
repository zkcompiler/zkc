#include "../CollectFold.h"
#include "../CollectionInterpretation.h"
#include "../HelperNormalization.h"
#include "../MathematicalSupport.h"
#include "../RealizationSubject.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"

#include "zkc/Transforms/Algorithms.h"

using namespace mlir;
using namespace llvm;
using namespace zkc::mathematical;
namespace zkc::kernel {
namespace {
// Read the retained numerical source and actual executable recipes. This
// reader never invokes conversion, selection or normalization producers.
class RecipeReader {
  Operation *sourceRoot;
  SymbolTable symbols;
  const CheckedHelperNormalizations &helpers;
  uint64_t remaining = 1000000;
  bool allowFiniteBulk = true;
  NumericalSelection *selection = nullptr;
  std::optional<RealizationSubject> activeSubject;
  unsigned nextChild = 0;
  uint64_t compositionInspection = 100000;
  finite::VerificationLimits finiteLimits;
  finite::VerificationResult finiteOutcome{finite::VerificationStatus::Mismatch,
                                           "numerical recipes differ"};
  bool charge(uint64_t amount = 1) {
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

  FailureOr<SmallVector<Value>> readHelper(Operation *helper, ValueRange args,
                                           Operation *&at, Value collected = {},
                                           Value position = {},
                                           Value element = {}) {
    // Only exact bounded closure snapshots are available here. Lookup
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
      if (collected && isa<data::BoundedAtOp>(op) && operands.size() == 2 &&
          operands[0] == collected && operands[1] == position) {
        if (op.getNumResults() != 1 ||
            op.getResult(0).getType() != element.getType())
          return failure();
        values[op.getResult(0)] = element;
        continue;
      }
      if (collected && is_contained(operands, collected))
        return failure();
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
  }
  FailureOr<SmallVector<Value>> finiteRecipe(Operation *source,
                                             Operation *&cursor,
                                             ValueRange inputs,
                                             bool root = false) {
    auto inherited = activeSubject;
    auto inheritedChild = nextChild;
    auto subject = root || !activeSubject
                       ? realizationSubject(source)
                       : NumericalSelection::childSubject(
                             *activeSubject, source->getName().getStringRef(),
                             nextChild++);
    if (!root)
      inheritedChild = nextChild;
    activeSubject = subject;
    nextChild = 0;
    auto restore = llvm::scope_exit([&] {
      activeSubject = inherited;
      nextChild = inheritedChild;
    });
    auto *begin = cursor;
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto result = finite::verifyExpression(
        source, inputs, cursor,
        [&](Operation *helper, ValueRange args,
            Operation *&at) -> FailureOr<SmallVector<Value>> {
          return readHelper(helper, args, at);
        },
        sourceRoot, finiteLimits, outcome, {allowFiniteBulk, false});
    if (failed(result) &&
        (outcome.status == finite::VerificationStatus::OptionalCapacity ||
         outcome.status == finite::VerificationStatus::RequiredCapacity))
      outcome.subject = subject;
    if (succeeded(result) && selection && !root) {
      auto owner = selection->discover(subject, allowFiniteBulk);
      if (!owner) {
        consumeError(owner.takeError());
        finiteOutcome = {finite::VerificationStatus::RequiredCapacity,
                         "numerical occurrence discovery",
                         {},
                         subject};
        return failure();
      }
      for (auto *at = begin; at != cursor; at = at->getNextNode()) {
        if (!at)
          return failure();
        at->walk([&](Operation *nested) { selection->record(nested, *owner); });
      }
    }
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

public:
  RecipeReader(Operation *sourceRoot, Operation *targetRoot,
               const CheckedHelperNormalizations &helpers,
               finite::VerificationLimits limits, NumericalSelection *selection)
      : sourceRoot(sourceRoot), symbols(targetRoot), helpers(helpers),
        selection(selection), finiteLimits(limits) {}
  FailureOr<SmallVector<Value>> read(func::FuncOp entry, StringRef callSite,
                                     ValueRange arguments, Operation *&cursor,
                                     uint64_t &budget, uint64_t &remainingBytes,
                                     MathematicalSelectionPolicy policy,
                                     finite::VerificationResult &outcome) {
    allowFiniteBulk = policy.finiteBulk;
    remaining = std::min<uint64_t>(remaining, budget);
    auto initial = remaining;
    auto finish =
        [&](bool valid,
            SmallVector<Value> values = {}) -> FailureOr<SmallVector<Value>> {
      budget -= initial - remaining;
      outcome =
          valid
              ? finite::VerificationResult{finite::VerificationStatus::Verified,
                                           {}}
              : finiteOutcome;
      return valid ? FailureOr<SmallVector<Value>>(std::move(values))
                   : FailureOr<SmallVector<Value>>(failure());
    };
    if (arguments.size() != entry.getNumArguments())
      return finish(false);
    llvm::DenseMap<Value, Value> values;
    for (auto [source, actual] : zip(entry.getArguments(), arguments)) {
      if (source.getType() != actual.getType())
        return finish(false);
      values[source] = actual;
    }
    unsigned ordinal = 0;
    Operation *consumed = nullptr;
    for (auto &op : entry.getBody().front()) {
      if (&op == consumed) {
        auto skippedSite =
            protocol::algorithmSite({{callSite.str(), "kernel"}},
                                    std::to_string(ordinal++), remainingBytes);
        if (!skippedSite) {
          consumeError(skippedSite.takeError());
          return finish(false);
        }
        consumed = nullptr;
        continue;
      }
      if (!charge(1 + op.getNumOperands() + op.getNumResults()))
        return finish(false);
      SmallVector<Value> inputs;
      for (Value value : op.getOperands()) {
        auto actual = values.lookup(value);
        if (!actual)
          return finish(false);
        inputs.push_back(actual);
      }
      if (isa<func::ReturnOp>(op))
        return finish(true, inputs);
      auto *begin = cursor;
      SmallVector<Value> results;
      bool finite = finite::isComputation(&op);
      if (finite) {
        activeSubject = realizationSubject(&op);
        nextChild = 0;
      }
      Operation *resultSource = &op;
      bool composed = false;
      std::optional<finite::VerificationResult> compositionFailure;
      if (finite && policy.collectFoldFusion) {
        auto pair = finite::readCollectFold(&op, op.getNextNode(),
                                            compositionInspection);
        if (succeeded(pair)) {
          SmallVector<Value> consumerInputs;
          bool complete = true;
          for (Value operand : pair->consumer.operation->getOperands()) {
            auto value =
                operand == pair->collected ? operand : values.lookup(operand);
            if (!value)
              complete = false;
            consumerInputs.push_back(value);
          }
          auto *at = cursor;
          if (complete) {
            finite::VerificationResult composedOutcome{
                finite::VerificationStatus::Mismatch, {}};
            auto read = finite::verifyCollectFold(
                *pair, inputs, consumerInputs, at,
                [&](Operation *helper, ValueRange args, Operation *&where) {
                  return readHelper(helper, args, where);
                },
                [&](Operation *helper, ValueRange args, Operation *&where,
                    Value collected, Value position, Value element) {
                  return readHelper(helper, args, where, collected, position,
                                    element);
                },
                finiteLimits, composedOutcome);
            if (succeeded(read)) {
              results = *read;
              cursor = at;
              consumed = pair->consumer.operation;
              resultSource = consumed;
              composed = true;
            } else
              compositionFailure = composedOutcome;
          }
        }
      }
      if (composed) {
        // Both source callbacks have been read against this actual traversal.
      } else if (finite) {
        auto read = finiteRecipe(&op, cursor, inputs, true);
        if (failed(read)) {
          if (compositionFailure &&
              finiteOutcome.status == finite::VerificationStatus::Mismatch)
            finiteOutcome = *compositionFailure;
          return finish(false);
        }
        results = *read;
      } else {
        auto value = recipe(&op, cursor, inputs);
        if (!value)
          return finish(false);
        results.push_back(value);
      }
      if (finite && selection) {
        auto owner =
            selection->discover(realizationSubject(&op), policy.finiteBulk,
                                policy.numericalExpressions);
        if (!owner) {
          consumeError(owner.takeError());
          finiteOutcome = {finite::VerificationStatus::RequiredCapacity,
                           "numerical occurrence discovery"};
          return finish(false);
        }
        for (auto *at = begin; at != cursor; at = at->getNextNode()) {
          if (!at)
            return finish(false);
          at->walk(
              [&](Operation *nested) { selection->record(nested, *owner); });
        }
      }
      auto site =
          protocol::algorithmSite({{callSite.str(), "kernel"}},
                                  std::to_string(ordinal++), remainingBytes);
      if (!site) {
        consumeError(site.takeError());
        return finish(false);
      }
      if (results.size() != resultSource->getNumResults() ||
          !occurrences(begin, cursor, *site, finite))
        return finish(false);
      // Primitive roots keep the original occurrence, while a finite recipe
      // has its documented traversal suffixes. No label establishes meaning.
      if (!finite && !results.empty()) {
        auto rootSite =
            results.back().getDefiningOp()->getAttrOfType<StringAttr>("site");
        if (!rootSite || rootSite.getValue() != *site)
          return finish(false);
      }
      for (auto [source, actual] : zip(resultSource->getResults(), results)) {
        if (source.getType() != actual.getType())
          return finish(false);
        values[source] = actual;
      }
    }
    return finish(false);
  }
};
} // namespace
FailureOr<SmallVector<Value>> verifyKernelRecipes(
    func::FuncOp source, Operation *targetRoot, StringRef callSite,
    ValueRange arguments, Operation *&cursor, uint64_t &remaining,
    uint64_t &remainingBytes, MathematicalSelectionPolicy policy,
    finite::VerificationLimits limits, finite::VerificationResult &outcome,
    NumericalSelection *selection) {
  outcome = {finite::VerificationStatus::Mismatch, "numerical recipes differ"};
  auto unit =
      source ? dyn_cast_or_null<ModuleOp>(source->getParentOp()) : ModuleOp();
  if (!unit || source != getEntry(unit) || !source.getBody().hasOneBlock() ||
      source.front().empty() || callSite.empty())
    return failure();
  CheckedHelperNormalizations helpers(unit);
  if (failed(helpers.readback(&remaining)))
    return failure();
  return RecipeReader(unit, targetRoot, helpers, limits, selection)
      .read(source, callSite, arguments, cursor, remaining, remainingBytes,
            policy, outcome);
}

LogicalResult verifyRecipeOutput(mlir::ModuleOp candidate) {
  if (!candidate || candidate->getNumRegions() != 1 ||
      !candidate.getBodyRegion().hasOneBlock() ||
      !candidate->getAttrs().empty() ||
      candidate.getBody()->getNumArguments() ||
      !hasSingleElement(*candidate.getBody()) ||
      failed(candidate->getName().verifyInvariants(candidate)))
    return failure();
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  // This is a Local fragment, not an independently runnable participant
  // program. Reuse its established admission instead of inventing dummy
  // participants or weakening whole-program Entry requirements.
  return verifyLocalFragment(owner);
}

LogicalResult verifyEntryRecipes(ModuleOp source, mlir::ModuleOp candidate,
                                 StringRef callSite,
                                 MathematicalSelectionPolicy policy,
                                 finite::VerificationLimits limits,
                                 finite::VerificationResult *reported,
                                 NumericalSelection *selection) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                     "numerical recipes differ"};
  auto finish = [&](bool valid) -> LogicalResult {
    if (valid)
      outcome = {finite::VerificationStatus::Verified, {}};
    else if (outcome.status == finite::VerificationStatus::Verified)
      outcome = {finite::VerificationStatus::Mismatch,
                 "numerical return differs"};
    if (reported)
      *reported = outcome;
    if (!valid && !reported) {
      const bool capacity =
          outcome.status == finite::VerificationStatus::OptionalCapacity ||
          outcome.status == finite::VerificationStatus::RequiredCapacity;
      return diagnostics::emit(candidate.emitError(),
                               capacity ? "finite-verification-capacity"
                                        : "mathematical-lowering-preservation",
                               outcome.detail);
    }
    return success(valid);
  };
  if (failed(verifyRecipeOutput(candidate)))
    return finish(false);
  auto entry = getEntry(source);
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!entry || !candidate->getAttrs().empty() || !owner ||
      owner.getProfile() != protocol_ir::Profile::Exec)
    return finish(false);
  SymbolTable symbols(owner);
  auto target = symbols.lookup<local::FuncOp>(entry.getSymName());
  Builder builder(candidate.getContext());
  NamedAttrList interface;
  interface.set("sym_name", entry.getSymNameAttr());
  interface.set("function_type", entry.getFunctionTypeAttr());
  interface.set(
      "logical_origin",
      builder.getArrayAttr({entry.getSymNameAttr(), builder.getArrayAttr({})}));
  if (!target ||
      interface.getDictionary(candidate.getContext()) !=
          target->getAttrDictionary() ||
      !target.getBody().hasOneBlock() || target.getBody().front().empty())
    return finish(false);
  // Local-definition admission above owns closed attributes, unique sites,
  // binding signatures and control/resource legality. This result contains
  // only the one output function and its used bindings. Source dependencies
  // remain in the immutable Kernel owner used by the independent reader.
  llvm::DenseSet<Operation *> used;
  uint64_t standalone = 1000000, standaloneBytes = 16 * 1024 * 1024;
  auto &remaining = limits.sharedContext ? *limits.sharedContext : standalone;
  auto &remainingBytes =
      limits.sharedSiteBytes ? *limits.sharedSiteBytes : standaloneBytes;
  std::optional<CapacityCause> capacity;
  if (!chargeCopy(candidate, remaining, &capacity)) {
    outcome = {finite::VerificationStatus::RequiredCapacity,
               "Kernel recipe context checking capacity",
               CapacityCause{WorkOwner::AlgorithmChecking}};
    return finish(false);
  }
  target.walk([&](Operation *op) {
    if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
      used.insert(symbols.lookup(ref.getValue()));
  });
  for (auto &definition : owner.getBody().front()) {
    if (&definition == target.getOperation())
      continue;
    if (!isa<local::OperationBindingOp>(definition) ||
        !used.contains(&definition))
      return finish(false);
  }
  auto *cursor = &target.getBody().front().front();
  auto outputs = verifyKernelRecipes(
      entry, owner, callSite, target.getArguments(), cursor, remaining,
      remainingBytes, policy, limits, outcome, selection);
  auto returned = dyn_cast_or_null<local::ReturnOp>(cursor);
  return finish(succeeded(outputs) && returned && !returned->getNextNode() &&
                returned.getInputs() == ValueRange(*outputs));
}
} // namespace zkc::kernel
