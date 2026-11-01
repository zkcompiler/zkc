#include "../CollectFold.h"
#include "../CollectionInterpretation.h"
#include "../FiniteVerification.h"
#include "../HelperNormalization.h"
#include "../NativeBindingApplication.h"
#include "../RealizationSubject.h"
#include "../ScopedCandidate.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include <functional>

#include "zkc/Transforms/Algorithms.h"

using namespace mlir;
using namespace llvm;
using namespace zkc::mathematical;
namespace zkc::computation {
namespace {
// Read the retained numerical source and actual executable recipes. This
// reader never invokes conversion, selection or normalization producers.
class RecipeReader {
  Operation *sourceRoot;
  SymbolTable symbols;
  CandidatePorts ports;
  const CheckedHelperNormalizations &helpers;
  uint64_t remaining = 1000000;
  bool allowFiniteBulk = true;
  MathematicalSelectionPolicy invocationPolicy;
  NumericalSelection *selection = nullptr;
  std::optional<RealizationSubject> activeSubject;
  unsigned nextChild = 0;
  uint64_t *siteBytes = nullptr;
  llvm::DenseSet<Operation *> checkedSelections;
  uint64_t compositionInspection = 100000;
  finite::VerificationLimits finiteLimits;
  finite::VerificationResult finiteOutcome{finite::VerificationStatus::Mismatch,
                                           "numerical recipes differ"};
  static bool representation(Type source, Type actual) {
    return isa<poly::QuotientType>(source) ? isa<data::IndicesType>(actual)
                                           : source == actual;
  }
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
    std::function<bool(Operation *, unsigned)> inspect = [&](Operation *op,
                                                             unsigned depth) {
      if (depth > 64 || !ports.contains(op) || !charge())
        return false;
      auto site = op->getAttrOfType<StringAttr>("site");
      if (site && site.getValue() != root &&
          !site.getValue().starts_with(prefix))
        return false;
      // Selected bodies have already been compared under their independently
      // derived arm namespaces. Long sites can be hashed by algorithmSite;
      // their exact check cannot be replaced with an outer prefix test.
      if (checkedSelections.contains(op))
        return true;
      for (unsigned index = 0; index < ports.bodies(op); ++index)
        for (auto *child = ports.first(ports.body(op, index)); child;
             child = ports.next(child))
          if (!inspect(child, depth + 1))
            return false;
      return true;
    };
    for (auto *op = begin; op != end; op = ports.next(op)) {
      if (!inspect(op, 0))
        return false;
    }
    return true;
  }
  // Sites are allocated by lowering and checked for uniqueness by the profile.
  // The resolved contract, arguments, implementation and parameters determine
  // the executable primitive; matching its operation name alone is
  // insufficient.
  bool primitive(Operation *op, StringRef contract, ValueRange inputs,
                 ArrayRef<Attribute> arguments = {},
                 ArrayRef<Attribute> expectedParameters = {}) {
    if (!op || !ports.contains(op) || !isa<exec::ApplyOp>(op) ||
        ports.outputs(op).size() != 1 || ports.bodies(op) != 0 ||
        ports.inputs(op) != inputs || !charge(1 + inputs.size()))
      return false;
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding = reference ? dyn_cast_or_null<runtime::BindingOp>(
                                   symbols.lookup(reference.getValue()))
                             : runtime::BindingOp();
    auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!binding || binding.getContract() != contract ||
        !binding.getImplementation().empty() || !site ||
        site.getValue().empty() || op->getAttrs().size() != 3 || !parameters ||
        parameters.size() != expectedParameters.size() ||
        binding.getArguments().size() != arguments.size())
      return false;
    if (!llvm::equal(parameters, expectedParameters))
      return false;
    if (!matchesNativeBinding(
            binding, {contract.str(), SmallVector<Attribute>(arguments), {}}))
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
      if (isa<data::BranchOp>(op)) {
        auto site = at ? at->getAttrOfType<StringAttr>("site") : StringAttr{};
        auto outputs = site && siteBytes
                           ? selected(&op, at, operands, site.getValue(),
                                      *siteBytes, invocationPolicy, 0)
                           : FailureOr<SmallVector<Value>>(failure());
        if (failed(outputs) || outputs->size() != op.getNumResults())
          return failure();
        for (auto [before, after] : zip(op.getResults(), *outputs))
          values[before] = after;
      } else if (finite::isComputation(&op)) {
        auto results = finiteRecipe(&op, at, operands);
        if (failed(results) || results->size() != op.getNumResults())
          return failure();
        for (auto [a, b] : zip(op.getResults(), *results))
          values[a] = b;
      } else {
        auto value = recipe(&op, at, operands);
        if (!value || op.getNumResults() != 1 ||
            !representation(op.getResult(0).getType(), value.getType()))
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
      for (auto *at = begin; at != cursor; at = ports.next(at)) {
        if (!at)
          return failure();
        if (ports
                .walk(at,
                      [&](Operation *nested) {
                        selection->record(nested, *owner);
                        return WalkResult::advance();
                      })
                .wasInterrupted())
          return failure();
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
    auto natural = [&](uint64_t value) {
      return IntegerAttr::get(
          IntegerType::get(source->getContext(), 64, IntegerType::Unsigned),
          value);
    };

    auto take = [&](StringRef contract, ValueRange operands,
                    ArrayRef<Attribute> arguments = {},
                    ArrayRef<Attribute> parameters = {}) -> Value {
      if (!primitive(cursor, contract, operands, arguments, parameters))
        return {};
      auto value = ports.outputs(cursor)[0];
      cursor = ports.next(cursor);
      return value;
    };
    if (isa<poly::ObserveQuotientOp>(source))
      return inputs[0];
    if (isa<poly::ProjectQuotientOp, poly::AddQuotientOp,
            poly::SubtractQuotientOp, poly::MultiplyQuotientOp>(source)) {
      auto ring = cast<poly::QuotientType>(source->getResult(0).getType());
      const auto modulus = natural(ring.getModulus());
      auto q = take("index.constant", {}, {}, {modulus});
      if (!q)
        return {};
      SmallVector<Value> args(inputs);
      args.push_back(q);
      if (isa<poly::ProjectQuotientOp>(source)) {
        const auto degree = natural(ring.getDegree());
        auto n = take("index.constant", {}, {}, {degree});
        if (!n)
          return {};
        args.push_back(n);
        return take("quotient.project", args);
      }
      if (isa<poly::AddQuotientOp>(source))
        return take("quotient.add", args);
      if (isa<poly::SubtractQuotientOp>(source))
        return take("quotient.subtract", args);
      return take("quotient.multiply", args);
    }
    if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(source)) {
      auto col = interpretCollection(inputs[0].getType());
      if (!primitive(cursor, col.access, inputs, col.arguments))
        return {};
      auto value = ports.outputs(cursor)[0];
      cursor = ports.next(cursor);
      return value;
    }
    if (isa<data::SequenceEmptyOp, data::SequenceAppendOp,
            data::SequenceLengthOp>(source)) {
      auto sequence = cast<data::SequenceType>(
          isa<data::SequenceEmptyOp>(source) ? source->getResult(0).getType()
                                             : source->getOperand(0).getType());
      StringRef contract = isa<data::SequenceEmptyOp>(source) ? "sequence.empty"
                           : isa<data::SequenceAppendOp>(source)
                               ? "sequence.append"
                               : "sequence.length";
      if (!primitive(cursor, contract, inputs,
                     {TypeAttr::get(sequence.getElementType())}))
        return {};
      auto value = ports.outputs(cursor)[0];
      cursor = ports.next(cursor);
      return value;
    }
    if (isa<data::PowerOfTwoOp>(source)) {
      // Read the complete circuit and every association from actual SSA.
      // No producer normalization or mathematical predicate receipt is used.
      auto zero = take("index.constant", {}, {}, {natural(0)});
      auto one = take("index.constant", {}, {}, {natural(1)});
      if (!zero || !one)
        return {};
      auto predecessor = take("index.wrapping_sub", {inputs[0], one});
      if (!predecessor)
        return {};
      auto lowerBits = take("index.bit_and", {inputs[0], predecessor});
      auto shifted = take("index.logical_shift_right", {inputs[0], inputs[1]});
      if (!lowerBits || !shifted)
        return {};
      auto singleBit = take("index.equal", {lowerBits, zero});
      auto position = take("index.equal", {shifted, one});
      if (!singleBit || !position)
        return {};
      return take("bool.and", {singleBit, position});
    }

    if (auto dim = dyn_cast<data::DimOp>(source)) {
      auto collection = cast<CollectionTypeInterface>(dim.getInput().getType());
      auto axis = dim.getAxisAttr().getInt();
      if (auto extent = collection.getStaticExtent(axis)) {
        auto length = natural(*extent);
        return take("index.constant", {}, {}, {length});
      }
      if (auto field =
              dyn_cast<algebra::FieldType>(collection.getElementType())) {
        if (collection.getRank() == 1)
          return take(
              "vector.length", inputs,
              {StringAttr::get(source->getContext(), field.getDomain())});
        auto coordinate = natural(axis);
        return take("matrix.dimension", inputs,
                    {StringAttr::get(source->getContext(), field.getDomain())},
                    {coordinate});
      }
      if (auto group =
              dyn_cast<algebra::GroupType>(collection.getElementType()))
        return take("curve.length", inputs,
                    {StringAttr::get(source->getContext(), group.getDomain())});
      return take(collection.getCollectionKind() == CollectionKind::Bytes
                      ? "bytes.length"
                      : "indices.length",
                  inputs);
    }
    if (auto constant = dyn_cast<data::IndexOp>(source))
      return take("index.constant", {}, {}, {constant.getValueAttr()});
    if (isa<data::EqualOp, data::LessOp>(source))
      return take(isa<data::EqualOp>(source) ? "index.equal" : "index.less",
                  inputs);
    if (isa<data::IndexWrappingAddOp>(source))
      return take("index.wrapping_add", inputs);
    if (isa<data::IndexWrappingSubtractOp>(source))
      return take("index.wrapping_sub", inputs);
    if (isa<data::IndexBitAndOp>(source))
      return take("index.bit_and", inputs);
    if (isa<data::IndexLogicalShiftRightOp>(source))
      return take("index.logical_shift_right", inputs);
    auto isBoolean = [&](Operation *op) {
      return ports.contains(op) && isa<exec::BooleanOp>(op);
    };
    auto isYield = [&](Operation *op) {
      return ports.contains(op) && isa<exec::CompleteOp>(op);
    };
    if (auto make = dyn_cast<data::MakeOp>(source)) {
      auto *target = cursor;
      if (!ports.contains(target) || !isa<exec::VariantOp>(target) ||
          ports.inputs(target) != inputs || ports.outputs(target).size() != 1 ||
          target->getAttr("alternative") != make.getAlternativeAttr())
        return {};
      cursor = ports.next(cursor);
      return ports.outputs(target)[0];
    }
    if (isa<data::GetOp, data::IsOp>(source)) {
      auto *target = cursor;
      auto arms = cast<data::VariantType>(source->getOperand(0).getType())
                      .getAlternatives();
      auto alternatives = target
                              ? target->getAttrOfType<ArrayAttr>("alternatives")
                              : ArrayAttr();
      if (!ports.contains(target) || !alternatives ||
          !isa<exec::MatchOp>(target) || ports.inputs(target) != inputs ||
          ports.bodies(target) != arms.size() ||
          alternatives.size() != arms.size() ||
          ports.outputs(target).size() != 1)
        return {};
      for (auto [i, arm] : enumerate(arms)) {
        auto *body = ports.body(target, i);
        auto arguments = ports.arguments(body);
        if (!body || alternatives[i] != arm.getLabel() ||
            TypeRange(arguments) != TypeRange(arm.getPayload()))
          return {};
        auto *at = ports.first(body);
        Value expected;
        if (auto get = dyn_cast<data::GetOp>(source)) {
          auto index = get.getIndexAttr().getInt();
          if (index < 0 || uint64_t(index) >= arguments.size())
            return {};
          expected = arguments[index];
        } else {
          if (!isBoolean(at) || ports.outputs(at).size() != 1 ||
              at->getAttrOfType<BoolAttr>("value") !=
                  BoolAttr::get(source->getContext(),
                                arm.getLabel().getValue() ==
                                    cast<data::IsOp>(source).getAlternative()))
            return {};
          expected = ports.outputs(at)[0];
          at = ports.next(at);
        }
        if (!isYield(at) || ports.inputs(at) != ValueRange{expected} ||
            ports.next(at))
          return {};
      }
      cursor = ports.next(cursor);
      return ports.outputs(target)[0];
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(source)) {
      auto *target = cursor;
      auto value = dyn_cast<IntegerAttr>(constant.getValue());
      if (!isBoolean(target) || !value ||
          !value.getType().isSignlessInteger(1) ||
          !constant.getType().isSignlessInteger(1) ||
          ports.outputs(target).size() != 1 ||
          target->getAttrOfType<BoolAttr>("value") !=
              BoolAttr::get(source->getContext(),
                            value.getValue().getBoolValue()))
        return {};
      cursor = ports.next(cursor);
      return ports.outputs(target)[0];
    }
    if (isa<arith::SelectOp>(source)) {
      auto type = source->getResult(0).getType();
      if (type.isSignlessInteger(1))
        return take("bool.select", inputs);
      if (type.isUnsignedInteger(64))
        return take("index.select", inputs);
      if (auto field = dyn_cast<algebra::FieldType>(type))
        return take("field.select", inputs,
                    {StringAttr::get(source->getContext(), field.getDomain())});
      if (auto group = dyn_cast<algebra::GroupType>(type))
        return take("curve.select", inputs,
                    {StringAttr::get(source->getContext(), group.getDomain())});
      return {};
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
                  {StringAttr::get(source->getContext(),
                                   constant.getResult().getType().getDomain())},
                  {constant.getValue()});
    if (auto at = dyn_cast<data::ArrayAtOp>(source)) {
      auto array = at.getArray().getType();
      auto field = StringAttr::get(
          source->getContext(),
          cast<algebra::FieldType>(array.getElementType()).getDomain());
      auto length = natural(array.getLength());
      auto index = natural(at.getIndexAttr().getInt());
      return take("field_array.at", inputs, {field, length}, {index});
    }
    if (isa<data::ArrayFromElementsOp>(source)) {
      auto array = cast<data::FieldArrayType>(source->getResult(0).getType());
      auto field = StringAttr::get(
          source->getContext(),
          cast<algebra::FieldType>(array.getElementType()).getDomain());
      auto length = natural(array.getLength());
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
    if (auto restrict = dyn_cast<algebra::MultilinearRestrictPrefixOp>(source))
      return take(
          "multilinear.restrict_prefix", inputs,
          {StringAttr::get(source->getContext(),
                           restrict.getResult().getType().getDomain())});
    if (auto identity = dyn_cast<algebra::GroupIdentityOp>(source))
      return take(
          "curve.identity", {},
          {StringAttr::get(source->getContext(),
                           identity.getResult().getType().getDomain())});
    if (isa<algebra::PairingOp>(source)) {
      auto group = cast<algebra::GroupType>(source->getOperand(0).getType());
      auto field = protocol::installedDomains().associatedIdentity(
          group.getDomain(), "Scalar");
      return take("pairing.apply", inputs,
                  {StringAttr::get(source->getContext(), field)});
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
    return take(contract, inputs,
                {StringAttr::get(source->getContext(), domain)});
  }

public:
  RecipeReader(Operation *sourceRoot, Operation *targetRoot,
               const CheckedHelperNormalizations &helpers,
               finite::VerificationLimits limits, NumericalSelection *selection)
      : sourceRoot(sourceRoot), symbols(targetRoot), ports(limits.candidate),
        helpers(helpers), selection(selection), finiteLimits(limits) {}
  FailureOr<SmallVector<Value>> selected(Operation *source, Operation *&cursor,
                                         ValueRange inputs, StringRef site,
                                         uint64_t &bytes,
                                         MathematicalSelectionPolicy policy,
                                         unsigned depth) {
    auto branch = cast<data::BranchOp>(source);
    bool boolean = inputs.front().getType().isSignlessInteger(1);
    if (depth > 64 || !charge(1 + inputs.size() + source->getNumResults()) ||
        !ports.contains(cursor) ||
        (boolean ? !isa<exec::TestOp>(cursor) : !isa<exec::MatchOp>(cursor)) ||
        ports.bodies(cursor) != source->getNumRegions() ||
        ports.outputs(cursor).getTypes() != source->getResultTypes())
      return failure();
    auto actualSite = cursor->getAttrOfType<StringAttr>("site");
    if (!actualSite || actualSite.getValue() != site ||
        (!boolean &&
         cursor->getAttr("alternatives") != branch.getAlternatives()))
      return failure();
    SmallVector<Value> canonical{inputs.front()};
    llvm::DenseMap<Value, unsigned> positions;
    SmallVector<unsigned> captures;
    for (Value input : inputs.drop_front()) {
      auto [found, inserted] = positions.try_emplace(input, positions.size());
      captures.push_back(found->second);
      if (inserted)
        canonical.push_back(input);
    }
    unsigned captureWidth = positions.size();
    if (ports.inputs(cursor) == inputs) {
      // Initial scoped recipes retain every capture slot. Later scoped
      // substitution may merge exact SSA aliases in first-use order. Both
      // carriers must preserve the original positional association.
      captureWidth = captures.size();
      for (auto [index, position] : enumerate(captures))
        position = index;
    } else if (ports.inputs(cursor) != ValueRange(canonical))
      return failure();
    for (auto [index, region] : enumerate(branch.getArms())) {
      auto *actual = ports.body(cursor, index);
      auto payload = selectedPayloadTypes(source, index);
      if (!actual || !payload) {
        if (!payload)
          consumeError(payload.takeError());
        return failure();
      }
      auto arguments = ports.arguments(actual);
      if (arguments.size() != payload->size() + captureWidth)
        return failure();
      SmallVector<Value> associated;
      append_range(associated, arguments.take_front(payload->size()));
      for (unsigned capture : captures)
        associated.push_back(arguments[payload->size() + capture]);
      auto *at = ports.first(actual);
      auto prefix = (site + "_recipe_arm_" + Twine(index) + "_").str();
      auto outputs = block(region.front(), prefix, associated, at, bytes,
                           policy, true, depth + 1);
      if (failed(outputs) || !isa_and_nonnull<exec::CompleteOp>(at) ||
          ports.next(at) || ports.inputs(at) != ValueRange(*outputs))
        return failure();
    }
    checkedSelections.insert(cursor);
    SmallVector<Value> results(ports.outputs(cursor));
    cursor = ports.next(cursor);
    return results;
  }
  FailureOr<SmallVector<Value>> block(Block &entry, StringRef callSite,
                                      ValueRange arguments, Operation *&cursor,
                                      uint64_t &remainingBytes,
                                      MathematicalSelectionPolicy policy,
                                      bool arm = false, unsigned depth = 0) {
    if (depth > 64)
      return failure();
    if (arguments.size() != entry.getNumArguments())
      return failure();
    llvm::DenseMap<Value, Value> values;
    for (auto [source, actual] : zip(entry.getArguments(), arguments)) {
      if (source.getType() != actual.getType())
        return failure();
      values[source] = actual;
    }
    unsigned ordinal = 0;
    Operation *consumed = nullptr;
    for (auto &op : entry) {
      if (&op == consumed) {
        auto skippedSite =
            arm ? protocol::algorithmSite(
                      {}, (callSite + Twine(ordinal++)).str(), remainingBytes)
                : protocol::algorithmSite({{callSite.str(), "kernel"}},
                                          std::to_string(ordinal++),
                                          remainingBytes);
        if (!skippedSite) {
          consumeError(skippedSite.takeError());
          return failure();
        }
        consumed = nullptr;
        continue;
      }
      if (!charge(1 + op.getNumOperands() + op.getNumResults()))
        return failure();
      SmallVector<Value> inputs;
      for (Value value : op.getOperands()) {
        auto actual = values.lookup(value);
        if (!actual)
          return failure();
        inputs.push_back(actual);
      }
      if (isa<func::ReturnOp, data::YieldOp>(op))
        return inputs;
      auto site =
          arm ? protocol::algorithmSite({}, (callSite + Twine(ordinal++)).str(),
                                        remainingBytes)
              : protocol::algorithmSite({{callSite.str(), "kernel"}},
                                        std::to_string(ordinal++),
                                        remainingBytes);
      if (!site) {
        consumeError(site.takeError());
        return failure();
      }
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
          return failure();
        }
        results = *read;
      } else if (isa<data::BranchOp>(op)) {
        auto read =
            selected(&op, cursor, inputs, *site, remainingBytes, policy, depth);
        if (failed(read))
          return failure();
        results = *read;
      } else {
        auto value = recipe(&op, cursor, inputs);
        if (!value)
          return failure();
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
          return failure();
        }
        for (auto *at = begin; at != cursor; at = ports.next(at)) {
          if (!at)
            return failure();
          if (ports
                  .walk(at,
                        [&](Operation *nested) {
                          selection->record(nested, *owner);
                          return WalkResult::advance();
                        })
                  .wasInterrupted())
            return failure();
        }
      }
      if (results.size() != resultSource->getNumResults() ||
          (!isa<data::BranchOp>(op) &&
           !occurrences(begin, cursor, *site, finite)))
        return failure();
      // Primitive roots keep the original occurrence, while a finite recipe
      // has its documented traversal suffixes. No label establishes meaning.
      if (!finite && !results.empty() &&
          !isa<poly::ObserveQuotientOp>(resultSource)) {
        auto rootSite =
            ports.producer(results.back())->getAttrOfType<StringAttr>("site");
        if (!rootSite || rootSite.getValue() != *site)
          return failure();
      }
      for (auto [source, actual] : zip(resultSource->getResults(), results)) {
        if (!representation(source.getType(), actual.getType()))
          return failure();
        values[source] = actual;
      }
    }
    return failure();
  }
  FailureOr<SmallVector<Value>> read(func::FuncOp entry, StringRef callSite,
                                     ValueRange arguments, Operation *&cursor,
                                     uint64_t &budget, uint64_t &remainingBytes,
                                     MathematicalSelectionPolicy policy,
                                     finite::VerificationResult &outcome) {
    allowFiniteBulk = policy.finiteBulk;
    invocationPolicy = policy;
    siteBytes = &remainingBytes;
    remaining = std::min<uint64_t>(remaining, budget);
    auto initial = remaining;
    auto result = block(entry.front(), callSite, arguments, cursor,
                        remainingBytes, policy);
    budget -= initial - remaining;
    outcome =
        succeeded(result)
            ? finite::VerificationResult{finite::VerificationStatus::Verified,
                                         {}}
            : finiteOutcome;
    return result;
  }
};
} // namespace
FailureOr<SmallVector<Value>> verifyComputationRecipes(
    func::FuncOp source, Operation *targetRoot, StringRef callSite,
    ValueRange arguments, Operation *&cursor, uint64_t &remaining,
    uint64_t &remainingBytes, MathematicalSelectionPolicy policy,
    finite::VerificationLimits limits, finite::VerificationResult &outcome,
    NumericalSelection *selection) {
  outcome = {finite::VerificationStatus::Mismatch, "numerical recipes differ"};
  auto unit = source ? dyn_cast_or_null<mlir::ModuleOp>(source->getParentOp())
                     : mlir::ModuleOp();
  if (!limits.candidate || !unit ||
      source != mathematical::getComputationEntry(unit) ||
      !source.getBody().hasOneBlock() || source.front().empty() ||
      callSite.empty())
    return failure();
  CheckedHelperNormalizations helpers(unit);
  if (failed(helpers.readback(&remaining)))
    return failure();
  return RecipeReader(unit, targetRoot, helpers, limits, selection)
      .read(source, callSite, arguments, cursor, remaining, remainingBytes,
            policy, outcome);
}

static LogicalResult verifyNumericalOutput(mlir::ModuleOp candidate,
                                           bool scheduled) {
  if (!candidate || candidate->getNumRegions() != 1 ||
      candidate->getNumOperands() || candidate->getNumResults() ||
      !candidate.getBodyRegion().hasOneBlock() ||
      !candidate->getAttrs().empty() ||
      candidate.getBody()->getNumArguments() ||
      !hasSingleElement(*candidate.getBody()) ||
      failed(candidate->getName().verifyInvariants(candidate)))
    return failure();
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!owner || !owner.getProfileAttr() ||
      owner.getProfile() != protocol_ir::Profile::Exec ||
      owner->getNumOperands() || owner->getNumResults() ||
      owner->getAttrs().size() != 1 || owner->getNumRegions() != 1 ||
      !owner.getBody().hasOneBlock() ||
      owner.getBody().front().getNumArguments())
    return failure();
  // A closed scoped fragment has no participant Entry. Admit its actual
  // functions and bindings without inventing a runnable protocol wrapper.
  for (auto &definition : owner.getBody().front()) {
    if (!isa<runtime::BindingOp, func::FuncOp>(definition))
      return failure();
    if (auto function = dyn_cast<func::FuncOp>(definition);
        function && !protocol::isScopedExecutionFunction(function))
      return failure();
  }
  auto view = scheduled ? ScopedCandidate::readSchedule(owner)
                        : ScopedCandidate::read(owner);
  if (!view) {
    consumeError(view.takeError());
    return failure();
  }
  return success();
}

LogicalResult verifyRecipeOutput(mlir::ModuleOp candidate) {
  return verifyNumericalOutput(candidate, false);
}
LogicalResult verifyScheduledRecipeOutput(mlir::ModuleOp candidate) {
  return verifyNumericalOutput(candidate, true);
}
static LogicalResult verifyRecipes(mlir::ModuleOp source,
                                   mlir::ModuleOp candidate, StringRef callSite,
                                   MathematicalSelectionPolicy policy,
                                   finite::VerificationLimits limits,
                                   finite::VerificationResult *reported,
                                   NumericalSelection *selection,
                                   bool scheduled) {
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
  if (failed(verifyNumericalOutput(candidate, scheduled)))
    return finish(false);
  auto entry = mathematical::getComputationEntry(source);
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!entry || !candidate->getAttrs().empty() || !owner ||
      owner.getProfile() != protocol_ir::Profile::Exec)
    return finish(false);
  SymbolTable symbols(owner);
  auto target = symbols.lookup<func::FuncOp>(entry.getSymName());
  Builder builder(candidate.getContext());
  NamedAttrList interface;
  interface.set("sym_name", entry.getSymNameAttr());
  SmallVector<Type> arguments{runtime::ScopeType::get(candidate.getContext())};
  append_range(arguments, entry.getArgumentTypes());
  interface.set(
      "function_type",
      TypeAttr::get(builder.getFunctionType(
          arguments, {exec::OutcomeType::get(candidate.getContext(),
                                             entry.getResultTypes())})));
  interface.set("sym_visibility", builder.getStringAttr("private"));
  interface.set("no_inline", builder.getUnitAttr());
  interface.set(
      "runtime.origin",
      builder.getArrayAttr({entry.getSymNameAttr(), builder.getArrayAttr({})}));
  if (!target ||
      interface.getDictionary(candidate.getContext()) !=
          target->getAttrDictionary() ||
      target.empty() || target.front().empty())
    return finish(false);
  auto view = scheduled ? ScopedCandidate::readSchedule(owner)
                        : ScopedCandidate::read(owner);
  if (!view) {
    consumeError(view.takeError());
    return finish(false);
  }
  limits.candidate = view->get();
  CandidatePorts ports(limits.candidate);
  // Admission checks every actual scoped body. This comparison must also
  // account for every declaration and every reached recipe body.
  llvm::DenseSet<Operation *> used;
  uint64_t standalone = 1000000, standaloneBytes = 16 * 1024 * 1024;
  auto &remaining = limits.sharedContext ? *limits.sharedContext : standalone;
  auto &remainingBytes =
      limits.sharedSiteBytes ? *limits.sharedSiteBytes : standaloneBytes;
  std::optional<CapacityCause> capacity;
  if (!chargeCopy(candidate, remaining, &capacity)) {
    outcome = {finite::VerificationStatus::RequiredCapacity,
               "computation recipe context checking capacity",
               CapacityCause{WorkOwner::AlgorithmChecking}};
    return finish(false);
  }
  llvm::DenseSet<Operation *> functions;
  for (auto *op = ports.first(&target.front()); op; op = ports.next(op))
    if (ports
            .walk(op,
                  [&](Operation *nested) {
                    functions.insert(nested->getParentOfType<func::FuncOp>());
                    if (auto ref =
                            nested->getAttrOfType<FlatSymbolRefAttr>("binding"))
                      used.insert(symbols.lookup(ref.getValue()));
                    return WalkResult::advance();
                  })
            .wasInterrupted())
      return finish(false);
  for (auto &definition : owner.getBody().front()) {
    if (functions.contains(&definition)) {
      if (&definition != target.getOperation() &&
          !definition.hasAttr("runtime.region"))
        return finish(false);
      continue;
    }
    if (!isa<runtime::BindingOp>(definition) || !used.contains(&definition))
      return finish(false);
  }
  auto *cursor = ports.first(&target.front());
  auto outputs = verifyComputationRecipes(
      entry, owner, callSite, target.getArguments().drop_front(), cursor,
      remaining, remainingBytes, policy, limits, outcome, selection);
  return finish(succeeded(outputs) && isa_and_nonnull<exec::ReturnOp>(cursor) &&
                !ports.next(cursor) &&
                ports.inputs(cursor) == ValueRange(*outputs));
}
LogicalResult verifyEntryRecipes(mlir::ModuleOp source,
                                 mlir::ModuleOp candidate, StringRef callSite,
                                 MathematicalSelectionPolicy policy,
                                 finite::VerificationLimits limits,
                                 finite::VerificationResult *outcome,
                                 NumericalSelection *selection) {
  return verifyRecipes(source, candidate, callSite, policy, limits, outcome,
                       selection, false);
}
LogicalResult verifyEntrySchedule(mlir::ModuleOp source,
                                  mlir::ModuleOp candidate, StringRef callSite,
                                  MathematicalSelectionPolicy policy,
                                  finite::VerificationLimits limits,
                                  finite::VerificationResult *outcome) {
  return verifyRecipes(source, candidate, callSite, policy, limits, outcome,
                       nullptr, true);
}
} // namespace zkc::computation
