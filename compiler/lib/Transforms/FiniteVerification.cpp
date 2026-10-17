#include "FiniteVerification.h"
#include "CollectionInterpretation.h"
#include "MathematicalComparison.h"
#include "RealizationSubject.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
// Consumes actual candidate instructions. This reader does not allocate IR,
// invoke the producer, or trust a recorded recognition/formation summary.
class Reader {
  Computation c;
  SymbolTable &symbols;
  llvm::DenseSet<Operation *> &bindings;
  Operation *cursor = nullptr;
  Type index, boolean;
  llvm::DenseMap<Value, Value> actual, cardinalities, offsets;
  bool valid = true, inlineMode = false;
  bool allowBulk;
  HelperReader helperReader;
  SmallVector<Value> expressionResults;
  uint64_t remaining;
  VerificationLimits limits;
  VerificationResult result{VerificationStatus::Mismatch,
                            "finite recipe differs from its domain/helper"};
  void fail() { valid = false; }
  Operation *consume(StringRef name) {
    if (!valid || !cursor || cursor->getName().getStringRef() != name) {
      fail();
      return nullptr;
    }
    if (!remaining) {
      result = {VerificationStatus::RequiredCapacity, "finite reader work",
                CapacityCause{WorkOwner::RequiredFiniteReader, 1, remaining},
                mathematical::realizationSubject(c.operation)};
      fail();
      return nullptr;
    }
    --remaining;
    auto *op = cursor;
    cursor = cursor->getNextNode();
    return op;
  }
  Value kernel(StringRef contract, ValueRange operands, Type result,
               ArrayRef<std::string> arguments = {},
               ArrayRef<std::string> parameters = {}) {
    auto *op = consume(protocol::boundOperationName(contract));
    if (!op)
      return {};
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    auto params = op->getAttrOfType<ArrayAttr>("parameters");
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!binding || !params || !site || op->getAttrs().size() != 3 ||
        op->getNumRegions() || op->getOperands() != operands ||
        op->getNumResults() != unsigned(bool(result)) ||
        (result && op->getResult(0).getType() != result) ||
        binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != arguments.size() ||
        params.size() != parameters.size()) {
      fail();
      return {};
    }
    for (auto [a, b] : zip(binding.getArguments(), arguments))
      if (a != StringAttr::get(op->getContext(), b))
        fail();
    for (auto [a, b] : zip(params, parameters))
      if (a != StringAttr::get(op->getContext(), b))
        fail();
    bindings.insert(binding);
    return result ? op->getResult(0) : Value();
  }
  Value natural(uint64_t n) {
    return kernel("index.constant", {}, index, {}, {std::to_string(n)});
  }
  void require(Value condition) {
    if (!condition) {
      fail();
      return;
    }
    kernel("control.require", condition, {});
  }
  Value extent(Value container, unsigned selected = 0) {
    if (!container) {
      fail();
      return {};
    }
    auto col = mathematical::interpretCollection(container.getType());
    if (col.staticExtent.has_value())
      return natural(
          cast<algebra::FieldArrayType>(container.getType()).getLength());
    return kernel(col.length, container, index, col.arguments,
                  col.matrix ? ArrayRef<std::string>{std::to_string(selected)}
                             : ArrayRef<std::string>{});
  }
  Operation *control(StringRef name, ValueRange operands, TypeRange results,
                     unsigned regions) {
    auto *op = consume(name);
    if (!op)
      return nullptr;
    if (op->getOperands() != operands || op->getResultTypes() != results ||
        op->getNumRegions() != regions ||
        !op->getAttrOfType<StringAttr>("site") || op->getAttrs().size() != 1) {
      fail();
      return nullptr;
    }
    return op;
  }
  Block *enter(Operation *op, unsigned region, TypeRange types) {
    if (!op || !op->getRegion(region).hasOneBlock()) {
      fail();
      return nullptr;
    }
    auto &block = op->getRegion(region).front();
    if (block.getArgumentTypes() != types || block.empty()) {
      fail();
      return nullptr;
    }
    cursor = &block.front();
    return &block;
  }
  void end(StringRef name, ValueRange inputs) {
    auto *op = consume(name);
    if (!op || op->getOperands() != inputs || op->getNumResults() ||
        op->getNumRegions() || !op->getAttrs().empty() || cursor)
      fail();
  }
  void bound(Value value) {
    auto *loop = control("local.for", {value, value}, {}, 1);
    Operation *after = cursor;
    if (enter(loop, 0, {index}))
      end("local.yield", {});
    cursor = after;
  }
  Value range(Value lower, Value upper) {
    Value condition = kernel("index.less", {lower, upper}, boolean);
    SmallVector<Value> inputs{condition, lower};
    if (upper != lower)
      inputs.push_back(upper);
    SmallVector<Type> types(inputs.size() - 1, index);
    auto *branch = control("local.if", inputs, {index}, 2);
    auto *after = cursor;
    if (auto *yes = enter(branch, 0, types)) {
      Value size = kernel(
          "index.sub",
          {yes->getArgument(upper == lower ? 0 : 1), yes->getArgument(0)},
          index);
      end("local.yield", size ? ValueRange{size} : ValueRange{});
    }
    if (enter(branch, 1, types)) {
      Value zero = natural(0);
      end("local.yield", zero ? ValueRange{zero} : ValueRange{});
    }
    cursor = after;
    return branch ? branch->getResult(0) : Value();
  }
  Value product(Value left, Value right) {
    bound(left);
    bound(right);
    Value result = kernel("index.mul", {left, right}, index);
    bound(result);
    return result;
  }
  void admission() {
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      if (!valid)
        return;
      Value size;
      if (isa<data::DomainElementsOp>(op))
        size = extent(actual.lookup(op.getOperand(0)));
      else if (auto indices = dyn_cast<data::DomainIndicesOp>(op))
        size = extent(actual.lookup(op.getOperand(0)), indices.getAxis());
      else if (isa<data::DomainRangeOp>(op)) {
        Value lower = actual.lookup(op.getOperand(0)),
              upper = actual.lookup(op.getOperand(1));
        bound(lower);
        bound(upper);
        size = range(lower, upper);
        offsets[op.getResult(0)] = lower;
      } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
        bool row = isa<data::DomainMatrixRowOp>(op);
        Value matrix = actual.lookup(op.getOperand(0));
        Value selected = actual.lookup(op.getOperand(1)),
              limit = extent(matrix, row ? 0 : 1);
        require(kernel("index.less", {selected, limit}, boolean));
        size = extent(matrix, row ? 1 : 0);
      } else if (isa<data::DomainZipOp>(op)) {
        size = cardinalities.lookup(op.getOperand(0));
        for (Value v : op.getOperands().drop_front())
          require(
              kernel("index.equal", {size, cardinalities.lookup(v)}, boolean));
      } else if (isa<data::DomainProductOp>(op)) {
        size = cardinalities.lookup(op.getOperand(0));
        for (Value v : op.getOperands().drop_front())
          size = product(size, cardinalities.lookup(v));
      } else if (auto coordinates =
                     dyn_cast<data::DomainMatrixCoordinatesOp>(op)) {
        Value matrix = actual.lookup(op.getOperand(0));
        Value rows = extent(matrix, 0), cols = extent(matrix, 1);
        size = product(rows, cols);
        offsets[op.getResult(0)] =
            coordinates.getOrder() == "row_major" ? cols : rows;
      } else
        fail();
      if (!size)
        fail();
      cardinalities[op.getResult(0)] = size;
    }
  }
  SmallVector<Value> enumerate(Value domain, Value position,
                               const llvm::DenseMap<Value, Value> &captures) {
    if (!valid)
      return {};
    auto *op = domain.getDefiningOp();
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Value> result;
      for (Value v : op->getOperands())
        append_range(result, enumerate(v, position, captures));
      return result;
    }
    if (isa<data::DomainProductOp>(op)) {
      SmallVector<SmallVector<Value>> backwards;
      Value q = position;
      for (Value v : reverse(op->getOperands())) {
        Value divisor = captures.lookup(cardinalities.lookup(v));
        Value r = kernel("index.mod", {q, divisor}, index);
        backwards.push_back(enumerate(v, r, captures));
        q = kernel("index.div", {q, divisor}, index);
      }
      SmallVector<Value> result;
      for (auto &part : reverse(backwards))
        append_range(result, part);
      return result;
    }
    if (isa<data::DomainIndicesOp>(op))
      return {position};
    if (isa<data::DomainRangeOp>(op))
      return {kernel("index.add",
                     {captures.lookup(offsets.lookup(domain)), position},
                     index)};
    if (auto coordinates = dyn_cast<data::DomainMatrixCoordinatesOp>(op)) {
      Value radix = captures.lookup(offsets.lookup(domain));
      Value major = kernel("index.div", {position, radix}, index),
            minor = kernel("index.mod", {position, radix}, index);
      return coordinates.getOrder() == "row_major"
                 ? SmallVector<Value>{major, minor}
                 : SmallVector<Value>{minor, major};
    }
    Value container = captures.lookup(actual.lookup(op->getOperand(0)));
    if (!container) {
      fail();
      return {};
    }
    auto col = mathematical::interpretCollection(container.getType());
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      Value selector = captures.lookup(actual.lookup(op->getOperand(1)));
      bool row = isa<data::DomainMatrixRowOp>(op);
      return {kernel(
          "matrix.get",
          {container, row ? selector : position, row ? position : selector},
          col.element, col.arguments)};
    }
    return {
        kernel(col.access, {container, position}, col.element, col.arguments)};
  }
  SmallVector<Value> invoke(CallbackRole role, CallbackValues actuals) {
    // Reconstruct from this reader's immutable source and actual candidate
    // values. No selected producer environment participates in correspondence.
    auto callback = readCallback(c, role);
    if (failed(callback)) {
      fail();
      return {};
    }
    auto environment = bindCallback(*callback, actuals);
    if (failed(environment)) {
      fail();
      return {};
    }
    auto *helper = callback->symbol;
    ValueRange args = environment->actuals;
    if (c.total) {
      auto result = helperReader(helper, args, cursor);
      if (failed(result)) {
        fail();
        return {};
      }
      return *result;
    }
    auto *op = consume("local.apply");
    if (!op)
      return {};
    auto type = callback->signature;
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("callee");
    if (!ref ||
        ref.getValue() != SymbolTable::getSymbolName(helper).getValue() ||
        op->getOperands() != args ||
        op->getResultTypes() != type.getResults() ||
        op->getAttrs().size() != 2 || !op->getAttrOfType<StringAttr>("site"))
      fail();
    return SmallVector<Value>(op->getResults());
  }
  SmallVector<Value> transition(ValueRange state, ValueRange items,
                                ValueRange env) {
    auto next =
        invoke(c.collect ? CallbackRole::Body : CallbackRole::Step,
               {c.collect ? ValueRange{} : state, items,
                env.take_front(c.arguments), env.drop_front(c.arguments)});
    if (!valid || !c.collect)
      return next;
    auto col = mathematical::interpretCollection(state[0].getType());
    return {kernel(col.append, {state[0], next[0]}, state[0].getType(),
                   col.arguments)};
  }

public:
  Reader(Computation computation, SymbolTable &symbols,
         llvm::DenseSet<Operation *> &bindings, VerificationLimits limits = {},
         bool allowBulk = true)
      : c(computation), symbols(symbols), bindings(bindings),
        index(IntegerType::get(c.operation->getContext(), 64,
                               IntegerType::Unsigned)),
        boolean(IntegerType::get(c.operation->getContext(), 1)),
        allowBulk(allowBulk), remaining(limits.reader), limits(limits) {}
  VerificationResult outcome() const { return result; }
  bool check(local::FuncOp target) {
    if (!target || target.getFunctionType() != c.signature ||
        !target.getBody().hasOneBlock() || target->getAttrs().size() != 3)
      return false;
    auto origin = target->getAttrOfType<ArrayAttr>("logical_origin");
    if (!origin || origin.size() != 2 ||
        origin[0] != SymbolTable::getSymbolName(c.operation) ||
        origin[1] != ArrayAttr::get(target.getContext(), {}))
      return false;
    auto &entry = target.getBody().front();
    return checkBody(entry.getArguments(), &entry.front());
  }
  void finish(ValueRange values) {
    if (inlineMode)
      expressionResults.assign(values.begin(), values.end());
    else
      end("local.return", values);
  }
  FailureOr<SmallVector<Value>> checkInline(ValueRange inputs, Operation *&at,
                                            HelperReader helper) {
    inlineMode = true;
    helperReader = helper;
    if (!checkBody(inputs, at))
      return failure();
    at = cursor;
    return expressionResults;
  }
  bool checkBody(ValueRange entry, Operation *begin) {
    cursor = begin;
    auto partitions = partitionEntry(c, entry);
    if (failed(partitions))
      return false;
    for (auto [a, b] :
         zip(c.domain.getBody().front().getArguments(), partitions->domain))
      actual[a] = b;
    admission();
    if (!valid)
      return false;
    Value rootDomain = c.domain.getBody().front().back().getOperand(0);
    if (allowBulk &&
        (mathematical::hasFinitePayloadContract(cursor, symbols) ||
         // An identity collect can return an existing vector without emitting
         // payload. Its ordered alternative starts with an empty container.
         (c.collect && cursor &&
          isa<algebra::FieldVectorType>(c.signature.getResult(0)) &&
          cursor->getName().getStringRef() !=
              protocol::boundOperationName("vector.empty")))) {
      // Semantic comparison is optional. Its bounded interpretation and
      // normalization cannot spend the ordered reader's admission budget.
      uint64_t comparisonWork = std::min(remaining, limits.comparison);
      mathematical::ComparisonCapacity capacity;
      std::optional<CapacityCause> debit;
      if (auto compared = mathematical::compareFinitePayload(
              c, entry, cardinalities.lookup(rootDomain), cursor, symbols,
              bindings, comparisonWork,
              inlineMode ? nullptr : &begin->getBlock()->back(), &capacity,
              &debit);
          succeeded(compared)) {
        finish(ValueRange{*compared});
        return valid;
      }
      if (capacity != mathematical::ComparisonCapacity::None) {
        result = {VerificationStatus::OptionalCapacity,
                  mathematical::comparisonCapacityName(capacity),
                  debit.value_or(
                      CapacityCause{WorkOwner::OptionalComparison, {}, {}}),
                  mathematical::realizationSubject(c.operation)};
        return false;
      }
    }
    SmallVector<Value> state, env;
    append_range(env, partitions->domain);
    append_range(env, partitions->captures);
    if (c.collect) {
      auto result = c.signature.getResult(0);
      auto col = mathematical::interpretCollection(result);
      if (col.staticExtent.has_value()) {
        result = algebra::FieldVectorType::get(
            col.element.getContext(),
            cast<algebra::FieldType>(col.element).getDomain());
        col = mathematical::interpretCollection(result);
      }
      state.push_back(kernel(col.empty, {}, result, col.arguments));
    } else
      append_range(state, partitions->initialState);
    Value zero = natural(0),
          root = c.domain.getBody().front().back().getOperand(0);
    SmallVector<Value> captures(env);
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      captures.push_back(cardinalities.lookup(op.getResult(0)));
      if (Value v = offsets.lookup(op.getResult(0)))
        captures.push_back(v);
    }
    if (!valid)
      return false;
    SmallVector<Value> unique;
    for (Value value : captures)
      if (!is_contained(unique, value))
        unique.push_back(value);
    captures = std::move(unique);
    SmallVector<Value> inputs{zero, cardinalities.lookup(root)};
    append_range(inputs, state);
    append_range(inputs, captures);
    SmallVector<Type> types;
    for (Value v : state)
      types.push_back(v.getType());
    auto *loop = control("local.for", inputs, types, 1);
    auto *after = cursor;
    SmallVector<Type> bt{index};
    append_range(bt, types);
    for (Value v : captures)
      bt.push_back(v.getType());
    auto *body = enter(loop, 0, bt);
    if (!body)
      return false;
    auto current = body->getArguments().slice(1, state.size()),
         captured = body->getArguments().drop_front(1 + state.size());
    llvm::DenseMap<Value, Value> mapping;
    for (auto [a, b] : zip(captures, captured))
      mapping[a] = b;
    auto item = enumerate(root, body->getArgument(0), mapping);
    SmallVector<Value> environment;
    for (Value v : env)
      environment.push_back(mapping.lookup(v));
    if (!valid)
      return false;
    SmallVector<Value> next;
    if (c.predicate) {
      auto pred = invoke(CallbackRole::Predicate,
                         {{},
                          item,
                          ValueRange(environment).take_front(c.arguments),
                          ValueRange(environment).drop_front(c.arguments)});
      if (!valid || pred.size() != 1)
        return false;
      SmallVector<Value> capturedValues;
      for (ValueRange operands :
           {ValueRange(current), ValueRange(item), ValueRange(environment)})
        for (Value value : operands)
          if (!is_contained(capturedValues, value))
            capturedValues.push_back(value);
      SmallVector<Value> bi{pred[0]};
      append_range(bi, capturedValues);
      auto *branch = control("local.if", bi, types, 2);
      auto *following = cursor;
      SmallVector<Type> branchTypes;
      for (Value v : capturedValues)
        branchTypes.push_back(v.getType());
      auto remap = [&](Block *block, ValueRange operands) {
        SmallVector<Value> result;
        for (Value value : operands) {
          auto position =
              llvm::find(capturedValues, value) - capturedValues.begin();
          result.push_back(block->getArgument(position));
        }
        return result;
      };
      if (auto *yes = enter(branch, 0, branchTypes)) {
        auto result = transition(remap(yes, current), remap(yes, item),
                                 remap(yes, environment));
        end("local.yield", result);
      }
      if (auto *no = enter(branch, 1, branchTypes))
        end("local.yield", remap(no, current));
      cursor = following;
      if (!valid)
        return false;
      append_range(next, branch->getResults());
    } else
      next = transition(current, item, environment);
    append_range(next, captured);
    end("local.yield", next);
    cursor = after;
    if (!valid)
      return false;
    SmallVector<Value> results(loop->getResults());
    if (c.collect && results[0].getType() != c.signature.getResult(0)) {
      auto col = mathematical::interpretCollection(c.signature.getResult(0));
      results[0] = kernel("field_array.from_vector", results,
                          c.signature.getResult(0), col.arguments);
    }
    finish(results);
    return valid;
  }
};
} // namespace
FailureOr<SmallVector<Value>>
verifyExpression(Operation *source, ValueRange inputs, Operation *&cursor,
                 HelperReader helper, Operation *symbolRoot) {
  VerificationResult outcome{VerificationStatus::Mismatch, {}};
  auto result =
      verifyExpression(source, inputs, cursor, helper, symbolRoot, {}, outcome);
  if (outcome.status == VerificationStatus::OptionalCapacity ||
      outcome.status == VerificationStatus::RequiredCapacity)
    diagnostics::emit(source->emitError(), "finite-verification-capacity",
                      outcome.detail);
  return result;
}

FailureOr<SmallVector<Value>>
verifyExpression(Operation *source, ValueRange inputs, Operation *&cursor,
                 HelperReader helper, Operation *symbolRoot,
                 VerificationLimits limits, VerificationResult &outcome,
                 MathematicalSelectionPolicy policy) {
  outcome = {VerificationStatus::Mismatch,
             "finite expression differs from its domain/helper"};
  if (!cursor)
    return failure();
  auto *unit = SymbolTable::getNearestSymbolTable(cursor);
  if (!unit || unit->getNumRegions() != 1 || !unit->getRegion(0).hasOneBlock())
    return failure();
  SymbolTable symbols(unit);
  llvm::DenseSet<Operation *> bindings;
  Computation c;
  SymbolTableCollection sourceSymbols;
  if (failed(describe(source, c, symbolRoot, &sourceSymbols)))
    return failure();
  Reader reader(c, symbols, bindings, limits, policy.finiteBulk);
  auto result = reader.checkInline(inputs, cursor, helper);
  outcome = succeeded(result)
                ? VerificationResult{VerificationStatus::Verified, {}}
                : reader.outcome();
  return result;
}

VerificationResult checkRealizations(ModuleOp original, ModuleOp candidate,
                                     VerificationLimits limits) {
  if (failed(mlir::verify(original)) || failed(mlir::verify(candidate)))
    return {VerificationStatus::Mismatch, "module verification"};
  auto refuse = [&](StringRef detail) {
    return VerificationResult{VerificationStatus::Mismatch, detail};
  };
  if (!hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()) ||
      original->getAttrDictionary() != candidate->getAttrDictionary())
    return refuse("module shape");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse("unit profile");
  SymbolTable symbols(after);
  SymbolTableCollection sourceSymbols;
  llvm::DenseSet<Operation *> retained, usedBindings;
  for (auto &op : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    Operation *replacement = name ? symbols.lookup(name) : nullptr;
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    if (isDeclaration(&op)) {
      Computation c;
      if (failed(describe(&op, c, before, &sourceSymbols)))
        return refuse("finite recipe differs from its domain/helper");
      Reader reader(c, symbols, usedBindings, limits);
      if (!reader.check(dyn_cast<local::FuncOp>(replacement)))
        return reader.outcome();
    } else if (!OperationEquivalence::isEquivalentTo(
                   &op, replacement, OperationEquivalence::IgnoreLocations))
      return refuse("changed retained definition or helper body");
  }
  for (auto &op : after.getBody().front())
    if (!retained.contains(&op) && !usedBindings.contains(&op))
      return refuse("unexpected declaration");
  return {VerificationStatus::Verified, {}};
}

LogicalResult VerificationResult::diagnose(ModuleOp candidate) const {
  if (status == VerificationStatus::Verified)
    return success();
  return diagnostics::emit(candidate.emitError(),
                           status == VerificationStatus::Mismatch
                               ? "finite-correspondence"
                               : "finite-verification-capacity",
                           detail);
}

LogicalResult verifyRealizations(ModuleOp original, ModuleOp candidate) {
  return checkRealizations(original, candidate).diagnose(candidate);
}
} // namespace zkc::finite
