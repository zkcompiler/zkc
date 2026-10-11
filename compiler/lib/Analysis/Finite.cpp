#include "zkc/Analysis/Finite.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Interfaces/Collection.h"
#include "llvm/ADT/DenseSet.h"
#include <optional>
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
LogicalResult refuse(Operation *op, StringRef reason,
                     StringRef code = "finite-formation") {
  return diagnostics::emit(op->emitOpError(), code, reason);
}
FunctionType signature(Operation *op) {
  auto attr = op ? op->getAttrOfType<TypeAttr>("function_type") : TypeAttr();
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
}
Operation *resolve(Operation *op, StringRef key) {
  auto ref = op->getAttrOfType<FlatSymbolRefAttr>(key);
  return ref ? SymbolTable::lookupNearestSymbolFrom(op, ref) : nullptr;
}
struct EvidenceWork {
  uint64_t local = 65536;
  uint64_t &remaining = local;
  EvidenceWork() = default;
  explicit EvidenceWork(uint64_t &remaining) : remaining(remaining) {}
  EvidenceWork(const EvidenceWork &) = delete;
  EvidenceWork &operator=(const EvidenceWork &) = delete;
  llvm::DenseMap<std::pair<Operation *, unsigned>, std::optional<unsigned>>
      inputs;
  llvm::DenseMap<Value, Value> forwarded;
  llvm::DenseMap<std::pair<Value, unsigned>, std::optional<uint64_t>> extents;
  bool charge(uint64_t count = 1) {
    if (count > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= count;
    return true;
  }
};
bool provesBoundUnder(Value, Value, unsigned, EvidenceWork &);
// Only exact argument forwarding transfers an SSA relationship. A successor,
// shifted index or reconstructed container cannot acquire its predecessor's
// fact.
std::optional<unsigned> forwardedInput(Operation *helper, unsigned result,
                                       unsigned depth, EvidenceWork &work) {
  if (!work.charge() || depth > 64 || !isa_and_nonnull<func::FuncOp>(helper) ||
      !helper->getRegion(0).hasOneBlock())
    return std::nullopt;
  auto key = std::make_pair(helper, result);
  if (auto found = work.inputs.find(key); found != work.inputs.end())
    return found->second;
  auto &block = helper->getRegion(0).front();
  if (block.empty() || !isa<func::ReturnOp>(block.back()) ||
      result >= block.back().getNumOperands())
    return std::nullopt;
  Value value = block.back().getOperand(result);
  for (unsigned step = 0; step < 64 && work.charge(); ++step) {
    if (auto arg = dyn_cast<BlockArgument>(value)) {
      auto input = arg.getOwner() == &block
                       ? std::optional<unsigned>(arg.getArgNumber())
                       : std::nullopt;
      work.inputs.try_emplace(key, input);
      return input;
    }
    auto call = value.getDefiningOp<func::CallOp>();
    if (!call)
      return std::nullopt;
    auto input = forwardedInput(resolve(call, "callee"),
                                cast<OpResult>(value).getResultNumber(),
                                depth + 1, work);
    if (!input || *input >= call.getNumOperands())
      return std::nullopt;
    value = call.getOperand(*input);
  }
  return std::nullopt;
}
Value forwarded(Value value, EvidenceWork &work) {
  if (auto found = work.forwarded.find(value); found != work.forwarded.end())
    return found->second;
  auto original = value;
  for (unsigned step = 0; step < 64 && work.charge(); ++step) {
    auto call = value.getDefiningOp<func::CallOp>();
    if (!call)
      break;
    auto input =
        forwardedInput(resolve(call, "callee"),
                       cast<OpResult>(value).getResultNumber(), 0, work);
    if (!input || *input >= call.getNumOperands())
      break;
    value = call.getOperand(*input);
  }
  work.forwarded.try_emplace(original, value);
  return value;
}
bool index(Type type) { return type.isUnsignedInteger(64); }
bool axis(Type type, unsigned axis) {
  auto collection = dyn_cast<CollectionTypeInterface>(type);
  return collection && axis < collection.getRank() &&
         bool(elementType(type, collection.getRank() == 2));
}
std::optional<uint64_t> staticExtent(Type type, unsigned axis) {
  if (auto collection = dyn_cast<CollectionTypeInterface>(type))
    return collection.getStaticExtent(axis);
  return std::nullopt;
}
// Constructor evidence can preserve a fixed extent across a private helper
// even when the Sequence carrier itself is dynamically sized. Only inspect
// exact immutable constructors and returns, with bounded work and call depth.
// An input or an unrecognized producer supplies no such evidence.
std::optional<uint64_t> constructedExtent(Value value, unsigned axis,
                                          uint64_t &remaining,
                                          unsigned depth = 0) {
  if (!remaining || depth > 64)
    return std::nullopt;
  --remaining;
  if (auto size = staticExtent(value.getType(), axis))
    return size;
  if (axis || !isa<data::SequenceType>(value.getType()))
    return std::nullopt;
  uint64_t appended = 0;
  while (remaining) {
    --remaining;
    if (value.getDefiningOp<data::SequenceEmptyOp>())
      return appended;
    if (auto append = value.getDefiningOp<data::SequenceAppendOp>()) {
      if (appended == UINT64_MAX)
        return std::nullopt;
      ++appended;
      value = append->getOperand(0);
      continue;
    }
    auto call = value.getDefiningOp<func::CallOp>();
    auto *helper = call ? resolve(call, "callee") : nullptr;
    if (!isa_and_nonnull<func::FuncOp>(helper) ||
        !helper->getRegion(0).hasOneBlock())
      return std::nullopt;
    auto &body = helper->getRegion(0).front();
    auto result = cast<OpResult>(value).getResultNumber();
    if (body.empty() || !isa<func::ReturnOp>(body.back()) ||
        result >= body.back().getNumOperands())
      return std::nullopt;
    auto size = constructedExtent(body.back().getOperand(result), axis,
                                  remaining, depth + 1);
    if (!size || *size > UINT64_MAX - appended)
      return std::nullopt;
    return *size + appended;
  }
  return std::nullopt;
}
std::optional<uint64_t> knownExtent(Value value, unsigned axis,
                                    EvidenceWork &work) {
  auto key = std::make_pair(value, axis);
  if (auto found = work.extents.find(key); found != work.extents.end())
    return found->second;
  auto result = constructedExtent(forwarded(value, work), axis, work.remaining);
  work.extents.try_emplace(key, result);
  return result;
}
std::optional<uint64_t> constant(Value value) {
  if (auto op = value.getDefiningOp<data::IndexOp>()) {
    uint64_t n;
    if (!op.getValue().getAsInteger(10, n))
      return n;
  }
  return std::nullopt;
}
Operation *argumentOwner(Value value) {
  auto arg = dyn_cast<BlockArgument>(value);
  return arg ? arg.getOwner()->getParentOp() : nullptr;
}
ArrayAttr preconditions(Operation *owner) {
  return owner ? owner->getAttrOfType<ArrayAttr>("data.preconditions")
               : ArrayAttr();
}
struct Extent {
  Value container;
  unsigned axis = 0;
};
// Formal equal-extent assumptions form an undirected relation. Its closure
// never equates containers for element identity; only their selected extents.
bool equalUnder(Value left, unsigned la, Value right, unsigned ra,
                EvidenceWork &work) {
  if (!work.charge())
    return false;
  if (left == right && la == ra)
    return true;
  left = forwarded(left, work);
  right = forwarded(right, work);
  if (left == right && la == ra)
    return true;
  auto a = knownExtent(left, la, work), b = knownExtent(right, ra, work);
  if (a && b)
    return *a == *b;
  Operation *owner = argumentOwner(left);
  if (!owner || owner != argumentOwner(right) || owner->getNumRegions() != 1 ||
      !owner->getRegion(0).hasOneBlock())
    return false;
  auto attrs = preconditions(owner);
  if (!attrs)
    return false;
  SmallVector<Extent> pending{{left, la}}, seen;
  auto &block = owner->getRegion(0).front();
  while (!pending.empty()) {
    auto current = pending.pop_back_val();
    if (current.container == right && current.axis == ra)
      return true;
    if (any_of(seen, [&](Extent x) {
          return x.container == current.container && x.axis == current.axis;
        }))
      continue;
    seen.push_back(current);
    if (!work.charge(attrs.size() + 1))
      return false;
    for (auto attr : attrs)
      if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
        if (equal.getLeftArg() >= block.getNumArguments() ||
            equal.getRightArg() >= block.getNumArguments())
          continue;
        Extent x{block.getArgument(equal.getLeftArg()), equal.getLeftAxis()};
        Extent y{block.getArgument(equal.getRightArg()), equal.getRightAxis()};
        if (x.container == current.container && x.axis == current.axis)
          pending.push_back(y);
        if (y.container == current.container && y.axis == current.axis)
          pending.push_back(x);
      }
  }
  return false;
}
// Each index item can carry a bound to one exact domain argument and axis.
struct ItemBound {
  int argument = -1;
  unsigned axis = 0;
};
SmallVector<ItemBound> itemBounds(Value descriptor, EvidenceWork &work) {
  if (!work.charge())
    return {};
  auto *op = descriptor.getDefiningOp();
  if (isa<data::DomainZipOp, data::DomainProductOp>(op)) {
    SmallVector<ItemBound> result;
    for (Value child : op->getOperands())
      append_range(result, itemBounds(child, work));
    return result;
  }
  auto container = op->getNumOperands()
                       ? dyn_cast<BlockArgument>(op->getOperand(0))
                       : BlockArgument();
  if (auto indices = dyn_cast<data::DomainIndicesOp>(op))
    return {{container ? int(container.getArgNumber()) : -1,
             unsigned(indices.getAxis())}};
  if (isa<data::DomainMatrixCoordinatesOp>(op))
    return {{container ? int(container.getArgNumber()) : -1, 0},
            {container ? int(container.getArgNumber()) : -1, 1}};
  return SmallVector<ItemBound>(
      cast<data::DomainType>(descriptor.getType()).getItemTypes().size());
}
Value domainResult(data::DomainOp domain) {
  return domain.getBody().front().back().getOperand(0);
}
struct Cardinality {
  Value container;
  unsigned axis = 0;
  std::optional<uint64_t> fixed;
};
Cardinality extent(Value domain, const Computation &c, EvidenceWork &work) {
  if (!work.charge())
    return {};
  auto *op = domain.getDefiningOp();
  if (isa<data::DomainZipOp>(op))
    return extent(op->getOperand(0), c, work);
  if (isa<data::DomainProductOp>(op)) {
    std::optional<uint64_t> count = 1;
    for (Value child : op->getOperands()) {
      auto factor = extent(child, c, work).fixed;
      if (factor && !*factor)
        return {{}, 0, 0};
      if (!factor || !count || (*factor && *count > UINT64_MAX / *factor))
        count.reset();
      else
        *count *= *factor;
    }
    return {{}, 0, count};
  }
  if (isa<data::DomainElementsOp, data::DomainIndicesOp,
          data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
    unsigned axis = isa<data::DomainMatrixRowOp>(op) ? 1 : 0;
    if (auto indices = dyn_cast<data::DomainIndicesOp>(op))
      axis = indices.getAxis();
    auto arg = cast<BlockArgument>(op->getOperand(0));
    Value actual =
        c.total ? c.operation->getOperand(arg.getArgNumber()) : Value(arg);
    return {actual, axis, knownExtent(actual, axis, work)};
  }
  if (auto range = dyn_cast<data::DomainRangeOp>(op); range && c.total) {
    auto lo = constant(c.operation->getOperand(
        cast<BlockArgument>(range.getLower()).getArgNumber()));
    auto hi = constant(c.operation->getOperand(
        cast<BlockArgument>(range.getUpper()).getArgNumber()));
    if (lo && hi)
      return {{}, 0, *hi > *lo ? *hi - *lo : 0};
  }
  return {};
}
bool sameExtent(Cardinality a, Cardinality b, EvidenceWork &work) {
  if (a.fixed && b.fixed)
    return *a.fixed == *b.fixed;
  return a.container && b.container &&
         equalUnder(a.container, a.axis, b.container, b.axis, work);
}
bool sameCardinality(Value left, Value right, const Computation &c,
                     EvidenceWork &work) {
  if (!work.charge())
    return false;
  if (left == right ||
      sameExtent(extent(left, c, work), extent(right, c, work), work))
    return true;
  auto *a = left.getDefiningOp(), *b = right.getDefiningOp();
  if (isa<data::DomainZipOp>(a))
    return sameCardinality(a->getOperand(0), right, c, work);
  if (isa<data::DomainZipOp>(b))
    return sameCardinality(left, b->getOperand(0), c, work);
  if (isa<data::DomainProductOp>(a) && isa<data::DomainProductOp>(b) &&
      a->getNumOperands() == b->getNumOperands()) {
    for (auto [x, y] : zip(a->getOperands(), b->getOperands()))
      if (!sameCardinality(x, y, c, work))
        return false;
    return true;
  }
  if (isa<data::DomainRangeOp>(a) && isa<data::DomainRangeOp>(b)) {
    for (auto [x, y] : zip(a->getOperands(), b->getOperands())) {
      if (c.total) {
        x = c.operation->getOperand(cast<BlockArgument>(x).getArgNumber());
        y = c.operation->getOperand(cast<BlockArgument>(y).getArgNumber());
      }
      if (forwarded(x, work) != forwarded(y, work))
        return false;
    }
    return true;
  }
  if (isa<data::DomainMatrixCoordinatesOp>(a) &&
      isa<data::DomainMatrixCoordinatesOp>(b)) {
    Value x = a->getOperand(0), y = b->getOperand(0);
    if (c.total) {
      x = c.operation->getOperand(cast<BlockArgument>(x).getArgNumber());
      y = c.operation->getOperand(cast<BlockArgument>(y).getArgNumber());
    }
    return equalUnder(x, 0, y, 0, work) && equalUnder(x, 1, y, 1, work);
  }
  return false;
}
LogicalResult helperAssumptions(const Computation &c, CallbackRole role,
                                EvidenceWork &work) {
  auto callback = readCallback(c, role);
  if (failed(callback))
    return failure();
  auto *helper = callback->symbol;
  auto attrs = preconditions(helper);
  if (!attrs)
    return success();
  if (failed(verifyPreconditions(helper)))
    return failure();
  auto items = itemBounds(domainResult(c.domain), work);
  if (items.size() != callback->formals.items.size())
    return refuse(c.operation, "finite item bound partition", "finite-bound");
  if (!work.charge(attrs.size() + 1))
    return refuse(c.operation, "finite evidence work limit", "finite-bound");
  unsigned offset = callback->formals.state.size();
  unsigned argBase = offset + callback->formals.items.size();
  llvm::DenseMap<Value, Value> invariants;
  if (c.total) {
    auto entry = partitionEntry(c, c.operation->getOperands());
    if (failed(entry))
      return failure();
    for (auto [formal, actual] : zip(callback->formals.domain, entry->domain))
      invariants[formal] = actual;
    for (auto [formal, actual] :
         zip(callback->formals.captures, entry->captures))
      invariants[formal] = actual;
  }
  auto actual = [&](unsigned param) -> Value {
    return param < callback->body->getNumArguments()
               ? invariants.lookup(callback->body->getArgument(param))
               : Value();
  };
  for (auto attr : attrs) {
    if (auto bound = dyn_cast<data::IndexBoundAttr>(attr)) {
      unsigned i = bound.getIndexArg(), a = bound.getContainerArg();
      bool valid = false;
      if (i >= offset && i < argBase && a >= argBase) {
        auto fact = items[i - offset];
        valid = a < argBase + c.arguments &&
                fact.argument == int(a - argBase) &&
                fact.axis == bound.getAxis();
        // A total computation can read a captured container using the domain
        // index when the caller establishes equality of the selected extents.
        // This transfers only a bound, never container or element identity.
        if (!valid && fact.argument >= 0 && actual(a))
          valid = equalUnder(c.operation->getOperand(fact.argument), fact.axis,
                             actual(a), bound.getAxis(), work);
      }
      if (!valid && actual(i) && actual(a))
        valid = provesBoundUnder(actual(i), actual(a), bound.getAxis(), work);
      if (!valid)
        return refuse(c.operation,
                      "finite helper bound is not discharged by the domain",
                      "finite-bound");
    } else if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
      Value l = actual(equal.getLeftArg()), r = actual(equal.getRightArg());
      if (!l || !r ||
          !equalUnder(l, equal.getLeftAxis(), r, equal.getRightAxis(), work))
        return refuse(c.operation,
                      "finite helper equal extent is not discharged",
                      "finite-bound");
    }
  }
  return success();
}
bool provesBoundUnder(Value idx, Value container, unsigned selectedAxis,
                      EvidenceWork &work) {
  if (!work.charge())
    return false;
  idx = forwarded(idx, work);
  container = forwarded(container, work);
  if (!index(idx.getType()) || !axis(container.getType(), selectedAxis))
    return false;
  auto n = constant(idx), size = knownExtent(container, selectedAxis, work);
  if (n && size && *n < *size)
    return true;
  auto arg = dyn_cast<BlockArgument>(idx);
  auto owner = argumentOwner(idx);
  auto attrs = preconditions(owner);
  if (!arg || !attrs || owner->getNumRegions() != 1 ||
      !owner->getRegion(0).hasOneBlock())
    return false;
  auto &block = owner->getRegion(0).front();
  if (arg.getOwner() != &block || !work.charge(attrs.size() + 1))
    return false;
  for (auto attr : attrs)
    if (auto bound = dyn_cast<data::IndexBoundAttr>(attr))
      if (bound.getIndexArg() == arg.getArgNumber() &&
          bound.getContainerArg() < block.getNumArguments() &&
          equalUnder(block.getArgument(bound.getContainerArg()),
                     bound.getAxis(), container, selectedAxis, work))
        return true;
  return false;
}
} // namespace
Type elementType(Type container, bool matrix) {
  auto bound = protocol::encodeBoundType(container, false);
  if (!bound) {
    consumeError(bound.takeError());
    return {};
  }
  if (matrix) {
    if (bound->kind != "matrix")
      return {};
  } else if (!is_contained(ArrayRef<StringRef>{"vector", "groups", "indices",
                                               "field_array", "sequence"},
                           bound->kind))
    return {};
  auto collection = dyn_cast<CollectionTypeInterface>(container);
  return collection ? collection.getElementType() : Type();
}
bool isComputation(Operation *op) {
  return isa_and_nonnull<local::FiniteFoldOp, local::FiniteCollectOp,
                         algebra::FiniteFoldOp, algebra::FiniteCollectOp>(op);
}
bool isDeclaration(Operation *op) {
  return isa_and_nonnull<local::FiniteFoldOp, local::FiniteCollectOp>(op);
}
bool provesEqualExtent(Value a, unsigned aa, Value b, unsigned ba) {
  EvidenceWork work;
  return equalUnder(a, aa, b, ba, work);
}
bool provesBound(Value idx, Value container, unsigned selectedAxis) {
  EvidenceWork work;
  return provesBoundUnder(idx, container, selectedAxis, work);
}
bool provesEqualExtent(Value a, unsigned aa, Value b, unsigned ba,
                       uint64_t &remaining) {
  EvidenceWork work(remaining);
  return equalUnder(a, aa, b, ba, work);
}
bool provesBound(Value idx, Value container, unsigned selectedAxis,
                 uint64_t &remaining) {
  EvidenceWork work(remaining);
  return provesBoundUnder(idx, container, selectedAxis, work);
}
LogicalResult verifyPreconditions(Operation *helper) {
  auto raw = helper->getAttr("data.preconditions");
  if (!raw)
    return success();
  auto attrs = dyn_cast<ArrayAttr>(raw);
  auto type = signature(helper);
  if (!attrs || !type || attrs.size() > 1024)
    return refuse(helper, "malformed helper preconditions", "finite-bound");
  auto validAxis = [&](unsigned arg, unsigned selected) {
    return arg < type.getNumInputs() && axis(type.getInput(arg), selected);
  };
  for (auto attr : attrs) {
    if (auto bound = dyn_cast<data::IndexBoundAttr>(attr)) {
      if (bound.getIndexArg() >= type.getNumInputs() ||
          !index(type.getInput(bound.getIndexArg())) ||
          !validAxis(bound.getContainerArg(), bound.getAxis()))
        return refuse(helper, "invalid index bound parameters", "finite-bound");
    } else if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
      if (!validAxis(equal.getLeftArg(), equal.getLeftAxis()) ||
          !validAxis(equal.getRightArg(), equal.getRightAxis()))
        return refuse(helper, "invalid equal extent parameters",
                      "finite-bound");
    } else
      return refuse(helper, "unknown helper precondition", "finite-bound");
  }
  return success();
}
LogicalResult verifyCallPreconditions(Operation *call) {
  EvidenceWork work;
  auto *helper = resolve(call, "callee");
  auto attrs = preconditions(helper);
  if (!attrs)
    return success();
  if (failed(verifyPreconditions(helper)))
    return failure();
  for (auto attr : attrs) {
    if (auto bound = dyn_cast<data::IndexBoundAttr>(attr)) {
      if (bound.getIndexArg() >= call->getNumOperands() ||
          bound.getContainerArg() >= call->getNumOperands() ||
          !provesBoundUnder(call->getOperand(bound.getIndexArg()),
                            call->getOperand(bound.getContainerArg()),
                            bound.getAxis(), work))
        return refuse(call, "call does not discharge index bound",
                      "finite-bound");
    } else if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
      if (equal.getLeftArg() >= call->getNumOperands() ||
          equal.getRightArg() >= call->getNumOperands() ||
          !equalUnder(call->getOperand(equal.getLeftArg()), equal.getLeftAxis(),
                      call->getOperand(equal.getRightArg()),
                      equal.getRightAxis(), work))
        return refuse(call, "call does not discharge equal extent",
                      "finite-bound");
    }
  }
  return success();
}
LogicalResult describe(Operation *op, Computation &c, Operation *symbolRoot,
                       SymbolTableCollection *symbols) {
  c = {};
  c.operation = op;
  if (!isComputation(op))
    return refuse(op, "expected finite computation");
  c.total = !isDeclaration(op);
  c.collect = isa<local::FiniteCollectOp, algebra::FiniteCollectOp>(op);
  c.signature = c.total
                    ? FunctionType::get(op->getContext(), op->getOperandTypes(),
                                        op->getResultTypes())
                    : signature(op);
  auto reference = [&](StringRef name) {
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>(name);
    if (symbols && ref)
      return symbolRoot ? symbols->lookupSymbolIn(symbolRoot, ref)
                        : symbols->lookupNearestSymbolFrom(op, ref);
    return symbolRoot && ref ? SymbolTable::lookupSymbolIn(symbolRoot, ref)
                             : resolve(op, name);
  };
  c.domain = dyn_cast_or_null<data::DomainOp>(reference("domain"));
  c.helper = reference(c.collect ? "body" : "step");
  c.predicate = reference("predicate");
  if (!c.signature || !c.domain || !c.helper ||
      (op->hasAttr("predicate") && !c.predicate))
    return refuse(op, "unresolved finite domain/helper signature");
  auto dt = c.domain.getFunctionType();
  if (!c.domain.getBody().hasOneBlock() || c.domain.getBody().front().empty() ||
      !isa<data::DomainYieldOp>(c.domain.getBody().front().back()))
    return refuse(op, "domain requires a constructor body");
  if (dt.getNumResults() != 1 || !isa<data::DomainType>(dt.getResult(0)))
    return refuse(op, "domain result signature");
  c.arguments = dt.getNumInputs();
  c.states = c.collect ? 0 : c.signature.getNumResults();
  if ((c.collect && c.signature.getNumResults() != 1) ||
      c.signature.getNumInputs() < c.arguments + c.states)
    return refuse(op, "finite operand partitions");
  c.captures = c.signature.getNumInputs() - c.arguments - c.states;
  return success();
}
namespace {
bool entryShape(const Computation &c) {
  if (!c.signature || !c.domain ||
      c.signature.getNumInputs() != c.arguments + c.states + c.captures ||
      (c.collect ? c.states != 0 || c.signature.getNumResults() != 1
                 : c.states != c.signature.getNumResults()))
    return false;
  auto domainType = signature(c.domain);
  return domainType && domainType.getNumInputs() == c.arguments &&
         domainType.getNumResults() == 1 &&
         isa<data::DomainType>(domainType.getResult(0)) &&
         c.signature.getInputs().take_front(c.arguments) ==
             domainType.getInputs() &&
         (c.collect || c.signature.getInputs().slice(c.arguments, c.states) ==
                           c.signature.getResults());
}
bool sameTypes(ValueRange values, TypeRange types) {
  return values.size() == types.size() &&
         llvm::all_of(llvm::zip(values, types), [](auto pair) {
           auto [value, type] = pair;
           return value && value.getType() == type;
         });
}
} // namespace
FailureOr<EntryValues> partitionEntry(const Computation &c,
                                      ValueRange actuals) {
  if (!entryShape(c) || !sameTypes(actuals, c.signature.getInputs()))
    return failure();
  return EntryValues{actuals.take_front(c.arguments),
                     actuals.slice(c.arguments, c.states),
                     actuals.drop_front(c.arguments + c.states)};
}
FailureOr<CallbackView> readCallback(const Computation &c, CallbackRole role) {
  if (!entryShape(c) || (role == CallbackRole::Step && c.collect) ||
      (role == CallbackRole::Body && !c.collect))
    return failure();
  auto *helper = role == CallbackRole::Predicate ? c.predicate : c.helper;
  auto type = signature(helper);
  auto visibility = helper ? helper->getAttrOfType<StringAttr>("sym_visibility")
                           : StringAttr();
  if (!type || !visibility || visibility.getValue() != "private" ||
      (c.total ? !isa<func::FuncOp>(helper) : !isa<local::FuncOp>(helper)) ||
      helper->getNumRegions() != 1 || !helper->getRegion(0).hasOneBlock())
    return failure();
  auto &body = helper->getRegion(0).front();
  auto items =
      cast<data::DomainType>(signature(c.domain).getResult(0)).getItemTypes();
  unsigned states = role == CallbackRole::Step ? c.states : 0;
  SmallVector<Type> inputs, outputs;
  if (states)
    append_range(inputs, c.signature.getResults());
  append_range(inputs, items);
  append_range(inputs, c.signature.getInputs().take_front(c.arguments));
  append_range(inputs,
               c.signature.getInputs().drop_front(c.arguments + c.states));
  if (role == CallbackRole::Predicate)
    outputs.push_back(IntegerType::get(helper->getContext(), 1));
  else if (role == CallbackRole::Body) {
    auto element = elementType(c.signature.getResult(0));
    if (!element)
      return failure();
    outputs.push_back(element);
  } else
    append_range(outputs, c.signature.getResults());
  if (type.getInputs() != ArrayRef<Type>(inputs) ||
      type.getResults() != ArrayRef<Type>(outputs) || body.empty() ||
      !sameTypes(body.getArguments(), inputs))
    return failure();
  auto *terminator = &body.back();
  bool stop = !c.total && isa<local::StopOp>(terminator);
  if (!stop && ((c.total ? !isa<func::ReturnOp>(terminator)
                         : !isa<local::ReturnOp>(terminator)) ||
                !sameTypes(terminator->getOperands(), outputs)))
    return failure();
  ValueRange formals = body.getArguments();
  return CallbackView{
      helper,
      &body,
      type,
      role,
      {formals.take_front(states), formals.slice(states, items.size()),
       formals.slice(states + items.size(), c.arguments),
       formals.drop_front(states + items.size() + c.arguments)},
      terminator,
      stop ? CallbackExit::Stop : CallbackExit::Return,
      stop ? ValueRange{} : ValueRange(terminator->getOperands())};
}
FailureOr<CallEnvironment> bindCallback(const CallbackView &callback,
                                        CallbackValues actuals) {
  CallEnvironment result{callback, {}};
  for (auto [formal, actual] :
       {std::pair{callback.formals.state, actuals.state},
        std::pair{callback.formals.items, actuals.items},
        std::pair{callback.formals.domain, actuals.domain},
        std::pair{callback.formals.captures, actuals.captures}}) {
    if (!sameTypes(actual, formal.getTypes()))
      return failure();
    append_range(result.actuals, actual);
  }
  return result;
}
FailureOr<Value> CallEnvironment::lookup(BlockArgument formal) const {
  if (!formal || formal.getOwner() != callback.body ||
      formal.getArgNumber() >= actuals.size())
    return failure();
  return actuals[formal.getArgNumber()];
}
LogicalResult verifyLocal(Operation *op) {
  if (!isComputation(op))
    return refuse(op, "expected finite computation");
  bool total = !isDeclaration(op);
  bool collect = isa<local::FiniteCollectOp, algebra::FiniteCollectOp>(op);
  for (auto attr : op->getAttrs()) {
    StringRef name = attr.getName().getValue();
    if (name == "domain" || name == "predicate" ||
        name == (collect ? "body" : "step"))
      continue;
    if (!total && (name == "sym_name" || name == "function_type"))
      continue;
    return refuse(op, "unexpected finite attribute");
  }
  auto type = total ? FunctionType::get(op->getContext(), op->getOperandTypes(),
                                        op->getResultTypes())
                    : signature(op);
  if (!type || (collect && type.getNumResults() != 1))
    return refuse(op, "finite result signature");
  return success();
}
LogicalResult verify(Operation *op) {
  SymbolTableCollection symbols;
  if (failed(verifyLocal(op)))
    return failure();
  return verifyReferences(op, symbols);
}
LogicalResult verifyReferences(Operation *op, SymbolTableCollection &symbols) {
  Computation c;
  if (failed(describe(op, c, nullptr, &symbols)))
    return failure();
  auto inputs = c.signature.getInputs();
  auto callback =
      readCallback(c, c.collect ? CallbackRole::Body : CallbackRole::Step);
  if (failed(callback) ||
      (c.predicate && failed(readCallback(c, CallbackRole::Predicate))))
    return refuse(op, "expected defined private helper with exact finite ABI");
  auto native = [&](Type type) {
    auto bound = protocol::encodeBoundType(type, false);
    if (!bound) {
      consumeError(bound.takeError());
      return false;
    }
    return true;
  };
  mathematical::NativeTypePolicies policies(op);
  for (auto [i, type] : enumerate(inputs)) {
    auto p = policies.get(type);
    bool state = i >= c.arguments && i < c.arguments + c.states;
    if (!native(type) || !p || (c.total && !p->total) || (!state && p->affine))
      return refuse(op, "finite input type/capture policy");
  }
  for (Type type : c.signature.getResults()) {
    auto p = policies.get(type);
    if (!native(type) || !p || (c.total && !p->total) ||
        (c.collect && p->affine))
      return refuse(op, "finite result policy");
  }
  EvidenceWork work;
  if (failed(helperAssumptions(c, callback->role, work)) ||
      (c.predicate &&
       failed(helperAssumptions(c, CallbackRole::Predicate, work))))
    return failure();
  if (c.total) {
    for (auto &constructor : c.domain.getBody().front()) {
      if (auto zip = dyn_cast<data::DomainZipOp>(constructor)) {
        for (Value child : zip.getOperands().drop_front())
          if (!sameCardinality(zip.getOperand(0), child, c, work))
            return refuse(op, "total zip requires equal-extent evidence",
                          "finite-bound");
      }
      if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
              constructor)) {
        auto container = c.operation->getOperand(
            cast<BlockArgument>(constructor.getOperand(0)).getArgNumber());
        auto selector = c.operation->getOperand(
            cast<BlockArgument>(constructor.getOperand(1)).getArgNumber());
        if (!provesBoundUnder(selector, container,
                              isa<data::DomainMatrixRowOp>(constructor) ? 0 : 1,
                              work))
          return refuse(op, "total matrix view requires a selector bound",
                        "finite-bound");
      }
    }
  }
  if (c.collect)
    if (auto array =
            dyn_cast<algebra::FieldArrayType>(c.signature.getResult(0))) {
      auto card = extent(domainResult(c.domain), c, work);
      if (c.predicate || !card.fixed || *card.fixed != array.getLength())
        return refuse(
            op,
            "fixed collection requires proven exact unfiltered cardinality");
    }
  return success();
}
LogicalResult verifyClosure(Operation *unit) {
  bool hasFinite = false;
  unit->walk([&](Operation *op) { hasFinite |= isComputation(op); });
  if (!hasFinite) {
    // Preserve the existing pure/local cycle diagnostics in units without a
    // finite reference edge. Preconditions still apply to ordinary calls.
    auto checked = unit->walk([&](Operation *op) -> WalkResult {
      if (isa<func::FuncOp, local::FuncOp>(op) &&
          failed(verifyPreconditions(op)))
        return WalkResult::interrupt();
      if (isa<func::CallOp, local::ApplyOp>(op) &&
          failed(verifyCallPreconditions(op)))
        return WalkResult::interrupt();
      return WalkResult::advance();
    });
    return failure(checked.wasInterrupted());
  }
  llvm::DenseMap<Operation *, unsigned> color;
  SymbolTableCollection symbols;
  unsigned work = 100000;
  std::function<LogicalResult(Operation *, unsigned)> visit =
      [&](Operation *definition, unsigned depth) -> LogicalResult {
    if (depth > 64 || !work)
      return refuse(definition, "static closure exceeds analysis limit");
    --work;
    if (color[definition] == 2)
      return success();
    if (color[definition] == 1)
      return refuse(definition, "all static references must be acyclic",
                    "finite-cycle");
    color[definition] = 1;
    auto walked = definition->walk([&](Operation *op) -> WalkResult {
      if (!work) {
        (void)refuse(op, "static closure exceeds analysis limit");
        return WalkResult::interrupt();
      }
      --work;
      // Symbol-table region verification has already checked each finite ABI.
      // This traversal owns reference cycles and call premises, not another
      // independent replay of every finite computation's verification.
      if (isa<func::FuncOp, local::FuncOp>(op) &&
          failed(verifyPreconditions(op)))
        return WalkResult::interrupt();
      if (isa<func::CallOp, local::ApplyOp>(op) &&
          failed(verifyCallPreconditions(op)))
        return WalkResult::interrupt();
      for (StringRef edge : {"callee", "helper", "step", "body", "predicate"}) {
        if (!op->hasAttrOfType<FlatSymbolRefAttr>(edge))
          continue;
        Operation *callee = symbols.lookupNearestSymbolFrom(
            op, op->getAttrOfType<FlatSymbolRefAttr>(edge));
        if (callee &&
            (isa<func::FuncOp, local::FuncOp, local::RealizeOp>(callee) ||
             isDeclaration(callee)))
          if (failed(visit(callee, depth + 1)))
            return WalkResult::interrupt();
      }
      return WalkResult::advance();
    });
    if (walked.wasInterrupted())
      return failure();
    color[definition] = 2;
    return success();
  };
  for (auto &op : unit->getRegion(0).front())
    if (failed(visit(&op, 0)))
      return failure();
  return success();
}
} // namespace zkc::finite

namespace zkc::local {
LogicalResult FiniteFoldOp::verify() { return finite::verifyLocal(*this); }
LogicalResult FiniteCollectOp::verify() { return finite::verifyLocal(*this); }
LogicalResult FiniteFoldOp::verifySymbolUses(SymbolTableCollection &symbols) {
  return finite::verifyReferences(*this, symbols);
}
LogicalResult
FiniteCollectOp::verifySymbolUses(SymbolTableCollection &symbols) {
  return finite::verifyReferences(*this, symbols);
}
} // namespace zkc::local
namespace zkc::algebra {
LogicalResult FiniteFoldOp::verify() { return finite::verifyLocal(*this); }
LogicalResult FiniteCollectOp::verify() { return finite::verifyLocal(*this); }
LogicalResult FiniteFoldOp::verifySymbolUses(SymbolTableCollection &symbols) {
  return finite::verifyReferences(*this, symbols);
}
LogicalResult
FiniteCollectOp::verifySymbolUses(SymbolTableCollection &symbols) {
  return finite::verifyReferences(*this, symbols);
}
} // namespace zkc::algebra

namespace zkc::finite {
namespace {
class DependencyAnalysis {
  llvm::DenseMap<Operation *, Summary> cache;
  llvm::DenseSet<Operation *> active;
  uint64_t remaining = 1000000;
  LogicalResult charge(Operation *op, uint64_t n) {
    if (n > remaining)
      return refuse(op, "finite dependency budget exceeded",
                    "finite-analysis-limit");
    remaining -= n;
    return success();
  }
  BitVector substitute(const BitVector &bits, ArrayRef<BitVector> arguments,
                       unsigned size) {
    BitVector result(size);
    for (int i = bits.find_first(); i >= 0; i = bits.find_next(i))
      result |= arguments[i];
    return result;
  }

public:
  LogicalResult helper(Operation *op, const Summary *&out) {
    if (auto it = cache.find(op); it != cache.end()) {
      out = &it->second;
      return success();
    }
    if (!active.insert(op).second || active.size() > 64)
      return refuse(op, "finite summary cycle/depth", "finite-cycle");
    auto type = signature(op);
    if (!type || op->getNumRegions() != 1 || !op->getRegion(0).hasOneBlock())
      return refuse(op, "summary needs a defined helper");
    auto &body = op->getRegion(0).front();
    unsigned size = body.getNumArguments();
    if (failed(charge(op, uint64_t(size) * ((size + 63) / 64 + 1))))
      return failure();
    Summary result;
    llvm::DenseMap<Value, BitVector> env;
    for (auto [i, arg] : enumerate(body.getArguments())) {
      BitVector b(size);
      b.set(i);
      env[arg] = b;
    }
    for (auto &operation : body) {
      auto *nested = &operation;
      if (failed(charge(
              nested, (1 + nested->getNumOperands() + nested->getNumResults()) *
                          ((size + 63) / 64 + 1))))
        return failure();
      SmallVector<BitVector> args;
      for (Value v : nested->getOperands())
        args.push_back(env.lookup(v));
      if (isa<func::ReturnOp, local::ReturnOp>(nested)) {
        result.results = args;
        continue;
      }
      Summary child;
      if (isComputation(nested)) {
        if (failed(computation(nested, child)))
          return failure();
      } else if (isa<func::CallOp, local::ApplyOp>(nested)) {
        auto callee = resolve(nested, "callee");
        if (!callee)
          return refuse(nested, "missing summary callee");
        if (isDeclaration(callee)) {
          if (failed(computation(callee, child)))
            return failure();
        } else {
          const Summary *summary;
          if (failed(helper(callee, summary)))
            return failure();
          child = *summary;
        }
      } else {
        // Local regions conservatively depend on all explicit captures. Their
        // complete syntax is separately checked by native/control admission.
        BitVector all(args.size(), true);
        child.results.assign(nested->getNumResults(), all);
        child.formation.push_back(all);
      }
      if (child.results.size() != nested->getNumResults())
        return refuse(nested, "summary result arity");
      for (auto &requirement : child.formation)
        result.formation.push_back(substitute(requirement, args, size));
      for (auto [v, bits] : zip(nested->getResults(), child.results))
        env[v] = substitute(bits, args, size);
    }
    if (result.results.empty())
      result.results.assign(type.getNumResults(), BitVector(size));
    if (result.results.size() != type.getNumResults())
      return refuse(op, "helper summary result arity");
    active.erase(op);
    out = &cache.try_emplace(op, std::move(result)).first->second;
    return success();
  }
  LogicalResult computation(Operation *op, Summary &out) {
    Computation c;
    if (failed(describe(op, c)))
      return failure();
    const Summary *step;
    if (failed(helper(c.helper, step)))
      return failure();
    unsigned size = c.signature.getNumInputs();
    BitVector admission(size);
    for (unsigned i = 0; i < c.arguments; ++i)
      admission.set(i);
    auto callback =
        readCallback(c, c.collect ? CallbackRole::Body : CallbackRole::Step);
    if (failed(callback))
      return failure();
    llvm::DenseMap<Value, BitVector> dependencies;
    auto inputs = [&](ValueRange formals, unsigned base) {
      for (auto [i, formal] : enumerate(formals)) {
        BitVector bits(size);
        bits.set(base + i);
        dependencies[formal] = std::move(bits);
      }
    };
    inputs(callback->formals.state, c.arguments);
    inputs(callback->formals.domain, 0);
    inputs(callback->formals.captures, c.arguments + c.states);
    for (Value formal : callback->formals.items)
      dependencies[formal] = admission;
    SmallVector<BitVector> args;
    for (Value formal : callback->body->getArguments())
      args.push_back(dependencies.lookup(formal));
    if (c.predicate) {
      const Summary *predicate;
      if (failed(helper(c.predicate, predicate)))
        return failure();
      auto predicateABI = readCallback(c, CallbackRole::Predicate);
      if (failed(predicateABI))
        return failure();
      auto binding = bindCallback(*predicateABI, {{},
                                                  callback->formals.items,
                                                  callback->formals.domain,
                                                  callback->formals.captures});
      if (failed(binding))
        return failure();
      SmallVector<BitVector> pa;
      for (Value actual : binding->actuals)
        pa.push_back(dependencies.lookup(actual));
      for (auto &bits : predicate->results)
        admission |= substitute(bits, pa, size);
      for (auto &bits : predicate->formation)
        out.formation.push_back(substitute(bits, pa, size));
    }
    if (c.collect) {
      BitVector result = admission;
      for (auto &bits : step->results)
        result |= substitute(bits, args, size);
      out.results.push_back(result);
    } else {
      out.results.assign(args.begin(), args.begin() + c.states);
      bool changed;
      do {
        changed = false;
        for (unsigned i = 0; i < c.states; ++i) {
          if (failed(charge(op, uint64_t(size + 1) * (args.size() + 1))))
            return failure();
          BitVector next = out.results[i];
          next |= admission;
          next |= substitute(step->results[i], args, size);
          if (next != out.results[i]) {
            out.results[i] = next;
            changed = true;
          }
        }
        for (unsigned i = 0; i < c.states; ++i)
          args[i] = out.results[i];
      } while (changed);
    }
    out.formation.push_back(admission);
    for (auto &bits : step->formation)
      out.formation.push_back(substitute(bits, args, size));
    return success();
  }
};
} // namespace
LogicalResult summarize(Operation *op, Summary &result) {
  result = {};
  if (failed(verify(op)))
    return failure();
  return DependencyAnalysis().computation(op, result);
}
} // namespace zkc::finite

namespace zkc::finite {
FailureOr<StringAttr> closureKey(Operation *op) {
  std::string text;
  raw_string_ostream out(text);
  llvm::DenseSet<Operation *> seen;
  unsigned remaining = 100000;
  std::function<LogicalResult(Operation *)> read =
      [&](Operation *at) -> LogicalResult {
    if (!seen.insert(at).second)
      return success();
    if (!remaining--)
      return failure();
    at->print(out, OpPrintingFlags().useLocalScope());
    out << "\n";
    if (text.size() > 1024 * 1024)
      return failure();
    auto walked = at->walk([&](Operation *nested) -> WalkResult {
      for (StringRef edge :
           {"domain", "step", "body", "predicate", "helper", "callee"}) {
        if (!nested->hasAttrOfType<FlatSymbolRefAttr>(edge))
          continue;
        auto *definition = resolve(nested, edge);
        if (!definition || failed(read(definition)))
          return WalkResult::interrupt();
      }
      return WalkResult::advance();
    });
    return failure(walked.wasInterrupted());
  };
  for (StringRef edge : {"domain", "step", "body", "predicate"}) {
    if (!op->hasAttrOfType<FlatSymbolRefAttr>(edge))
      continue;
    auto *definition = resolve(op, edge);
    if (!definition || failed(read(definition)))
      return failure();
  }
  return StringAttr::get(op->getContext(), text);
}
} // namespace zkc::finite
