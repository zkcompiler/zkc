#include "zkc/Analysis/Finite.h"
#include "FiniteCardinality.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Analysis/MathematicalFacts.h"
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
LogicalResult requireEvidence(Operation *op, facts::Status status,
                              StringRef reason,
                              StringRef code = "finite-bound") {
  if (status == facts::Status::Capacity)
    return refuse(op, "finite evidence work limit", "finite-analysis-limit");
  return status == facts::Status::Proven ? success() : refuse(op, reason, code);
}
FunctionType signature(Operation *op) {
  auto attr = op ? op->getAttrOfType<TypeAttr>("function_type") : TypeAttr();
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
}
Operation *resolve(Operation *op, StringRef key) {
  auto ref = op->getAttrOfType<FlatSymbolRefAttr>(key);
  return ref ? SymbolTable::lookupNearestSymbolFrom(op, ref) : nullptr;
}
// One immutable symbol-closure view and one allowance for a complete
// formation check. Nested queries never create their own work budgets.
struct EvidenceWork {
  uint64_t local = 65536;
  uint64_t &remaining;
  facts::Work context;
  MathematicalFactAnalysis analysis;
  explicit EvidenceWork(Operation *subject)
      : remaining(local), context(remaining),
        analysis(MathematicalFactAnalysis::rootFor(subject)) {}
  EvidenceWork(Operation *subject, uint64_t &remaining)
      : remaining(remaining), context(remaining),
        analysis(MathematicalFactAnalysis::rootFor(subject)) {}
  bool charge(uint64_t count = 1) { return context.charge(count); }
  facts::Status status(bool proven) const {
    return context.exhausted() ? facts::Status::Capacity
           : proven            ? facts::Status::Proven
                               : facts::Status::Unknown;
  }
};
Operation *valueOwner(Value value) {
  return value ? value.getParentRegion()->getParentOp() : nullptr;
}
facts::Status equalUnder(Value left, unsigned la, Value right, unsigned ra,
                         EvidenceWork &work) {
  return work.analysis.equalExtent(left, la, right, ra, work.context);
}
facts::Status provesBoundUnder(Value index, Value container, unsigned axis,
                               EvidenceWork &work) {
  return work.analysis.bound(index, container, axis, work.context);
}
bool index(Type type) { return type.isUnsignedInteger(64); }
bool axis(Type type, unsigned axis) {
  auto collection = dyn_cast<CollectionTypeInterface>(type);
  return collection && axis < collection.getRank() &&
         bool(elementType(type, collection.getRank() == 2));
}
ArrayAttr preconditions(Operation *owner) {
  return owner ? owner->getAttrOfType<ArrayAttr>("data.preconditions")
               : ArrayAttr();
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
template <typename Query>
auto domainEvidence(const Computation &c, EvidenceWork &work, Query query) {
  auto actual = [&](facts::DomainLeaf leaf) {
    Value value = detail::domainValue(leaf);
    return c.total ? c.operation->getOperand(
                         cast<BlockArgument>(value).getArgNumber())
                   : value;
  };
  auto node = detail::cardinalityNode;
  auto child = detail::cardinalityChild;
  auto extent = [&](facts::DomainExtent leaf, unsigned) {
    return work.analysis.cardinality(actual(leaf.value), leaf.axis,
                                     work.context);
  };
  auto integer = [&](facts::DomainLeaf leaf, unsigned) {
    return work.analysis.integer(actual(leaf), work.context);
  };
  auto same = [&](facts::DomainLeaf a, facts::DomainLeaf b) {
    auto left = work.analysis.origin(actual(a), work.context);
    auto right = work.analysis.origin(actual(b), work.context);
    return work.status(left.value && right.value &&
                       *left.value == *right.value);
  };
  auto equal = [&](facts::DomainExtent a, facts::DomainExtent b) {
    return equalUnder(actual(a.value), a.axis, actual(b.value), b.axis, work);
  };
  facts::DomainCardinality cardinality(
      work.context, {node, child, extent, integer, same, equal}, 256);
  return query(cardinality);
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
  if (work.context.exhausted())
    return requireEvidence(c.operation, facts::Status::Capacity, {});
  if (items.size() != callback->formals.items.size())
    return refuse(c.operation, "finite item bound partition", "finite-bound");
  if (!work.charge(attrs.size() + 1))
    return requireEvidence(c.operation, facts::Status::Capacity, {});
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
                             actual(a), bound.getAxis(),
                             work) == facts::Status::Proven;
      }
      if (!valid && actual(i) && actual(a))
        valid = provesBoundUnder(actual(i), actual(a), bound.getAxis(), work) ==
                facts::Status::Proven;
      if (failed(requireEvidence(
              c.operation, work.status(valid),
              "finite helper bound is not discharged by the domain")))
        return failure();
    } else if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
      Value l = actual(equal.getLeftArg()), r = actual(equal.getRightArg());
      auto status = l && r ? equalUnder(l, equal.getLeftAxis(), r,
                                        equal.getRightAxis(), work)
                           : work.status(false);
      if (failed(
              requireEvidence(c.operation, status,
                              "finite helper equal extent is not discharged")))
        return failure();
    }
  }
  return success();
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
  EvidenceWork work(valueOwner(a));
  return equalUnder(a, aa, b, ba, work) == facts::Status::Proven;
}
bool provesBound(Value idx, Value container, unsigned selectedAxis) {
  EvidenceWork work(valueOwner(idx));
  return provesBoundUnder(idx, container, selectedAxis, work) ==
         facts::Status::Proven;
}
bool provesEqualExtent(Value a, unsigned aa, Value b, unsigned ba,
                       uint64_t &remaining) {
  return equalExtentStatus(a, aa, b, ba, remaining) == facts::Status::Proven;
}
facts::Status equalExtentStatus(Value a, unsigned aa, Value b, unsigned ba,
                                uint64_t &remaining) {
  EvidenceWork work(valueOwner(a), remaining);
  return equalUnder(a, aa, b, ba, work);
}
bool provesBound(Value idx, Value container, unsigned selectedAxis,
                 uint64_t &remaining) {
  return boundStatus(idx, container, selectedAxis, remaining) ==
         facts::Status::Proven;
}
facts::Status boundStatus(Value idx, Value container, unsigned selectedAxis,
                          uint64_t &remaining) {
  EvidenceWork work(valueOwner(idx), remaining);
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
  EvidenceWork work(call);
  auto *helper = resolve(call, "callee");
  auto attrs = preconditions(helper);
  if (!attrs)
    return success();
  if (failed(verifyPreconditions(helper)))
    return failure();
  for (auto attr : attrs) {
    if (auto bound = dyn_cast<data::IndexBoundAttr>(attr)) {
      if (bound.getIndexArg() >= call->getNumOperands() ||
          bound.getContainerArg() >= call->getNumOperands())
        return refuse(call, "call does not discharge index bound",
                      "finite-bound");
      if (failed(requireEvidence(
              call,
              provesBoundUnder(call->getOperand(bound.getIndexArg()),
                               call->getOperand(bound.getContainerArg()),
                               bound.getAxis(), work),
              "call does not discharge index bound")))
        return failure();
    } else if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
      if (equal.getLeftArg() >= call->getNumOperands() ||
          equal.getRightArg() >= call->getNumOperands())
        return refuse(call, "call does not discharge equal extent",
                      "finite-bound");
      if (failed(
              requireEvidence(call,
                              equalUnder(call->getOperand(equal.getLeftArg()),
                                         equal.getLeftAxis(),
                                         call->getOperand(equal.getRightArg()),
                                         equal.getRightAxis(), work),
                              "call does not discharge equal extent")))
        return failure();
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
  EvidenceWork work(op);
  if (failed(helperAssumptions(c, callback->role, work)) ||
      (c.predicate &&
       failed(helperAssumptions(c, CallbackRole::Predicate, work))))
    return failure();
  if (c.total) {
    for (auto &constructor : c.domain.getBody().front()) {
      if (auto zip = dyn_cast<data::DomainZipOp>(constructor)) {
        for (Value child : zip.getOperands().drop_front()) {
          auto same =
              domainEvidence(c, work, [&](facts::DomainCardinality &view) {
                return view.equal(detail::domainRef(zip.getOperand(0)),
                                  detail::domainRef(child));
              });
          if (failed(requireEvidence(
                  op, same, "total zip requires equal-extent evidence")))
            return failure();
        }
      }
      if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
              constructor)) {
        auto container = c.operation->getOperand(
            cast<BlockArgument>(constructor.getOperand(0)).getArgNumber());
        auto selector = c.operation->getOperand(
            cast<BlockArgument>(constructor.getOperand(1)).getArgNumber());
        if (failed(requireEvidence(
                op,
                provesBoundUnder(
                    selector, container,
                    isa<data::DomainMatrixRowOp>(constructor) ? 0 : 1, work),
                "total matrix view requires a selector bound")))
          return failure();
      }
    }
  }
  if (c.collect)
    if (auto array =
            dyn_cast<algebra::FieldArrayType>(c.signature.getResult(0))) {
      auto card = domainEvidence(c, work, [&](facts::DomainCardinality &view) {
        return view.exact(detail::domainRef(domainResult(c.domain)));
      });
      if (failed(requireEvidence(
              op,
              work.status(!c.predicate && card.value &&
                          *card.value == array.getLength()),
              "fixed collection requires proven exact unfiltered cardinality",
              "finite-formation")))
        return failure();
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
