#include "zkc/Analysis/MathematicalFacts.h"
#include "FiniteCardinality.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Interfaces/Collection.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLFunctionalExtras.h"

using namespace mlir;
namespace zkc {
namespace {
using facts::Cardinality;
using facts::Precision;
using facts::Result;
using facts::Status;
using Count = Result<Cardinality>;
using KnownCount = llvm::function_ref<Count(Value, unsigned)>;
Operation *owner(Value value) {
  return value ? value.getParentRegion()->getParentOp() : nullptr;
}
Operation *formationOwner(Value value) {
  for (auto *op = owner(value); op; op = op->getParentOp())
    if (isa<func::FuncOp, local::FuncOp>(op))
      return op;
  return nullptr;
}
bool validAxis(Value value, unsigned axis) {
  auto collection = value ? dyn_cast<CollectionTypeInterface>(value.getType())
                          : CollectionTypeInterface();
  return collection && axis < collection.getRank() &&
         bool(finite::elementType(value.getType(), collection.getRank() == 2));
}
Count exact(uint64_t n) { return {Status::Proven, Cardinality{n}}; }
template <typename T> Result<T> missing(facts::Work &work) {
  return {work.exhausted() ? Status::Capacity : Status::Unknown, std::nullopt};
}
bool enterExtraction(facts::Work &work, unsigned depth) {
  if (depth > 256)
    work.exhaust();
  return work.charge();
}
// Each frame preserves the complete actual order. Aliased actuals must not be
// reverse-mapped to one arbitrarily chosen formal position.
struct Environment {
  Block *body;
  ValueRange actuals;
  const Environment *parent = nullptr;
};
struct AxisValue {
  Value value;
  unsigned axis = 0;
};
} // namespace

struct MathematicalFactAnalysis::Impl {
  Operation *root;
  struct Helper {
    Block *body = nullptr;
    SmallVector<Value> returned;
  };
  llvm::DenseMap<Operation *, Helper> helpers;
  explicit Impl(Operation *root) : root(root) {}
  bool contains(Operation *op) const {
    return root && op && (root == op || root->isAncestor(op));
  }
  bool contains(Value value) const { return contains(owner(value)); }
  Operation *resolve(Operation *op, StringRef key) {
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>(key);
    auto *callee =
        ref ? SymbolTable::lookupNearestSymbolFrom(op, ref) : nullptr;
    return contains(callee) ? callee : nullptr;
  }
  const Helper *helper(Operation *op, facts::Work &work) {
    if (!work.charge() || !contains(op))
      return nullptr;
    if (auto found = helpers.find(op); found != helpers.end()) {
      if (!work.charge(found->second.returned.size()))
        return nullptr;
      return found->second.body ? &found->second : nullptr;
    }
    Helper result;
    if (isa<func::FuncOp, local::FuncOp>(op) &&
        op->getRegion(0).hasOneBlock()) {
      auto &body = op->getRegion(0).front();
      if (!body.empty() && isa<func::ReturnOp, local::ReturnOp>(body.back())) {
        // Read the body, not a serialized summary claim. Return expressions
        // are interpreted below, with a fresh explicit call environment.
        if (!work.charge(body.back().getNumOperands()))
          return nullptr;
        result.body = &body;
        result.returned.append(body.back().operand_begin(),
                               body.back().operand_end());
      }
    }
    auto &stored = helpers.try_emplace(op, std::move(result)).first->second;
    return stored.body ? &stored : nullptr;
  }
  // Deduplicate recursive observations within one query, including shared
  // helper DAGs. Keeping these caches query-local makes the logical charge
  // independent of previous queries on the reusable immutable helper view.
  struct Extraction {
    Impl &analysis;
    llvm::DenseMap<std::pair<Operation *, unsigned>, std::optional<unsigned>>
        inputs;
    llvm::DenseMap<Value, Value> origins;
    explicit Extraction(Impl &analysis) : analysis(analysis) {}
    bool contains(Operation *op) const { return analysis.contains(op); }
    bool contains(Value value) const { return analysis.contains(value); }
    Operation *resolve(Operation *op, StringRef key) {
      return analysis.resolve(op, key);
    }
    const Helper *helper(Operation *op, facts::Work &work) {
      return analysis.helper(op, work);
    }
    bool enter(facts::Work &work, unsigned depth) {
      return enterExtraction(work, depth);
    }
    std::optional<unsigned> forwardedInput(Operation *op, unsigned result,
                                           facts::Work &work, unsigned depth) {
      if (!enter(work, depth))
        return std::nullopt;
      auto key = std::make_pair(op, result);
      if (auto found = inputs.find(key); found != inputs.end())
        return found->second;
      auto *view = helper(op, work);
      if (!view || result >= view->returned.size())
        return std::nullopt;
      // Copy borrowed values before nested cache insertions can rehash helpers.
      auto *body = view->body;
      Value value = view->returned[result];
      for (unsigned step = depth; enter(work, step); ++step) {
        if (auto arg = dyn_cast<BlockArgument>(value)) {
          auto input = arg.getOwner() == body
                           ? std::optional<unsigned>(arg.getArgNumber())
                           : std::nullopt;
          inputs.try_emplace(key, input);
          return input;
        }
        auto *call = value.getDefiningOp();
        if (!isa_and_nonnull<func::CallOp, local::ApplyOp>(call)) {
          inputs.try_emplace(key, std::nullopt);
          return std::nullopt;
        }
        auto input = forwardedInput(resolve(call, "callee"),
                                    cast<OpResult>(value).getResultNumber(),
                                    work, step + 1);
        if (!input || *input >= call->getNumOperands())
          return std::nullopt;
        value = call->getOperand(*input);
      }
      return std::nullopt;
    }
    Result<Value> origin(Value value, facts::Work &work, unsigned depth) {
      if (!enter(work, depth))
        return missing<Value>(work);
      if (!contains(value))
        return missing<Value>(work);
      if (auto found = origins.find(value); found != origins.end())
        return {Status::Proven, found->second};
      auto original = value;
      auto finish = [&]() -> Result<Value> {
        origins.try_emplace(original, value);
        return {Status::Proven, value};
      };
      for (; enter(work, depth); ++depth) {
        auto *call = value.getDefiningOp();
        if (!isa_and_nonnull<func::CallOp, local::ApplyOp>(call))
          return finish();
        auto input = forwardedInput(resolve(call, "callee"),
                                    cast<OpResult>(value).getResultNumber(),
                                    work, depth + 1);
        if (work.exhausted())
          return missing<Value>(work);
        if (!input || *input >= call->getNumOperands())
          return finish();
        value = call->getOperand(*input);
      }
      return missing<Value>(work);
    }
    Result<uint64_t> integer(Value value, const Environment *env,
                             facts::Work &work, unsigned depth) {
      if (!enter(work, depth))
        return missing<uint64_t>(work);
      if (auto arg = dyn_cast<BlockArgument>(value);
          arg && env && arg.getOwner() == env->body) {
        if (arg.getArgNumber() >= env->actuals.size())
          return {};
        return integer(env->actuals[arg.getArgNumber()], env->parent, work,
                       depth + 1);
      }
      if (!env) {
        auto forwarded = origin(value, work, depth);
        if (!forwarded.value)
          return missing<uint64_t>(work);
        value = *forwarded.value;
      }
      if (auto index = value.getDefiningOp<data::IndexOp>()) {
        uint64_t n;
        if (!index.getValue().getAsInteger(10, n))
          return {Status::Proven, n};
      }
      auto *call = value.getDefiningOp();
      if (isa_and_nonnull<func::CallOp, local::ApplyOp>(call)) {
        auto *view = helper(resolve(call, "callee"), work);
        unsigned result = cast<OpResult>(value).getResultNumber();
        if (view && result < view->returned.size()) {
          Environment nested{view->body, call->getOperands(), env};
          return integer(view->returned[result], &nested, work, depth + 1);
        }
      }
      return missing<uint64_t>(work);
    }
    Count domain(Value descriptor, const Environment &env, facts::Work &work,
                 unsigned depth, KnownCount known) {
      if (!enter(work, depth))
        return missing<Cardinality>(work);
      auto node = finite::detail::cardinalityNode;
      auto child = finite::detail::cardinalityChild;
      auto extent = [&](facts::DomainExtent leaf, unsigned nestedDepth) {
        return cardinality(finite::detail::domainValue(leaf.value), leaf.axis,
                           &env, work, depth + nestedDepth, known);
      };
      auto number = [&](facts::DomainLeaf leaf, unsigned nestedDepth) {
        return integer(finite::detail::domainValue(leaf), &env, work,
                       depth + nestedDepth);
      };
      // Counting does not request equality evidence. Formation separately
      // checks every zip and selector on its own substituted actuals.
      auto same = [](facts::DomainLeaf, facts::DomainLeaf, unsigned) {
        return Status::Unknown;
      };
      auto equal = [](facts::DomainExtent, facts::DomainExtent, unsigned) {
        return Status::Unknown;
      };
      facts::DomainCardinality view(
          work, {node, child, extent, number, same, equal}, 256 - depth);
      return view.count(finite::detail::domainRef(descriptor));
    }
    Count cardinality(Value value, unsigned axis, const Environment *env,
                      facts::Work &work, unsigned depth, KnownCount known) {
      if (!enter(work, depth))
        return missing<Cardinality>(work);
      if (!validAxis(value, axis))
        return {};
      if (auto size = cast<CollectionTypeInterface>(value.getType())
                          .getStaticExtent(axis))
        return exact(*size);
      if (auto arg = dyn_cast<BlockArgument>(value);
          arg && env && arg.getOwner() == env->body) {
        if (arg.getArgNumber() >= env->actuals.size())
          return {};
        return cardinality(env->actuals[arg.getArgNumber()], axis, env->parent,
                           work, depth + 1, known);
      }
      if (!env) {
        auto forwarded = origin(value, work, depth);
        if (!forwarded.value)
          return missing<Cardinality>(work);
        value = *forwarded.value;
      }
      if (value.getDefiningOp<data::SequenceEmptyOp>())
        return exact(0);
      if (value.getDefiningOp<data::SequenceAppendOp>()) {
        uint64_t appended = 0;
        while (auto append = value.getDefiningOp<data::SequenceAppendOp>()) {
          if (!work.charge())
            return missing<Cardinality>(work);
          ++appended;
          value = append->getOperand(0);
        }
        return facts::sum(work,
                          cardinality(value, axis, env, work, depth + 1, known),
                          exact(appended));
      }
      auto *op = value.getDefiningOp();
      if (isa_and_nonnull<func::CallOp, local::ApplyOp>(op)) {
        auto *view = helper(resolve(op, "callee"), work);
        unsigned result = cast<OpResult>(value).getResultNumber();
        if (view && result < view->returned.size()) {
          Environment nested{view->body, op->getOperands(), env};
          return cardinality(view->returned[result], axis, &nested, work,
                             depth + 1, known);
        }
      }
      if (isa_and_nonnull<algebra::FiniteCollectOp>(op)) {
        auto domainOp = dyn_cast_or_null<data::DomainOp>(resolve(op, "domain"));
        if (domainOp && domainOp.getBody().hasOneBlock()) {
          auto &body = domainOp.getBody().front();
          if (!body.empty() && isa<data::DomainYieldOp>(body.back()) &&
              body.getNumArguments() <= op->getNumOperands()) {
            Environment nested{
                &body, op->getOperands().take_front(body.getNumArguments()),
                env};
            return facts::collect(work,
                                  domain(body.back().getOperand(0), nested,
                                         work, depth + 1, known),
                                  op->hasAttr("predicate"));
          }
        }
      }
      if (!env && !work.exhausted())
        return known(value, axis);
      return missing<Cardinality>(work);
    }
    // An exact unfiltered collect can preserve a symbolic input extent even
    // when no numeric extent is known. It never preserves the input's identity.
    AxisValue source(Value value, unsigned axis, const Environment *env,
                     facts::Work &work, unsigned depth) {
      if (!enter(work, depth))
        return {};
      if (auto arg = dyn_cast<BlockArgument>(value);
          arg && env && arg.getOwner() == env->body) {
        if (arg.getArgNumber() >= env->actuals.size())
          return {};
        return source(env->actuals[arg.getArgNumber()], axis, env->parent, work,
                      depth + 1);
      }
      if (!env) {
        auto forwarded = origin(value, work, depth);
        if (!forwarded.value)
          return {};
        value = *forwarded.value;
      }
      auto *op = value.getDefiningOp();
      if (isa_and_nonnull<func::CallOp, local::ApplyOp>(op)) {
        auto *view = helper(resolve(op, "callee"), work);
        unsigned result = cast<OpResult>(value).getResultNumber();
        if (view && result < view->returned.size()) {
          Environment nested{view->body, op->getOperands(), env};
          auto resultSource =
              source(view->returned[result], axis, &nested, work, depth + 1);
          if (resultSource.value)
            return resultSource;
        }
      }
      if (isa_and_nonnull<algebra::FiniteCollectOp>(op) &&
          !op->hasAttr("predicate")) {
        auto domainOp = dyn_cast_or_null<data::DomainOp>(resolve(op, "domain"));
        if (domainOp && domainOp.getBody().hasOneBlock()) {
          auto &body = domainOp.getBody().front();
          if (!body.empty() && isa<data::DomainYieldOp>(body.back())) {
            auto *descriptor = body.back().getOperand(0).getDefiningOp();
            while (isa_and_nonnull<data::DomainZipOp>(descriptor)) {
              if (!work.charge())
                return {};
              descriptor = descriptor->getOperand(0).getDefiningOp();
            }
            if (isa_and_nonnull<data::DomainElementsOp, data::DomainIndicesOp,
                                data::DomainMatrixRowOp,
                                data::DomainMatrixColumnOp>(descriptor)) {
              unsigned selected =
                  isa<data::DomainMatrixRowOp>(descriptor) ? 1 : 0;
              if (auto indices = dyn_cast<data::DomainIndicesOp>(descriptor))
                selected = indices.getAxis();
              Environment nested{&body, op->getOperands(), env};
              return source(descriptor->getOperand(0), selected, &nested, work,
                            depth + 1);
            }
          }
        }
      }
      // Never expose a helper-local constructor as an invocation's SSA origin.
      return env ? AxisValue{} : AxisValue{value, axis};
    }
  };

  struct Query {
    Extraction analysis;
    facts::Work &work;
    unsigned depth;
    facts::Snapshot kernel;
    facts::Scope scope;
    llvm::DenseMap<Value, facts::Value> identities;
    llvm::DenseSet<std::pair<Value, unsigned>> typed;
    llvm::DenseSet<std::pair<Value, unsigned>> seeded;
    Query(Impl &analysis, facts::Work &work, unsigned depth)
        : analysis(analysis), work(work), depth(depth), kernel(work),
          scope(kernel.root()) {}
    facts::Value identity(Value value) {
      auto origin = analysis.origin(value, work, depth);
      if (!origin.value)
        return {};
      value = *origin.value;
      if (auto found = identities.find(value); found != identities.end())
        return found->second;
      auto result = kernel.intern(
          reinterpret_cast<uintptr_t>(value.getAsOpaquePointer()));
      if (!result.value)
        return {};
      identities.try_emplace(value, *result.value);
      return *result.value;
    }
    facts::Extent seed(Value value, unsigned axis) {
      facts::Extent result{identity(value), axis};
      if (typed.insert({value, axis}).second && validAxis(value, axis))
        if (auto size = cast<CollectionTypeInterface>(value.getType())
                            .getStaticExtent(axis))
          kernel.addExtent(scope, result, *size, facts::Premise::Formation);
      return result;
    }
    facts::Extent extent(Value value, unsigned axis) {
      auto result = seed(value, axis);
      if (!seeded.insert({value, axis}).second || !validAxis(value, axis))
        return result;
      // Formal formation facts were already seeded. Asking the full graph
      // for each formal while importing premises repeats closure derivation.
      if (isa<BlockArgument>(value))
        return result;
      auto count = analysis.cardinality(
          value, axis, nullptr, work, depth,
          [&](Value input, unsigned selected) {
            return kernel.cardinality(scope, {identity(input), selected});
          });
      if (count.value)
        kernel.addCardinality(scope, result, *count.value,
                              facts::Premise::Result);
      auto source = analysis.source(value, axis, nullptr, work, depth);
      if (source.value && (source.value != value || source.axis != axis)) {
        auto input = extent(source.value, source.axis);
        kernel.addEquality(scope, result, input, facts::Premise::Result);
      }
      return result;
    }
    void formation(Operation *owner) {
      if (!owner || !analysis.contains(owner) ||
          !isa<func::FuncOp, local::FuncOp>(owner) ||
          !owner->getRegion(0).hasOneBlock())
        return;
      auto attrs = owner->getAttrOfType<ArrayAttr>("data.preconditions");
      if (!attrs)
        return;
      auto &body = owner->getRegion(0).front();
      auto arg = [&](unsigned i) -> Value {
        return i < body.getNumArguments() ? body.getArgument(i) : Value();
      };
      for (auto attr : attrs) {
        if (!work.charge())
          return;
        if (auto equal = dyn_cast<data::EqualExtentAttr>(attr)) {
          auto a = arg(equal.getLeftArg()), b = arg(equal.getRightArg());
          if (validAxis(a, equal.getLeftAxis()) &&
              validAxis(b, equal.getRightAxis()))
            kernel.addEquality(scope, seed(a, equal.getLeftAxis()),
                               seed(b, equal.getRightAxis()),
                               facts::Premise::Formation);
        } else if (auto bound = dyn_cast<data::IndexBoundAttr>(attr)) {
          auto i = arg(bound.getIndexArg()), a = arg(bound.getContainerArg());
          if (i && i.getType().isUnsignedInteger(64) &&
              validAxis(a, bound.getAxis()))
            kernel.addBound(scope, identity(i), seed(a, bound.getAxis()),
                            facts::Premise::Formation);
        }
      }
    }
  };
};

MathematicalFactAnalysis::MathematicalFactAnalysis(Operation *root)
    : impl_(std::make_unique<Impl>(root)) {}
MathematicalFactAnalysis::~MathematicalFactAnalysis() = default;
void MathematicalFactAnalysis::clear() { impl_->helpers.clear(); }
Operation *MathematicalFactAnalysis::getRoot() const { return impl_->root; }
Operation *MathematicalFactAnalysis::rootFor(Operation *op) {
  Operation *root = nullptr;
  for (; op; op = op->getParentOp())
    if (op->hasTrait<OpTrait::SymbolTable>())
      root = op;
  return root;
}
Result<Value> MathematicalFactAnalysis::origin(Value value, facts::Work &work,
                                               unsigned depth) {
  return Impl::Extraction(*impl_).origin(value, work, depth);
}
Result<uint64_t> MathematicalFactAnalysis::integer(Value value,
                                                   facts::Work &work,
                                                   unsigned depth) {
  if (!enterExtraction(work, depth))
    return missing<uint64_t>(work);
  if (!impl_->contains(value) || !value.getType().isUnsignedInteger(64))
    return {};
  Impl::Extraction extraction(*impl_);
  return extraction.integer(value, nullptr, work, depth);
}
Status MathematicalFactAnalysis::equalExtent(Value a, unsigned aa, Value b,
                                             unsigned ba, facts::Work &work,
                                             unsigned depth) {
  if (!enterExtraction(work, depth))
    return Status::Capacity;
  if (!impl_->contains(a) || !impl_->contains(b) || !validAxis(a, aa) ||
      !validAxis(b, ba))
    return Status::Unknown;
  if (a == b && aa == ba)
    return Status::Proven;
  Impl::Query query(*impl_, work, depth);
  auto *formation = formationOwner(a);
  if (formation == formationOwner(b))
    query.formation(formation);
  auto left = query.seed(a, aa), right = query.seed(b, ba);
  auto established = query.kernel.equal(query.scope, left, right);
  if (established != Status::Unknown)
    return established;
  query.extent(a, aa);
  query.extent(b, ba);
  return query.kernel.equal(query.scope, left, right);
}
Status MathematicalFactAnalysis::bound(Value i, Value a, unsigned axis,
                                       facts::Work &work, unsigned depth) {
  if (!enterExtraction(work, depth))
    return Status::Capacity;
  if (!impl_->contains(i) || !impl_->contains(a) ||
      !i.getType().isUnsignedInteger(64) || !validAxis(a, axis))
    return Status::Unknown;
  Impl::Query query(*impl_, work, depth);
  auto *formation = formationOwner(i);
  if (formation == formationOwner(a))
    query.formation(formation);
  auto index = query.identity(i);
  auto target = query.seed(a, axis);
  auto established = query.kernel.bound(query.scope, index, target);
  if (established != Status::Unknown)
    return established;
  query.extent(a, axis);
  auto n = query.analysis.integer(i, nullptr, work, depth);
  if (n.value)
    query.kernel.addInteger(query.scope, index, *n.value,
                            facts::Premise::Result);
  return query.kernel.bound(query.scope, index, target);
}
Result<Cardinality> MathematicalFactAnalysis::cardinality(Value value,
                                                          unsigned axis,
                                                          facts::Work &work,
                                                          unsigned depth) {
  if (!enterExtraction(work, depth))
    return missing<Cardinality>(work);
  if (!impl_->contains(value) || !validAxis(value, axis))
    return {};
  Impl::Query query(*impl_, work, depth);
  query.formation(formationOwner(value));
  auto subject = query.extent(value, axis);
  return query.kernel.cardinality(query.scope, subject);
}
Result<uint64_t> MathematicalFactAnalysis::extent(Value value, unsigned axis,
                                                  facts::Work &work,
                                                  unsigned depth) {
  auto result = cardinality(value, axis, work, depth);
  if (result.value && result.value->precision == Precision::Exact)
    return {Status::Proven, result.value->value};
  return missing<uint64_t>(work);
}
} // namespace zkc
