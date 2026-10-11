#include "zkc/Contracts/MathematicalFacts.h"
#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace zkc::facts {
namespace detail {
struct Identity {};
} // namespace detail
namespace {
template <typename T> Result<T> proven(T value) {
  return {Status::Proven, std::move(value)};
}
template <typename T> Result<T> absent(Status status = Status::Unknown) {
  return {status, std::nullopt};
}
Cardinality normalized(Cardinality value) {
  if (!value.value)
    value.precision = Precision::Exact;
  return value;
}
bool available(const Result<Cardinality> &result) {
  return result.status == Status::Proven && result.value.has_value();
}
// Keys are local to a snapshot. Public operations validate owner tokens before
// using these indices; a numeric key never establishes cross-snapshot identity.
using ExtentKey = std::pair<uint64_t, unsigned>;
using CountKey = std::pair<Precision, uint64_t>;
enum class Kind { Equality, Integer, Cardinality, Bound };
struct Fact {
  Kind kind;
  Premise premise;
  ExtentKey left, right;
  uint64_t number = 0;
  Precision precision = Precision::Exact;

  bool operator<(const Fact &other) const {
    return std::tie(kind, premise, left, right, number, precision) <
           std::tie(other.kind, other.premise, other.left, other.right,
                    other.number, other.precision);
  }

  uint64_t copyWork() const {
    // One explicit premise plus its entries in the query indices.
    return kind == Kind::Equality ||
                   (kind == Kind::Cardinality && precision == Precision::Exact)
               ? 3
               : 2;
  }
};
} // namespace

Work::Work(uint64_t &remaining)
    : Work([&remaining](uint64_t amount) {
        if (amount > remaining) {
          remaining = 0;
          return false;
        }
        remaining -= amount;
        return true;
      }) {}
Work::Work(std::function<bool(uint64_t)> charger)
    : charger_(std::move(charger)) {}
bool Work::charge(uint64_t amount) {
  if (exhausted_)
    return false;
  if (!charger_ || !charger_(amount)) {
    exhausted_ = true;
    return false;
  }
  return true;
}
bool Value::operator==(const Value &other) const {
  return owner_ == other.owner_ && index_ == other.index_;
}

struct Snapshot::Impl {
  struct Origin {
    uint64_t root;
    std::vector<unsigned> path;
    bool operator==(const Origin &other) const {
      return root == other.root && path == other.path;
    }
  };
  struct OriginHash {
    size_t operator()(const Origin &origin) const {
      size_t hash = std::hash<uint64_t>{}(origin.root);
      for (unsigned component : origin.path)
        hash ^= std::hash<unsigned>{}(component) + 0x9e3779b9 + (hash << 6) +
                (hash >> 2);
      return hash;
    }
  };
  struct Facts {
    std::set<Fact> premises;
    std::map<ExtentKey, std::set<ExtentKey>> equalities;
    std::map<uint64_t, std::set<uint64_t>> integers;
    std::map<ExtentKey, std::set<CountKey>> cardinalities;
    std::map<uint64_t, std::set<ExtentKey>> exactExtents;
    std::map<uint64_t, std::set<ExtentKey>> bounds;
    uint64_t copyWork = 0;

    Status add(Fact fact, Work &work) {
      if (fact.kind == Kind::Equality && fact.right < fact.left)
        std::swap(fact.left, fact.right);
      if (!work.charge())
        return Status::Capacity;
      if (premises.find(fact) != premises.end())
        return Status::Proven;
      // Debit every insertion before publishing any part of the premise.
      if (!work.charge(fact.copyWork()))
        return Status::Capacity;
      premises.insert(fact);
      copyWork += fact.copyWork();
      switch (fact.kind) {
      case Kind::Equality:
        equalities[fact.left].insert(fact.right);
        equalities[fact.right].insert(fact.left);
        break;
      case Kind::Integer:
        integers[fact.left.first].insert(fact.number);
        break;
      case Kind::Cardinality:
        cardinalities[fact.left].insert({fact.precision, fact.number});
        if (fact.precision == Precision::Exact)
          exactExtents[fact.number].insert(fact.left);
        break;
      case Kind::Bound:
        bounds[fact.left.first].insert(fact.right);
        break;
      }
      return Status::Proven;
    }
  };
  std::unordered_map<Origin, uint64_t, OriginHash> origins;
  std::vector<Facts> scopes{1};

  static ExtentKey key(Extent extent) {
    return {extent.container.index_, extent.axis};
  }

  // Ordered indices make traversal and charged work independent of hash layout
  // and premise insertion order. Each extent and numeric bucket is expanded
  // once. The visitor returns Proven only when it has sufficient evidence.
  template <typename Visitor>
  Status walk(const Facts &facts, ExtentKey start, Work &work,
              const Visitor &visit) const {
    std::vector<ExtentKey> pending;
    std::set<ExtentKey> seen;
    std::set<uint64_t> numbers;
    auto append = [&](ExtentKey next) {
      if (!work.charge())
        return Status::Capacity;
      if (!seen.insert(next).second)
        return Status::Unknown;
      pending.push_back(next);
      return visit(next);
    };
    Status status = append(start);
    if (status != Status::Unknown)
      return status;
    for (size_t position = 0; position < pending.size(); ++position) {
      ExtentKey current = pending[position];
      if (!work.charge())
        return Status::Capacity;
      auto edges = facts.equalities.find(current);
      if (edges != facts.equalities.end())
        for (ExtentKey next : edges->second) {
          status = append(next);
          if (status != Status::Unknown)
            return status;
        }
      if (!work.charge())
        return Status::Capacity;
      auto counts = facts.cardinalities.find(current);
      if (counts == facts.cardinalities.end())
        continue;
      for (CountKey count : counts->second) {
        if (!work.charge())
          return Status::Capacity;
        if (count.first != Precision::Exact ||
            !numbers.insert(count.second).second)
          continue;
        if (!work.charge())
          return Status::Capacity;
        for (ExtentKey next : facts.exactExtents.at(count.second)) {
          status = append(next);
          if (status != Status::Unknown)
            return status;
        }
      }
    }
    return Status::Unknown;
  }
};

Snapshot::Snapshot(Work &work)
    : impl_(std::make_unique<Impl>()),
      owner_(std::make_shared<detail::Identity>()), work_(work) {}
Snapshot::~Snapshot() = default;
bool Snapshot::owns(Value value) const {
  return value.owner_ == owner_ && value.index_ < impl_->origins.size();
}
bool Snapshot::owns(Scope scope) const {
  return scope.owner_ == owner_ && scope.index_ < impl_->scopes.size();
}
Scope Snapshot::root() const {
  Scope scope;
  scope.owner_ = owner_;
  return scope;
}
Result<Value> Snapshot::intern(uint64_t root, llvm::ArrayRef<unsigned> path) {
  if (!work_.charge(1 + path.size()))
    return absent<Value>(Status::Capacity);
  auto entry = impl_->origins.emplace(Impl::Origin{root, path.vec()},
                                      impl_->origins.size());
  Value value;
  value.owner_ = owner_;
  value.index_ = entry.first->second;
  return proven(value);
}

Result<Scope> Snapshot::fork(Scope parent) {
  if (!work_.charge())
    return absent<Scope>(Status::Capacity);
  if (!owns(parent))
    return absent<Scope>();
  if (!work_.charge(impl_->scopes[parent.index_].copyWork))
    return absent<Scope>(Status::Capacity);
  auto facts = impl_->scopes[parent.index_];
  Scope scope;
  scope.owner_ = owner_;
  scope.index_ = impl_->scopes.size();
  impl_->scopes.push_back(std::move(facts));
  return proven(scope);
}
Result<Scope> Snapshot::intersect(llvm::ArrayRef<Scope> incoming) {
  if (!work_.charge(1 + incoming.size()))
    return absent<Scope>(Status::Capacity);
  if (incoming.empty())
    return absent<Scope>();
  for (Scope scope : incoming)
    if (!owns(scope))
      return absent<Scope>();
  Impl::Facts common;
  for (const Fact &fact : impl_->scopes[incoming.front().index_].premises) {
    if (!work_.charge())
      return absent<Scope>(Status::Capacity);
    bool shared = true;
    for (Scope scope : incoming.drop_front()) {
      if (!work_.charge())
        return absent<Scope>(Status::Capacity);
      const auto &premises = impl_->scopes[scope.index_].premises;
      if (premises.find(fact) == premises.end()) {
        shared = false;
        break;
      }
    }
    if (shared && common.add(fact, work_) == Status::Capacity)
      return absent<Scope>(Status::Capacity);
  }
  Scope scope;
  scope.owner_ = owner_;
  scope.index_ = impl_->scopes.size();
  impl_->scopes.push_back(std::move(common));
  return proven(scope);
}

Status Snapshot::addEquality(Scope scope, Extent left, Extent right,
                             Premise premise) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(left.container) || !owns(right.container))
    return Status::Unknown;
  return impl_->scopes[scope.index_].add(
      {Kind::Equality, premise, Impl::key(left), Impl::key(right)}, work_);
}
Status Snapshot::addInteger(Scope scope, Value value, uint64_t number,
                            Premise premise) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(value))
    return Status::Unknown;
  return impl_->scopes[scope.index_].add(
      {Kind::Integer, premise, {value.index_, 0}, {}, number}, work_);
}
Status Snapshot::addExtent(Scope scope, Extent extent, uint64_t number,
                           Premise premise) {
  return addCardinality(scope, extent, {number, Precision::Exact}, premise);
}
Status Snapshot::addBound(Scope scope, Value index, Extent extent,
                          Premise premise) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(index) || !owns(extent.container))
    return Status::Unknown;
  return impl_->scopes[scope.index_].add(
      {Kind::Bound, premise, {index.index_, 0}, Impl::key(extent)}, work_);
}
Status Snapshot::addCardinality(Scope scope, Extent extent, Cardinality count,
                                Premise premise) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(extent.container))
    return Status::Unknown;
  count = normalized(count);
  return impl_->scopes[scope.index_].add({Kind::Cardinality,
                                          premise,
                                          Impl::key(extent),
                                          {},
                                          count.value,
                                          count.precision},
                                         work_);
}

Status Snapshot::equal(Scope scope, Extent left, Extent right) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(left.container) || !owns(right.container))
    return Status::Unknown;
  if (left == right)
    return Status::Proven;
  const auto &facts = impl_->scopes[scope.index_];
  ExtentKey target = Impl::key(right);
  if (!work_.charge())
    return Status::Capacity;
  auto edges = facts.equalities.find(Impl::key(left));
  if (edges != facts.equalities.end() &&
      edges->second.find(target) != edges->second.end())
    return Status::Proven;
  return impl_->walk(facts, Impl::key(left), work_, [&](ExtentKey member) {
    return member == target ? Status::Proven : Status::Unknown;
  });
}
Result<uint64_t> Snapshot::integer(Scope scope, Value value) {
  if (!work_.charge())
    return absent<uint64_t>(Status::Capacity);
  if (!owns(scope) || !owns(value))
    return absent<uint64_t>();
  if (!work_.charge())
    return absent<uint64_t>(Status::Capacity);
  const auto &integers = impl_->scopes[scope.index_].integers;
  auto found = integers.find(value.index_);
  if (found == integers.end() || found->second.size() != 1)
    return absent<uint64_t>();
  return proven(*found->second.begin());
}
Result<Cardinality> Snapshot::cardinality(Scope scope, Extent extent) {
  if (!work_.charge())
    return absent<Cardinality>(Status::Capacity);
  if (!owns(scope) || !owns(extent.container))
    return absent<Cardinality>();
  const auto &facts = impl_->scopes[scope.index_];
  std::optional<uint64_t> exact, upper;
  bool conflict = false;
  Status status =
      impl_->walk(facts, Impl::key(extent), work_, [&](ExtentKey member) {
        if (!work_.charge())
          return Status::Capacity;
        auto counts = facts.cardinalities.find(member);
        if (counts == facts.cardinalities.end())
          return Status::Unknown;
        for (CountKey count : counts->second) {
          if (!work_.charge())
            return Status::Capacity;
          if (count.first == Precision::Exact) {
            if (exact && *exact != count.second) {
              conflict = true;
              return Status::Proven;
            }
            exact = count.second;
          } else {
            upper = upper ? std::min(*upper, count.second) : count.second;
          }
        }
        return Status::Unknown;
      });
  if (status == Status::Capacity)
    return absent<Cardinality>(status);
  if (conflict || (exact && upper && *exact > *upper))
    return absent<Cardinality>();
  if (exact)
    return proven(Cardinality{*exact, Precision::Exact});
  if (upper)
    return proven(Cardinality{*upper, Precision::Upper});
  return absent<Cardinality>();
}
Status Snapshot::bound(Scope scope, Value index, Extent extent) {
  if (!work_.charge())
    return Status::Capacity;
  if (!owns(scope) || !owns(index) || !owns(extent.container))
    return Status::Unknown;
  if (!work_.charge())
    return Status::Capacity;
  const auto &facts = impl_->scopes[scope.index_];
  auto bounds = facts.bounds.find(index.index_);
  if (bounds != facts.bounds.end()) {
    ExtentKey target = Impl::key(extent);
    if (bounds->second.find(target) != bounds->second.end())
      return Status::Proven;
    // One traversal tests every bound for this index, instead of repeating a
    // closure for each premise or inspecting bounds on unrelated values.
    Status status = impl_->walk(facts, target, work_, [&](ExtentKey member) {
      if (!work_.charge())
        return Status::Capacity;
      return bounds->second.find(member) != bounds->second.end()
                 ? Status::Proven
                 : Status::Unknown;
    });
    if (status != Status::Unknown)
      return status;
  }
  auto number = integer(scope, index);
  if (number.status != Status::Proven)
    return number.status;
  auto count = cardinality(scope, extent);
  if (count.status != Status::Proven)
    return count.status;
  return count.value->precision == Precision::Exact &&
                 *number.value < count.value->value
             ? Status::Proven
             : Status::Unknown;
}

Result<Cardinality> product(Work &work,
                            llvm::ArrayRef<Result<Cardinality>> factors) {
  if (!work.charge(1 + factors.size()))
    return absent<Cardinality>(Status::Capacity);
  // Inspect every status before zero annihilation; exhaustion is never proof.
  bool zero = false, missing = false;
  for (const auto &factor : factors) {
    if (factor.status == Status::Capacity)
      return absent<Cardinality>(Status::Capacity);
    if (!available(factor))
      missing = true;
    else
      zero |= !factor.value->value;
  }
  if (zero)
    return proven(Cardinality{});
  if (missing)
    return absent<Cardinality>();
  Cardinality result{1, Precision::Exact};
  for (const auto &factor : factors) {
    if (!work.charge())
      return absent<Cardinality>(Status::Capacity);
    if (result.value >
        std::numeric_limits<uint64_t>::max() / factor.value->value)
      return absent<Cardinality>();
    result.value *= factor.value->value;
    if (factor.value->precision == Precision::Upper)
      result.precision = Precision::Upper;
  }
  return proven(result);
}
Result<Cardinality> sum(Work &work, Result<Cardinality> left,
                        Result<Cardinality> right) {
  if (!work.charge() || left.status == Status::Capacity ||
      right.status == Status::Capacity)
    return absent<Cardinality>(Status::Capacity);
  if (!available(left) || !available(right))
    return absent<Cardinality>();
  auto a = normalized(*left.value), b = normalized(*right.value);
  if (a.value > std::numeric_limits<uint64_t>::max() - b.value)
    return absent<Cardinality>();
  return proven(
      Cardinality{a.value + b.value, a.precision == Precision::Exact &&
                                             b.precision == Precision::Exact
                                         ? Precision::Exact
                                         : Precision::Upper});
}
Result<Cardinality> range(Work &work, uint64_t lower, uint64_t upper) {
  if (!work.charge())
    return absent<Cardinality>(Status::Capacity);
  return proven(
      Cardinality{upper > lower ? upper - lower : 0, Precision::Exact});
}
Result<Cardinality> collect(Work &work, Result<Cardinality> input,
                            bool filtered) {
  if (!work.charge() || input.status == Status::Capacity)
    return absent<Cardinality>(Status::Capacity);
  if (!available(input))
    return absent<Cardinality>();
  auto result = *input.value;
  if (filtered)
    result.precision = Precision::Upper;
  return proven(normalized(result));
}

} // namespace zkc::facts
