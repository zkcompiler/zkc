#include "zkc/Contracts/FiniteCardinality.h"

namespace zkc::facts {
namespace {
template <typename T> Result<T> capacity() {
  return {Status::Capacity, std::nullopt};
}
template <typename T> Result<T> checked(Work &work, Result<T> result) {
  if (result.status == Status::Capacity)
    work.exhaust();
  if (work.exhausted())
    return capacity<T>();
  return result.status == Status::Proven && result.value ? result : Result<T>{};
}
Status checked(Work &work, Status status) {
  if (status == Status::Capacity)
    work.exhaust();
  return work.exhausted() ? Status::Capacity : status;
}
bool exactCount(const Result<Cardinality> &count) {
  return count.status == Status::Proven && count.value &&
         (count.value->precision == Precision::Exact || !count.value->value);
}
} // namespace

bool DomainCardinality::enter(unsigned depth) {
  if (depth > maximumDepth)
    work.exhaust();
  return work.charge();
}
Result<Cardinality> DomainCardinality::extent(DomainExtent leaf,
                                              unsigned depth) {
  if (!enter(depth))
    return capacity<Cardinality>();
  return checked(work, adapter.extent(leaf, depth));
}
Result<uint64_t> DomainCardinality::integer(DomainLeaf leaf, unsigned depth) {
  if (!enter(depth))
    return capacity<uint64_t>();
  return checked(work, adapter.integer(leaf, depth));
}
Status DomainCardinality::same(DomainLeaf left, DomainLeaf right,
                               unsigned depth) {
  if (!enter(depth))
    return Status::Capacity;
  return checked(work, adapter.same(left, right, depth));
}
Status DomainCardinality::equalExtent(DomainExtent left, DomainExtent right,
                                      unsigned depth) {
  if (!enter(depth))
    return Status::Capacity;
  return checked(work, adapter.equalExtent(left, right, depth));
}
Result<Cardinality> DomainCardinality::count(DomainRef domain, unsigned depth) {
  if (!enter(depth))
    return capacity<Cardinality>();
  auto node = adapter.node(domain);
  if (work.exhausted())
    return capacity<Cardinality>();
  switch (node.kind) {
  case DomainKind::Unknown:
    return {};
  case DomainKind::Extent:
    return extent(node.extent, depth + 1);
  case DomainKind::Range: {
    auto lower = integer(node.lower, depth + 1);
    if (lower.status == Status::Capacity)
      return capacity<Cardinality>();
    auto upper = integer(node.upper, depth + 1);
    if (upper.status == Status::Capacity)
      return capacity<Cardinality>();
    if (!lower.value || !upper.value)
      return {};
    return range(work, *lower.value, *upper.value);
  }
  case DomainKind::Zip:
    if (!node.children)
      return {};
    if (!work.charge())
      return capacity<Cardinality>();
    return count(adapter.child(domain, 0), depth + 1);
  case DomainKind::Product: {
    std::vector<Result<Cardinality>> factors;
    for (size_t i = 0; i < node.children; ++i) {
      if (!work.charge())
        return capacity<Cardinality>();
      auto factor = count(adapter.child(domain, i), depth + 1);
      if (factor.status == Status::Capacity)
        return capacity<Cardinality>();
      factors.push_back(factor);
    }
    return product(work, factors);
  }
  case DomainKind::MatrixCoordinates: {
    auto rows = extent({node.extent.value, 0}, depth + 1);
    if (rows.status == Status::Capacity)
      return capacity<Cardinality>();
    auto columns = extent({node.extent.value, 1}, depth + 1);
    return checked(work, product(work, {rows, columns}));
  }
  }
  return {};
}
Result<uint64_t> DomainCardinality::exact(DomainRef domain) {
  auto result = count(domain);
  if (result.status == Status::Capacity)
    return capacity<uint64_t>();
  if (exactCount(result))
    return {Status::Proven, result.value->value};
  return {};
}
Status DomainCardinality::equal(DomainRef left, DomainRef right,
                                unsigned depth) {
  if (!enter(depth))
    return Status::Capacity;
  if (left == right)
    return Status::Proven;
  auto a = count(left, depth), b = count(right, depth);
  if (work.exhausted())
    return Status::Capacity;
  if (exactCount(a) && exactCount(b))
    return a.value->value == b.value->value ? Status::Proven : Status::Unknown;
  if (!work.charge(2))
    return Status::Capacity;
  auto x = adapter.node(left), y = adapter.node(right);
  if (work.exhausted())
    return Status::Capacity;
  if (x.kind == DomainKind::Zip && x.children) {
    if (!work.charge())
      return Status::Capacity;
    return equal(adapter.child(left, 0), right, depth + 1);
  }
  if (y.kind == DomainKind::Zip && y.children) {
    if (!work.charge())
      return Status::Capacity;
    return equal(left, adapter.child(right, 0), depth + 1);
  }
  if (x.kind == DomainKind::Extent && y.kind == DomainKind::Extent)
    return equalExtent(x.extent, y.extent, depth + 1);
  if (x.kind == DomainKind::Product && y.kind == DomainKind::Product &&
      x.children == y.children) {
    for (size_t i = 0; i < x.children; ++i) {
      if (!work.charge(2))
        return Status::Capacity;
      auto status =
          equal(adapter.child(left, i), adapter.child(right, i), depth + 1);
      if (status != Status::Proven)
        return status;
    }
    return Status::Proven;
  }
  if (x.kind == DomainKind::Range && y.kind == DomainKind::Range) {
    auto lower = same(x.lower, y.lower, depth + 1);
    return lower == Status::Proven ? same(x.upper, y.upper, depth + 1) : lower;
  }
  if (x.kind == DomainKind::MatrixCoordinates &&
      y.kind == DomainKind::MatrixCoordinates) {
    auto rows =
        equalExtent({x.extent.value, 0}, {y.extent.value, 0}, depth + 1);
    return rows == Status::Proven ? equalExtent({x.extent.value, 1},
                                                {y.extent.value, 1}, depth + 1)
                                  : rows;
  }
  return Status::Unknown;
}
} // namespace zkc::facts
