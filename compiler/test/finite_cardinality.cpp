#include "support/NativeCases.h"
#include "zkc/Contracts/FiniteCardinality.h"
#include <limits>
#include <map>
#include <set>
using namespace zkc::facts;
using namespace zkc::test;
namespace {
struct Node {
  DomainNode view;
  std::vector<DomainRef> children;
};
struct Graph {
  std::vector<Node> nodes;
  std::map<std::pair<DomainLeaf, unsigned>, Cardinality> extents;
  std::map<DomainLeaf, uint64_t> integers;
  std::set<std::pair<DomainLeaf, DomainLeaf>> aliases;
  std::optional<DomainLeaf> capacityLeaf;
  std::optional<unsigned> missingEqualityAxis;
  unsigned equalityQueries = 0;
  unsigned extentDepth = 0;
  DomainRef leaf(DomainLeaf value, unsigned axis = 0) {
    nodes.push_back({{DomainKind::Extent, {value, axis}}, {}});
    return nodes.size() - 1;
  }
  DomainRef range(DomainLeaf lower, DomainLeaf upper) {
    nodes.push_back({{DomainKind::Range, {}, lower, upper}, {}});
    return nodes.size() - 1;
  }
  DomainRef coordinates(DomainLeaf matrix) {
    nodes.push_back({{DomainKind::MatrixCoordinates, {matrix, 0}}, {}});
    return nodes.size() - 1;
  }
  DomainRef combine(DomainKind kind, std::vector<DomainRef> children) {
    nodes.push_back({{kind, {}, 0, 0, children.size()}, std::move(children)});
    return nodes.size() - 1;
  }
  void query(Work &work, llvm::function_ref<void(DomainCardinality &)> check,
             unsigned depth = 64) {
    auto node = [&](DomainRef ref) { return nodes.at(ref).view; };
    auto child = [&](DomainRef ref, size_t i) {
      return nodes.at(ref).children.at(i);
    };
    auto extent = [&](DomainExtent leaf,
                      unsigned depth) -> Result<Cardinality> {
      extentDepth = depth;
      if (capacityLeaf == leaf.value)
        return {Status::Capacity, std::nullopt};
      auto it = extents.find({leaf.value, leaf.axis});
      return it == extents.end()
                 ? Result<Cardinality>{}
                 : Result<Cardinality>{Status::Proven, it->second};
    };
    auto integer = [&](DomainLeaf leaf, unsigned) -> Result<uint64_t> {
      if (capacityLeaf == leaf)
        return {Status::Capacity, std::nullopt};
      auto it = integers.find(leaf);
      return it == integers.end()
                 ? Result<uint64_t>{}
                 : Result<uint64_t>{Status::Proven, it->second};
    };
    auto same = [&](DomainLeaf a, DomainLeaf b) {
      return a == b || aliases.count({a, b}) || aliases.count({b, a})
                 ? Status::Proven
                 : Status::Unknown;
    };
    auto equal = [&](DomainExtent a, DomainExtent b) {
      ++equalityQueries;
      if (missingEqualityAxis == a.axis)
        return Status::Unknown;
      return a.axis == b.axis ? same(a.value, b.value) : Status::Unknown;
    };
    DomainCardinality view(work, {node, child, extent, integer, same, equal},
                           depth);
    check(view);
  }
};
void number(Result<uint64_t> result, uint64_t expected) {
  require(result.status == Status::Proven && result.value == expected,
          "unexpected exact cardinality");
}
} // namespace
int main() {
  Cases cases;
  cases.run("half-open ranges agree with bounded independent enumeration", [] {
    Graph graph;
    auto domain = graph.range(10, 11);
    uint64_t remaining = 10000;
    Work work(remaining);
    for (uint64_t lower = 0; lower < 9; ++lower)
      for (uint64_t upper = 0; upper < 9; ++upper) {
        graph.integers = {{10, lower}, {11, upper}};
        uint64_t expected = 0;
        for (auto item = lower; item < upper; ++item)
          ++expected;
        graph.query(work, [&](DomainCardinality &view) {
          number(view.exact(domain), expected);
        });
      }
  });
  cases.run("numeric range equality and exact forwarded endpoint equality", [] {
    Graph graph;
    auto a = graph.range(1, 2), b = graph.range(3, 4);
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.aliases = {{1, 3}, {2, 4}};
    graph.query(work, [&](DomainCardinality &view) {
      require(view.equal(a, b) == Status::Proven, "matching endpoints lost");
      require(view.exact(a).status == Status::Unknown, "identity became count");
    });
    graph.aliases.erase({2, 4});
    graph.query(work, [&](DomainCardinality &view) {
      require(view.equal(a, b) == Status::Unknown,
              "unmatched endpoint equated");
    });
    graph.integers = {{1, 0}, {2, 4}, {3, 7}, {4, 11}};
    graph.query(work, [&](DomainCardinality &view) {
      require(view.equal(a, b) == Status::Proven, "equal range lengths lost");
    });
  });
  cases.run("extent identity retains axes and does not use upper bounds", [] {
    Graph graph;
    auto rows = graph.leaf(1, 0), columns = graph.leaf(1, 1);
    auto other = graph.leaf(2, 0);
    graph.extents = {{{1, 0}, {4, Precision::Upper}},
                     {{2, 0}, {4, Precision::Upper}}};
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.query(work, [&](DomainCardinality &view) {
      require(view.exact(rows).status == Status::Unknown, "upper became exact");
      require(view.equal(rows, other) == Status::Unknown,
              "upper sizes equated");
      require(view.equal(rows, columns) == Status::Unknown, "axes equated");
      require(view.count(rows).value->precision == Precision::Upper,
              "result count lost upper precision");
    });
  });
  cases.run(
      "checked products preserve unknown zero and overflow semantics", [] {
        Graph graph;
        auto big = graph.leaf(1), two = graph.leaf(2), zero = graph.leaf(3);
        auto unknown = graph.leaf(4);
        graph.extents = {{{1, 0}, {std::numeric_limits<uint64_t>::max()}},
                         {{2, 0}, {2}},
                         {{3, 0}, {0}}};
        auto overflowing = graph.combine(DomainKind::Product, {big, two});
        auto empty =
            graph.combine(DomainKind::Product, {overflowing, zero, unknown});
        auto unit = graph.combine(DomainKind::Product, {});
        uint64_t remaining = 10000;
        Work work(remaining);
        graph.query(work, [&](DomainCardinality &view) {
          require(view.exact(overflowing).status == Status::Unknown,
                  "overflow wrapped or became Capacity");
          number(view.exact(empty), 0);
          number(view.exact(unit), 1);
        });
      });
  cases.run("matrix coordinates use both axes for counts and equality", [] {
    Graph graph;
    auto a = graph.coordinates(1), b = graph.coordinates(2);
    graph.extents = {{{1, 0}, {3}}, {{1, 1}, {5}}};
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.query(work,
                [&](DomainCardinality &view) { number(view.exact(a), 15); });
    graph.extents.clear();
    graph.aliases.insert({1, 2});
    graph.query(work, [&](DomainCardinality &view) {
      require(view.equal(a, b) == Status::Proven, "matrix axes not matched");
      require(graph.equalityQueries == 2, "matrix did not check both axes");
    });
    graph.missingEqualityAxis = 1;
    graph.query(work, [&](DomainCardinality &view) {
      require(view.equal(a, b) == Status::Unknown,
              "row equality incorrectly proved coordinate equality");
    });
  });
  cases.run(
      "structural products match ordered factors with independent leaves", [] {
        Graph graph;
        auto a = graph.leaf(1), b = graph.leaf(2), c = graph.leaf(3),
             d = graph.leaf(4);
        auto x = graph.combine(DomainKind::Product, {a, c});
        auto y = graph.combine(DomainKind::Product, {b, d});
        graph.aliases = {{1, 2}, {3, 4}};
        uint64_t remaining = 10000;
        Work work(remaining);
        graph.query(work, [&](DomainCardinality &view) {
          require(view.equal(x, y) == Status::Proven, "factor equality lost");
        });
        graph.aliases.erase({3, 4});
        graph.query(work, [&](DomainCardinality &view) {
          require(view.equal(x, y) == Status::Unknown,
                  "missing factor equated");
        });
      });
  cases.run("zip count does not discharge separate strict admission", [] {
    Graph graph;
    auto a = graph.leaf(1), b = graph.leaf(2);
    graph.extents = {{{1, 0}, {2}}, {{2, 0}, {3}}};
    auto zip = graph.combine(DomainKind::Zip, {a, b});
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.query(work, [&](DomainCardinality &view) {
      number(view.exact(zip), 2);
      require(view.equal(zip, a) == Status::Proven, "zip first count lost");
      require(view.equal(a, b) == Status::Unknown, "strict zip was admitted");
    });
  });
  cases.run("filtered result upper bound cannot justify fixed size", [] {
    Graph graph;
    auto a = graph.leaf(1);
    graph.extents = {{{1, 0}, {4}}};
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.query(work, [&](DomainCardinality &view) {
      auto result = collect(work, view.count(a), true);
      require(result.value && result.value->precision == Precision::Upper,
              "filter retained exact positive count");
      graph.extents[{1, 0}] = *result.value;
    });
    graph.query(work, [&](DomainCardinality &view) {
      require(view.exact(a).status == Status::Unknown, "filtered exact size");
    });
  });
  for (bool zeroFirst : {true, false})
    cases.run(zeroFirst ? "capacity after zero is sticky"
                        : "capacity before zero is sticky",
              [&] {
                Graph graph;
                auto zero = graph.leaf(1), exhausted = graph.leaf(2);
                graph.extents = {{{1, 0}, {0}}};
                graph.capacityLeaf = 2;
                auto p = graph.combine(
                    DomainKind::Product,
                    zeroFirst ? std::vector<DomainRef>{zero, exhausted}
                              : std::vector<DomainRef>{exhausted, zero});
                uint64_t remaining = 10000;
                Work work(remaining);
                graph.query(work, [&](DomainCardinality &view) {
                  require(view.exact(p).status == Status::Capacity,
                          "zero erased capacity");
                  require(view.equal(zero, zero) == Status::Capacity,
                          "capacity unstuck");
                  require(remaining != 0,
                          "adapter capacity drained unrelated budget");
                });
              });
  cases.run("every count and structural equality debit the cumulative work",
            [] {
              Graph graph;
              auto a = graph.leaf(1), b = graph.leaf(2);
              graph.aliases.insert({1, 2});
              auto x = graph.combine(DomainKind::Product, {a, a});
              auto y = graph.combine(DomainKind::Product, {b, b});
              uint64_t remaining = 10000;
              Work work(remaining);
              graph.query(work, [&](DomainCardinality &view) {
                require(view.equal(x, y) == Status::Proven,
                        "unbounded reference failed");
              });
              auto required = 10000 - remaining;
              for (uint64_t budget = 0; budget < required; ++budget) {
                uint64_t available = budget;
                Work limited(available);
                graph.query(limited, [&](DomainCardinality &view) {
                  require(view.equal(x, y) == Status::Capacity,
                          "partial equality proof");
                  require(view.count(a).status == Status::Capacity,
                          "nested budget reset");
                });
              }
              remaining = required;
              Work exactBudget(remaining);
              graph.query(exactBudget, [&](DomainCardinality &view) {
                require(view.equal(x, y) == Status::Proven,
                        "exact budget did not suffice");
                require(view.equal(x, y) == Status::Capacity,
                        "query reset its allowance");
              });
            });
  cases.run("depth is bounded without draining the caller counter", [] {
    Graph graph;
    auto a = graph.leaf(1);
    for (unsigned i = 0; i < 8; ++i)
      a = graph.combine(DomainKind::Zip, {a});
    uint64_t remaining = 10000;
    Work work(remaining);
    graph.query(
        work,
        [&](DomainCardinality &view) {
          require(view.exact(a).status == Status::Capacity,
                  "depth was unbounded");
          require(remaining > 9000, "depth drained the shared counter");
        },
        4);
  });
  cases.run("recursive leaf extraction receives the consumed domain depth", [] {
    Graph graph;
    auto value = graph.leaf(1);
    graph.extents = {{{1, 0}, {3}}};
    value = graph.combine(DomainKind::Zip, {value});
    value = graph.combine(DomainKind::Zip, {value});
    uint64_t remaining = 100;
    Work work(remaining);
    graph.query(work, [&](DomainCardinality &view) {
      number(view.exact(value), 3);
      require(graph.extentDepth == 3, "leaf extraction reset domain depth");
    });
  });
  return cases.result();
}
