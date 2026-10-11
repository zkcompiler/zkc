#include "zkc/Contracts/MathematicalFacts.h"
#include <cstdlib>
#include <iostream>
#include <limits>
#include <new>
#include <type_traits>
#include <vector>

using namespace zkc::facts;

namespace {
unsigned checks = 0, failures = 0;
void expect(bool condition, const char *message) {
  ++checks;
  if (!condition) {
    ++failures;
    std::cerr << message << '\n';
  }
}
template <typename T> T value(Result<T> result) {
  if (result.status != Status::Proven || !result.value) {
    std::cerr << "fixture requires a proven value\n";
    std::exit(1);
  }
  return *result.value;
}
template <typename T> void absent(Result<T> result, Status status) {
  expect(result.status == status && !result.value,
         "unproven result must have the expected status and no payload");
}
Result<Cardinality> count(uint64_t n, Precision precision = Precision::Exact) {
  return {Status::Proven, Cardinality{n, precision}};
}
void expectCount(Result<Cardinality> result, uint64_t n, Precision precision) {
  expect(result.status == Status::Proven && result.value &&
             result.value->value == n && result.value->precision == precision,
         "cardinality value/precision differs");
}
struct Fixture {
  uint64_t remaining = 10000000;
  Work work{remaining};
  Snapshot facts{work};
  Scope scope = facts.root();
  Value origin(uint64_t root, llvm::ArrayRef<unsigned> path = {}) {
    return value(facts.intern(root, path));
  }
};
constexpr Premise formation = Premise::Formation;
constexpr Premise result = Premise::Result;

void identityAndOwners() {
  static_assert(!std::is_copy_constructible_v<Snapshot>);
  static_assert(!std::is_move_constructible_v<Snapshot>);
  static_assert(!std::is_copy_constructible_v<Work>);
  Fixture a, b;
  Value root = a.origin(7), path = a.origin(7, {1, 2});
  expect(root == a.origin(7), "same root retains exact identity");
  expect(path == a.origin(7, {1, 2}), "same full path retains exact identity");
  expect(root != path && path != a.origin(7, {2, 1}) &&
             path != a.origin(7, {1}) && path != a.origin(8, {1, 2}),
         "root, path order, path length and selected subject stay distinct");
  Value foreign = b.origin(7);
  expect(root != foreign, "equal local roots cannot cross snapshots");
  expect(a.facts.addExtent(a.scope, {root, 0}, 5, formation) == Status::Proven,
         "admit exact extent");
  expect(a.facts.addExtent(a.scope, {path, 0}, 5, result) == Status::Proven,
         "admit separately constructed equal extent");
  expect(a.facts.equal(a.scope, {root, 0}, {path, 0}) == Status::Proven,
         "known equal numbers imply equal extents");
  expect(root != path, "equal shape cannot imply container identity");
  expect(a.facts.equal(a.scope, {root, 0}, {root, 1}) == Status::Unknown,
         "axis identity matters");
  expect(a.facts.equal(a.scope, {foreign, 0}, {foreign, 0}) == Status::Unknown,
         "foreign reflexivity is rejected");
  expect(a.facts.equal(b.scope, {root, 0}, {root, 0}) == Status::Unknown,
         "foreign scope is rejected before reflexivity");
  expect(a.facts.equal(a.scope, {}, {}) == Status::Unknown,
         "default handles are not evidence");
  expect(a.facts.addEquality(a.scope, {root, 0}, {foreign, 0}, formation) ==
             Status::Unknown,
         "foreign equality admission refused");
  expect(a.facts.addInteger(a.scope, foreign, 1, formation) == Status::Unknown,
         "foreign integer admission refused");
  expect(a.facts.addBound(a.scope, root, {foreign, 0}, result) ==
             Status::Unknown,
         "foreign bound admission refused");
  expect(a.facts.addExtent(b.scope, {root, 0}, 2, result) == Status::Unknown,
         "foreign scope admission refused");
  absent(a.facts.integer(a.scope, foreign), Status::Unknown);
  absent(a.facts.cardinality(a.scope, {foreign, 0}), Status::Unknown);
  absent(a.facts.fork(b.scope), Status::Unknown);
  absent(a.facts.intersect({a.scope, b.scope}), Status::Unknown);
  Value old;
  Scope oldScope;
  {
    Fixture expired;
    old = expired.origin(7);
    oldScope = expired.scope;
  }
  expect(old != root, "destroyed owner does not alias a live owner");
  absent(a.facts.integer(oldScope, old), Status::Unknown);

  alignas(Snapshot) unsigned char storage[sizeof(Snapshot)];
  auto *reused = new (storage) Snapshot(a.work);
  Value stale = value(reused->intern(7));
  Scope staleScope = reused->root();
  reused->~Snapshot();
  reused = new (storage) Snapshot(a.work);
  Value fresh = value(reused->intern(7));
  expect(stale != fresh, "snapshot address reuse cannot revive an old handle");
  absent(reused->integer(reused->root(), stale), Status::Unknown);
  absent(reused->fork(staleScope), Status::Unknown);
  reused->~Snapshot();
}

void closureAndBounds() {
  Fixture f;
  Value a = f.origin(1), b = f.origin(2), c = f.origin(3), d = f.origin(4);
  Value index = f.origin(5, {0}), otherIndex = f.origin(5, {1});
  expect(f.facts.addEquality(f.scope, {a, 0}, {b, 1}, formation) ==
             Status::Proven,
         "first equality admitted");
  expect(f.facts.addEquality(f.scope, {b, 1}, {c, 0}, result) == Status::Proven,
         "second equality admitted");
  expect(f.facts.equal(f.scope, {c, 0}, {a, 0}) == Status::Proven,
         "equality is transitive and symmetric");
  expect(f.facts.equal(f.scope, {a, 0}, {d, 0}) == Status::Unknown,
         "unrelated extent remains unknown");
  expect(f.facts.addBound(f.scope, index, {a, 0}, formation) == Status::Proven,
         "strict bound admitted");
  expect(f.facts.bound(f.scope, index, {c, 0}) == Status::Proven,
         "strict bound transfers along transitive extent equality");
  expect(f.facts.bound(f.scope, otherIndex, {c, 0}) == Status::Unknown,
         "bound does not transfer to a different projected index");
  expect(f.facts.bound(f.scope, index, {b, 0}) == Status::Unknown,
         "bound does not transfer to a different axis");
  expect(f.facts.addExtent(f.scope, {c, 0}, 8, result) == Status::Proven,
         "known extent at transitive endpoint admitted");
  expectCount(f.facts.cardinality(f.scope, {a, 0}), 8, Precision::Exact);
  expect(f.facts.addInteger(f.scope, otherIndex, 7, result) == Status::Proven,
         "known integer admitted");
  expect(f.facts.bound(f.scope, otherIndex, {a, 0}) == Status::Proven,
         "known integer and transferred exact size establish strict bound");
  Value boundary = f.origin(6), larger = f.origin(7);
  expect(f.facts.addInteger(f.scope, boundary, 8, result) == Status::Proven,
         "boundary integer admitted");
  expect(f.facts.addInteger(f.scope, larger, 9, result) == Status::Proven,
         "larger integer admitted");
  expect(f.facts.bound(f.scope, boundary, {a, 0}) == Status::Unknown &&
             f.facts.bound(f.scope, larger, {a, 0}) == Status::Unknown,
         "strict means less than, not equal or greater");
  expect(f.facts.addCardinality(f.scope, {d, 0}, {8, Precision::Upper},
                                result) == Status::Proven,
         "upper bound admitted");
  expect(f.facts.bound(f.scope, otherIndex, {d, 0}) == Status::Unknown,
         "cardinality upper bound cannot prove index safety");
  expect(f.facts.equal(f.scope, {a, 0}, {d, 0}) == Status::Unknown,
         "equal numeric upper and exact bounds do not prove equal extents");
  expect(f.facts.addExtent(f.scope, {d, 0}, 8, result) == Status::Proven,
         "additional exact evidence admitted");
  expect(f.facts.bound(f.scope, index, {d, 0}) == Status::Proven,
         "strict bound transfers across exact numeric equality");
  Value tail = f.origin(8);
  expect(f.facts.addEquality(f.scope, {d, 0}, {tail, 1}, formation) ==
             Status::Proven,
         "equality beyond numeric bridge admitted");
  expect(f.facts.equal(f.scope, {a, 0}, {tail, 1}) == Status::Proven,
         "closure composes symbolic and exact numeric equality edges");
  expect(f.facts.bound(f.scope, index, {tail, 1}) == Status::Proven,
         "bound traverses symbolic and numeric equality edges");
  expectCount(f.facts.cardinality(f.scope, {tail, 1}), 8, Precision::Exact);
}

void branchScopes() {
  Fixture f;
  Value a = f.origin(1), b = f.origin(2), index = f.origin(3);
  expect(f.facts.addInteger(f.scope, index, 0, formation) == Status::Proven,
         "parent formation fact admitted");
  Scope left = value(f.facts.fork(f.scope));
  Scope right = value(f.facts.fork(f.scope));
  expect(f.facts.addEquality(left, {a, 0}, {b, 0}, result) == Status::Proven,
         "left result fact admitted");
  expect(f.facts.addBound(left, index, {a, 0}, result) == Status::Proven,
         "left branch bound admitted");
  expect(f.facts.equal(right, {a, 0}, {b, 0}) == Status::Unknown,
         "left premise does not leak into sibling");
  Scope firstJoin = value(f.facts.intersect({left, right}));
  expect(f.facts.equal(firstJoin, {a, 0}, {b, 0}) == Status::Unknown &&
             f.facts.bound(firstJoin, index, {a, 0}) == Status::Unknown,
         "one-branch facts are absent at join");
  expect(value(f.facts.integer(firstJoin, index)) == 0,
         "inherited common formation fact remains at join");
  expect(f.facts.addEquality(right, {b, 0}, {a, 0}, result) == Status::Proven,
         "right symmetric result fact admitted");
  Scope join = value(f.facts.intersect({left, right}));
  expect(f.facts.equal(join, {a, 0}, {b, 0}) == Status::Proven,
         "symmetric common premise survives join");
  expect(f.facts.equal(firstJoin, {a, 0}, {b, 0}) == Status::Unknown,
         "completed join is a fact-set snapshot");
  expect(f.facts.addExtent(f.scope, {a, 0}, 3, result) == Status::Proven,
         "later parent result admitted");
  absent(f.facts.cardinality(left, {a, 0}), Status::Unknown);
  Scope laterChild = value(f.facts.fork(f.scope));
  expectCount(f.facts.cardinality(laterChild, {a, 0}), 3, Precision::Exact);
  expect(f.facts.bound(f.scope, index, {b, 0}) == Status::Unknown,
         "callback or loop-body premise cannot establish entry/zero-trip fact");
  Scope differentTag = value(f.facts.fork(f.scope));
  expect(f.facts.addEquality(differentTag, {a, 0}, {b, 0}, formation) ==
             Status::Proven,
         "formation equality admitted separately");
  Scope tagJoin = value(f.facts.intersect({left, differentTag}));
  expect(f.facts.equal(tagJoin, {a, 0}, {b, 0}) == Status::Unknown,
         "conservative join does not erase premise tags");
  absent(f.facts.intersect({}), Status::Unknown);
}

void cardinalities() {
  Fixture f;
  constexpr auto maximum = std::numeric_limits<uint64_t>::max();
  expectCount(product(f.work, {}), 1, Precision::Exact);
  expectCount(product(f.work, {count(3), count(4)}), 12, Precision::Exact);
  expectCount(product(f.work, {count(3, Precision::Upper), count(4)}), 12,
              Precision::Upper);
  expectCount(product(f.work, {{}, count(0)}), 0, Precision::Exact);
  expectCount(product(f.work, {count(maximum), count(2), count(0)}), 0,
              Precision::Exact);
  absent(product(f.work, {count(maximum), count(2)}), Status::Unknown);
  absent(product(f.work, {count(4), {}}), Status::Unknown);
  expectCount(sum(f.work, count(maximum), count(0)), maximum, Precision::Exact);
  absent(sum(f.work, count(maximum), count(1)), Status::Unknown);
  expectCount(sum(f.work, count(2, Precision::Upper), count(3)), 5,
              Precision::Upper);
  expectCount(range(f.work, 0, maximum), maximum, Precision::Exact);
  expectCount(range(f.work, maximum, 0), 0, Precision::Exact);
  expectCount(range(f.work, 5, 5), 0, Precision::Exact);
  expectCount(collect(f.work, count(7), false), 7, Precision::Exact);
  expectCount(collect(f.work, count(7), true), 7, Precision::Upper);
  expectCount(collect(f.work, count(7, Precision::Upper), false), 7,
              Precision::Upper);
  expectCount(collect(f.work, count(0, Precision::Upper), true), 0,
              Precision::Exact);
  absent(collect(f.work, {}, false), Status::Unknown);
  Result<Cardinality> capacity{Status::Capacity, std::nullopt};
  absent(product(f.work, {count(0), capacity}), Status::Capacity);
  absent(product(f.work, {capacity, count(0)}), Status::Capacity);
  absent(sum(f.work, {}, capacity), Status::Capacity);
  absent(collect(f.work, capacity, true), Status::Capacity);
  Value empty = f.origin(1), zeroIndex = f.origin(2);
  expect(f.facts.addCardinality(f.scope, {empty, 0}, {0, Precision::Upper},
                                result) == Status::Proven,
         "zero upper premise admitted");
  expectCount(f.facts.cardinality(f.scope, {empty, 0}), 0, Precision::Exact);
  expect(f.facts.addInteger(f.scope, zeroIndex, 0, result) == Status::Proven,
         "zero index admitted");
  expect(f.facts.bound(f.scope, zeroIndex, {empty, 0}) == Status::Unknown,
         "empty domain contains no bounded index");
}

void capacity() {
  Fixture f;
  Value a = f.origin(1), b = f.origin(2), c = f.origin(3);
  expect(f.facts.addEquality(f.scope, {a, 0}, {b, 0}, formation) ==
             Status::Proven,
         "capacity test first edge");
  expect(f.facts.addEquality(f.scope, {b, 0}, {c, 0}, formation) ==
             Status::Proven,
         "capacity test second edge");
  f.remaining = 1;
  expect(f.facts.equal(f.scope, {a, 0}, {c, 0}) == Status::Capacity,
         "closure exhaustion does not become a fact");
  expect(f.work.exhausted(), "failed charge sticks");
  f.remaining = 100;
  expect(f.facts.equal(f.scope, {a, 0}, {a, 0}) == Status::Capacity,
         "replenishing counter cannot erase exhaustion");
  absent(f.facts.intern(4), Status::Capacity);
  absent(f.facts.fork(f.scope), Status::Capacity);
  absent(f.facts.cardinality(f.scope, {a, 0}), Status::Capacity);
  absent(product(f.work, {count(0)}), Status::Capacity);

  uint64_t remaining = 2, calls = 0;
  Work callback([&](uint64_t n) {
    ++calls;
    if (n > remaining)
      return false;
    remaining -= n;
    return true;
  });
  expect(callback.charge(), "adapter extraction charges common callback");
  expectCount(range(callback, 2, 5), 3, Precision::Exact);
  absent(collect(callback, count(0), false), Status::Capacity);
  expect(calls == 3, "extraction and core use the same allowance");
  expect(!callback.charge() && calls == 3,
         "sticky failure avoids invoking callback again");
  uint64_t structuralAllowance = 100;
  Work structural(structuralAllowance);
  structural.exhaust();
  expect(structural.exhausted() && structuralAllowance == 100 &&
             !structural.charge(),
         "adapter structural limit is sticky without a fabricated debit");
  absent(range(structural, 0, 0), Status::Capacity);
  Fixture join;
  Value item = join.origin(1);
  expect(join.facts.addInteger(join.scope, item, 2, formation) ==
             Status::Proven,
         "join capacity premise");
  Scope child = value(join.facts.fork(join.scope));
  join.remaining = 3;
  absent(join.facts.intersect({join.scope, child}), Status::Capacity);
}

void directEvidenceInLargeComponent() {
  Fixture f;
  Value index = f.origin(1000), first = f.origin(0), second = f.origin(1);
  expect(f.facts.addBound(f.scope, index, {first, 0}, formation) ==
             Status::Proven,
         "direct bound before a large equality component");
  expect(f.facts.addEquality(f.scope, {first, 0}, {second, 0}, formation) ==
             Status::Proven,
         "direct target before a large equality component");
  Value previous = second;
  for (unsigned i = 2; i < 128; ++i) {
    Value next = f.origin(i);
    expect(f.facts.addEquality(f.scope, {previous, 0}, {next, 0}, formation) ==
               Status::Proven,
           "large equality chain edge");
    previous = next;
  }
  f.remaining = 48;
  expect(f.facts.equal(f.scope, {first, 0}, {second, 0}) == Status::Proven,
         "direct target does not saturate unrelated transitive consequences");
  expect(f.facts.bound(f.scope, index, {first, 0}) == Status::Proven,
         "direct bound does not saturate its equality component");
  expect(f.facts.bound(f.scope, index, {second, 0}) == Status::Proven,
         "bound transfer stops after a charged sufficient equality proof");
  expect(!f.work.exhausted(), "direct proofs fit a small shared allowance");
  expect(f.facts.equal(f.scope, {first, 0}, {previous, 0}) == Status::Capacity,
         "distant proof still reports insufficient capacity");
}

void indexedIdentityScale() {
  uint64_t remaining = 65536;
  Work work(remaining);
  Snapshot facts(work);
  std::vector<Value> values;
  for (unsigned i = 0; i < 10000; ++i)
    values.push_back(value(facts.intern(7, {i, i % 5})));
  uint64_t construction = 65536 - remaining;
  for (unsigned i = 0; i < values.size(); ++i)
    expect(value(facts.intern(7, {i, i % 5})) == values[i],
           "indexed full paths retain identity after table growth");
  expect(construction == 30000 && 65536 - remaining == 60000,
         "identity work is one plus path length for new and repeated roots");
  expect(!work.exhausted(), "10000 identities fit the unchanged allowance");
  std::cout << "identity work: " << construction << " new, "
            << 65536 - remaining - construction << " repeated\n";
}

void indexedEqualityScale() {
  uint64_t remaining = 65536;
  Work work(remaining);
  Snapshot facts(work);
  Scope scope = facts.root();
  std::vector<Value> vertices;
  for (unsigned i = 0; i <= 1024; ++i)
    vertices.push_back(value(facts.intern(i)));
  Value index = value(facts.intern(2048));
  for (unsigned i = 0; i < 1024; ++i)
    expect(facts.addEquality(scope, {vertices[i], 0}, {vertices[i + 1], 0},
                             formation) == Status::Proven,
           "1024 equality premises fit the shared allowance");
  expect(facts.addBound(scope, index, {vertices.back(), 0}, result) ==
             Status::Proven,
         "bound admitted after the 1024 equality premises");
  expect(facts.addExtent(scope, {vertices.back(), 0}, 9, result) ==
             Status::Proven,
         "exact count at the distant endpoint");
  uint64_t setup = 65536 - remaining, before = remaining;
  for (unsigned i = 0; i < 1024; ++i)
    expect(facts.addEquality(scope, {vertices[i + 1], 0}, {vertices[i], 0},
                             formation) == Status::Proven,
           "symmetric duplicate premises use indexed membership");
  uint64_t duplicates = before - remaining;
  before = remaining;
  for (unsigned i = 0; i < 1024; ++i)
    expect(facts.equal(scope, {vertices[i], 0}, {vertices[i + 1], 0}) ==
               Status::Proven,
           "direct equalities do not traverse the large component");
  uint64_t direct = before - remaining;
  before = remaining;
  expect(facts.bound(scope, index, {vertices.back(), 0}) == Status::Proven,
         "late direct bound ignores the large equality component");
  expect(before - remaining == 2, "direct bound pays only its indexed lookup");
  before = remaining;
  expect(facts.equal(scope, {vertices.front(), 0}, {vertices.back(), 0}) ==
             Status::Proven,
         "1024-edge transitive equality remains within shared work");
  uint64_t closure = before - remaining;
  before = remaining;
  expect(facts.bound(scope, index, {vertices.front(), 0}) == Status::Proven,
         "strict bound transfers through 1024 equality edges");
  uint64_t bound = before - remaining;
  before = remaining;
  expectCount(facts.cardinality(scope, {vertices.front(), 0}), 9,
              Precision::Exact);
  uint64_t cardinality = before - remaining;
  before = remaining;
  Scope copied = value(facts.fork(scope));
  Scope joined = value(facts.intersect({scope, copied}));
  uint64_t scopes = before - remaining;
  expect(facts.bound(joined, index, {vertices.back(), 0}) == Status::Proven,
         "copied and intersected scopes retain their query indices");
  expect(setup < 8192 && duplicates <= 2048 && direct <= 2048 &&
             closure < 8192 && bound < 8192 && cardinality < 8192 &&
             scopes < 16384 && !work.exhausted(),
         "setup, duplicates, closure and explicit scope copies stay bounded");
  std::cout << "1024-premise work: setup=" << setup
            << ", duplicates=" << duplicates << ", direct=" << direct
            << ", closure=" << closure << ", bound=" << bound
            << ", cardinality=" << cardinality << ", scopes=" << scopes
            << ", total=" << 65536 - remaining << '\n';
}

void unrelatedFactIndices() {
  uint64_t remaining = 65536;
  Work work(remaining);
  Snapshot facts(work);
  Scope scope = facts.root();
  Value index = value(facts.intern(0)), target = value(facts.intern(1));
  Value unknown = value(facts.intern(2));
  for (unsigned i = 0; i < 1024; ++i) {
    Value item = value(facts.intern(i + 3));
    expect(facts.addInteger(scope, item, i, result) == Status::Proven &&
               facts.addCardinality(scope, {item, 0}, {i + 1, Precision::Upper},
                                    result) == Status::Proven &&
               facts.addBound(scope, item, {item, 0}, formation) ==
                   Status::Proven &&
               facts.addBound(scope, index, {item, 0}, formation) ==
                   Status::Proven,
           "unrelated facts and other bounds for the same index admitted");
  }
  expect(facts.addBound(scope, index, {target, 0}, result) == Status::Proven,
         "direct bound recorded after thousands of unrelated facts");
  uint64_t before = remaining;
  expect(facts.bound(scope, index, {target, 0}) == Status::Proven,
         "direct bound is found independently of earlier bounds");
  expect(before - remaining == 2,
         "unrelated facts add no charged work to direct bound lookup");
  before = remaining;
  expect(facts.bound(scope, index, {unknown, 0}) == Status::Unknown,
         "unrelated bound targets cannot establish an unknown bound");
  uint64_t missingBound = before - remaining;
  expect(missingBound <= 8,
         "one target traversal handles every candidate bound for the index");
  before = remaining;
  absent(facts.integer(scope, unknown), Status::Unknown);
  expect(before - remaining == 2,
         "integer lookup does not scan unrelated fact kinds or values");
  before = remaining;
  absent(facts.cardinality(scope, {unknown, 0}), Status::Unknown);
  expect(before - remaining <= 5,
         "absent cardinality only explores the requested extent");
  std::cout << "unrelated-fact work: direct bound=2, missing bound="
            << missingBound << ", total=" << 65536 - remaining << '\n';
}

void numericEqualityScale() {
  uint64_t remaining = 65536;
  Work work(remaining);
  Snapshot facts(work);
  Scope scope = facts.root();
  std::vector<Value> containers;
  for (unsigned i = 0; i < 1024; ++i) {
    Value container = value(facts.intern(i));
    containers.push_back(container);
    expect(facts.addExtent(scope, {container, 0}, 4, formation) ==
               Status::Proven,
           "same-sized independent container admitted");
  }
  Value index = value(facts.intern(1024));
  expect(facts.addInteger(scope, index, 0, result) == Status::Proven,
         "literal index admitted");
  uint64_t before = remaining;
  expectCount(facts.cardinality(scope, {containers.back(), 0}), 4,
              Precision::Exact);
  uint64_t cardinality = before - remaining;
  before = remaining;
  expect(facts.bound(scope, index, {containers.back(), 0}) == Status::Proven,
         "literal bound across 1024 equal-sized containers");
  uint64_t bound = before - remaining;
  before = remaining;
  expect(facts.equal(scope, {containers.front(), 0}, {containers.back(), 0}) ==
             Status::Proven,
         "numeric equality connects distinct containers");
  uint64_t equality = before - remaining;
  expect(cardinality < 8192 && bound < 8192 && equality < 2048 &&
             !work.exhausted(),
         "numeric bucket is expanded once rather than as a quadratic clique");
  expect(containers.front() != containers.back(),
         "numeric equality does not collapse identities");
  std::cout << "1024 equal-count work: cardinality=" << cardinality
            << ", bound=" << bound << ", equality=" << equality << '\n';

  // Reproduce the shape of the source regression: a separate literal access
  // for each of 64 independent arrays with the same static count.
  uint64_t repeatedRemaining = 65536;
  Work repeatedWork(repeatedRemaining);
  Snapshot repeated(repeatedWork);
  Scope repeatedScope = repeated.root();
  Value zero = value(repeated.intern(64));
  expect(repeated.addInteger(repeatedScope, zero, 0, result) == Status::Proven,
         "repeated access literal");
  containers.clear();
  for (unsigned i = 0; i < 64; ++i) {
    containers.push_back(value(repeated.intern(i)));
    expect(repeated.addExtent(repeatedScope, {containers.back(), 0}, 4,
                              formation) == Status::Proven,
           "repeated access static count");
  }
  for (Value container : containers)
    expect(repeated.bound(repeatedScope, zero, {container, 0}) ==
               Status::Proven,
           "all 64 independent same-sized literal accesses fit shared work");
  expect(!repeatedWork.exhausted(),
         "same-size access regression stays bounded");
  std::cout << "64 same-sized literal accesses: " << 65536 - repeatedRemaining
            << " total work\n";
}

void indexedScopeProvenance() {
  Fixture f;
  Value a = f.origin(0), b = f.origin(1), index = f.origin(2);
  Scope left = value(f.facts.fork(f.scope));
  Scope right = value(f.facts.fork(f.scope));
  Scope branches[] = {left, right};
  for (unsigned i = 0; i < 2; ++i) {
    Scope branch = branches[i];
    Premise tag = i == 0 ? formation : result;
    expect(f.facts.addEquality(branch, {a, 0}, {b, 0}, tag) == Status::Proven &&
               f.facts.addInteger(branch, index, 1, tag) == Status::Proven &&
               f.facts.addExtent(branch, {a, 0}, 4, tag) == Status::Proven &&
               f.facts.addBound(branch, index, {b, 0}, tag) == Status::Proven,
           "each fact kind can have distinct premise provenance");
  }
  Scope joined = value(f.facts.intersect({left, right}));
  expect(f.facts.equal(joined, {a, 0}, {b, 0}) == Status::Unknown &&
             f.facts.bound(joined, index, {b, 0}) == Status::Unknown,
         "indexed equality and bound do not survive a different-tag join");
  absent(f.facts.integer(joined, index), Status::Unknown);
  absent(f.facts.cardinality(joined, {a, 0}), Status::Unknown);
  expect(f.facts.addExtent(left, {a, 0}, 4, result) == Status::Proven,
         "query-index duplicate keeps its separate explicit provenance");
  joined = value(f.facts.intersect({left, right}));
  expectCount(f.facts.cardinality(joined, {a, 0}), 4, Precision::Exact);
  absent(f.facts.cardinality(joined, {b, 0}), Status::Unknown);
  absent(f.facts.cardinality(f.scope, {a, 0}), Status::Unknown);
}

void conflictingIndexedFacts() {
  Fixture f;
  Value a = f.origin(0), b = f.origin(1), index = f.origin(2);
  expect(f.facts.addInteger(f.scope, index, 1, formation) == Status::Proven &&
             f.facts.addInteger(f.scope, index, 2, result) == Status::Proven,
         "conflicting integer premises admitted for conservative query");
  absent(f.facts.integer(f.scope, index), Status::Unknown);
  expect(f.facts.addExtent(f.scope, {a, 0}, 4, formation) == Status::Proven &&
             f.facts.addExtent(f.scope, {b, 0}, 4, result) == Status::Proven &&
             f.facts.addCardinality(f.scope, {b, 0}, {3, Precision::Upper},
                                    result) == Status::Proven,
         "conflicting upper count is reachable through numeric equality");
  absent(f.facts.cardinality(f.scope, {a, 0}), Status::Unknown);
  expect(f.facts.addExtent(f.scope, {b, 0}, 5, formation) == Status::Proven,
         "conflicting exact count admitted");
  absent(f.facts.cardinality(f.scope, {a, 0}), Status::Unknown);
  Scope child = value(f.facts.fork(f.scope));
  absent(f.facts.integer(child, index), Status::Unknown);
  absent(f.facts.cardinality(child, {a, 0}), Status::Unknown);
}

void deterministicQueryWork() {
  std::vector<uint64_t> costs[2];
  for (unsigned order = 0; order < 2; ++order) {
    Fixture f;
    Value vertices[8];
    for (unsigned i = 0; i < 8; ++i)
      vertices[i] = f.origin(i);
    // Reverse admission order without changing the exact identities. Include
    // cycles and a numeric bridge to exercise both forms of visited set.
    constexpr unsigned edges[][2] = {{0, 1}, {1, 2}, {2, 0}, {3, 4}, {4, 5}};
    for (unsigned i = 0; i < 5; ++i) {
      unsigned e = order ? 4 - i : i;
      expect(f.facts.addEquality(f.scope, {vertices[edges[e][0]], 0},
                                 {vertices[edges[e][1]], 0},
                                 formation) == Status::Proven,
             "deterministic traversal edge");
    }
    for (unsigned i = 0; i < 2; ++i) {
      unsigned v = (order ? 1 - i : i) + 2;
      expect(f.facts.addExtent(f.scope, {vertices[v], 0}, 7, result) ==
                 Status::Proven,
             "deterministic numeric bridge");
    }
    expect(f.facts.addBound(f.scope, vertices[7], {vertices[0], 0}, result) ==
               Status::Proven,
           "deterministic bound premise");
    uint64_t before = f.remaining;
    expect(f.facts.equal(f.scope, {vertices[0], 0}, {vertices[5], 0}) ==
               Status::Proven,
           "mixed symbolic and numeric closure reaches the endpoint");
    costs[order].push_back(before - f.remaining);
    before = f.remaining;
    expect(f.facts.bound(f.scope, vertices[7], {vertices[5], 0}) ==
               Status::Proven,
           "bound crosses the mixed closure");
    costs[order].push_back(before - f.remaining);
    before = f.remaining;
    expectCount(f.facts.cardinality(f.scope, {vertices[5], 0}), 7,
                Precision::Exact);
    costs[order].push_back(before - f.remaining);
    before = f.remaining;
    expect(f.facts.equal(f.scope, {vertices[0], 0}, {vertices[6], 0}) ==
               Status::Unknown,
           "cycle does not connect an unrelated extent");
    costs[order].push_back(before - f.remaining);
    f.remaining = 4;
    absent(f.facts.cardinality(f.scope, {vertices[5], 0}), Status::Capacity);
  }
  expect(costs[0] == costs[1],
         "query work is independent of premise admission order");
}

// An independent connected-component oracle over every undirected graph on
// four vertices checks both positive closure and absence between components.
void exhaustiveEqualityGraphs() {
  constexpr unsigned edges[6][2] = {{0, 1}, {0, 2}, {0, 3},
                                    {1, 2}, {1, 3}, {2, 3}};
  for (unsigned mask = 0; mask < 64; ++mask) {
    Fixture f;
    Value vertices[4];
    unsigned component[4] = {0, 1, 2, 3};
    for (unsigned i = 0; i < 4; ++i)
      vertices[i] = f.origin(i);
    for (unsigned e = 0; e < 6; ++e) {
      if (!(mask & (1 << e)))
        continue;
      unsigned a = edges[e][0], b = edges[e][1];
      expect(f.facts.addEquality(f.scope, {vertices[a], 0}, {vertices[b], 0},
                                 formation) == Status::Proven,
             "graph edge admitted");
      unsigned old = component[b], replacement = component[a];
      for (unsigned &c : component)
        if (c == old)
          c = replacement;
    }
    for (unsigned a = 0; a < 4; ++a)
      for (unsigned b = 0; b < 4; ++b)
        expect(f.facts.equal(f.scope, {vertices[a], 0}, {vertices[b], 0}) ==
                   (component[a] == component[b] ? Status::Proven
                                                 : Status::Unknown),
               "extent closure agrees with independent component oracle");
  }
}

// Enumerate all represented concrete counts, checking that every claimed
// exact/upper answer contains the actual sum/product/filtered cardinality.
void concreteCardinalityModels() {
  Fixture f;
  auto contains = [](Cardinality summary, uint64_t actual) {
    return summary.precision == Precision::Exact ? summary.value == actual
                                                 : actual <= summary.value;
  };
  for (uint64_t a = 0; a < 5; ++a)
    for (uint64_t b = 0; b < 5; ++b)
      for (auto pa : {Precision::Exact, Precision::Upper})
        for (auto pb : {Precision::Exact, Precision::Upper}) {
          auto added = value(sum(f.work, count(a, pa), count(b, pb)));
          auto multiplied =
              value(product(f.work, {count(a, pa), count(b, pb)}));
          auto filtered = value(collect(f.work, count(a, pa), true));
          for (uint64_t x = pa == Precision::Exact ? a : 0; x <= a; ++x) {
            for (uint64_t y = pb == Precision::Exact ? b : 0; y <= b; ++y) {
              expect(contains(added, x + y), "sum contains actual cardinality");
              expect(contains(multiplied, x * y),
                     "product contains actual cardinality");
            }
            for (uint64_t kept = 0; kept <= x; ++kept)
              expect(contains(filtered, kept),
                     "filtered bound contains every possible predicate result");
          }
        }
}
} // namespace

int main() {
  identityAndOwners();
  closureAndBounds();
  branchScopes();
  cardinalities();
  capacity();
  directEvidenceInLargeComponent();
  indexedIdentityScale();
  indexedEqualityScale();
  unrelatedFactIndices();
  numericEqualityScale();
  indexedScopeProvenance();
  conflictingIndexedFacts();
  deterministicQueryWork();
  exhaustiveEqualityGraphs();
  concreteCardinalityModels();
  std::cout << checks << " mathematical fact checks, " << failures
            << " failures\n";
  return failures ? 1 : 0;
}
