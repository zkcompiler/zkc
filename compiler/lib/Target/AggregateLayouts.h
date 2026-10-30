#ifndef ZKC_TARGET_AGGREGATE_LAYOUTS_H
#define ZKC_TARGET_AGGREGATE_LAYOUTS_H

#include "../Transforms/NumericalSelection.h"
#include "NativePlanTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/SmallBitVector.h"
#include <functional>
#include <limits>

namespace zkc::target {
/// Proposal-local structural equations. Each logical node has its own layout
/// variable, so constraining one variant payload never fixes its siblings.
/// Equalities and exact ports are solved before constructor leaf preferences.
/// This is selection machinery; the independent plan reader does not use it.
class AggregateLayouts {
public:
  using Id = size_t;

private:
  static constexpr Id NoEvidence = std::numeric_limits<Id>::max();
  struct Node {
    mlir::Type logical;
    Id parent;
    size_t size = 1;
    llvm::SmallVector<Id> children;
    std::string representation;
    std::string ordinary;
    Id evidence = NoEvidence;
    llvm::SmallVector<size_t> owners;
    mlir::Type physical;
  };
  llvm::SmallVector<Node, 0> nodes;
  llvm::DenseMap<mlir::Value, Id> values;
  llvm::SmallVector<std::pair<Id, Id>> preferences;
  struct Join {
    Id target;
    llvm::SmallVector<Id> sources;
  };
  llvm::SmallVector<Join> joins;
  mathematical::NumericalSelection &work;
  std::function<void(llvm::ArrayRef<size_t>)> conflict;

  llvm::Error charge() {
    return work.chargeCatalog() ? llvm::Error::success()
                                : error("finite-analysis-limit");
  }
  Id root(Id id) {
    if (nodes[id].parent != id)
      nodes[id].parent = root(nodes[id].parent);
    return nodes[id].parent;
  }
  llvm::Expected<Id> create(mlir::Type logical) {
    if (auto e = charge())
      return e;
    auto schemas = planLogicalChildren(logical);
    if (!schemas)
      return schemas.takeError();
    Id id = nodes.size();
    nodes.push_back({logical, id, 1, {}, {}, {}, NoEvidence, {}, {}});
    // A missing complete default is allowed while exact child equations are
    // unresolved. Sequence and variant wrappers have fixed structural layouts.
    auto ordinary = defaultPlanType(logical);
    if (ordinary)
      nodes[id].representation = mlir::cast<runtime::RepresentedType>(*ordinary)
                                     .getRepresentation()
                                     .str();
    else {
      llvm::consumeError(ordinary.takeError());
      if (planTypeConstructor(logical) == "sequence")
        nodes[id].representation = "logical.sequence/0";
      else if (planTypeConstructor(logical) == "variant")
        nodes[id].representation = "logical.variant/0";
    }
    nodes[id].ordinary = nodes[id].representation;
    for (const auto &schema : *schemas) {
      auto child = create(schema);
      if (!child)
        return child.takeError();
      nodes[id].children.push_back(*child);
    }
    return id;
  }

public:
  AggregateLayouts(mathematical::NumericalSelection &work,
                   std::function<void(llvm::ArrayRef<size_t>)> conflict)
      : work(work), conflict(std::move(conflict)) {}

  llvm::Expected<Id> get(mlir::Value value) {
    auto found = values.find(value);
    if (found != values.end())
      return found->second;
    auto id = create(value.getType());
    if (id)
      values[value] = *id;
    return id;
  }
  Id child(Id id, unsigned index) { return nodes[root(id)].children[index]; }

  llvm::Error equate(Id left, Id right) {
    if (auto e = charge())
      return e;
    left = root(left);
    right = root(right);
    if (left == right)
      return llvm::Error::success();
    if (!(nodes[left].logical == nodes[right].logical))
      return error("binding-operation-signature");
    if (nodes[left].size < nodes[right].size)
      std::swap(left, right);
    auto &a = nodes[left];
    auto &b = nodes[right];
    if (!a.owners.empty() && !b.owners.empty() &&
        a.representation != b.representation) {
      llvm::SmallVector<size_t> owners = a.owners;
      llvm::append_range(owners, b.owners);
      conflict(owners);
      return error("binding-no-conversion");
    }
    if (!b.owners.empty() || (a.owners.empty() && a.representation.empty()))
      a.representation = b.representation;
    llvm::append_range(a.owners, b.owners);
    a.size += b.size;
    b.parent = left;
    auto children = llvm::zip(a.children, b.children);
    for (auto [x, y] : children)
      if (auto e = equate(x, y))
        return e;
    return llvm::Error::success();
  }
  llvm::Error pin(Id id, mlir::Type type, size_t owner) {
    if (auto e = charge())
      return e;
    if (auto e = checkPhysicalType(type))
      return e;
    auto represented = mlir::cast<runtime::RepresentedType>(type);
    id = root(id);
    auto &node = nodes[id];
    if (node.logical != represented.getLogical())
      return error("binding-operation-signature");
    if (!node.owners.empty() &&
        node.representation != represented.getRepresentation()) {
      auto owners = node.owners;
      owners.push_back(owner);
      conflict(owners);
      return error("binding-no-conversion");
    }
    node.representation = represented.getRepresentation().str();
    node.owners.push_back(owner);
    if (node.children.size() != represented.getChildren().size())
      return error("binding-representation");
    for (auto [child, physical] :
         llvm::zip(node.children, represented.getChildren()))
      if (auto e = pin(child, physical, owner))
        return e;
    return llvm::Error::success();
  }
  /// Packing aggregate children requires equality. Packing a leaf may instead
  /// insert a reached conversion, so its actual representation is a preference.
  llvm::Error pack(Id source, Id target, bool aggregate) {
    if (aggregate)
      return equate(source, target);
    if (auto e = charge())
      return e;
    preferences.emplace_back(source, target);
    return llvm::Error::success();
  }
  /// Scalar joins retain the existing policy: live yields agree exactly or
  /// select the native default, with any conversion at the reached yield.
  /// Their result is evidence for packing only after dependencies settle.
  /// Each final scalar equivalence class must have one defining join at most.
  llvm::Error join(Id target, llvm::SmallVector<Id> sources) {
    if (auto e = charge())
      return e;
    joins.push_back({target, std::move(sources)});
    return llvm::Error::success();
  }
  llvm::Error solve() {
    llvm::SmallVector<Id> roots;
    for (Id id = 0; id < nodes.size(); ++id) {
      if (auto e = charge())
        return e;
      // A subsequent solve must not reuse a physical tree or soft evidence
      // derived before a new pin, equality, or packing edge was added.
      nodes[id].physical = {};
      if (root(id) != id)
        continue;
      roots.push_back(id);
      auto &node = nodes[id];
      node.evidence = node.owners.empty() ? NoEvidence : id;
      if (node.owners.empty())
        node.representation = node.ordinary;
    }
    llvm::SmallBitVector definitions(nodes.size());
    for (auto &join : joins) {
      if (auto e = charge())
        return e;
      join.target = root(join.target);
      if (definitions.test(join.target))
        return error("binding-operation-signature");
      definitions.set(join.target);
      // A scalar join is a definition, not a constructor preference. Its
      // reached yields choose its layout unless an exact port fixes it.
      nodes[join.target].evidence = join.target;
    }

    // Resolve preference provenance before reading any representation. Exact
    // ports and joins are evidence sources; other leaves choose the smallest
    // reachable source id. Visit sources in id order, claiming each soft node
    // once, including in packing cycles. Defaults never become exact evidence.
    llvm::SmallVector<llvm::SmallVector<Id>, 0> users(nodes.size());
    for (auto [from, to] : preferences) {
      if (auto e = charge())
        return e;
      users[root(from)].push_back(root(to));
    }
    llvm::SmallVector<Id> pending;
    for (auto id : roots) {
      if (auto e = charge())
        return e;
      if (nodes[id].evidence != id)
        continue;
      pending.push_back(id);
      while (!pending.empty()) {
        if (auto e = charge())
          return e;
        auto from = pending.pop_back_val();
        for (auto to : users[from]) {
          if (auto e = charge())
            return e;
          auto &target = nodes[to];
          if (target.evidence != NoEvidence)
            continue;
          target.evidence = id;
          pending.push_back(to);
        }
      }
    }

    // Unanimity/default is a join with the ordinary layout as its top element.
    // Starting there, a definition can change only once: all live yields must
    // resolve to the same nondefault layout. Count each yield once rather than
    // rescanning a large match every time one of its dependencies settles.
    // Cyclic joins without sufficient evidence deterministically stay default.
    struct Unanimity {
      size_t remaining = 0;
      std::string selected;
      bool disagrees = false;
    };
    llvm::SmallVector<Unanimity, 0> states(joins.size());
    for (auto &list : users) {
      if (auto e = charge())
        return e;
      list.clear();
    }
    auto receive = [&](size_t index, const std::string &representation) {
      auto &state = states[index];
      --state.remaining;
      if (state.selected.empty())
        state.selected = representation;
      else if (state.selected != representation)
        state.disagrees = true;
      if (!state.remaining && !state.disagrees) {
        auto target = joins[index].target;
        nodes[target].representation = state.selected;
        pending.push_back(target);
      }
    };
    for (auto [index, join] : llvm::enumerate(joins)) {
      if (auto e = charge())
        return e;
      auto &target = nodes[join.target];
      if (!target.owners.empty())
        continue;
      states[index].remaining = join.sources.size();
      for (auto source : join.sources) {
        if (auto e = charge())
          return e;
        source = root(source);
        auto evidence = nodes[source].evidence;
        const auto &definition =
            nodes[evidence == NoEvidence ? source : evidence];
        if (!definition.representation.empty() &&
            definition.representation != target.ordinary)
          receive(index, definition.representation);
        else if (evidence != NoEvidence && definition.owners.empty()) {
          // Read the definition directly, so a changed source cannot leave a
          // stale representation circulating through constructor preferences.
          users[evidence].push_back(index);
        }
      }
    }
    while (!pending.empty()) {
      if (auto e = charge())
        return e;
      auto source = pending.pop_back_val();
      for (auto index : users[source]) {
        if (auto e = charge())
          return e;
        receive(index, nodes[source].representation);
      }
    }
    for (auto id : roots) {
      if (auto e = charge())
        return e;
      if (nodes[id].evidence != NoEvidence)
        nodes[id].representation = nodes[nodes[id].evidence].representation;
    }
    return llvm::Error::success();
  }
  llvm::Expected<mlir::Type> physical(Id id) {
    id = root(id);
    auto &node = nodes[id];
    if (node.physical)
      return node.physical;
    if (auto e = charge())
      return e;
    llvm::SmallVector<mlir::Type> children;
    for (auto child : node.children) {
      auto type = physical(child);
      if (!type)
        return type.takeError();
      children.push_back(std::move(*type));
    }
    auto type = formPhysicalType(node.logical, node.representation, children);
    if (type)
      node.physical = *type;
    return type;
  }
};
} // namespace zkc::target

#endif
