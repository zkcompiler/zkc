#include "MathematicalValues.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/StringMap.h"
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
struct ValueCorrespondence::Implementation {
  using Node = Expression;
  struct Scope {
    llvm::DenseMap<Value, Term> values;
    llvm::DenseMap<Operation *, Environment> helpers;
    llvm::StringMap<Attribute> roles;
    StringAttr component;
  };
  Operation *diagnostic;
  Builder builder;
  SymbolTableCollection symbols;
  SmallVector<Node> nodes{Node{}}; // Zero denotes an unsupported term.
  llvm::DenseMap<size_t, SmallVector<Term>> interned;
  PolynomialValueCache polynomialNormalForms, polynomialFixings;
  SmallVector<Scope> scopes;
  // Both source and candidate traversal, term interning and independent laws
  // consume work. Leave room for the admitted 100000-operation preparation
  // expansion; this remains a separate conservative implementation limit.
  size_t remaining = 4000000;
  bool exhausted = false;
  bool roleComponents;

  explicit Implementation(Operation *op, bool components)
      : diagnostic(op), builder(op->getContext()), roleComponents(components) {}
  bool charge(size_t amount = 1) {
    if (exhausted || amount > remaining) {
      exhausted = true;
      return false;
    }
    remaining -= amount;
    return true;
  }
  std::optional<bool> constant(Term id) const {
    const auto &node = nodes[id];
    if (node.name && node.name.getValue() == "arith.constant" &&
        node.type.isSignlessInteger(1))
      if (auto attr = node.attributes.getAs<IntegerAttr>("value"))
        return attr.getValue().getBoolValue();
    return std::nullopt;
  }
  Term expression(StringRef operation, Type type, DictionaryAttr attributes,
                  unsigned result, ArrayRef<Term> operands) {
    if (!charge(1 + operands.size()) || is_contained(operands, Term(0)))
      return 0;
    if (operation == "arith.select") {
      if (operands[1] == operands[2])
        return operands[1];
      if (auto condition = constant(operands[0]))
        return operands[*condition ? 1 : 2];
    }
    auto name = builder.getStringAttr(operation);
    size_t hash = size_t(
        hash_combine(name, type, attributes, result,
                     hash_combine_range(operands.begin(), operands.end())));
    auto &bucket = interned[hash];
    for (Term id : bucket) {
      if (!charge())
        return 0;
      const auto &node = nodes[id];
      if (node.name == name && node.type == type &&
          node.attributes == attributes && node.coordinate == result &&
          ArrayRef(node.operands) == operands)
        return id;
    }
    Term id = nodes.size();
    nodes.push_back(
        {type, name, attributes, SmallVector<Term>(operands), result});
    bucket.push_back(id);
    return id;
  }
  bool booleanOperator(Term id) const {
    const auto &n = nodes[id];
    if (!n.name || !n.type.isSignlessInteger(1))
      return false;
    StringRef name = n.name.getValue();
    return (name == "arith.andi" || name == "arith.ori" ||
            name == "arith.xori" || name == "arith.cmpi") &&
           n.operands.size() == 2 && all_of(n.operands, [&](Term input) {
             return nodes[input].type.isSignlessInteger(1);
           });
  }
  bool selection(Term id) const {
    const auto &node = nodes[id];
    return node.name && node.name.getValue() == "arith.select" &&
           node.operands.size() == 3 &&
           nodes[node.operands[0]].type.isSignlessInteger(1);
  }
  // Inspect only Boolean connectives and typed selections. Algebraic leaves
  // retain their exact identity; this makes no field/group equality decision.
  bool descendants(Term root, llvm::DenseSet<Term> &seen) {
    SmallVector<Term> pending{root};
    while (!pending.empty()) {
      Term id = pending.pop_back_val();
      if (!charge())
        return false;
      if (!seen.insert(id).second)
        continue;
      if (booleanOperator(id) || selection(id))
        append_range(pending, nodes[id].operands);
    }
    return true;
  }
  bool decision(Term a, Term b, bool cuts) {
    if (!a || !b || nodes[a].type != nodes[b].type || !charge())
      return false;
    if (a == b)
      return true;
    llvm::DenseSet<Term> left, right;
    if (cuts && (!descendants(a, left) || !descendants(b, right)))
      return false;
    llvm::DenseMap<Term, unsigned> variables;
    SmallVector<Term> pending{a, b}, order;
    llvm::DenseSet<Term> seen;
    while (!pending.empty()) {
      Term id = pending.pop_back_val();
      if (!charge())
        return false;
      if (!seen.insert(id).second)
        continue;
      // Equal Boolean subterms are independent cut points. Structural matches
      // therefore never incur a global variable bound.
      bool cut = cuts && left.contains(id) && right.contains(id);
      if (nodes[id].type.isSignlessInteger(1) && !constant(id) &&
          (cut || (!booleanOperator(id) && !selection(id)))) {
        if (variables.size() == 12)
          return false;
        variables[id] = variables.size();
      } else if (booleanOperator(id) || selection(id)) {
        append_range(pending, nodes[id].operands);
      }
      order.push_back(id);
    }
    // Interned operands precede their users. Sorting avoids recursive SSA
    // walks.
    llvm::sort(order);
    struct Result {
      Term leaf = 0;
      bool bit = false;
    };
    llvm::DenseMap<Term, Result> values;
    for (unsigned assignment = 0; assignment < (1u << variables.size());
         ++assignment) {
      for (Term id : order) {
        if (!charge())
          return false;
        const auto &n = nodes[id];
        if (auto found = variables.find(id); found != variables.end()) {
          values[id] = {0, bool((assignment >> found->second) & 1)};
        } else if (auto bit = constant(id)) {
          values[id] = {0, *bit};
        } else if (selection(id)) {
          values[id] = values.lookup(
              n.operands[values.lookup(n.operands[0]).bit ? 1 : 2]);
        } else if (booleanOperator(id)) {
          bool x = values.lookup(n.operands[0]).bit;
          bool y = values.lookup(n.operands[1]).bit;
          bool bit;
          StringRef name = n.name.getValue();
          if (name == "arith.andi")
            bit = x && y;
          else if (name == "arith.ori")
            bit = x || y;
          else if (name == "arith.xori")
            bit = x != y;
          else {
            auto predicate =
                n.attributes.getAs<arith::CmpIPredicateAttr>("predicate");
            if (!predicate)
              return false;
            switch (predicate.getValue()) {
            case arith::CmpIPredicate::eq:
              bit = x == y;
              break;
            case arith::CmpIPredicate::ne:
              bit = x != y;
              break;
            case arith::CmpIPredicate::slt:
              bit = x && !y;
              break;
            case arith::CmpIPredicate::sle:
              bit = x || !y;
              break;
            case arith::CmpIPredicate::sgt:
              bit = !x && y;
              break;
            case arith::CmpIPredicate::sge:
              bit = !x || y;
              break;
            case arith::CmpIPredicate::ult:
              bit = !x && y;
              break;
            case arith::CmpIPredicate::ule:
              bit = !x || y;
              break;
            case arith::CmpIPredicate::ugt:
              bit = x && !y;
              break;
            case arith::CmpIPredicate::uge:
              bit = x || !y;
              break;
            }
          }
          values[id] = {0, bit};
        } else {
          values[id] = {id, false};
        }
      }
      auto x = values.lookup(a), y = values.lookup(b);
      if (x.leaf != y.leaf || x.bit != y.bit)
        return false;
    }
    return true;
  }
  bool equal(Term a, Term b) {
    using Pair = std::pair<Term, Term>;
    struct Frame {
      Pair pair;
      bool children = false;
    };
    SmallVector<Frame> pending{{{a, b}, false}};
    llvm::DenseMap<Pair, bool> checked;
    while (!pending.empty()) {
      if (!charge())
        return false;
      auto pair = pending.back().pair;
      auto [x, y] = pair;
      if (checked.contains(pair)) {
        pending.pop_back();
        continue;
      }
      if (!x || !y || nodes[x].type != nodes[y].type) {
        checked[pair] = false;
        pending.pop_back();
        continue;
      }
      if (x == y) {
        checked[pair] = true;
        pending.pop_back();
        continue;
      }
      const auto &left = nodes[x], &right = nodes[y];
      bool matching = left.name && left.name == right.name &&
                      left.attributes == right.attributes &&
                      left.coordinate == right.coordinate &&
                      left.operands.size() == right.operands.size();
      if (matching && !pending.back().children) {
        pending.back().children = true;
        for (auto [u, v] : zip(left.operands, right.operands))
          if (!checked.contains({u, v}))
            pending.push_back({{u, v}, false});
        continue;
      }
      bool same = matching;
      if (matching)
        for (auto [u, v] : zip(left.operands, right.operands))
          same &= checked.lookup({u, v});
      // Try a decision only after structural congruence reaches a mismatch.
      // Leaves first preserve correlations across shared subexpressions.
      // Cutting shared cones is a conservative fallback for larger problems.
      if (!same &&
          (left.type.isSignlessInteger(1) || selection(x) || selection(y)))
        same = decision(x, y, false) || (!exhausted && decision(x, y, true));
      checked[pair] = same;
      pending.pop_back();
    }
    return checked.lookup({a, b});
  }
};

ValueCorrespondence::ValueCorrespondence(Operation *op, bool roleComponents)
    : implementation(std::make_unique<Implementation>(op, roleComponents)) {}
ValueCorrespondence::~ValueCorrespondence() = default;
ValueCorrespondence::Environment ValueCorrespondence::environment() {
  auto id = implementation->scopes.size();
  implementation->scopes.emplace_back();
  return id;
}
ValueCorrespondence::Term ValueCorrespondence::anchor(Type type) {
  auto &p = *implementation;
  if (!p.charge())
    return 0;
  Term id = p.nodes.size();
  p.nodes.push_back({type, {}, {}, {}});
  return id;
}
ValueCorrespondence::Term
ValueCorrespondence::restrictRoles(Term input, Type type, ArrayAttr roles) {
  auto &p = *implementation;
  SmallVector<Attribute> owners(roles.begin(), roles.end());
  llvm::sort(owners, [](Attribute a, Attribute b) {
    return cast<StringAttr>(a).getValue() < cast<StringAttr>(b).getValue();
  });
  return p.expression("protocol.restrict_roles", type,
                      p.builder.getDictionaryAttr({p.builder.getNamedAttr(
                          "roles", p.builder.getArrayAttr(owners))}),
                      0, {input});
}
void ValueCorrespondence::roleMap(Environment env, ArrayAttr from,
                                  ArrayAttr to) {
  for (auto [a, b] : zip(from, to))
    implementation->scopes[env].roles[cast<StringAttr>(a).getValue()] = b;
}
void ValueCorrespondence::roleComponent(Environment env, StringAttr role) {
  implementation->scopes[env].component = role;
}
void ValueCorrespondence::bind(Environment env, Value value, Term term) {
  implementation->scopes[env].values[value] = term;
}
ValueCorrespondence::Term ValueCorrespondence::value(Environment env,
                                                     Value root) {
  auto &p = *implementation;
  struct Visit {
    Environment env;
    Value value;
  };
  SmallVector<Visit> pending{{env, root}};
  while (!pending.empty()) {
    if (!p.charge())
      return 0;
    auto [scope, current] = pending.back();
    if (p.scopes[scope].values.contains(current)) {
      pending.pop_back();
      continue;
    }
    auto *op = current.getDefiningOp();
    if (!op ||
        (!isTotal(op) && !isa<func::CallOp, protocol_ir::RestrictRolesOp>(op)))
      return 0;
    bool ready = true;
    for (Value input : op->getOperands()) {
      if (!p.charge())
        return 0;
      if (!p.scopes[scope].values.contains(input)) {
        pending.push_back({scope, input});
        ready = false;
      }
    }
    if (!ready)
      continue;
    SmallVector<Term> inputs;
    for (Value input : op->getOperands())
      inputs.push_back(p.scopes[scope].values.lookup(input));
    Term result = 0;
    if (auto call = dyn_cast<func::CallOp>(op)) {
      auto helper = p.symbols.lookupNearestSymbolFrom<func::FuncOp>(
          call, call.getCalleeAttr());
      if (!helper || helper.empty())
        return 0;
      Environment nested;
      if (auto found = p.scopes[scope].helpers.find(op);
          found != p.scopes[scope].helpers.end()) {
        nested = found->second;
      } else {
        nested = environment();
        p.scopes[scope].helpers[op] = nested;
        for (auto [arg, input] : zip(helper.getArguments(), inputs))
          bind(nested, arg, input);
      }
      Value returned = helper.front().back().getOperand(
          cast<OpResult>(current).getResultNumber());
      if (!p.scopes[nested].values.contains(returned)) {
        pending.push_back({nested, returned});
        continue;
      }
      result = p.scopes[nested].values.lookup(returned);
    } else if (auto restriction = dyn_cast<protocol_ir::RestrictRolesOp>(op);
               restriction && p.roleComponents) {
      if (!p.scopes[scope].component ||
          !is_contained(restriction.getRoles(), p.scopes[scope].component))
        return 0;
      result = inputs[0];
    } else {
      auto attributes = op->getAttrDictionary();
      if (auto restriction = dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
        SmallVector<Attribute> owners;
        for (auto role : restriction.getRoles()) {
          auto mapped =
              p.scopes[scope].roles.lookup(cast<StringAttr>(role).getValue());
          owners.push_back(mapped ? mapped : role);
        }
        result = restrictRoles(inputs[0], current.getType(),
                               p.builder.getArrayAttr(owners));
      } else {
        result = p.expression(
            op->getName().getStringRef(), current.getType(), attributes,
            cast<OpResult>(current).getResultNumber(), inputs);
      }
    }
    if (!result)
      return 0;
    bind(scope, current, result);
    pending.pop_back();
  }
  return p.scopes[env].values.lookup(root);
}
ValueCorrespondence::Expression
ValueCorrespondence::expression(Term term) const {
  return implementation->nodes[term];
}
ValueCorrespondence::Term
ValueCorrespondence::expression(StringRef name, Type type,
                                DictionaryAttr attributes,
                                ArrayRef<Term> inputs, unsigned coordinate) {
  return implementation->expression(name, type, attributes, coordinate, inputs);
}
bool ValueCorrespondence::equal(Term a, Term b) {
  auto &p = *implementation;
  if (p.equal(a, b))
    return true;
  if (!a || !b || p.exhausted)
    return false;
  auto fixedLeft = normalizePolynomialFixings(*this, a, p.polynomialFixings);
  auto fixedRight = normalizePolynomialFixings(*this, b, p.polynomialFixings);
  if (p.equal(fixedLeft, fixedRight))
    return true;
  if (p.exhausted)
    return false;
  auto left = normalizePolynomialValues(*this, a, p.polynomialNormalForms);
  auto right = normalizePolynomialValues(*this, b, p.polynomialNormalForms);
  return p.equal(left, right);
}
bool ValueCorrespondence::compare(Environment a, Value x, Environment b,
                                  Value y) {
  return equal(value(a, x), value(b, y));
}
bool ValueCorrespondence::charge(size_t amount) {
  return implementation->charge(amount);
}
LogicalResult ValueCorrespondence::refuse(StringRef detail) {
  return diagnostics::emit(implementation->diagnostic->emitOpError(),
                           implementation->exhausted
                               ? "mathematical-correspondence-limit"
                               : "mathematical-correspondence",
                           detail);
}
} // namespace zkc::mathematical
