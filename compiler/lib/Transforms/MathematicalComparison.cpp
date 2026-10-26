#include "MathematicalComparison.h"
#include "ScopedCandidate.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MathExtras.h"
#include <map>
#include <optional>
#include <set>
#include <tuple>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// Read the actual admitted call target, including an owned numerical unit.
// This reader never uses the producer's substituted callback or normalization.
Operation *sourceCallee(Operation *op) {
  if (auto call = dyn_cast<exec::ComputeOp>(op)) {
    if (auto policy = call.getPolicyAttr())
      if (policy.size() != 3 || !isa<BoolAttr>(policy[0]) ||
          !isa<BoolAttr>(policy[1]) || !isa<BoolAttr>(policy[2]) ||
          !cast<BoolAttr>(policy[0]).getValue())
        return nullptr;
    SymbolTableCollection symbols;
    return call.resolveCallee(symbols);
  }
  if (auto call = dyn_cast<kernel::CallOp>(op)) {
    if (auto policy = call.getPolicyAttr())
      if (policy.size() != 3 || !isa<BoolAttr>(policy[0]) ||
          !isa<BoolAttr>(policy[1]) || !isa<BoolAttr>(policy[2]) ||
          !cast<BoolAttr>(policy[0]).getValue())
        return nullptr;
    SymbolTableCollection symbols;
    return kernel::resolve(call, symbols);
  }
  auto reference = op->getAttrOfType<FlatSymbolRefAttr>("callee");
  return reference ? SymbolTable::lookupNearestSymbolFrom(op, reference)
                   : nullptr;
}

using Term = uint32_t;
constexpr Term invalidTerm = UINT32_MAX;

// Admission retains the original DAG, including unused operations and neutral
// operands. Normal forms are separate exact keys, never hashes. AC operands
// form persistent binary tries keyed by normal-form ID, with exact counts:
// extending a chain shares its prefixes, and doubling a DAG never unfolds it.
class Terms {
  uint64_t &remaining;
  ComparisonCapacity capacity = ComparisonCapacity::None;
  std::optional<CapacityCause> debit;
  std::vector<ring::Input> inputs;
  std::vector<ring::Node> nodes;
  std::map<std::tuple<ring::Kind, std::string, std::string, Term, Term, Term>,
           Term>
      shared;
  std::map<std::pair<std::string, std::vector<uint64_t>>, Term> atoms;
  std::vector<unsigned> depths;
  std::vector<Term> normalized;
  struct Normal {
    ring::Kind kind;
    Term value; // Original leaf, normalized negand, or operand trie.
  };
  std::vector<Normal> forms;
  std::map<std::pair<ring::Kind, Term>, Term> sharedForms;
  // A depth-d binary DAG has at most 2^(d-1) unfolded leaves. The extra bit
  // makes overflow detectable; counts are never reduced modulo the field.
  static constexpr unsigned countBits = ring::Limits::depth + 1;
  struct OperandSet {
    Term first, left, right;
    unsigned height;
    APInt count;
  };
  struct CountLess {
    bool operator()(const std::pair<Term, APInt> &left,
                    const std::pair<Term, APInt> &right) const {
      if (left.first != right.first)
        return left.first < right.first;
      if (left.second.getBitWidth() != right.second.getBitWidth())
        return left.second.getBitWidth() < right.second.getBitWidth();
      return left.second.ult(right.second);
    }
  };
  std::vector<OperandSet> sets;
  std::map<std::pair<Term, APInt>, Term, CountLess> leaves;
  std::map<std::pair<Term, Term>, Term> branches, unions;
  bool valid = true, neutralLaws = false;

  Term insert(ring::Node node) {
    if (!charge())
      return invalidTerm;
    auto key = std::make_tuple(node.kind, node.field, node.constant, node.left,
                               node.right, node.input);
    auto found = shared.find(key);
    if (found != shared.end())
      return found->second;
    unsigned depth = 1;
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul)
      depth += std::max(depths[node.left], depths[node.right]);
    else if (node.kind == ring::Kind::Neg)
      depth += depths[node.left];
    if (nodes.size() >= ring::Limits::nodes) {
      exhaust(ComparisonCapacity::Nodes);
      return invalidTerm;
    }
    if (depth > ring::Limits::depth) {
      exhaust(ComparisonCapacity::Depth);
      return invalidTerm;
    }
    Term result = nodes.size();
    nodes.push_back(std::move(node));
    depths.push_back(depth);
    normalized.push_back(invalidTerm);
    shared.emplace(std::move(key), result);
    return result;
  }

  Term form(ring::Kind kind, Term value) {
    if (value == invalidTerm || !charge())
      return invalidTerm;
    auto key = std::make_pair(kind, value);
    auto [found, inserted] = sharedForms.try_emplace(key, forms.size());
    if (inserted)
      forms.push_back({kind, value});
    return found->second;
  }
  Term leaf(Term operand, APInt count) {
    // Store only significant words. Small formulas should not pay for the
    // worst-case multiplicity of a depth-limit doubling DAG at every leaf.
    count = count.zextOrTrunc(std::max(1u, count.getActiveBits()));
    if (!charge(count.getNumWords()))
      return invalidTerm;
    auto key = std::make_pair(operand, count);
    auto [found, inserted] = leaves.try_emplace(key, sets.size());
    if (inserted)
      sets.push_back({operand, invalidTerm, invalidTerm, 0, count});
    return found->second;
  }
  Term branch(Term left, Term right) {
    if (left == invalidTerm || right == invalidTerm || !charge())
      return invalidTerm;
    if (sets[right].first < sets[left].first)
      std::swap(left, right);
    auto key = std::make_pair(left, right);
    auto [found, inserted] = branches.try_emplace(key, sets.size());
    if (inserted) {
      unsigned height = Log2_32(sets[left].first ^ sets[right].first) + 1;
      sets.push_back({sets[left].first, left, right, height, APInt(1, 0)});
    }
    return found->second;
  }
  Term unite(Term left, Term right) {
    if (left == invalidTerm || right == invalidTerm || !charge())
      return invalidTerm;
    if (right < left)
      std::swap(left, right);
    auto key = std::make_pair(left, right);
    if (auto found = unions.find(key); found != unions.end())
      return found->second;
    // Recursive calls may reallocate sets. Retain values, never references.
    auto a = sets[left], b = sets[right];
    Term result;
    if (!a.height && !b.height && a.first == b.first) {
      unsigned width =
          std::max(a.count.getBitWidth(), b.count.getBitWidth()) + 1;
      if (!charge((width + 63) / 64))
        return invalidTerm;
      auto count = a.count.zext(width) + b.count.zext(width);
      if (count.getActiveBits() > countBits) {
        exhaust(ComparisonCapacity::Multiplicity);
        return invalidTerm;
      }
      result = leaf(a.first, count);
    } else {
      unsigned difference = a.first ^ b.first;
      unsigned height = difference ? Log2_32(difference) + 1 : 0;
      if (height > std::max(a.height, b.height))
        result = branch(left, right);
      else if (a.height == b.height) {
        Term low = unite(a.left, b.left);
        Term high = unite(a.right, b.right);
        result = branch(low, high);
      } else {
        if (a.height < b.height) {
          std::swap(a, b);
          std::swap(left, right);
        }
        if ((b.first >> (a.height - 1)) & 1)
          result = branch(a.left, unite(a.right, right));
        else
          result = branch(unite(a.left, right), a.right);
      }
    }
    if (result != invalidTerm)
      unions.emplace(key, result);
    return result;
  }
  bool neutral(Term value, ring::Kind kind) const {
    const auto normal = forms[value];
    return neutralLaws && normal.kind == ring::Kind::Constant &&
           nodes[normal.value].constant ==
               (kind == ring::Kind::Add ? "0" : "1");
  }
  Term operands(Term value, ring::Kind kind) {
    return forms[value].kind == kind ? forms[value].value
                                     : leaf(value, APInt(1, 1));
  }

public:
  explicit Terms(uint64_t &remaining) : remaining(remaining) {}
  ComparisonCapacity exhausted() const { return capacity; }
  std::optional<CapacityCause> failedDebit() const { return debit; }
  bool exhaust(ComparisonCapacity reason) {
    if (capacity == ComparisonCapacity::None)
      capacity = reason;
    valid = false;
    return false;
  }
  bool withinDepth(unsigned depth, ComparisonCapacity reason) {
    return depth <= 64 || exhaust(reason);
  }
  // Retain the evidence status at the caller's exact allowance, including a
  // successful proof that spends its final unit and structural exhaustion.
  template <typename Query> bool evidence(Query query) {
    auto status = query(remaining);
    if (status == facts::Status::Capacity)
      return exhaust(ComparisonCapacity::Work);
    return status == facts::Status::Proven;
  }
  void useNeutralLaws() { neutralLaws = true; }
  bool charge(uint64_t work = 1) {
    if (remaining < work) {
      if (!debit)
        debit = CapacityCause{WorkOwner::OptionalComparison, work, remaining};
      remaining = 0;
      return exhaust(ComparisonCapacity::Work);
    }
    remaining -= work;
    return true;
  }
  Term atom(StringRef field, std::vector<uint64_t> meaning) {
    auto key = std::make_pair(field.str(), std::move(meaning));
    auto found = atoms.find(key);
    if (found != atoms.end())
      return found->second;
    if (inputs.size() >= ring::Limits::inputs) {
      exhaust(ComparisonCapacity::Inputs);
      return invalidTerm;
    }
    Term result = insert(ring::Node::slot(inputs.size()));
    if (result == invalidTerm)
      return invalidTerm;
    inputs.push_back({field.str()});
    atoms.emplace(std::move(key), result);
    return result;
  }
  Term literal(StringRef field, StringRef value) {
    return insert(ring::Node::literal(field.str(), value.str()));
  }
  Term binary(ring::Kind kind, Term left, Term right) {
    if (left == invalidTerm || right == invalidTerm)
      return invalidTerm;
    return insert(kind == ring::Kind::Add ? ring::Node::add(left, right)
                                          : ring::Node::mul(left, right));
  }
  Term neg(Term operand) {
    return operand == invalidTerm ? invalidTerm
                                  : insert(ring::Node::neg(operand));
  }
  Term arithmetic(StringRef contract, Term left, Term right) {
    if (left == invalidTerm || right == invalidTerm)
      return invalidTerm;
    if (contract.ends_with(".sub"))
      right = insert(ring::Node::neg(right));
    return binary(contract.ends_with(".mul") || contract == "vector.scale"
                      ? ring::Kind::Mul
                      : ring::Kind::Add,
                  left, right);
  }
  // Normal IDs are only meaningful in this invocation. Raw terms remain the
  // operands of subsequent instructions, preserving their original depth.
  Term canonical(Term value) {
    if (value == invalidTerm || !valid)
      return invalidTerm;
    if (normalized[value] != invalidTerm)
      return normalized[value];
    if (!charge())
      return invalidTerm;
    const auto node = nodes[value];
    Term result;
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
      Term left = canonical(node.left), right = canonical(node.right);
      if (left == invalidTerm || right == invalidTerm)
        return invalidTerm;
      if (neutral(left, node.kind))
        result = right;
      else if (neutral(right, node.kind))
        result = left;
      else {
        Term a = operands(left, node.kind), b = operands(right, node.kind);
        result = form(node.kind, unite(a, b));
      }
    } else if (node.kind == ring::Kind::Neg) {
      Term operand = canonical(node.left);
      if (operand == invalidTerm)
        return invalidTerm;
      result = neutral(operand, ring::Kind::Add) ? operand
                                                 : form(node.kind, operand);
    } else
      result = form(node.kind, value);
    normalized[value] = result;
    return result;
  }
  bool equal(Term left, Term right) {
    if (left == invalidTerm || right == invalidTerm || !valid)
      return false;
    if (left == right)
      return true;
    Term a = canonical(left), b = canonical(right);
    return a != invalidTerm && b != invalidTerm && a == b;
  }
  bool contains(Term term, Term sought, std::map<Term, bool> &memo) {
    if (auto found = memo.find(term); found != memo.end())
      return found->second;
    if (!charge() || term == invalidTerm)
      return true;
    if (equal(term, sought))
      return memo[term] = true;
    auto node = nodes[term];
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul)
      return memo[term] = contains(node.left, sought, memo) ||
                          contains(node.right, sought, memo);
    return memo[term] = node.kind == ring::Kind::Neg &&
                        contains(node.left, sought, memo);
  }
  std::optional<std::pair<ring::Kind, Term>> reduction(Term value, Term state) {
    Term normal = canonical(value);
    if (normal == invalidTerm)
      return std::nullopt;
    auto kind = forms[normal].kind;
    if (kind != ring::Kind::Add && kind != ring::Kind::Mul)
      return std::nullopt;
    // Remove exactly one top-level state occurrence while retaining the DAG.
    // Memoization counts a shared state on every incoming edge, but never
    // enumerates the exponentially many leaves of a shared payload.
    using Part = std::pair<bool, Term>;
    std::map<Term, Part> parts;
    std::map<Term, bool> dependencies;
    auto split = [&](auto &&self, Term term) -> std::optional<Part> {
      if (!charge())
        return std::nullopt;
      if (auto found = parts.find(term); found != parts.end())
        return found->second;
      Part result;
      if (equal(term, state))
        result = {true, invalidTerm};
      else if (!contains(term, state, dependencies))
        result = {false, term};
      else {
        const auto node = nodes[term];
        if (node.kind != kind) {
          // Neutral wrappers may expose the same associative operation.
          if ((node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) &&
              equal(term, node.left))
            return self(self, node.left);
          if ((node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) &&
              equal(term, node.right))
            return self(self, node.right);
          return std::nullopt;
        }
        auto left = self(self, node.left), right = self(self, node.right);
        if (!left || !right || (left->first && right->first))
          return std::nullopt;
        Term payload = left->second == invalidTerm ? right->second
                       : right->second == invalidTerm
                           ? left->second
                           : binary(kind, left->second, right->second);
        result = {left->first || right->first, payload};
      }
      parts.emplace(term, result);
      return result;
    };
    auto result = split(split, value);
    if (!result || !result->first || result->second == invalidTerm || !valid)
      return std::nullopt;
    return std::make_pair(kind, result->second);
  }
  bool admit() {
    if (!valid || nodes.empty())
      return false;
    // Sink outputs retain all constructed nodes, so an invalid unused literal
    // or a field mismatch cannot disappear during liveness pruning.
    std::vector<bool> used(nodes.size(), false);
    for (const auto &node : nodes) {
      if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
        used[node.left] = true;
        used[node.right] = true;
      } else if (node.kind == ring::Kind::Neg)
        used[node.left] = true;
    }
    std::vector<Term> outputs;
    for (Term i = 0; i < nodes.size(); ++i)
      if (!used[i])
        outputs.push_back(i);
    if (outputs.size() > ring::Limits::outputs)
      return exhaust(ComparisonCapacity::Outputs);
    if (!charge(nodes.size()))
      return false;
    auto expression = ring::Expression::create(inputs, nodes, outputs);
    if (!expression) {
      handleAllErrors(expression.takeError(), [&](const zkc::Refusal &error) {
        if (error.code == "ring-limit")
          exhaust(ComparisonCapacity::Encoding);
        else if (error.code == "ring-depth")
          exhaust(ComparisonCapacity::Depth);
      });
      return false;
    }
    return true;
  }
};

// A bounded borrowed view of actual source instructions. Scoped association
// only recovers data ports from admitted CFG edges; it supplies no equations,
// recipe choices or projected producer IR. Pure callees retain raw SSA ports.
struct SourceInstruction {
  Operation *operation;
  ValueRange inputs, outputs;
  const protocol::SourceExecutionStep *scoped = nullptr;
};
struct SourceBody {
  ValueRange arguments, returned;
  SmallVector<SourceInstruction> payload;
  Block *plain = nullptr;
  Operation *owner = nullptr;
  ArrayRef<protocol::SourceExecutionStep> scoped;
  bool read(Block &block, const protocol::SourceExecutionClosure *closure) {
    owner = block.getParentOp();
    auto function = dyn_cast<func::FuncOp>(block.getParentOp());
    if (function && protocol::isScopedExecutionFunction(function)) {
      if (!closure || function.empty() || &function.front() != &block ||
          function->hasAttr("runtime.region"))
        return false;
      auto found = closure->bodies.find(function.getSymName().str());
      if (found == closure->bodies.end() || found->second.empty())
        return false;
      scoped = found->second;
      if (!isa<exec::ReturnOp>(scoped.back().operation))
        return false;
      arguments = block.getArguments().drop_front();
      returned = scoped.back().inputs;
    } else {
      if (!block.getParent()->hasOneBlock() || block.empty() ||
          !isa<func::ReturnOp, local::ReturnOp>(block.back()) ||
          !block.back().getAttrs().empty())
        return false;
      plain = &block;
      arguments = block.getArguments();
      returned = block.back().getOperands();
    }
    return true;
  }
  // Memoized calls have already interpreted every instruction under this
  // exact assignment. Charge and materialize payload only on a cache miss.
  bool visit(Terms &work) {
    if (plain) {
      for (Operation &op : plain->without_terminator()) {
        if (!work.charge(1 + op.getNumOperands() + op.getNumResults()))
          return false;
        payload.push_back({&op, op.getOperands(), op.getResults()});
      }
    } else {
      for (const auto &step : scoped) {
        if (!work.charge(1 + step.inputs.size() + step.outputs.size()) ||
            step.operation->getParentOp() != owner || !step.regions.empty())
          return false;
        if (&step != &scoped.back())
          payload.push_back({step.operation, step.inputs, step.outputs, &step});
      }
    }
    return true;
  }
};

struct Primitive {
  StringRef contract;
  SmallVector<StringRef> parameters;
  runtime::BindingOp binding;
};
// Read the actual operation and independently resolve its installed signature.
// Explicit implementations are outside the law-replacement boundary.
std::optional<Primitive>
primitive(Operation &op, SymbolTable *symbols,
          CandidatePorts ports = CandidatePorts{},
          const protocol::SourceExecutionStep *source = nullptr,
          const llvm::DenseSet<Operation *> *fixedBindings = nullptr) {
  auto inputs = source ? ValueRange(source->inputs) : ports.inputs(&op);
  auto outputs = source ? ValueRange(source->outputs) : ports.outputs(&op);
  bool scoped = source || ports.isScoped();
  auto reference = op.getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding =
      reference
          ? dyn_cast_or_null<runtime::BindingOp>(
                symbols ? symbols->lookup(reference.getValue())
                        : SymbolTable::lookupNearestSymbolFrom(&op, reference))
          : runtime::BindingOp();
  auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
  if (!binding || !binding.getImplementation().empty() ||
      (fixedBindings && fixedBindings->contains(binding)) || !parameters ||
      !op.getAttrOfType<StringAttr>("site") || op.getAttrs().size() != 3 ||
      (!source && !ports.contains(&op)) ||
      (source ? !source->regions.empty() : ports.bodies(&op) != 0) ||
      outputs.size() != 1 ||
      (scoped ? !isa<exec::ApplyOp>(op)
              : !protocol::operationSupportsContract(
                    op.getName().getStringRef(), binding.getContract())))
    return std::nullopt;
  auto decoded = protocol::readBinding(binding);
  if (!decoded) {
    consumeError(decoded.takeError());
    return std::nullopt;
  }
  auto signature = protocol::resolveBinding(decoded->application, false);
  if (!signature) {
    consumeError(signature.takeError());
    return std::nullopt;
  }
  if (signature->inputs.size() != inputs.size() ||
      signature->outputs.size() != 1)
    return std::nullopt;
  for (auto [expected, actual] : zip(signature->inputs, inputs.getTypes()))
    if (protocol::decodeBoundType(op.getContext(), expected) != actual)
      return std::nullopt;
  if (protocol::decodeBoundType(op.getContext(), signature->outputs[0]) !=
      outputs[0].getType())
    return std::nullopt;
  Primitive result{binding.getContract(), {}, binding};
  for (Attribute parameter : parameters) {
    auto text = dyn_cast<StringAttr>(parameter);
    if (!text)
      return std::nullopt;
    result.parameters.push_back(text.getValue());
  }
  std::vector<std::string> arguments;
  for (StringRef parameter : result.parameters)
    arguments.push_back(parameter.str());
  if (auto error = protocol::checkParameters(decoded->application, arguments)) {
    consumeError(std::move(error));
    return std::nullopt;
  }
  return result;
}

bool fieldArithmetic(StringRef contract) {
  return contract == "field.add" || contract == "field.sub" ||
         contract == "field.mul";
}
bool laneArithmetic(StringRef contract) {
  return contract == "vector.add" || contract == "vector.sub" ||
         contract == "vector.mul" || contract == "vector.scale";
}
bool candidateContract(StringRef contract) {
  return protocol::numericalContract(contract) || fieldArithmetic(contract) ||
         laneArithmetic(contract) || contract == "field.constant" ||
         contract == "vector.fill" || contract == "vector.sum" ||
         contract == "vector.product" || contract == "vector.dot" ||
         contract == "matrix.row_dot" || contract == "matrix.column_dot" ||
         contract == "matrix.bilinear";
}
algebra::FieldType scalarField(Type type) {
  if (isa<algebra::FieldVectorType, algebra::FieldMatrixType,
          algebra::FieldArrayType>(type))
    type = cast<CollectionTypeInterface>(type).getElementType();
  return dyn_cast<algebra::FieldType>(type);
}
bool vectorType(Type type) { return isa<algebra::FieldVectorType>(type); }

// Index terms distinguish each product coordinate from a captured selector.
// SSA identities are invocation-local; source captures are assigned to actual
// candidate inputs before constructing any term.
struct Index {
  bool varying = false;
  unsigned identity = 0;
  bool operator==(const Index &other) const {
    return varying == other.varying && identity == other.identity;
  }
};
struct Meaning {
  enum Kind {
    Unknown,
    Scalar,
    Lane,
    Container,
    Position,
    Array
  } kind = Unknown;
  Term term = invalidTerm;
  Value container = {};
  Index index = {};
  unsigned axis = 0;
};
struct Extent {
  Value container;
  unsigned axis = 0;
  bool operator==(const Extent &other) const {
    return container == other.container && axis == other.axis;
  }
};
struct Dimension {
  SmallVector<Extent> equal;
};

class Comparison {
  Terms terms;
  SymbolTable &symbols;
  CandidatePorts ports;
  const protocol::SourceExecutionClosure *sourceClosure = nullptr;
  const llvm::DenseSet<Operation *> *fixedBindings = nullptr;
  llvm::DenseSet<Operation *> usedBindings;
  llvm::DenseMap<Value, unsigned> identities;
  SmallVector<Dimension> dimensions;
  SmallVector<SmallVector<Meaning>> arrays;
  std::set<std::tuple<unsigned, unsigned, unsigned>> selectedBounds;
  llvm::DenseMap<Value, Meaning> candidate;
  Value rows;
  llvm::DenseMap<Block *, std::map<std::vector<uint64_t>, SmallVector<Meaning>>>
      helpers;
  // Exact argument meanings of the original callback, retained while reading
  // its call closure. Callee substitution does not change this fact scope.
  // In particular, these are not the finite occurrence's caller assumptions.
  SmallVector<std::pair<Value, Meaning>> rootArguments;

  bool rootEqualExtent(Value container, unsigned axis, Extent other) {
    for (const auto &[source, meaning] : rootArguments) {
      if (!terms.charge())
        return false;
      if (meaning.kind != Meaning::Container || meaning.container != container)
        continue;
      for (const auto &[otherSource, otherMeaning] : rootArguments) {
        if (!terms.charge())
          return false;
        if (otherMeaning.kind == Meaning::Container &&
            otherMeaning.container == other.container &&
            terms.evidence(
                [&, left = source, right = otherSource](uint64_t &work) {
                  return finite::equalExtentStatus(left, axis, right,
                                                   other.axis, work);
                }))
          return true;
      }
    }
    return false;
  }
  unsigned identity(Value value) {
    auto [found, inserted] = identities.try_emplace(value, identities.size());
    return found->second;
  }
  Meaning input(Value value) {
    if (auto field = dyn_cast<algebra::FieldType>(value.getType()))
      return {Meaning::Scalar,
              terms.atom(field.getDomain(), {0, identity(value)})};
    if (value.getType().isUnsignedInteger(64))
      return {Meaning::Position, invalidTerm, {}, {false, identity(value)}};
    return {Meaning::Container, invalidTerm, value};
  }
  bool extentIs(Value container, unsigned axis, unsigned dimension) const {
    return dimension < dimensions.size() &&
           is_contained(dimensions[dimension].equal, Extent{container, axis});
  }
  Meaning access(Value container, ArrayRef<Index> indices) {
    auto field = scalarField(container.getType());
    if (!field)
      return {};
    std::vector<uint64_t> key{1, identity(container), indices.size()};
    bool varying = false;
    unsigned dimension = 0;
    for (Index index : indices) {
      key.push_back(index.varying);
      key.push_back(index.identity);
      if (index.varying) {
        varying = true;
        dimension = index.identity;
      }
    }
    return {varying ? Meaning::Lane : Meaning::Scalar,
            terms.atom(field.getDomain(), std::move(key)),
            {},
            {},
            dimension};
  }
  Term aggregate(StringRef field, ring::Kind combine, Term payload) {
    payload = terms.canonical(payload);
    return payload == invalidTerm
               ? invalidTerm
               : terms.atom(field, {combine == ring::Kind::Add ? 2u : 3u,
                                    dimensions.size(), payload});
  }
  Meaning arithmetic(StringRef contract, Meaning left, Meaning right) {
    if ((left.kind != Meaning::Scalar && left.kind != Meaning::Lane) ||
        (right.kind != Meaning::Scalar && right.kind != Meaning::Lane))
      return {};
    auto term = terms.arithmetic(contract, left.term, right.term);
    return {left.kind == Meaning::Lane || right.kind == Meaning::Lane
                ? Meaning::Lane
                : Meaning::Scalar,
            term,
            {},
            {},
            left.kind == Meaning::Lane ? left.axis : right.axis};
  }
  std::optional<SmallVector<Meaning>>
  readSource(Block &block, ArrayRef<Meaning> inputs, unsigned depth = 0) {
    SourceBody body;
    if (!terms.charge(inputs.size() + 1) ||
        !terms.withinDepth(depth, ComparisonCapacity::HelperDepth) ||
        !body.read(block, sourceClosure) ||
        inputs.size() != body.arguments.size())
      return {};
    if (depth == 0) {
      rootArguments.clear();
      for (auto [argument, meaning] : zip(body.arguments, inputs))
        rootArguments.emplace_back(argument, meaning);
    }
    std::vector<uint64_t> key;
    for (const Meaning &value : inputs) {
      key.insert(key.end(),
                 {uint64_t(value.kind), value.term,
                  value.container ? identity(value.container) + 1u : 0u,
                  value.index.varying, value.index.identity, value.axis});
    }
    auto &memo = helpers[&block];
    if (auto found = memo.find(key); found != memo.end())
      return found->second;
    if (!body.visit(terms))
      return {};
    // Extent evidence consumes bounded work while visiting these entries.
    // Preserve source order so pointer hashes cannot change which proof fits.
    llvm::MapVector<Value, Meaning> values;
    for (auto [argument, meaning] : zip(body.arguments, inputs))
      values[argument] = meaning;
    for (const auto &step : body.payload) {
      Operation &op = *step.operation;
      auto operands = step.inputs;
      auto outputs = step.outputs;
      if (!terms.charge() || op.getNumRegions())
        return {};
      Meaning result;
      // Calls are interpreted from actual retained bodies, with exact operand
      // assignments and a shared work/depth bound, including unused calls.
      if (isa<func::CallOp, local::ApplyOp, kernel::CallOp, exec::ComputeOp>(
              op)) {
        auto *helper = sourceCallee(&op);
        if (!helper || !isa<func::FuncOp, local::FuncOp>(helper) ||
            helper->getNumRegions() != 1 || helper->getRegion(0).empty())
          return {};
        SmallVector<Meaning> arguments;
        for (Value operand : operands) {
          auto found = values.find(operand);
          if (found == values.end())
            return {};
          arguments.push_back(found->second);
        }
        auto returned =
            readSource(helper->getRegion(0).front(), arguments, depth + 1);
        if (!returned || returned->size() != outputs.size())
          return {};
        for (auto [value, meaning] : zip(outputs, *returned))
          values[value] = meaning;
        continue;
      } else if (auto pack = dyn_cast<algebra::ArrayFromElementsOp>(op)) {
        if (!op.getAttrs().empty() || arrays.size() >= invalidTerm ||
            !terms.charge(pack.getNumOperands() + 1))
          return {};
        SmallVector<Meaning> elements;
        for (Value operand : pack.getElements()) {
          auto element = values.lookup(operand);
          if (element.kind != Meaning::Scalar && element.kind != Meaning::Lane)
            return {};
          elements.push_back(element);
        }
        // Array identities are local to this reader. They retain every ordered
        // element meaning across calls; equal types or sizes never substitute
        // elements. This reader does not invoke the producer's MLIR fold.
        arrays.push_back(std::move(elements));
        result = {Meaning::Array, static_cast<Term>(arrays.size() - 1)};
      } else if (auto projection = dyn_cast<algebra::ArrayAtOp>(op)) {
        auto array = values.lookup(projection.getArray());
        auto index = projection.getIndexAttr().getInt();
        if (array.kind != Meaning::Array || index < 0 ||
            uint64_t(index) >= arrays[array.term].size())
          return {};
        result = arrays[array.term][index];
      } else {
        if (outputs.size() != 1)
          return {};
        StringRef contract;
        SmallVector<StringRef> parameters;
        if (algebra::isRingOperation(op)) {
          contract = isa<algebra::ConstantFieldOp>(op)   ? "field.constant"
                     : isa<algebra::FieldAddOp>(op)      ? "field.add"
                     : isa<algebra::SubtractFieldOp>(op) ? "field.sub"
                                                         : "field.mul";
          if (contract == "field.constant")
            parameters.push_back(
                op.getAttrOfType<StringAttr>("value").getValue());
        } else if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(op) &&
                   op.getAttrs().empty())
          contract = isa<data::BoundedAtOp>(op) ? "vector.get" : "matrix.get";
        else if (auto bound = primitive(op, nullptr, CandidatePorts{},
                                        step.scoped, fixedBindings)) {
          contract = bound->contract;
          parameters = bound->parameters;
        } else
          return {};
        if (contract == "field.constant") {
          auto field = dyn_cast<algebra::FieldType>(outputs[0].getType());
          if (!field || parameters.size() != 1 || operands.size())
            return {};
          result = {Meaning::Scalar,
                    terms.literal(field.getDomain(), parameters[0])};
        } else if (!parameters.empty())
          return {};
        else if (fieldArithmetic(contract) && operands.size() == 2)
          result = arithmetic(contract, values.lookup(operands[0]),
                              values.lookup(operands[1]));
        else if ((contract == "vector.get" && operands.size() == 2) ||
                 (contract == "matrix.get" && operands.size() == 3)) {
          auto container = values.lookup(operands[0]);
          if (container.kind != Meaning::Container)
            return {};
          SmallVector<Index> indices;
          for (Value operand : operands.drop_front()) {
            auto position = values.lookup(operand);
            if (position.kind != Meaning::Position)
              return {};
            indices.push_back(position.index);
          }
          for (auto [axis, index] : enumerate(indices)) {
            if (index.varying) {
              if (!extentIs(container.container, axis, index.identity)) {
                bool equal = false;
                // Read admitted helper extent premises through their actual
                // argument assignment. They equate lengths, never elements.
                for (auto &entry : values) {
                  if (equal)
                    break;
                  if (entry.second.kind == Meaning::Container)
                    for (Extent extent : dimensions[index.identity].equal)
                      if (terms.charge() &&
                          extent.container == entry.second.container &&
                          terms.evidence(
                              [&, selectedAxis = axis](uint64_t &work) {
                                return finite::equalExtentStatus(
                                    operands[0], selectedAxis, entry.first,
                                    extent.axis, work);
                              })) {
                        equal = true;
                        break;
                      }
                }
                if (!equal)
                  for (Extent extent : dimensions[index.identity].equal) {
                    if (rootEqualExtent(container.container, axis, extent)) {
                      equal = true;
                      break;
                    }
                  }
                if (!equal)
                  return {};
                dimensions[index.identity].equal.push_back(
                    {container.container, unsigned(axis)});
              }
            } else {
              auto key = std::make_tuple(identity(container.container),
                                         unsigned(axis), index.identity);
              if (!selectedBounds.count(key)) {
                // A captured selector may fail on a zero-trip source. Its
                // bound must already follow from source formation before an
                // eager scalar contraction is permitted.
                if (!terms.evidence([&, selectedAxis = axis](uint64_t &work) {
                      return finite::boundStatus(operands[selectedAxis + 1],
                                                 operands[0], selectedAxis,
                                                 work);
                    }))
                  return {};
                selectedBounds.insert(key);
              }
            }
          }
          result = access(container.container, indices);
        } else
          return {};
      }
      if (result.kind == Meaning::Unknown ||
          ((result.kind == Meaning::Scalar || result.kind == Meaning::Lane) &&
           result.term == invalidTerm))
        return {};
      values[outputs[0]] = result;
    }
    SmallVector<Meaning> result;
    for (Value value : body.returned) {
      auto found = values.find(value);
      if (found == values.end() || found->second.kind == Meaning::Unknown)
        return {};
      result.push_back(found->second);
    }
    // Cache only fully interpreted bodies, including every unused operation.
    // Re-find the block: recursive reads can reallocate the outer DenseMap.
    helpers[&block].emplace(std::move(key), result);
    return result;
  }
  Value assigned(Value source, const llvm::DenseMap<Value, Value> &mapping) {
    return mapping.lookup(source);
  }
  // Zip aligns coordinates and contributes exact extent equalities; product
  // introduces independent coordinates. This is read from domain SSA, not a
  // selected access plan. Dead constructors remain the admission reader's job.
  bool domain(Value descriptor, const llvm::DenseMap<Value, Value> &mapping,
              unsigned dimension, SmallVectorImpl<Meaning> &items,
              unsigned depth = 0) {
    if (!terms.charge() ||
        !terms.withinDepth(depth, ComparisonCapacity::DomainDepth))
      return false;
    Operation *op = descriptor.getDefiningOp();
    if (!op)
      return false;
    if (isa<data::DomainZipOp>(op)) {
      for (Value operand : op->getOperands())
        if (!domain(operand, mapping, dimension, items, depth + 1))
          return false;
      return true;
    }
    if (isa<data::DomainProductOp>(op)) {
      // Only a root product gives its factors independent coordinates. Under
      // a zip its flattened position is aligned with the other operands.
      if (depth != 0)
        return false;
      for (Value operand : op->getOperands()) {
        unsigned selected = dimensions.size();
        dimensions.emplace_back();
        if (!domain(operand, mapping, selected, items, depth + 1))
          return false;
      }
      return true;
    }
    if (dimension >= dimensions.size() || op->getNumOperands() == 0)
      return false;
    Value container = assigned(op->getOperand(0), mapping);
    if (!container)
      return false;
    if (auto indices = dyn_cast<data::DomainIndicesOp>(op)) {
      dimensions[dimension].equal.push_back(
          {container, unsigned(indices.getAxis())});
      items.push_back({Meaning::Position, invalidTerm, {}, {true, dimension}});
      return true;
    }
    if (isa<data::DomainElementsOp>(op)) {
      if (!vectorType(container.getType()))
        return false;
      dimensions[dimension].equal.push_back({container, 0});
      items.push_back(access(container, {{true, dimension}}));
      return true;
    }
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      if (op->getNumOperands() != 2)
        return false;
      Value selector = assigned(op->getOperand(1), mapping);
      if (!selector)
        return false;
      bool row = isa<data::DomainMatrixRowOp>(op);
      dimensions[dimension].equal.push_back({container, row ? 1u : 0u});
      selectedBounds.emplace(identity(container), row ? 0u : 1u,
                             identity(selector));
      Index fixed{false, identity(selector)}, varying{true, dimension};
      items.push_back(access(container, row ? ArrayRef<Index>{fixed, varying}
                                            : ArrayRef<Index>{varying, fixed}));
      return true;
    }
    return false;
  }
  Meaning lane(Value value, unsigned dimension) {
    auto found = candidate.find(value);
    if (found != candidate.end() && found->second.kind == Meaning::Lane &&
        found->second.axis == dimension)
      return found->second;
    if (!vectorType(value.getType()) || !extentIs(value, 0, dimension))
      return {};
    return access(value, {{true, dimension}});
  }
  Meaning scalar(Value value) {
    auto found = candidate.find(value);
    return found != candidate.end() && found->second.kind == Meaning::Scalar
               ? found->second
               : Meaning{};
  }
  Meaning readCandidate(Operation &op, const Primitive &bound) {
    StringRef contract = bound.contract;
    auto field = scalarField(ports.outputs(&op)[0].getType());
    if (!field)
      return {};
    if (contract == "field.constant") {
      if (bound.parameters.size() != 1)
        return {};
      return {Meaning::Scalar,
              terms.literal(field.getDomain(), bound.parameters[0])};
    }
    if (protocol::numericalContract(contract)) {
      if (dimensions.size() != 1 || ports.inputs(&op).size() == 0 ||
          ports.inputs(&op)[0] != rows || bound.parameters.size() != 1)
        return {};
      auto decoded = protocol::readBinding(bound.binding);
      if (!decoded) {
        consumeError(decoded.takeError());
        return {};
      }
      // Signature formation and parameter admission are independently checked
      // by primitive(); interpret the actual E and positional operands here.
      const auto &arguments = decoded->application.arguments;
      if (arguments.size() != 2)
        return {};
      const auto &mask = arguments[1];
      auto expression = protocol::readNumericalExpression(
          bound.parameters.front(), arguments[0], mask.size());
      if (!expression) {
        consumeError(expression.takeError());
        return {};
      }
      SmallVector<Term> slots;
      for (auto [i, bit] : enumerate(mask)) {
        Meaning value = bit == '1' ? lane(ports.inputs(&op)[i + 1], 0)
                                   : scalar(ports.inputs(&op)[i + 1]);
        // Even unused slots must be aligned with the admitted row domain.
        if (value.term == invalidTerm ||
            value.kind != (bit == '1' ? Meaning::Lane : Meaning::Scalar))
          return {};
        slots.push_back(value.term);
      }
      SmallVector<Term> nodes;
      for (const auto &node : expression->nodes()) {
        if (!terms.charge())
          return {};
        Term value = invalidTerm;
        switch (node.kind) {
        case ring::Kind::Constant:
          value = terms.literal(arguments[0], node.constant);
          break;
        case ring::Kind::Input:
          value = slots[node.input];
          break;
        case ring::Kind::Add:
        case ring::Kind::Mul:
          value = terms.binary(node.kind, nodes[node.left], nodes[node.right]);
          break;
        case ring::Kind::Neg:
          value = terms.neg(nodes[node.left]);
          break;
        case ring::Kind::Embed:
          return {};
        }
        if (value == invalidTerm)
          return {};
        nodes.push_back(value);
      }
      Term payload = nodes[expression->outputs().front()];
      if (contract == "numerical.map")
        return {Meaning::Lane, payload};
      auto combine =
          contract == "numerical.sum" ? ring::Kind::Add : ring::Kind::Mul;
      return {Meaning::Scalar, aggregate(arguments[0], combine, payload)};
    }
    if (!bound.parameters.empty())
      return {};
    if (fieldArithmetic(contract))
      return arithmetic(contract, scalar(ports.inputs(&op)[0]),
                        scalar(ports.inputs(&op)[1]));
    if (contract == "vector.fill") {
      auto value = scalar(ports.inputs(&op)[0]);
      if (dimensions.size() != 1 || ports.inputs(&op)[1] != rows ||
          value.kind != Meaning::Scalar)
        return {};
      value.kind = Meaning::Lane;
      return value;
    }
    if (laneArithmetic(contract)) {
      if (dimensions.size() != 1)
        return {};
      auto left = lane(ports.inputs(&op)[0], 0);
      auto right = contract == "vector.scale" ? scalar(ports.inputs(&op)[1])
                                              : lane(ports.inputs(&op)[1], 0);
      return arithmetic(contract, left, right);
    }
    Term payload = invalidTerm;
    ring::Kind combine = ring::Kind::Add;
    if (contract == "vector.sum" || contract == "vector.product") {
      if (dimensions.size() != 1)
        return {};
      payload = lane(ports.inputs(&op)[0], 0).term;
      if (contract == "vector.product")
        combine = ring::Kind::Mul;
    } else if (contract == "vector.dot") {
      if (dimensions.size() != 1)
        return {};
      payload =
          terms.binary(ring::Kind::Mul, lane(ports.inputs(&op)[0], 0).term,
                       lane(ports.inputs(&op)[1], 0).term);
    } else if (contract == "matrix.row_dot" ||
               contract == "matrix.column_dot") {
      if (dimensions.size() != 1)
        return {};
      Value matrix = ports.inputs(&op)[0], vector = ports.inputs(&op)[1],
            selector = ports.inputs(&op)[2];
      bool row = contract == "matrix.row_dot";
      if (!extentIs(matrix, row ? 1 : 0, 0) || !candidate.contains(matrix) ||
          !candidate.contains(selector) ||
          !selectedBounds.count(std::make_tuple(identity(matrix), row ? 0u : 1u,
                                                identity(selector))))
        return {};
      Index fixed{false, identity(selector)}, varying{true, 0};
      auto cell = access(matrix, row ? ArrayRef<Index>{fixed, varying}
                                     : ArrayRef<Index>{varying, fixed});
      payload = terms.binary(ring::Kind::Mul, cell.term, lane(vector, 0).term);
    } else if (contract == "matrix.bilinear") {
      if (dimensions.size() != 2)
        return {};
      Value matrix = ports.inputs(&op)[0];
      if (!candidate.contains(matrix) || !extentIs(matrix, 0, 0) ||
          !extentIs(matrix, 1, 1))
        return {};
      auto cell = access(matrix, {{true, 0}, {true, 1}});
      payload = terms.binary(ring::Kind::Mul,
                             lane(ports.inputs(&op)[1], 0).term, cell.term);
      payload = terms.binary(ring::Kind::Mul, payload,
                             lane(ports.inputs(&op)[2], 1).term);
    } else
      return {};
    return {Meaning::Scalar, aggregate(field.getDomain(), combine, payload)};
  }
  FailureOr<Value>
  consume(Meaning expected, Type resultType, Operation *&cursor,
          llvm::DenseSet<Operation *> &bindings, Operation *end,
          std::optional<Value> requestedOutput = std::nullopt) {
    if (expected.term == invalidTerm || expected.kind == Meaning::Unknown)
      return failure();
    Value result;
    // A closed body names its output. Read and admit all its instructions,
    // but compare only that output; normalizing every intermediate prefix is
    // unnecessary and can exhaust the shared budget on otherwise valid maps.
    auto output = [&](Value value) {
      return requestedOutput ? !*requestedOutput || value == *requestedOutput
                             : !end || (ports.inputs(end).size() == 1 &&
                                        ports.inputs(end)[0] == value);
    };
    // An identity formula need not emit any payload instruction.
    for (auto &entry : candidate) {
      Meaning value = entry.second;
      if (expected.kind == Meaning::Lane && vectorType(entry.first.getType()))
        value = lane(entry.first, 0);
      if (output(entry.first) && entry.first.getType() == resultType &&
          value.kind == expected.kind && terms.equal(value.term, expected.term))
        result = entry.first;
    }
    Operation *at = cursor;
    while (at && at != end && (end || !result)) {
      auto reference = at->getAttrOfType<FlatSymbolRefAttr>("binding");
      auto declaration =
          reference ? symbols.lookup<runtime::BindingOp>(reference.getValue())
                    : runtime::BindingOp();
      if (!declaration || !candidateContract(declaration.getContract()))
        break;
      uint64_t cost = 1;
      if (protocol::numericalContract(declaration.getContract())) {
        cost += ports.inputs(at).size() + ports.outputs(at).size();
        if (auto parameters = at->getAttrOfType<ArrayAttr>("parameters"))
          for (Attribute parameter : parameters)
            if (auto text = dyn_cast<StringAttr>(parameter)) {
              if (text.getValue().size() >
                      protocol::NumericalLimits::bodyBytes ||
                  !terms.charge(4 * text.getValue().size()))
                return failure();
            }
      }
      if (!terms.charge(cost))
        return failure();
      auto bound = primitive(*at, &symbols, ports);
      if (!bound)
        return failure();
      auto value = readCandidate(*at, *bound);
      if ((value.kind != Meaning::Scalar && value.kind != Meaning::Lane) ||
          value.term == invalidTerm)
        return failure();
      candidate[ports.outputs(at)[0]] = value;
      usedBindings.insert(bound->binding);
      if (output(ports.outputs(at)[0]) &&
          ports.outputs(at)[0].getType() == resultType &&
          value.kind == expected.kind && terms.equal(value.term, expected.term))
        result = ports.outputs(at)[0];
      at = ports.next(at);
    }
    if (!result || (end && at != end) || !terms.admit())
      return failure();
    cursor = at;
    bindings.insert(usedBindings.begin(), usedBindings.end());
    return result;
  }

public:
  Comparison(SymbolTable &symbols, Value rows, uint64_t &remaining,
             const ScopedCandidate *candidate = nullptr)
      : terms(remaining), symbols(symbols), ports(candidate), rows(rows) {}
  ComparisonCapacity exhausted() const { return terms.exhausted(); }
  std::optional<CapacityCause> failedDebit() const {
    return terms.failedDebit();
  }
  FailureOr<Value> map(Block &source, ArrayRef<bool> rowwise, ValueRange inputs,
                       Operation *&cursor,
                       llvm::DenseSet<Operation *> &bindings, Operation *end,
                       bool sum = false,
                       std::optional<Value> output = std::nullopt) {
    if (!rows || !rows.getType().isUnsignedInteger(64) ||
        rowwise.size() != inputs.size() ||
        source.getNumArguments() != inputs.size())
      return failure();
    if (sum)
      terms.useNeutralLaws();
    dimensions.emplace_back();
    SmallVector<Meaning> arguments;
    for (auto [i, value] : enumerate(inputs)) {
      Meaning meaning = input(value);
      if (rowwise[i]) {
        if (!vectorType(value.getType()) ||
            scalarField(value.getType()) != source.getArgument(i).getType())
          return failure();
        dimensions[0].equal.push_back({value, 0});
        meaning = access(value, {{true, 0}});
      } else if (value.getType() != source.getArgument(i).getType() ||
                 !isa<algebra::FieldType>(value.getType()))
        return failure();
      candidate[value] = meaning;
      arguments.push_back(meaning);
    }
    if (dimensions[0].equal.empty())
      return failure();
    auto returned = readSource(source, arguments);
    if (!returned || returned->size() != 1)
      return failure();
    Meaning expected = returned->front();
    if (expected.kind != Meaning::Scalar && expected.kind != Meaning::Lane)
      return failure();
    expected.kind = Meaning::Lane;
    auto field = scalarField(source.back().getOperand(0).getType());
    if (!field)
      return failure();
    if (sum) {
      expected = {Meaning::Scalar,
                  aggregate(field.getDomain(), ring::Kind::Add, expected.term)};
      return consume(expected, field, cursor, bindings, end, output);
    }
    return consume(
        expected,
        algebra::FieldVectorType::get(field.getContext(), field.getDomain()),
        cursor, bindings, end, output);
  }
  FailureOr<Value> finite(const finite::Computation &source, ValueRange inputs,
                          Operation *&cursor,
                          llvm::DenseSet<Operation *> &bindings, Operation *end,
                          bool sumCollection = false) {
    sourceClosure = source.scopedSource;
    fixedBindings = source.fixedBindings;
    if (source.predicate || !source.helper ||
        source.signature.getNumResults() != 1 ||
        inputs.size() != source.signature.getNumInputs() ||
        (!source.collect && source.states != 1) ||
        (!source.scoped && !source.helper->getRegion(0).hasOneBlock()))
      return failure();
    Type resultType = source.signature.getResult(0);
    auto field = scalarField(resultType);
    if (!field || (source.collect && !vectorType(resultType)))
      return failure();
    if (sumCollection && !source.collect)
      return failure();
    if (!source.collect || sumCollection)
      terms.useNeutralLaws();
    auto &descriptor = source.domain->getRegion(0).front();
    llvm::DenseMap<Value, Value> mapping;
    for (auto [argument, value] : zip(descriptor.getArguments(), inputs))
      mapping[argument] = value;
    for (auto [value, type] : zip(inputs, source.signature.getInputs())) {
      if (value.getType() != type)
        return failure();
      candidate[value] = input(value);
    }
    Value root = descriptor.back().getOperand(0);
    if (!isa_and_nonnull<data::DomainProductOp>(root.getDefiningOp()))
      dimensions.emplace_back();
    SmallVector<Meaning> items;
    if (!domain(root, mapping, 0, items) || dimensions.empty() ||
        dimensions.size() > 2)
      return failure();
    SmallVector<Meaning> arguments;
    Term state = invalidTerm;
    if (!source.collect) {
      state = terms.atom(field.getDomain(), {4});
      arguments.push_back({Meaning::Scalar, state});
    }
    append_range(arguments, items);
    for (Value value : inputs.take_front(source.arguments))
      arguments.push_back(input(value));
    for (Value value : inputs.drop_front(source.arguments + source.states))
      arguments.push_back(input(value));
    auto returned = readSource(source.helper->getRegion(0).front(), arguments);
    if (!returned || returned->size() != 1)
      return failure();
    Meaning expected = returned->front();
    if (expected.kind != Meaning::Scalar && expected.kind != Meaning::Lane)
      return failure();
    if (source.collect) {
      if (dimensions.size() != 1)
        return failure();
      expected.kind = Meaning::Lane;
      if (sumCollection) {
        expected = {Meaning::Scalar, aggregate(field.getDomain(),
                                               ring::Kind::Add, expected.term)};
        resultType = field;
      }
    } else {
      auto reduction = terms.reduction(expected.term, state);
      // Identity normalization can erase an additive zero term completely.
      // The unchanged state is independently equal to a seeded sum of zeros.
      if (!reduction && terms.equal(expected.term, state))
        reduction = std::make_pair(ring::Kind::Add,
                                   terms.literal(field.getDomain(), "0"));
      if (!reduction)
        return failure();
      auto [combine, payload] = *reduction;
      Term folded = aggregate(field.getDomain(), combine, payload);
      expected = {
          Meaning::Scalar,
          terms.binary(combine, scalar(inputs[source.arguments]).term, folded)};
    }
    return consume(expected, resultType, cursor, bindings, end);
  }
};
// The one supported group rule is the installed module sum of scalar actions.
// This reader uses its own typed module terms. It never passes a group value
// through Ring or gives an arbitrary operation field commutativity.
class ModuleComparison {
  enum Kind { Unknown, State, Scalar, Point, Scale, Add, Fold };
  struct Node {
    Kind kind;
    unsigned left = 0, right = 0;
  };
  SymbolTable &symbols;
  CandidatePorts ports;
  const protocol::SourceExecutionClosure *sourceClosure = nullptr;
  const llvm::DenseSet<Operation *> *fixedBindings = nullptr;
  Terms fieldTerms;
  std::vector<Node> nodes{{Unknown}};
  std::map<std::tuple<Kind, unsigned, unsigned>, unsigned> shared;
  std::map<std::tuple<Kind, unsigned, unsigned>, unsigned> sharedMeanings;
  std::map<unsigned, unsigned> meanings;
  llvm::DenseMap<Value, unsigned> identities;
  llvm::DenseSet<Operation *> used;
  bool charge() { return fieldTerms.charge(); }
  unsigned identity(Value value) {
    return identities.try_emplace(value, identities.size()).first->second;
  }
  unsigned scalarElement(Value container) {
    auto field = scalarField(container.getType());
    if (!field)
      return 0;
    return node(Scalar,
                fieldTerms.atom(field.getDomain(), {1, identity(container)}));
  }
  unsigned node(Kind kind, unsigned left = 0, unsigned right = 0) {
    if (!charge())
      return 0;
    if (kind == Add && right < left)
      std::swap(left, right);
    auto key = std::make_tuple(kind, left, right);
    auto found = shared.find(key);
    if (found != shared.end())
      return found->second;
    unsigned result = nodes.size();
    nodes.push_back({kind, left, right});
    shared.emplace(key, result);
    return result;
  }
  unsigned meaning(unsigned value) {
    if (auto found = meanings.find(value); found != meanings.end())
      return found->second;
    if (!value || !charge())
      return 0;
    auto [kind, left, right] = nodes[value];
    if (kind == Scalar) {
      left = fieldTerms.canonical(left);
      if (left == invalidTerm)
        return 0;
    } else if (kind == Scale || kind == Add || kind == Fold) {
      left = meaning(left);
      right = meaning(right);
      if (!left || !right)
        return 0;
      if (kind == Add && right < left)
        std::swap(left, right);
    }
    unsigned result = sharedMeanings
                          .try_emplace(std::make_tuple(kind, left, right),
                                       sharedMeanings.size() + 1)
                          .first->second;
    meanings.emplace(value, result);
    return result;
  }
  unsigned source(Block &block, ArrayRef<unsigned> args, unsigned depth = 0) {
    SourceBody body;
    if (!fieldTerms.withinDepth(depth, ComparisonCapacity::HelperDepth) ||
        !body.read(block, sourceClosure) || !body.visit(fieldTerms) ||
        args.size() != body.arguments.size() || body.returned.size() != 1)
      return 0;
    llvm::DenseMap<Value, unsigned> values;
    for (auto [argument, term] : zip(body.arguments, args))
      values[argument] = term;
    for (const auto &step : body.payload) {
      Operation &op = *step.operation;
      auto operands = step.inputs;
      auto results = step.outputs;
      if (!charge() || op.getNumRegions() || results.size() != 1)
        return 0;
      unsigned result = 0;
      if (isa<func::CallOp, local::ApplyOp, kernel::CallOp, exec::ComputeOp>(
              op)) {
        auto *helper = sourceCallee(&op);
        if (!helper || !isa<func::FuncOp, local::FuncOp>(helper) ||
            helper->getNumRegions() != 1 || helper->getRegion(0).empty())
          return 0;
        SmallVector<unsigned> arguments;
        for (Value operand : operands)
          arguments.push_back(values.lookup(operand));
        result = source(helper->getRegion(0).front(), arguments, depth + 1);
      } else {
        StringRef contract;
        if (auto bound = primitive(op, nullptr, CandidatePorts{}, step.scoped,
                                   fixedBindings)) {
          if (!bound->parameters.empty() && bound->contract != "field.constant")
            return 0;
          contract = bound->contract;
        } else if (op.getAttrs().empty() && operands.size() == 2) {
          if (isa<algebra::GroupAddOp>(op))
            contract = "curve.add";
          else if (isa<algebra::GroupScaleOp>(op))
            contract = "curve.scale";
        }
        if (algebra::isRingOperation(op))
          contract = isa<algebra::ConstantFieldOp>(op)   ? "field.constant"
                     : isa<algebra::FieldAddOp>(op)      ? "field.add"
                     : isa<algebra::SubtractFieldOp>(op) ? "field.sub"
                                                         : "field.mul";
        if (auto field = dyn_cast<algebra::FieldType>(results[0].getType())) {
          Term term = invalidTerm;
          if (contract == "field.constant") {
            auto literal = op.getAttrOfType<StringAttr>("value");
            auto bound = primitive(op, nullptr, CandidatePorts{}, step.scoped,
                                   fixedBindings);
            if (literal)
              term = fieldTerms.literal(field.getDomain(), literal.getValue());
            else if (bound && bound->parameters.size() == 1)
              term =
                  fieldTerms.literal(field.getDomain(), bound->parameters[0]);
          } else if (fieldArithmetic(contract) && operands.size() == 2) {
            unsigned left = values.lookup(operands[0]),
                     right = values.lookup(operands[1]);
            if (left && right && nodes[left].kind == Scalar &&
                nodes[right].kind == Scalar)
              term = fieldTerms.arithmetic(contract, nodes[left].left,
                                           nodes[right].left);
          }
          if (term == invalidTerm)
            return 0;
          values[results[0]] = node(Scalar, term);
          continue;
        }
        auto group = dyn_cast<algebra::GroupType>(results[0].getType());
        if (!group)
          return 0;
        SmallVector<protocol::BoundType> inputs, outputs;
        for (Value operand : operands) {
          auto type = protocol::encodeBoundType(operand.getType(), false);
          if (!type) {
            consumeError(type.takeError());
            return 0;
          }
          inputs.push_back(*type);
        }
        auto type = protocol::encodeBoundType(group, false);
        if (!type) {
          consumeError(type.takeError());
          return 0;
        }
        outputs.push_back(*type);
        const auto *facet = protocol::admitComputationContract(
            {contract.str(), {group.getDomain().str()}, ""}, inputs, outputs);
        if (!facet ||
            facet->law.algebra != protocol::ComputationAlgebra::GroupModule ||
            !facet->law.total || operands.size() != 2)
          return 0;
        unsigned left = values.lookup(operands[0]),
                 right = values.lookup(operands[1]);
        if (!left || !right)
          return 0;
        if (contract == "curve.add" && facet->law.commutative)
          result = node(Add, left, right);
        else if (contract == "curve.scale")
          result = node(Scale, left, right);
      }
      if (!result)
        return 0;
      values[results[0]] = result;
    }
    return values.lookup(body.returned[0]);
  }
  bool elements(Value value, const llvm::DenseMap<Value, Value> &mapping,
                SmallVectorImpl<unsigned> &items,
                llvm::DenseSet<Value> &containers, unsigned depth = 0) {
    if (!charge() ||
        !fieldTerms.withinDepth(depth, ComparisonCapacity::DomainDepth))
      return false;
    auto *op = value.getDefiningOp();
    if (isa_and_nonnull<data::DomainZipOp>(op)) {
      for (Value operand : op->getOperands())
        if (!elements(operand, mapping, items, containers, depth + 1))
          return false;
      return true;
    }
    if (!isa_and_nonnull<data::DomainElementsOp>(op))
      return false;
    Value container = mapping.lookup(op->getOperand(0));
    if (!container)
      return false;
    Kind kind = isa<algebra::GroupVectorType>(container.getType())   ? Point
                : isa<algebra::FieldVectorType>(container.getType()) ? Scalar
                                                                     : Unknown;
    if (kind == Unknown)
      return false;
    containers.insert(container);
    items.push_back(kind == Scalar ? scalarElement(container)
                                   : node(kind, identity(container)));
    return true;
  }

public:
  ModuleComparison(SymbolTable &symbols, uint64_t &remaining,
                   const ScopedCandidate *candidate = nullptr)
      : symbols(symbols), ports(candidate), fieldTerms(remaining) {
    fieldTerms.useNeutralLaws();
  }
  ComparisonCapacity exhausted() const { return fieldTerms.exhausted(); }
  std::optional<CapacityCause> failedDebit() const {
    return fieldTerms.failedDebit();
  }
  FailureOr<Value> check(const finite::Computation &computation,
                         ValueRange inputs, Operation *&cursor,
                         llvm::DenseSet<Operation *> &bindings,
                         Operation *end) {
    sourceClosure = computation.scopedSource;
    fixedBindings = computation.fixedBindings;
    if (computation.collect || computation.predicate ||
        computation.states != 1 || computation.signature.getNumResults() != 1 ||
        !isa<algebra::GroupType>(computation.signature.getResult(0)) ||
        inputs.size() != computation.signature.getNumInputs())
      return failure();
    auto group = cast<algebra::GroupType>(computation.signature.getResult(0));
    // Signature resolution establishes the installed group/scalar module,
    // rather than inferring that every nominal group has a scalar action.
    auto module = protocol::resolveBinding(
        {"curve.scale", {group.getDomain().str()}, ""}, false);
    if (!module) {
      consumeError(module.takeError());
      return failure();
    }
    llvm::DenseMap<Value, Value> mapping;
    auto &domain = computation.domain->getRegion(0).front();
    for (auto [argument, value] : zip(domain.getArguments(), inputs))
      mapping[argument] = value;
    SmallVector<unsigned> items;
    llvm::DenseSet<Value> containers;
    if (!elements(domain.back().getOperand(0), mapping, items, containers))
      return failure();
    unsigned state = node(State);
    SmallVector<unsigned> args{state};
    append_range(args, items);
    // Containers/captures remain exact inputs. This specific rule only uses
    // the item scalar/point and carried state; unknown accesses refuse.
    auto capture = [&](Value value) {
      if (auto field = dyn_cast<algebra::FieldType>(value.getType()))
        return node(Scalar,
                    fieldTerms.atom(field.getDomain(), {0, identity(value)}));
      return node(Unknown, identity(value));
    };
    for (Value value : inputs.take_front(computation.arguments))
      args.push_back(capture(value));
    for (Value value :
         inputs.drop_front(computation.arguments + computation.states))
      args.push_back(capture(value));
    unsigned result = source(computation.helper->getRegion(0).front(), args);
    if (!result || nodes[result].kind != Add)
      return failure();
    auto combine = nodes[result];
    unsigned payload = combine.left == state    ? combine.right
                       : combine.right == state ? combine.left
                                                : 0;
    if (!payload || nodes[payload].kind != Scale ||
        nodes[nodes[payload].left].kind != Point ||
        nodes[nodes[payload].right].kind != Scalar)
      return failure();
    unsigned expected =
        node(Add, node(State, identity(inputs[computation.arguments]) + 1),
             node(Fold, nodes[payload].left, nodes[payload].right));
    llvm::DenseMap<Value, unsigned> values;
    values[inputs[computation.arguments]] =
        node(State, identity(inputs[computation.arguments]) + 1);
    Operation *at = cursor;
    Value output;
    while (at && !output) {
      if (!charge())
        return failure();
      auto bound = primitive(*at, &symbols, ports);
      if (!bound || !bound->parameters.empty() ||
          ports.outputs(at)[0].getType() != group)
        return failure();
      unsigned term = 0;
      if (bound->contract == "curve.msm" &&
          containers.contains(ports.inputs(at)[0]) &&
          containers.contains(ports.inputs(at)[1]))
        term = node(Fold, node(Point, identity(ports.inputs(at)[1])),
                    scalarElement(ports.inputs(at)[0]));
      else if (bound->contract == "curve.add") {
        unsigned left = values.lookup(ports.inputs(at)[0]),
                 right = values.lookup(ports.inputs(at)[1]);
        if (left && right)
          term = node(Add, left, right);
      }
      if (!term)
        return failure();
      values[ports.outputs(at)[0]] = term;
      used.insert(bound->binding);
      unsigned actualMeaning = meaning(term);
      if (actualMeaning && actualMeaning == meaning(expected))
        output = ports.outputs(at)[0];
      at = ports.next(at);
    }
    if (!output || (end && at != end) || !fieldTerms.admit())
      return failure();
    cursor = at;
    bindings.insert(used.begin(), used.end());
    return output;
  }
};
} // namespace

FailureOr<Value> compareLaneFormula(
    Block &source, ArrayRef<bool> rowwise, ValueRange inputs, Value rows,
    Operation *&cursor, SymbolTable &symbols,
    llvm::DenseSet<Operation *> &bindings, uint64_t &remaining, Operation *end,
    ComparisonCapacity *capacity, std::optional<CapacityCause> *debit,
    std::optional<Value> output, const ScopedCandidate *candidate) {
  if (capacity)
    *capacity = ComparisonCapacity::None;
  if (debit)
    debit->reset();
  Comparison comparison(symbols, rows, remaining, candidate);
  auto result = comparison.map(source, rowwise, inputs, cursor, bindings, end,
                               false, output);
  if (failed(result)) {
    if (capacity)
      *capacity = comparison.exhausted();
    if (debit)
      *debit = comparison.failedDebit();
  }
  return result;
}
FailureOr<Value>
compareLaneSum(Block &source, ArrayRef<bool> rowwise, ValueRange inputs,
               Value rows, Operation *&cursor, SymbolTable &symbols,
               llvm::DenseSet<Operation *> &bindings, uint64_t &remaining,
               Operation *end, ComparisonCapacity *capacity,
               std::optional<CapacityCause> *debit, std::optional<Value> output,
               const ScopedCandidate *candidate) {
  if (capacity)
    *capacity = ComparisonCapacity::None;
  if (debit)
    debit->reset();
  Comparison comparison(symbols, rows, remaining, candidate);
  auto result = comparison.map(source, rowwise, inputs, cursor, bindings, end,
                               true, output);
  if (failed(result)) {
    if (capacity)
      *capacity = comparison.exhausted();
    if (debit)
      *debit = comparison.failedDebit();
  }
  return result;
}
FailureOr<Value>
compareFinitePayload(const finite::Computation &source, ValueRange inputs,
                     Value rows, Operation *&cursor, SymbolTable &symbols,
                     llvm::DenseSet<Operation *> &bindings, uint64_t &remaining,
                     Operation *end, ComparisonCapacity *capacity,
                     std::optional<CapacityCause> *debit,
                     const ScopedCandidate *candidate, bool sumCollection) {
  if (capacity)
    *capacity = ComparisonCapacity::None;
  if (debit)
    debit->reset();
  auto check = [&](auto &comparison, auto result) -> FailureOr<Value> {
    if (failed(result)) {
      if (capacity)
        *capacity = comparison.exhausted();
      if (debit)
        *debit = comparison.failedDebit();
    }
    return result;
  };
  if (source.signature.getNumResults() == 1 &&
      isa<algebra::GroupType>(source.signature.getResult(0))) {
    ModuleComparison comparison(symbols, remaining, candidate);
    return check(comparison,
                 comparison.check(source, inputs, cursor, bindings, end));
  }
  Comparison comparison(symbols, rows, remaining, candidate);
  return check(comparison, comparison.finite(source, inputs, cursor, bindings,
                                             end, sumCollection));
}
StringRef comparisonCapacityName(ComparisonCapacity capacity) {
  switch (capacity) {
  case ComparisonCapacity::None:
    return "none";
  case ComparisonCapacity::Work:
    return "finite comparison work";
  case ComparisonCapacity::Inputs:
    return "finite comparison term inputs";
  case ComparisonCapacity::Nodes:
    return "finite comparison term nodes";
  case ComparisonCapacity::Depth:
    return "finite comparison term depth";
  case ComparisonCapacity::Outputs:
    return "finite comparison term outputs";
  case ComparisonCapacity::Encoding:
    return "finite comparison term encoding bytes";
  case ComparisonCapacity::Multiplicity:
    return "finite comparison term multiplicity";
  case ComparisonCapacity::HelperDepth:
    return "finite comparison helper depth";
  case ComparisonCapacity::DomainDepth:
    return "finite comparison domain depth";
  }
  llvm_unreachable("unknown comparison capacity");
}
bool hasFinitePayloadContract(Operation *cursor, SymbolTable &symbols) {
  if (!cursor)
    return false;
  auto reference = cursor->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding = reference
                     ? symbols.lookup<runtime::BindingOp>(reference.getValue())
                     : runtime::BindingOp();
  return binding && (candidateContract(binding.getContract()) ||
                     binding.getContract() == "curve.msm" ||
                     binding.getContract() == "curve.add");
}
} // namespace zkc::mathematical
