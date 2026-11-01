#include "ScopedNestedContraction.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
using namespace llvm;
namespace zkc::nested {
namespace {
class Work {
  uint64_t &remaining;
  bool &exhausted;

public:
  Work(uint64_t &remaining, bool &exhausted)
      : remaining(remaining), exhausted(exhausted) {}
  bool charge(uint64_t amount = 1) {
    if (amount > remaining) {
      exhausted = true;
      return false;
    }
    remaining -= amount;
    return true;
  }
};
struct Instruction {
  Operation *operation;
  ValueRange inputs, outputs;
};
struct Body {
  ValueRange arguments, returned;
  SmallVector<Instruction> instructions;
  bool read(Operation *owner, const protocol::SourceExecutionClosure &source,
            Work &work) {
    auto function = dyn_cast<func::FuncOp>(owner);
    if (!function || function.empty() || !work.charge())
      return false;
    if (protocol::isScopedExecutionFunction(function)) {
      auto found = source.bodies.find(function.getSymName().str());
      if (found == source.bodies.end() || found->second.empty() ||
          function->hasAttr("runtime.region") ||
          !isa<exec::ReturnOp>(found->second.back().operation))
        return false;
      arguments = function.getArguments().drop_front();
      returned = found->second.back().inputs;
      for (const auto &step : found->second) {
        if (!work.charge(1 + step.inputs.size() + step.outputs.size()) ||
            step.operation->getParentOp() != owner || !step.regions.empty())
          return false;
        if (&step != &found->second.back())
          instructions.push_back({step.operation, step.inputs, step.outputs});
      }
    } else {
      if (!function.getBody().hasOneBlock() ||
          !isa<func::ReturnOp>(function.front().back()))
        return false;
      arguments = function.getArguments();
      returned = function.front().back().getOperands();
      for (auto &op : function.front().without_terminator()) {
        if (!work.charge(1 + op.getNumOperands() + op.getNumResults()) ||
            op.getNumRegions())
          return false;
        instructions.push_back({&op, op.getOperands(), op.getResults()});
      }
    }
    return work.charge(arguments.size() + returned.size());
  }
};
// Actual source SSA is read independently of optional computation analysis.
// Invocation identities distinguish repeated uses of the same helper body.
class ScalarSource {
public:
  using Scalar = std::pair<Value, unsigned>;

private:
  struct Invocation {
    llvm::DenseMap<Value, Scalar> values;
  };
  SmallVector<Invocation> invocations;
  SmallVector<Scalar> instructions;
  llvm::DenseMap<Value, Instruction> producers;
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection symbols;
  const finite::Computation &computation;
  Operation *nestedCall;
  Work &work;
  SmallVector<Scalar> read(Operation *owner, const Body &body,
                           ArrayRef<Scalar> arguments) {
    if (active.size() >= 64 || !active.insert(owner).second ||
        body.arguments.size() != arguments.size() || !work.charge()) {
      valid = false;
      return {};
    }
    auto leave = scope_exit([&] { active.erase(owner); });
    unsigned invocation = invocations.size();
    invocations.emplace_back();
    for (auto [formal, input] : zip(body.arguments, arguments)) {
      if (!input.first || formal.getType() != input.first.getType()) {
        valid = false;
        return {};
      }
      invocations[invocation].values[formal] = input;
    }
    for (const auto &step : body.instructions) {
      auto *op = step.operation;
      if (!work.charge(1 + step.inputs.size() + step.outputs.size())) {
        valid = false;
        return {};
      }
      SmallVector<Scalar> inputs;
      for (Value operand : step.inputs)
        inputs.push_back(actual(operand, invocation));
      if (!valid)
        return {};
      func::FuncOp callee;
      if (auto call = dyn_cast<exec::ComputeOp>(op))
        callee = call.resolveCallee(symbols);
      else if (auto call = dyn_cast<func::CallOp>(op))
        callee = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
      if (isa<exec::ComputeOp, func::CallOp>(op)) {
        if (auto policy = op->getAttrOfType<ArrayAttr>("policy"))
          if (policy.size() != 3 || !isa<BoolAttr>(policy[0]) ||
              !isa<BoolAttr>(policy[1]) || !isa<BoolAttr>(policy[2]) ||
              !cast<BoolAttr>(policy[0]).getValue()) {
            valid = false;
            return {};
          }
        Body target;
        if (!callee || !target.read(callee, *computation.scopedSource, work)) {
          valid = false;
          return {};
        }
        auto outputs = read(callee, target, inputs);
        if (!valid || outputs.size() != step.outputs.size()) {
          valid = false;
          return {};
        }
        for (auto [result, output] : zip(step.outputs, outputs)) {
          if (result.getType() != output.first.getType()) {
            valid = false;
            return {};
          }
          invocations[invocation].values[result] = output;
        }
        continue;
      }
      auto *meaning = finite::semantics(op);
      bool fixed = false;
      if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding")) {
        auto binding =
            symbols.lookupNearestSymbolFrom<runtime::BindingOp>(op, reference);
        fixed = computation.fixedBindings &&
                computation.fixedBindings->contains(binding);
      }
      if (step.outputs.size() != 1 ||
          (op != nestedCall &&
           (!meaning || !meaning->law.total || meaning->access || fixed ||
            !finite::replaceable(op)))) {
        valid = false;
        return {};
      }
      Value output = step.outputs.front();
      Scalar value{output, invocation};
      producers[output] = step;
      instructions.push_back(value);
      invocations[invocation].values[output] = value;
    }
    SmallVector<Scalar> result;
    for (Value value : body.returned)
      result.push_back(actual(value, invocation));
    return result;
  }
  Scalar actual(Value value, unsigned invocation) {
    if (!work.charge() || invocation >= invocations.size()) {
      valid = false;
      return {};
    }
    auto found = invocations[invocation].values.find(value);
    if (found == invocations[invocation].values.end()) {
      valid = false;
      return {};
    }
    return found->second;
  }

public:
  bool valid = true;
  Body root;
  SmallVector<Scalar> returned;
  ScalarSource(const finite::Computation &computation, Work &work,
               Operation *nestedCall = nullptr)
      : computation(computation), nestedCall(nestedCall), work(work) {
    if (!root.read(computation.helper, *computation.scopedSource, work)) {
      valid = false;
      return;
    }
    SmallVector<Scalar> arguments;
    for (Value value : root.arguments)
      arguments.emplace_back(value, 0);
    returned = read(computation.helper, root, arguments);
    if (!valid)
      return;
    llvm::DenseSet<Scalar> live(returned.begin(), returned.end());
    for (auto value : llvm::reverse(instructions)) {
      auto found = producers.find(value.first);
      if (!work.charge() || found == producers.end() || !live.contains(value)) {
        valid = false;
        return;
      }
      for (Value input : found->second.inputs)
        live.insert(actual(input, value.second));
    }
  }
  Operation *producer(Scalar value) const {
    auto found = producers.find(value.first);
    return found == producers.end() ? nullptr : found->second.operation;
  }
  ValueRange operands(Scalar value) const {
    auto found = producers.find(value.first);
    return found == producers.end() ? ValueRange{} : found->second.inputs;
  }
  Scalar operand(Scalar value, unsigned index) {
    auto inputs = operands(value);
    if (index >= inputs.size()) {
      valid = false;
      return {};
    }
    return scalar(actual(inputs[index], value.second));
  }
  std::optional<unsigned> input(Scalar value) {
    if (valid && value.second == 0)
      for (auto [i, formal] : enumerate(root.arguments)) {
        if (!work.charge()) {
          valid = false;
          return std::nullopt;
        }
        if (value.first == formal)
          return i;
      }
    return std::nullopt;
  }
  Scalar scalar(Value value) { return scalar(actual(value, 0)); }
  Scalar scalar(Scalar value) {
    for (unsigned depth = 0; valid && value.first && depth < 64; ++depth) {
      if (!work.charge()) {
        valid = false;
        return {};
      }
      auto *op = producer(value);
      auto inputs = operands(value);
      const auto *meaning = finite::semantics(op);
      if (!meaning || inputs.size() != 2 ||
          meaning->law.algebra != protocol::ComputationAlgebra::FieldRing)
        break;
      auto neutral = [&](Value input, protocol::ScalarIdentity identity) {
        auto resolved = actual(input, value.second);
        auto *constant = producer(resolved);
        auto text = finite::fieldConstant(constant);
        return text && ((identity == protocol::ScalarIdentity::Zero &&
                         text.getValue().getValue().isZero()) ||
                        (identity == protocol::ScalarIdentity::One &&
                         text.getValue().getValue().isOne()));
      };
      if (neutral(inputs[1], meaning->law.rightIdentity))
        value = actual(inputs[0], value.second);
      else if (neutral(inputs[0], meaning->law.leftIdentity))
        value = actual(inputs[1], value.second);
      else
        break;
    }
    return valid ? value : Scalar{};
  }
};
std::optional<unsigned> argument(Value value, Block &block) {
  auto formal = dyn_cast<BlockArgument>(value);
  return formal && formal.getOwner() == &block
             ? std::optional<unsigned>(formal.getArgNumber())
             : std::nullopt;
}
bool nativeVector(Type type, Type field) {
  auto vector = dyn_cast<data::FieldVectorType>(type);
  return vector && vector.getElementType() == field;
}
bool nativeMatrix(Type type, Type field) {
  auto matrix = dyn_cast<data::FieldMatrixType>(type);
  return matrix && matrix.getElementType() == field;
}
} // namespace
std::optional<ScopedSource>
readScopedSource(const finite::Computation &computation, uint64_t &remaining,
                 bool &exhausted) {
  Work work(remaining, exhausted);
  ScopedSource source;
  source.outer = computation;
  if (!work.charge() || !computation.scoped || !computation.scopedSource ||
      !computation.collect || computation.predicate)
    return std::nullopt;
  auto &outerDomain = source.outer.domain.getBody().front();
  if (!work.charge(outerDomain.getOperations().size()) ||
      std::distance(outerDomain.begin(), outerDomain.end()) != 2)
    return std::nullopt;
  auto indices = dyn_cast<data::DomainIndicesOp>(outerDomain.front());
  if (!indices || outerDomain.back().getOperand(0) != indices.getOutput())
    return std::nullopt;
  auto m = argument(indices.getInput(), outerDomain);
  if (!m || indices.getAxis() > 1)
    return std::nullopt;
  source.matrix = *m;
  source.axis = indices.getAxis();
  Body body;
  if (!body.read(source.outer.helper, *computation.scopedSource, work) ||
      body.returned.size() != 1)
    return std::nullopt;
  Instruction nested{nullptr, {}, {}};
  for (const auto &step : body.instructions)
    if (isa<exec::FoldOp>(step.operation)) {
      if (source.call)
        return std::nullopt;
      source.call = step.operation;
      nested = step;
    }
  ScalarSource outerScalar(source.outer, work, source.call);
  if (!source.call || nested.outputs.size() != 1 || !outerScalar.valid ||
      outerScalar.scalar(body.returned.front()) !=
          outerScalar.scalar(nested.outputs.front()) ||
      failed(finite::describe(source.call, source.inner)) ||
      source.inner.predicate || source.inner.states != 1)
    return std::nullopt;
  source.inner.scopedSource = computation.scopedSource;
  source.inner.fixedBindings = computation.fixedBindings;
  Type field = source.inner.signature.getResult(0);
  if (!isa<algebra::FieldType>(field) ||
      !nativeVector(source.outer.signature.getResult(0), field) ||
      !nativeMatrix(source.outer.signature.getInput(source.matrix), field))
    return std::nullopt;
  auto seed = outerScalar.scalar(nested.inputs[source.inner.arguments]);
  if (!outerScalar.valid || !seed.first)
    return std::nullopt;
  if (auto formal = outerScalar.input(seed)) {
    if (!*formal || seed.first.getType() != field)
      return std::nullopt;
    source.seed.input = *formal - 1;
  } else {
    auto constant = finite::fieldConstant(outerScalar.producer(seed));
    if (!constant || !finite::replaceable(outerScalar.producer(seed)) ||
        seed.first.getType() != field)
      return std::nullopt;
    source.seed.constant = constant;
  }
  // Domain inputs are mapped through the nested call to the actual outer
  // helper environment. Zero denotes the enumerated index, i+1 input i.
  for (Value operand : nested.inputs.take_front(source.inner.arguments)) {
    if (!work.charge())
      return std::nullopt;
    auto input = outerScalar.input(outerScalar.scalar(operand));
    if (!input)
      return std::nullopt;
    source.inputMap.push_back(*input);
  }
  auto &domain = source.inner.domain.getBody().front();
  llvm::DenseMap<Value, SmallVector<Operation *>> items;
  auto actual = [&](Value value) -> std::optional<unsigned> {
    auto formal = argument(value, domain);
    if (!formal || *formal >= source.inputMap.size())
      return std::nullopt;
    return source.inputMap[*formal];
  };
  for (auto &op : domain.without_terminator()) {
    if (!work.charge(1 + op.getNumOperands()))
      return std::nullopt;
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Operation *> lanes;
      for (Value operand : op.getOperands()) {
        auto found = items.find(operand);
        if (found == items.end())
          return std::nullopt;
        if (!work.charge(found->second.size()))
          return std::nullopt;
        append_range(lanes, found->second);
      }
      items[op.getResult(0)] = std::move(lanes);
      continue;
    }
    if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
             data::DomainMatrixColumnOp>(op))
      return std::nullopt;
    auto input = actual(op.getOperand(0));
    if (!input || !*input)
      return std::nullopt;
    Type type = source.outer.signature.getInput(*input - 1);
    if (isa<data::DomainElementsOp>(op)) {
      if (!nativeVector(type, field))
        return std::nullopt;
    } else {
      auto selected = actual(op.getOperand(1));
      if (*input - 1 != source.matrix || !selected || *selected != 0 ||
          isa<data::DomainMatrixColumnOp>(op) != bool(source.axis))
        return std::nullopt;
    }
    items[op.getResult(0)] = {&op};
  }
  auto root = items.find(domain.back().getOperand(0));
  if (root == items.end())
    return std::nullopt;
  ScalarSource innerScalar(source.inner, work);
  if (!innerScalar.valid || innerScalar.returned.size() != 1)
    return std::nullopt;
  auto sum = innerScalar.scalar(innerScalar.returned.front());
  if (!innerScalar.valid || !sum.first)
    return std::nullopt;
  Operation *add = innerScalar.producer(sum);
  auto *sumLaw = finite::replaceable(add) ? finite::semantics(add) : nullptr;
  if (!sumLaw || sumLaw->identity != MathematicalIdentity::FieldAdd ||
      !sumLaw->law.total || !sumLaw->law.associative ||
      !sumLaw->law.commutative)
    return std::nullopt;
  ScalarSource::Scalar state{innerScalar.root.arguments[0], 0}, term;
  auto left = innerScalar.operand(sum, 0);
  auto right = innerScalar.operand(sum, 1);
  if (left == state)
    term = right;
  else if (right == state)
    term = left;
  else
    return std::nullopt;
  if (!innerScalar.valid || !term.first)
    return std::nullopt;
  Operation *mul = innerScalar.producer(term);
  auto *productLaw =
      finite::replaceable(mul) ? finite::semantics(mul) : nullptr;
  if (!productLaw ||
      productLaw->identity != MathematicalIdentity::FieldMultiply ||
      !productLaw->law.total || !productLaw->law.commutative || mul == add ||
      sum.first.getType() != field || term.first.getType() != field)
    return std::nullopt;
  bool matrixLane = false, vectorLane = false;
  for (unsigned index = 0; index < innerScalar.operands(term).size(); ++index) {
    auto item = innerScalar.input(innerScalar.operand(term, index));
    if (!item || !*item || *item > root->second.size())
      return std::nullopt;
    auto *access = root->second[*item - 1];
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(access)) {
      if (matrixLane)
        return std::nullopt;
      matrixLane = true;
    } else {
      if (vectorLane)
        return std::nullopt;
      vectorLane = true;
      source.vector = *actual(access->getOperand(0)) - 1;
    }
  }
  if (!innerScalar.valid || !matrixLane || !vectorLane)
    return std::nullopt;
  return source;
}

} // namespace zkc::nested
