#ifdef ZKC_ENABLE_HEIR
#include "Quotient.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
bool charge(uint64_t &remaining, uint64_t cost, bool *exhausted) {
  if (cost > remaining) {
    remaining = 0;
    if (exhausted)
      *exhausted = true;
    return false;
  }
  remaining -= cost;
  return true;
}
bool chargeCopy(const heir::Expression &expression, uint64_t &remaining,
                bool *exhausted) {
  for (const auto &[term, coefficient] : expression)
    if (!charge(remaining, 1 + term.size(), exhausted))
      return false;
  return true;
}
struct Meaning {
  heir::Expression expression;
  enum Form { Raw, Coefficient, Evaluation } form = Raw;
  uint64_t root = 0;
};
} // namespace
FailureOr<heir::ArithmeticMeaning>
readQuotientSource(func::FuncOp source, uint64_t &remaining,
                   ArrayRef<unsigned> variables, bool *exhausted) {
  if (exhausted)
    *exhausted = false;
  if (!source || !source.getBody().hasOneBlock() || source.front().empty() ||
      source.getNumArguments() > 128 || source.getNumResults() > 128 ||
      !source.getNumResults() || source.front().getOperations().size() > 512)
    return failure();
  heir::ArithmeticMeaning result;
  result.inputs = source.getNumArguments();
  if (!variables.empty() && variables.size() != result.inputs)
    return failure();
  llvm::DenseMap<Value, heir::Expression> values;
  llvm::DenseSet<Value> canonical;
  for (auto [i, argument] : enumerate(source.getArguments())) {
    if (!isa<algebra::IndicesType>(argument.getType()))
      return failure();
    values[argument] = {{{variables.empty() ? unsigned(i) : variables[i]}, 1}};
  }
  auto ring = [&](Type type) {
    auto quotient = dyn_cast<algebra::QuotientType>(type);
    if (!quotient)
      return false;
    if (!result.modulus) {
      // Bound trial division even when a hostile modulus is prime.
      if (!charge(remaining, 32768, exhausted) ||
          !heir::qualifiedProfile(quotient.getModulus(), quotient.getDegree()))
        return false;
      result.modulus = quotient.getModulus();
      result.degree = quotient.getDegree();
    }
    return quotient.getModulus() == result.modulus &&
           quotient.getDegree() == result.degree;
  };
  for (auto &op : source.front()) {
    if (!charge(remaining, 1 + op.getNumOperands() + op.getNumResults(),
                exhausted) ||
        op.getNumRegions() || op.getNumSuccessors())
      return failure();
    if (auto returned = dyn_cast<func::ReturnOp>(op)) {
      if (&op != &source.front().back() ||
          returned.getNumOperands() != source.getNumResults())
        return failure();
      for (Value value : returned.getOperands()) {
        if (!isa<algebra::IndicesType>(value.getType()) ||
            !canonical.contains(value) || !values.contains(value))
          return failure();
        const auto &expression = values.find(value)->second;
        if (!chargeCopy(expression, remaining, exhausted))
          return failure();
        result.outputs.push_back(expression);
      }
      return result.modulus ? FailureOr<heir::ArithmeticMeaning>(result)
                            : FailureOr<heir::ArithmeticMeaning>(failure());
    }
    if (op.getNumResults() != 1 || op.getNumOperands() < 1 ||
        op.getNumOperands() > 2)
      return failure();
    for (Value value : op.getOperands())
      if (!values.contains(value))
        return failure();
    auto output = op.getResult(0);
    if (isa<algebra::ProjectQuotientOp>(op)) {
      if (op.getNumOperands() != 1 || !ring(output.getType()) ||
          !isa<algebra::IndicesType>(op.getOperand(0).getType()))
        return failure();
      const auto &expression = values.find(op.getOperand(0))->second;
      if (!chargeCopy(expression, remaining, exhausted))
        return failure();
      // Insertion may rehash values and invalidate the source reference.
      auto copy = expression;
      values[output] = std::move(copy);
    } else if (isa<algebra::ObserveQuotientOp>(op)) {
      if (op.getNumOperands() != 1 || !ring(op.getOperand(0).getType()) ||
          !canonical.contains(op.getOperand(0)) ||
          !isa<algebra::IndicesType>(output.getType()))
        return failure();
      const auto &expression = values.find(op.getOperand(0))->second;
      if (!chargeCopy(expression, remaining, exhausted))
        return failure();
      // Insertion may rehash values and invalidate the source reference.
      auto copy = expression;
      values[output] = std::move(copy);
    } else if (isa<algebra::AddQuotientOp, algebra::SubtractQuotientOp,
                   algebra::MultiplyQuotientOp>(op)) {
      if (op.getNumOperands() != 2 || !ring(output.getType()))
        return failure();
      for (Value value : op.getOperands())
        if (!ring(value.getType()) || !canonical.contains(value))
          return failure();
      auto expression = heir::combine(isa<algebra::AddQuotientOp>(op)
                                          ? heir::ArithmeticOperation::Add
                                      : isa<algebra::SubtractQuotientOp>(op)
                                          ? heir::ArithmeticOperation::Subtract
                                          : heir::ArithmeticOperation::Multiply,
                                      values.find(op.getOperand(0))->second,
                                      values.find(op.getOperand(1))->second,
                                      result.modulus, remaining, exhausted);
      if (failed(expression))
        return failure();
      values[output] = std::move(*expression);
    } else
      return failure();
    canonical.insert(output);
  }
  return failure();
}

FailureOr<SmallVector<Value>>
readQuotientExecution(func::FuncOp source, Operation *targetRoot,
                      StringRef rootSite, ValueRange arguments,
                      Operation *&cursor, uint64_t &remaining, bool *exhausted,
                      uint64_t *siteBytes) {
  if (exhausted)
    *exhausted = false;
  llvm::DenseMap<Value, unsigned> representatives;
  SmallVector<unsigned> variables;
  for (auto [i, value] : enumerate(arguments)) {
    auto inserted = representatives.try_emplace(value, unsigned(i));
    variables.push_back(inserted.first->second);
  }
  auto original = readQuotientSource(source, remaining, variables, exhausted);
  if (failed(original) || arguments.size() != original->inputs)
    return failure();
  const auto q = original->modulus, n = original->degree;
  SymbolTable symbols(targetRoot);
  llvm::DenseMap<Value, Meaning> meanings;
  llvm::DenseMap<Value, uint64_t> constants;
  for (auto [i, argument] : enumerate(arguments)) {
    if (!isa<algebra::IndicesType>(argument.getType()))
      return failure();
    meanings[argument] = {{{{variables[i]}, 1}}, Meaning::Raw, 0};
  }
  SmallVector<Value> outputs(original->outputs.size());
  auto prefix = (rootSite + "_recipe_quotient_").str();
  bool first = true;
  while (cursor) {
    auto site = cursor->getAttrOfType<StringAttr>("site");
    if (!site || !site.getValue().starts_with(prefix))
      break;
    if (siteBytes && !charge(*siteBytes, site.getValue().size(), exhausted))
      return failure();
    if (!charge(remaining,
                1 + cursor->getNumOperands() + cursor->getNumResults(),
                exhausted) ||
        cursor->getNumResults() != 1 || cursor->getNumRegions() ||
        cursor->getNumSuccessors() || cursor->getAttrs().size() != 3)
      return failure();
    StringRef suffix = site.getValue().drop_front(prefix.size());
    if (first && suffix != "begin")
      return failure();
    first = false;
    auto reference = cursor->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding = reference ? dyn_cast_or_null<local::OperationBindingOp>(
                                   symbols.lookup(reference.getValue()))
                             : local::OperationBindingOp();
    auto parameters = cursor->getAttrOfType<ArrayAttr>("parameters");
    if (!binding || !binding.getArguments().empty() ||
        !binding.getImplementation().empty() || !parameters ||
        cursor->getName().getStringRef() !=
            protocol::boundOperationName(binding.getContract()))
      return failure();
    auto contract = binding.getContract();
    auto output = cursor->getResult(0);
    if (contract == "index.constant") {
      if (cursor->getNumOperands() || parameters.size() != 1 ||
          !output.getType().isUnsignedInteger(64))
        return failure();
      auto text = dyn_cast<StringAttr>(parameters[0]);
      uint64_t value;
      if (!text || text.getValue().getAsInteger(10, value) ||
          text.getValue() != std::to_string(value) ||
          suffix.starts_with("outputs_"))
        return failure();
      constants[output] = value;
    } else {
      if (!parameters.empty() || !isa<algebra::IndicesType>(output.getType()))
        return failure();
      auto operands = cursor->getOperands();
      auto literal = [&](unsigned position, uint64_t expected) {
        if (position >= operands.size())
          return false;
        auto it = constants.find(operands[position]);
        return it != constants.end() && it->second == expected;
      };
      if (operands.empty() || !meanings.contains(operands[0]))
        return failure();
      const auto &left = meanings.find(operands[0])->second;
      if (!chargeCopy(left.expression, remaining, exhausted))
        return failure();
      Meaning result = left;
      if (contract == "quotient.project") {
        if (operands.size() != 3 || !literal(1, q) || !literal(2, n) ||
            left.form == Meaning::Evaluation)
          return failure();
        result.form = Meaning::Coefficient;
        result.root = 0;
      } else if (contract == "quotient.ntt" || contract == "quotient.intt") {
        bool inverse = contract == "quotient.intt";
        if (operands.size() != 3 || !literal(1, q) ||
            !constants.contains(operands[2]) ||
            left.form != (inverse ? Meaning::Evaluation : Meaning::Coefficient))
          return failure();
        auto root = constants.lookup(operands[2]);
        if (!root || root >= q || heir::modularPower(root, n, q) != q - 1 ||
            (inverse && left.root * root % q != 1))
          return failure();
        result.form = inverse ? Meaning::Coefficient : Meaning::Evaluation;
        result.root = inverse ? 0 : root;
      } else if (contract == "quotient.add" ||
                 contract == "quotient.subtract" ||
                 contract == "quotient.multiply" ||
                 contract == "quotient.pointwise") {
        if (operands.size() != 3 || !literal(2, q) ||
            !meanings.contains(operands[1]))
          return failure();
        const auto &right = meanings.find(operands[1])->second;
        if (left.form == Meaning::Raw || left.form != right.form ||
            left.root != right.root ||
            (contract == "quotient.multiply" &&
             left.form != Meaning::Coefficient) ||
            (contract == "quotient.pointwise" &&
             left.form != Meaning::Evaluation))
          return failure();
        auto expression = heir::combine(
            contract == "quotient.add" ? heir::ArithmeticOperation::Add
            : contract == "quotient.subtract"
                ? heir::ArithmeticOperation::Subtract
                : heir::ArithmeticOperation::Multiply,
            left.expression, right.expression, q, remaining, exhausted);
        if (failed(expression))
          return failure();
        result.expression = std::move(*expression);
      } else
        return failure();
      // Occurrence labels locate proposed output values. Their meanings are
      // independently checked; labels alone never establish correspondence.
      if (suffix.consume_front("outputs_")) {
        if (result.form != Meaning::Coefficient || suffix.empty())
          return failure();
        SmallVector<StringRef> slots;
        suffix.split(slots, '_', -1, true);
        for (auto text : slots) {
          unsigned index;
          if (text.getAsInteger(10, index) || text != std::to_string(index) ||
              index >= outputs.size() || outputs[index] ||
              result.expression != original->outputs[index])
            return failure();
          outputs[index] = output;
        }
      }
      meanings[output] = std::move(result);
    }
    cursor = cursor->getNextNode();
  }
  if (first || llvm::any_of(outputs, [](Value value) { return !value; }))
    return failure();
  return outputs;
}
} // namespace zkc::kernel

#endif
