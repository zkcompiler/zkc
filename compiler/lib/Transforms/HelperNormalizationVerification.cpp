#include "HelperNormalization.h"
#include "MathematicalValues.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Interfaces/Collection.h"
#include <limits>
#include <vector>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
struct HelperNormalizationChecker::Implementation {
  using Term = ValueCorrespondence::Term;
  Operation *root;
  ValueCorrespondence terms;
  SymbolTableCollection symbols;
  // Memoize the complete invocation, including unused operations. Positional
  // substitutions distinguish same-type permutations and every result slot.
  std::map<std::pair<Operation *, std::vector<Term>>, SmallVector<Term>> calls;
  llvm::DenseMap<Term, SmallVector<uint64_t>> degrees;
  Builder builder;
  bool depthExhausted = false;

  explicit Implementation(Operation *root, size_t work)
      : root(root), terms(root, false, work), builder(root->getContext()) {}

  LogicalResult refuse(Operation *subject) {
    if (terms.workExhausted() || depthExhausted)
      return diagnostics::emit(subject->emitOpError(),
                               "mathematical-helper-limit",
                               "helper comparison work or depth exhausted");
    return diagnostics::emit(
        subject->emitOpError(), "mathematical-helper-correspondence",
        "helper normalization is unsupported or its meaning differs");
  }

  // Check observation premises before dropping anything. In particular, a
  // formal parameter's degree becomes known only at its actual invocation.
  // These are the defining degree laws, not the elimination implementation.
  bool formation(Operation &op, ArrayRef<Term> inputs, ArrayRef<Term> outputs) {
    if (isa<poly::PolynomialCoefficientsOp>(op)) {
      auto bound = degrees.find(inputs[0]);
      auto width =
          cast<algebra::FieldArrayType>(op.getResult(0).getType()).getLength();
      if (bound == degrees.end() || bound->second.size() != 1 ||
          bound->second[0] >= uint64_t(width))
        return false;
    }
    if (outputs.size() != 1)
      return true;
    auto type = dyn_cast<poly::PolynomialType>(op.getResult(0).getType());
    if (!type)
      return true;
    if (!terms.charge(type.getArity() + 1))
      return false;
    SmallVector<uint64_t> bound;
    if (isa<poly::ConstantPolynomialOp>(op))
      bound.assign(type.getArity(), 0);
    else if (isa<poly::MultilinearPolynomialOp>(op))
      bound.assign(type.getArity(), 1);
    else if (isa<poly::CoefficientPolynomialOp, poly::InterpolateDomainOp>(op))
      bound.push_back(cast<algebra::FieldArrayType>(op.getOperand(0).getType())
                          .getLength() -
                      1);
    else {
      auto first = degrees.find(inputs[0]);
      if (first == degrees.end())
        return false;
      bound = first->second;
      if (isa<poly::AddPolynomialOp, poly::MultiplyPolynomialOp>(op)) {
        auto second = degrees.find(inputs[1]);
        if (second == degrees.end() || bound.size() != second->second.size())
          return false;
        for (auto [a, b] : zip(bound, second->second)) {
          if (isa<poly::AddPolynomialOp>(op))
            a = std::max(a, b);
          else {
            if (a > std::numeric_limits<uint64_t>::max() - b)
              return false;
            a += b;
          }
        }
      } else if (auto fix = dyn_cast<poly::FixPolynomialOp>(op)) {
        if (bound.size() < fix.getPrefix().size())
          return false;
        bound.erase(bound.begin(), bound.begin() + fix.getPrefix().size());
      } else if (isa<poly::SumPolynomialOp>(op))
        bound.resize(type.getArity());
      else
        return false;
    }
    if (bound.size() != type.getArity())
      return false;
    degrees[outputs[0]] = std::move(bound);
    return true;
  }

  FailureOr<SmallVector<Term>> read(Block &block, ArrayRef<Term> inputs,
                                    bool source, unsigned depth = 0) {
    if (depth > 64) {
      depthExhausted = true;
      return failure();
    }
    if (block.empty() || inputs.size() != block.getNumArguments() ||
        !terms.charge(1 + inputs.size()))
      return failure();
    llvm::DenseMap<Value, Term> values;
    for (auto [value, term] : zip(block.getArguments(), inputs)) {
      if (!term || value.getType() != terms.expression(term).type)
        return failure();
      values[value] = term;
    }
    for (auto &op : block.without_terminator()) {
      if (!terms.charge(1 + op.getNumOperands() + op.getNumResults()) ||
          op.getNumRegions())
        return failure();
      SmallVector<Term> operands, results;
      for (Value value : op.getOperands()) {
        auto term = values.lookup(value);
        if (!term)
          return failure();
        operands.push_back(term);
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        // A candidate must actually be expanded. Source lookup is always in
        // the frozen unit, including when the candidate block is detached.
        auto helper =
            symbols.lookupSymbolIn<func::FuncOp>(root, call.getCalleeAttr());
        if (!source || !helper || !helper.getBody().hasOneBlock())
          return failure();
        auto key =
            std::make_pair(helper.getOperation(),
                           std::vector<Term>(operands.begin(), operands.end()));
        auto found = calls.find(key);
        if (found != calls.end())
          results = found->second;
        else {
          auto returned = read(helper.front(), operands, true, depth + 1);
          if (failed(returned))
            return failure();
          results = *returned;
          calls.emplace(std::move(key), results);
        }
      } else {
        if (!isTotal(&op))
          return failure();
        NamedAttrList attributes(op.getAttrs());
        // Mathematical occurrence labels are assigned after normalization;
        // executable occurrence admission remains the recipe caller's job.
        attributes.erase("site");
        auto name = op.getName().getStringRef();
        if (auto dim = dyn_cast<data::DimOp>(op)) {
          auto type = cast<CollectionTypeInterface>(dim.getInput().getType());
          auto axis = dim.getAxisAttr().getInt();
          if (auto extent = type.getStaticExtent(axis)) {
            name = data::IndexOp::getOperationName();
            attributes.clear();
            attributes.set("value",
                           builder.getIntegerAttr(
                               builder.getIntegerType(64, false), *extent));
            operands.clear();
          }
        }
        for (auto [coordinate, value] : enumerate(op.getResults())) {
          auto term =
              terms.expression(name, value.getType(),
                               attributes.getDictionary(builder.getContext()),
                               operands, coordinate);
          if (!term)
            return failure();
          results.push_back(term);
        }
        if (!formation(op, operands, results))
          return failure();
      }
      if (results.size() != op.getNumResults())
        return failure();
      for (auto [value, term] : zip(op.getResults(), results)) {
        if (!term || value.getType() != terms.expression(term).type)
          return failure();
        values[value] = term;
      }
    }
    auto &ret = block.back();
    if (!isa<func::ReturnOp>(ret) || !ret.getAttrs().empty() ||
        !terms.charge(1 + ret.getNumOperands()))
      return failure();
    SmallVector<Term> result;
    for (Value value : ret.getOperands()) {
      auto term = values.lookup(value);
      if (!term)
        return failure();
      result.push_back(term);
    }
    return result;
  }
  LogicalResult check(func::FuncOp source, Block &candidate) {
    if (!source.getBody().hasOneBlock() ||
        !llvm::equal(source.getArgumentTypes(), candidate.getArgumentTypes()))
      return refuse(source);
    SmallVector<Term> inputs;
    for (Type type : source.getArgumentTypes())
      inputs.push_back(terms.anchor(type));
    auto before = read(source.front(), inputs, true);
    auto after = read(candidate, inputs, false);
    if (failed(before) || failed(after) || before->size() != after->size())
      return refuse(source);
    for (auto [a, b] : zip(*before, *after))
      if (!terms.equal(a, b))
        return refuse(source);
    return success();
  }
};
HelperNormalizationChecker::HelperNormalizationChecker(Operation *root,
                                                       size_t work)
    : implementation(std::make_unique<Implementation>(root, work)) {}
HelperNormalizationChecker::~HelperNormalizationChecker() = default;
LogicalResult HelperNormalizationChecker::check(func::FuncOp source,
                                                Block &candidate) {
  return implementation->check(source, candidate);
}
} // namespace zkc::mathematical
