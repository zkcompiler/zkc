#include "zkc/Analysis/ResidueArithmetic.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallString.h"
#include <map>
#include <optional>
#include <tuple>

using namespace mlir;
using llvm::APInt;
namespace zkc::residue {
namespace {
constexpr unsigned maximumInstructions = 4096, maximumArguments = 256;
bool attrs(Operation *op, ArrayRef<StringRef> names) {
  return llvm::all_of(op->getAttrs(), [&](NamedAttribute attr) {
    return llvm::is_contained(names, attr.getName().getValue());
  });
}
unsigned width(Type type) {
  if (auto word = dyn_cast<IntegerType>(type))
    return word.isSignless() ? word.getWidth() : 0;
  if (auto residue = dyn_cast<ValueType>(type)) {
    auto modulus = residue.getModulus();
    auto word =
        modulus ? dyn_cast<IntegerType>(modulus.getType()) : IntegerType{};
    return word && word.isUnsigned() ? word.getWidth() : 0;
  }
  return 0;
}
func::FuncOp packet(ModuleOp module, unsigned maximumWidth) {
  if (!module || !module.getBodyRegion().hasOneBlock() ||
      !module->getAttrs().empty() || !llvm::hasSingleElement(*module.getBody()))
    return {};
  auto function = dyn_cast<func::FuncOp>(module.getBody()->front());
  if (!function || !function.getBody().hasOneBlock() ||
      !attrs(function, {"sym_name", "function_type"}) ||
      function.getNumArguments() > maximumArguments ||
      function.getNumResults() > maximumArguments)
    return {};
  auto bounded = [&](Type type) {
    unsigned bits = width(type);
    return bits && bits <= maximumWidth;
  };
  if (!llvm::all_of(function.getArgumentTypes(), bounded) ||
      !llvm::all_of(function.getResultTypes(), bounded))
    return {};
  unsigned instructions = 0;
  for (Operation &op : function.front()) {
    if (++instructions > maximumInstructions || op.getNumRegions() ||
        op.getNumSuccessors() || op.getNumResults() > 1 ||
        op.getNumOperands() > maximumArguments ||
        !llvm::all_of(op.getResultTypes(), bounded))
      return {};
  }
  return function;
}

// Hash-consed expressions in Z/qZ. Only local ring laws are used: constants,
// identities, commutativity and double negation. This deliberately does not
// expand polynomials or promise a complete equivalence decision procedure.
// Both readers use this algebra; neither reader constructs the other's IR.
class Expressions {
  enum class Kind { Literal, Input, Add, Multiply, Negate };
  using Key = std::tuple<Kind, unsigned, unsigned, std::string>;
  struct Term {
    Kind kind;
    unsigned left, right;
    std::optional<APInt> literal;
  };
  std::map<Key, unsigned> interned;
  SmallVector<Term> terms;
  APInt q;
  unsigned intern(Key key, std::optional<APInt> literal = {}) {
    auto found = interned.find(key);
    if (found != interned.end())
      return found->second;
    unsigned id = terms.size();
    terms.push_back({std::get<0>(key), std::get<1>(key), std::get<2>(key),
                     std::move(literal)});
    interned.emplace(std::move(key), id);
    return id;
  }

public:
  explicit Expressions(APInt modulus) : q(std::move(modulus)) {}
  unsigned literal(APInt value) {
    value = value.urem(q);
    llvm::SmallString<32> text;
    value.toString(text, 16, false);
    return intern({Kind::Literal, 0, 0, text.str().str()}, value);
  }
  unsigned input(unsigned slot) { return intern({Kind::Input, slot, 0, {}}); }
  unsigned negate(unsigned value) {
    const auto &term = terms[value];
    if (term.literal)
      return literal(q - *term.literal);
    if (term.kind == Kind::Negate)
      return term.left;
    return intern({Kind::Negate, value, 0, {}});
  }
  unsigned binary(bool multiply, unsigned left, unsigned right) {
    auto a = terms[left].literal, b = terms[right].literal;
    if (a && b)
      return literal(multiply ? *a * *b : *a + *b);
    if (a && a->isZero())
      return multiply ? left : right;
    if (b && b->isZero())
      return multiply ? right : left;
    if (multiply && a && a->isOne())
      return right;
    if (multiply && b && b->isOne())
      return left;
    if (!multiply &&
        ((terms[left].kind == Kind::Negate && terms[left].left == right) ||
         (terms[right].kind == Kind::Negate && terms[right].left == left)))
      return literal(APInt(q.getBitWidth(), 0));
    if (right < left)
      std::swap(left, right);
    return intern({multiply ? Kind::Multiply : Kind::Add, left, right, {}});
  }
  OwningOpRef<ModuleOp> render(func::FuncOp signature, ValueType type,
                               unsigned root) {
    OwningOpRef<ModuleOp> module(ModuleOp::create(signature.getLoc()));
    OpBuilder builder(module->getBodyRegion());
    auto function = func::FuncOp::create(builder, signature.getLoc(),
                                         signature.getSymName(),
                                         signature.getFunctionType());
    auto *body = function.addEntryBlock();
    builder.setInsertionPointToEnd(body);
    SmallVector<bool> live(terms.size(), false);
    SmallVector<unsigned> pending{root};
    while (!pending.empty()) {
      unsigned id = pending.pop_back_val();
      if (live[id])
        continue;
      live[id] = true;
      const auto &term = terms[id];
      if (term.kind == Kind::Add || term.kind == Kind::Multiply)
        pending.push_back(term.right);
      if (term.kind == Kind::Add || term.kind == Kind::Multiply ||
          term.kind == Kind::Negate)
        pending.push_back(term.left);
    }
    auto location = signature.getLoc();
    auto literal = [&](const APInt &value) -> Value {
      auto attr = LiteralAttr::get(
          type.getContext(), type,
          IntegerAttr::get(type.getModulus().getType(),
                           value.zextOrTrunc(type.getWidth())));
      return ResidueConstantOp::create(builder, location, type, attr);
    };
    SmallVector<Value> values(terms.size());
    for (auto [id, term] : llvm::enumerate(terms)) {
      if (!live[id])
        continue;
      switch (term.kind) {
      case Kind::Input:
        values[id] = body->getArgument(term.left);
        break;
      case Kind::Literal:
        values[id] = literal(*term.literal);
        break;
      case Kind::Add:
        values[id] = ResidueAddOp::create(
            builder, location, type, values[term.left], values[term.right]);
        break;
      case Kind::Multiply:
        values[id] = ResidueMultiplyOp::create(
            builder, location, type, values[term.left], values[term.right]);
        break;
      case Kind::Negate:
        values[id] = ResidueSubtractOp::create(
            builder, location, type, literal(APInt(type.getWidth(), 0)),
            values[term.left]);
        break;
      }
    }
    func::ReturnOp::create(builder, location, values[root]);
    return module;
  }
};

enum class Meaning { Natural, Centered, Shifted, Threshold };
struct Fact {
  unsigned expression;
  APInt low, high;
  Meaning meaning = Meaning::Natural;
  // Non-natural facts name the same canonical expression. Their interpretation
  // is exact only at the checked select boundary, not ordinary integer algebra.
};
using Facts = llvm::DenseMap<Value, Fact>;
class Reader {
  APInt q, zero;
  Expressions expressions;
  unsigned bits;
  APInt extend(const APInt &value) { return value.zextOrTrunc(bits); }
  Fact canonical(unsigned expression) { return {expression, zero, q - 1}; }
  bool isCanonical(const Fact &fact) {
    return fact.meaning == Meaning::Natural && fact.high.ult(q);
  }
  bool fits(const Fact &fact, unsigned width) {
    return fact.high.getActiveBits() <= width;
  }
  Fact constant(const APInt &value) {
    auto natural = extend(value);
    return {expressions.literal(natural), natural, natural};
  }
  std::optional<Fact> operation(Operation &op, const Facts &facts,
                                bool source) {
    SmallVector<Fact> inputs;
    for (Value operand : op.getOperands()) {
      auto found = facts.find(operand);
      if (found == facts.end())
        return {};
      inputs.push_back(found->second);
    }
    if (op.getNumResults() != 1)
      return {};
    if (source) {
      if (auto literal = dyn_cast<ResidueConstantOp>(op)) {
        if (!attrs(&op, {"value"}))
          return {};
        return constant(literal.getValue().getValue().getValue());
      }
      if (auto literal = dyn_cast<arith::ConstantOp>(op)) {
        if (!attrs(&op, {"value"}))
          return {};
        auto value = dyn_cast<IntegerAttr>(literal.getValue());
        return value ? std::optional<Fact>(constant(value.getValue()))
                     : std::nullopt;
      }
      if (!op.getAttrs().empty())
        return {};
      if (isa<ResidueAddOp, ResidueSubtractOp, ResidueMultiplyOp>(op)) {
        if (!isCanonical(inputs[0]) || !isCanonical(inputs[1]))
          return {};
        unsigned right = inputs[1].expression;
        if (isa<ResidueSubtractOp>(op))
          right = expressions.negate(right);
        return canonical(expressions.binary(isa<ResidueMultiplyOp>(op),
                                            inputs[0].expression, right));
      }
      if (isa<ResidueProjectOp>(op) && inputs[0].meaning == Meaning::Natural)
        return canonical(inputs[0].expression);
      if (isa<ResidueLiftOp, ResidueCenteredLiftOp>(op) &&
          isCanonical(inputs[0])) {
        auto result = inputs[0];
        if (isa<ResidueCenteredLiftOp>(op))
          result.meaning = Meaning::Centered;
        return result;
      }
      return {};
    }
    if (auto literal = dyn_cast<arith::ConstantOp>(op)) {
      auto value = dyn_cast<IntegerAttr>(literal.getValue());
      return value && attrs(&op, {"value"})
                 ? std::optional<Fact>(constant(value.getValue()))
                 : std::nullopt;
    }
    if (isa<arith::ExtUIOp, arith::TruncIOp>(op)) {
      bool admitted = op.getAttrs().empty();
      if (auto truncate = dyn_cast<arith::TruncIOp>(op))
        admitted =
            attrs(&op, {"overflowFlags"}) &&
            truncate.getOverflowFlags() == arith::IntegerOverflowFlags::none;
      if (!admitted || inputs[0].meaning != Meaning::Natural ||
          !fits(inputs[0], width(op.getResult(0).getType())))
        return {};
      return inputs[0];
    }
    if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
      if (!attrs(&op, {"predicate"}) ||
          compare.getPredicate() != arith::CmpIPredicate::uge ||
          !isCanonical(inputs[0]) || inputs[1].meaning != Meaning::Natural ||
          inputs[1].low != inputs[1].high ||
          inputs[1].low != q.lshr(1) + (q & 1))
        return {};
      return Fact{inputs[0].expression, zero, zero + 1, Meaning::Threshold};
    }
    if (isa<arith::SelectOp>(op)) {
      if (!op.getAttrs().empty() || inputs[0].meaning != Meaning::Threshold ||
          inputs[1].meaning != Meaning::Shifted || !isCanonical(inputs[2]) ||
          inputs[0].expression != inputs[1].expression ||
          inputs[0].expression != inputs[2].expression)
        return {};
      auto result = inputs[2];
      result.meaning = Meaning::Centered;
      return result;
    }
    if (inputs.size() != 2 || inputs[0].meaning != Meaning::Natural ||
        inputs[1].meaning != Meaning::Natural)
      return {};
    const auto &a = inputs[0], &b = inputs[1];
    if (isa<arith::RemUIOp>(op)) {
      if (!op.getAttrs().empty() || b.low != q || b.high != q)
        return {};
      return canonical(a.expression);
    }
    if (!attrs(&op, {"overflowFlags"}))
      return {};
    Fact result = canonical(0);
    if (auto add = dyn_cast<arith::AddIOp>(op)) {
      if (add.getOverflowFlags() != arith::IntegerOverflowFlags::none)
        return {};
      result = {expressions.binary(false, a.expression, b.expression),
                a.low + b.low, a.high + b.high};
    } else if (auto multiply = dyn_cast<arith::MulIOp>(op)) {
      if (multiply.getOverflowFlags() != arith::IntegerOverflowFlags::none)
        return {};
      result = {expressions.binary(true, a.expression, b.expression),
                a.low * b.low, a.high * b.high};
    } else if (auto subtract = dyn_cast<arith::SubIOp>(op)) {
      if (subtract.getOverflowFlags() != arith::IntegerOverflowFlags::none)
        return {};
      if (isCanonical(a) && b.low == q && b.high == q) {
        result = a;
        result.meaning = Meaning::Shifted;
        return result;
      }
      if (a.low.ult(b.high))
        return {};
      result = {expressions.binary(false, a.expression,
                                   expressions.negate(b.expression)),
                a.low - b.high, a.high - b.low};
    } else {
      return {};
    }
    return fits(result, width(op.getResult(0).getType()))
               ? std::optional<Fact>(result)
               : std::nullopt;
  }

  std::optional<SmallVector<Fact>> read(func::FuncOp function,
                                        func::FuncOp signature, bool source) {
    Facts facts;
    for (auto [arg, original] :
         llvm::zip(function.getArguments(), signature.getArguments())) {
      auto fact = canonical(expressions.input(arg.getArgNumber()));
      if (!isa<ValueType>(original.getType()))
        fact.high = APInt::getLowBitsSet(bits, width(original.getType()));
      facts.try_emplace(arg, std::move(fact));
    }
    for (Operation &op : function.front()) {
      if (auto returned = dyn_cast<func::ReturnOp>(op)) {
        if (&op != &function.front().back() || !op.getAttrs().empty())
          return {};
        SmallVector<Fact> outputs;
        for (Value value : returned.getOperands()) {
          auto found = facts.find(value);
          if (found == facts.end() ||
              (!isCanonical(found->second) &&
               found->second.meaning != Meaning::Centered))
            return {};
          outputs.push_back(found->second);
        }
        return outputs;
      }
      auto fact = operation(op, facts, source);
      if (!fact)
        return {};
      facts.try_emplace(op.getResult(0), std::move(*fact));
    }
    return {};
  }

public:
  Reader(APInt modulus, unsigned arithmeticWidth)
      : q(modulus.zext(arithmeticWidth)), zero(arithmeticWidth, 0),
        expressions(q), bits(arithmeticWidth) {}
  bool equivalent(func::FuncOp source, func::FuncOp candidate,
                  OwningOpRef<ModuleOp> *decoded = nullptr) {
    auto expected = read(source, source, true);
    auto actual = read(candidate, source, false);
    if (!expected || !actual || expected->size() != actual->size())
      return false;
    for (auto [a, b] : llvm::zip(*expected, *actual))
      if (a.expression != b.expression || a.meaning != b.meaning)
        return false;
    if (decoded) {
      if (source.getNumResults() != 1)
        return false;
      auto type = dyn_cast<ValueType>(source.getResultTypes()[0]);
      if (!type || !llvm::all_of(source.getArgumentTypes(),
                                 [&](Type input) { return input == type; }))
        return false;
      *decoded = expressions.render(source, type, actual->front().expression);
    }
    return true;
  }
};

bool correspondence(ModuleOp source, ModuleOp candidate,
                    OwningOpRef<ModuleOp> *decoded = nullptr) {
  auto original = packet(source, MaximumWordWidth);
  auto actual = packet(candidate, 2 * MaximumWordWidth);
  if (!original || !actual || failed(verify(source)) ||
      failed(verify(candidate)) || original.getSymName() != actual.getSymName())
    return false;
  ValueType residue;
  unsigned widest = 0;
  auto inspect = [&](Type type) {
    widest = std::max(widest, width(type));
    if (auto value = dyn_cast<ValueType>(type)) {
      auto modulus = value.getModulus();
      auto word =
          modulus ? dyn_cast<IntegerType>(modulus.getType()) : IntegerType{};
      if (!word || !word.isUnsigned() || modulus.getValue().ult(2))
        return false;
      if (residue && residue != value)
        return false;
      residue = value;
    }
    return true;
  };
  if (!llvm::all_of(original.getArgumentTypes(), inspect) ||
      !llvm::all_of(original.getResultTypes(), inspect))
    return false;
  for (Operation &op : original.front())
    if (!llvm::all_of(op.getResultTypes(), inspect))
      return false;
  if (!residue)
    return false;
  auto converted = [&](Type type) -> Type {
    return isa<ValueType>(type)
               ? IntegerType::get(source.getContext(), width(type))
               : type;
  };
  SmallVector<Type> inputs, outputs;
  llvm::transform(original.getArgumentTypes(), std::back_inserter(inputs),
                  converted);
  llvm::transform(original.getResultTypes(), std::back_inserter(outputs),
                  converted);
  if (actual.getFunctionType() !=
      FunctionType::get(source.getContext(), inputs, outputs))
    return false;
  for (Operation &op : actual.front())
    for (Type type : op.getResultTypes()) {
      if (!isa<IntegerType>(type))
        return false;
      widest = std::max(widest, width(type));
    }
  // Enough bits for every intermediate range product, including a malicious
  // candidate's largest words. Range arithmetic itself never silently wraps.
  return Reader(residue.getModulus().getValue(), 2 * widest + 1)
      .equivalent(original, actual, decoded);
}
} // namespace
LogicalResult verifyArithmetic(ModuleOp source, ModuleOp candidate) {
  if (correspondence(source, candidate))
    return success();
  return candidate ? diagnostics::emit(
                         candidate.emitError(), "represented-arithmetic",
                         "word candidate lacks exact residue correspondence")
                   : failure();
}
OwningOpRef<ModuleOp> consumeArithmetic(ModuleOp source, ModuleOp candidate) {
  OwningOpRef<ModuleOp> decoded;
  if (!correspondence(source, candidate, &decoded) || failed(verify(*decoded)))
    return {};
  return decoded;
}
} // namespace zkc::residue
