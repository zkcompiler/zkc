#ifndef ZKC_CONTRACTS_RING_EXPRESSION_H
#define ZKC_CONTRACTS_RING_EXPRESSION_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace zkc::ring {

struct Limits {
  static constexpr size_t bytes = 8 * 1024 * 1024;
  static constexpr uint32_t nodes = 65536, inputs = 65536, outputs = 4096;
  static constexpr uint32_t degree = 1048576, depth = 1024;
};

struct Input {
  std::string field;
};

enum class Kind { Constant, Input, Add, Mul, Neg, Embed };
struct Node {
  Kind kind = Kind::Constant;
  std::string field, constant = "0";
  uint32_t left = 0, right = 0, input = 0;
  static Node literal(std::string field, std::string canonicalNatural);
  static Node slot(uint32_t index);
  static Node add(uint32_t left, uint32_t right);
  static Node mul(uint32_t left, uint32_t right);
  static Node neg(uint32_t operand);
  static Node embed(std::string targetField, uint32_t operand);
};

struct Fact {
  std::string field;
  /// Unit-weight degree, saturated at Limits::degree + 1 (not a bound there).
  uint32_t degree, depth;
};

/// A closed, typed DAG for formal ring substitution. This contract admits only
/// prime-subfield natural literals; arbitrary extension constants are explicit
/// degree-zero inputs. Inputs have meanings assigned by a separate closed view.
/// This arena does not contain AIR reads, challenges, callbacks or inverses.
class Expression {
public:
  static llvm::Expected<Expression> create(std::vector<Input> inputs,
                                           std::vector<Node> nodes,
                                           std::vector<uint32_t> outputs);
  llvm::ArrayRef<Input> inputs() const { return inputs_; }
  llvm::ArrayRef<Node> nodes() const { return nodes_; }
  llvm::ArrayRef<uint32_t> outputs() const { return outputs_; }
  llvm::ArrayRef<Fact> facts() const { return facts_; }
  /// Per-node degree bounds for a particular substitution. The closed view
  /// derives weights from its bindings. Formation facts use weight one for
  /// every input and saturate at Limits::degree + 1. They do not restrict
  /// admission; public/constant bindings can use weight zero.
  llvm::Expected<std::vector<uint32_t>>
  degrees(llvm::ArrayRef<uint32_t> inputWeights) const;
  /// Sorted input indices actually used by the selected output positions.
  llvm::Expected<std::vector<uint32_t>>
  usedInputs(llvm::ArrayRef<uint32_t> outputPositions) const;
  llvm::json::Value encode() const;
  std::string identity() const;

  /// Interpret the selected outputs in an algebra over each declared field.
  /// Algebra methods return Expected<Value>: input(index,field),
  /// constant(field,natural), add(field,a,b), mul(field,a,b), neg(field,a),
  /// embed(sourceField,targetField,a). The caller supplies an immutable input
  /// assignment with the admitted types. Each used input is requested once.
  /// Arithmetic and its allocation/work limits remain the provider's contract;
  /// scalar, packed and coefficient interpreters must preserve this expression.
  template <typename Value, typename Algebra>
  llvm::Expected<std::vector<Value>>
  evaluate(llvm::ArrayRef<uint32_t> outputPositions, Algebra &algebra) const {
    auto needed = dependencies(outputPositions);
    if (!needed)
      return needed.takeError();
    std::vector<std::optional<Value>> values(nodes_.size()),
        slots(inputs_.size());
    for (uint32_t i = 0; i < nodes_.size(); ++i) {
      if (!(*needed)[i])
        continue;
      const auto &node = nodes_[i];
      const auto &field = facts_[i].field;
      auto eval = [&]() -> llvm::Expected<Value> {
        switch (node.kind) {
        case Kind::Constant:
          return algebra.constant(field, node.constant);
        case Kind::Input:
          if (!slots[node.input]) {
            auto value = algebra.input(node.input, field);
            if (!value)
              return value.takeError();
            slots[node.input] = std::move(*value);
          }
          return *slots[node.input];
        case Kind::Add:
          return algebra.add(field, *values[node.left], *values[node.right]);
        case Kind::Mul:
          return algebra.mul(field, *values[node.left], *values[node.right]);
        case Kind::Neg:
          return algebra.neg(field, *values[node.left]);
        case Kind::Embed:
          return algebra.embed(facts_[node.left].field, field,
                               *values[node.left]);
        }
        llvm_unreachable("admitted ring node");
      };
      auto result = eval();
      if (!result)
        return result.takeError();
      values[i] = std::move(*result);
    }
    std::vector<Value> result;
    result.reserve(outputPositions.size());
    for (uint32_t position : outputPositions)
      result.push_back(*values[outputs_[position]]);
    return result;
  }

private:
  Expression(std::vector<Input>, std::vector<Node>, std::vector<uint32_t>,
             std::vector<Fact>);
  llvm::Expected<std::vector<bool>>
  dependencies(llvm::ArrayRef<uint32_t> outputPositions) const;
  std::vector<Input> inputs_;
  std::vector<Node> nodes_;
  std::vector<uint32_t> outputs_;
  std::vector<Fact> facts_;
};

llvm::Expected<Expression> readExpression(const llvm::json::Value &);
llvm::Expected<Expression> readExpressionText(llvm::StringRef);

} // namespace zkc::ring
#endif
