#ifndef ZKC_RELATION_AIR_H
#define ZKC_RELATION_AIR_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace zkc::relation {

struct AIRLimits {
  static constexpr size_t bytes = 8 * 1024 * 1024;
  static constexpr uint32_t nodes = 65536, depth = 64, constraints = 4096;
  static constexpr uint32_t columns = 65536, height = 65536,
                            publicInputs = 65536;
  static constexpr uint32_t degree = 1048576, offset = 65536;
  static constexpr uint64_t cells = 1048576, work = 4194304;
};

/// A trace cell, absolute in a plan, relative (row = offset) in analysis.
struct AIRCell {
  uint32_t row = 0, column = 0;
  bool operator==(const AIRCell &other) const {
    return row == other.row && column == other.column;
  }
  bool operator<(const AIRCell &other) const {
    return row < other.row || (row == other.row && column < other.column);
  }
};

enum class AIRKind { Constant, Public, Read, Add, Mul, Neg };
/// Nodes refer strictly backwards within a constraint. Last node is the root;
/// all nodes must be reachable. Inactive members must keep their default value.
struct AIRNode {
  AIRKind kind = AIRKind::Constant;
  std::string value = "0";
  uint32_t lhs = 0, rhs = 0, offset = 0, column = 0, index = 0;
  static AIRNode constant(std::string value);
  static AIRNode publicInput(uint32_t index);
  static AIRNode read(uint32_t offset, uint32_t column);
  static AIRNode add(uint32_t lhs, uint32_t rhs);
  static AIRNode mul(uint32_t lhs, uint32_t rhs);
  static AIRNode neg(uint32_t operand);
};

enum class AIRScopeKind { Every, First, Last, Transition };
struct AIRScope {
  AIRScopeKind kind = AIRScopeKind::Every;
  uint32_t lookahead = 0; // Only Transition admits a nonzero lookahead.
};
struct AIRConstraint {
  AIRScope scope;
  std::vector<AIRNode> expression;
  std::optional<uint32_t> declaredMaxOffset, declaredDegree;
};
struct AIRConstraintAnalysis {
  std::vector<AIRCell> reads; // Sorted unique relative coordinates.
  uint32_t maxOffset = 0, degree = 0, depth = 0;
  uint32_t readNodes = 0;
};
struct AIRTraceLayout {
  std::string field;
  uint32_t height = 0, columns = 0;
};
struct AIRTrace {
  AIRTraceLayout layout;
  std::vector<std::string> cells; // Row major, including unused columns.
};
struct AIRResidual {
  uint32_t row, constraint;
  std::string value;
};
struct AIREvaluation {
  bool satisfied = true;
  uint64_t scheduledReads = 0;
  std::vector<AIRResidual> residuals;
  llvm::json::Value encode() const;
};
class AIRPlan;

/// Finite arithmetic AIR, aligned with Zkc.Relation.AIR's noncyclic semantics.
/// Degree counts trace variables; public values and field constants have degree
/// zero. Neg is multiplication by -1. No algebraic cancellation is assumed.
/// Polynomial-consumer bounds live in AIRPolynomial.h; this relation itself
/// does not select a domain, selector, commitment or proof protocol.
class AIR {
public:
  static llvm::Expected<AIR> create(std::string field, uint32_t columns,
                                    uint32_t publicInputs,
                                    std::vector<AIRConstraint> constraints);
  llvm::StringRef field() const { return fieldName; }
  uint32_t columns() const { return columnCount; }
  uint32_t publicInputs() const { return publicCount; }
  llvm::ArrayRef<AIRConstraint> constraints() const { return constraints_; }
  llvm::ArrayRef<AIRConstraintAnalysis> facts() const { return facts_; }
  llvm::json::Value encode() const;
  llvm::json::Value analysis() const;
  llvm::Expected<AIRPlan> compile(uint32_t height) const;
  /// Dense admission checks every field value, including unused coordinates.
  /// scheduledReads counts only subsequent selective evaluation fetches.
  llvm::Expected<AIREvaluation>
  evaluate(const AIRTrace &, llvm::ArrayRef<std::string> statement) const;

private:
  AIR(std::string field, uint32_t columns, uint32_t publicInputs,
      std::vector<AIRConstraint>, std::vector<AIRConstraintAnalysis>);
  std::string fieldName;
  uint32_t columnCount, publicCount;
  std::vector<AIRConstraint> constraints_;
  std::vector<AIRConstraintAnalysis> facts_;
};

/// Immutable compiled schedule. A global cache fetches each referenced absolute
/// cell once, including reads shared by different rows/constraints. Compilation
/// checks windows and bounds total instruction work before expanding schedules.
class AIRPlan {
public:
  struct Invocation {
    uint32_t row, constraint;
    std::vector<uint32_t> slots; // One per syntactic read node, in node order.
  };
  llvm::ArrayRef<AIRCell> cells() const { return cells_; }
  llvm::ArrayRef<Invocation> invocations() const { return invocations_; }
  llvm::json::Value encode() const;
  /// The reader must describe one immutable field-valued trace. Only selected
  /// cells are requested; the callback's unused cells cannot be validated.
  llvm::Expected<AIREvaluation>
  evaluate(const AIRTraceLayout &, llvm::ArrayRef<std::string> statement,
           llvm::function_ref<llvm::Expected<std::string>(AIRCell)> read) const;
  llvm::Expected<AIREvaluation>
  evaluate(const AIRTrace &, llvm::ArrayRef<std::string> statement) const;

private:
  friend class AIR;
  AIRPlan(AIR relation, uint32_t height);
  AIR relation;
  uint32_t height;
  uint64_t naiveReads = 0, instructionWork = 0;
  std::vector<AIRCell> cells_;
  std::vector<Invocation> invocations_;
};

/// Strict v1 object codec: nodes are an ordered arena, constants canonical
/// decimal strings. Encoding is deterministic, not a semantic normal form.
llvm::Expected<AIR> readAIR(const llvm::json::Value &);
/// Use this at untrusted text boundaries: limits bytes/nesting before JSON
/// parse.
llvm::Expected<AIR> readAIRText(llvm::StringRef);
llvm::Expected<AIRTrace> readAIRTrace(const llvm::json::Value &);
/// Shared bounded JSON reader for standalone AIR fixture/driver input.
llvm::Expected<llvm::json::Value> readAIRJson(llvm::StringRef);

} // namespace zkc::relation
#endif
