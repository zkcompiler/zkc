#ifndef ZKC_FRONTEND_SEMANTICS_OPERATORS_H
#define ZKC_FRONTEND_SEMANTICS_OPERATORS_H
#include "llvm/ADT/StringRef.h"
#include <array>
namespace zkc::frontend {
/// The spelling of an installed operation as an infix or prefix operator.
/// What the operation means stays with its installed contract; this table
/// only names it, as `Types.h` names logical types. `operands` are the logical
/// constructors in written order, and `order[k]` is the written operand passed
/// as the operation's k-th input. A unary entry leaves the second slot empty.
struct OperatorSpelling {
  llvm::StringLiteral symbol;
  std::array<llvm::StringLiteral, 2> operands;
  llvm::StringLiteral operation;
  std::array<unsigned, 2> order;
  unsigned arity() const { return operands[1].empty() ? 1 : 2; }
};
// Elementwise vector multiplication is left to its name: `*` between two
// vectors reads as a dot product as easily as a Hadamard product.
inline constexpr OperatorSpelling operatorSpellings[] = {
    {"+", {"field", "field"}, "field.add", {0, 1}},
    {"-", {"field", "field"}, "field.sub", {0, 1}},
    {"*", {"field", "field"}, "field.mul", {0, 1}},
    {"-", {"field", ""}, "field.neg", {0, 0}},
    {"+", {"group", "group"}, "curve.add", {0, 1}},
    {"-", {"group", ""}, "curve.neg", {0, 0}},
    {"*", {"group", "field"}, "curve.scale", {0, 1}},
    {"*", {"field", "group"}, "curve.scale", {1, 0}},
    {"+", {"vector", "vector"}, "vector.add", {0, 1}},
    {"-", {"vector", "vector"}, "vector.sub", {0, 1}},
    {"*", {"vector", "field"}, "vector.scale", {0, 1}},
    {"*", {"field", "vector"}, "vector.scale", {1, 0}},
    {"+", {"index", "index"}, "index.add", {0, 1}},
    {"-", {"index", "index"}, "index.sub", {0, 1}},
    {"*", {"index", "index"}, "index.mul", {0, 1}}};
} // namespace zkc::frontend
#endif
