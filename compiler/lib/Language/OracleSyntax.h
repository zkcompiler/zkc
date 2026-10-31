#ifndef ZKC_LANGUAGE_ORACLESYNTAX_H
#define ZKC_LANGUAGE_ORACLESYNTAX_H
#include "Internal.h"
namespace zkc::language::detail {
/// Authored spellings of the fixed oracle syntax. Formation and execution
/// remain owned by the ordinary oracle checker and Protocol IR contracts.
struct OracleSyntax {
  llvm::StringLiteral name;
  Expression::Kind kind;
  unsigned operands, parameters;
};
inline const OracleSyntax *oracleSyntax(llvm::StringRef name) {
  using K = Expression::Kind;
  static constexpr OracleSyntax operations[] = {
      {"query", K::OracleQuery, 2, 0},
      {"data", K::OracleContents, 1, 0},
      {"rows", K::OracleRows, 1, 0},
      {"forget_rows", K::OracleForgetRows, 1, 0},
      {"length", K::OracleSequenceLength, 1, 0},
      {"append", K::OracleSequenceAppend, 2, 0},
      {"at", K::OracleSequenceAt, 2, 0},
      {"empty", K::OracleSequenceEmpty, 0, 2}};
  for (const auto &operation : operations)
    if (operation.name == name)
      return &operation;
  return nullptr;
}
} // namespace zkc::language::detail
#endif
