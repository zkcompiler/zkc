#ifndef ZKC_SYNTAX_NOTATION_H
#define ZKC_SYNTAX_NOTATION_H

#include "llvm/ADT/ArrayRef.h"
#include <string>

namespace zkc::syntax {
/// Syntax associated with an ordinary callable. A descriptor asserts no
/// algebraic law; native operations and callable signatures own semantics.
struct NotationDescriptor {
  enum class Position { Prefix, Infix, Postfix, Delimited, Reduction, Index };
  enum class Association { None, Left, Right };
  Position position = Position::Infix;
  Association association = Association::None;
  std::string symbol, closing;
  unsigned precedence = 0, arity = 0;

  /// Visibility and replacement use the token and syntactic position. Other
  /// fields must agree when declarations contribute to the same environment.
  std::string key() const {
    return std::to_string(static_cast<unsigned>(position)) + ":" + symbol +
           (position == Position::Index ? ":" + std::to_string(arity) : "");
  }
  bool operator==(const NotationDescriptor &other) const {
    return position == other.position && association == other.association &&
           symbol == other.symbol && closing == other.closing &&
           precedence == other.precedence && arity == other.arity;
  }
  bool operator!=(const NotationDescriptor &other) const {
    return !(*this == other);
  }
};
/// Shared syntax inventory for parsing, short declarations and validation.
llvm::ArrayRef<NotationDescriptor> defaultNotations();
/// Validate the fixed token repertoire and bounded descriptor shape.
bool validNotationDescriptor(const NotationDescriptor &);
} // namespace zkc::syntax

#endif
