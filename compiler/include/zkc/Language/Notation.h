#ifndef ZKC_LANGUAGE_NOTATION_H
#define ZKC_LANGUAGE_NOTATION_H

#include <string>

namespace zkc::language {
/// Syntax associated with an ordinary callable. A descriptor asserts no
/// algebraic law; native operations and callable signatures own semantics.
struct NotationDescriptor {
  enum class Position { Prefix, Infix, Postfix, Delimited, Reduction };
  enum class Association { None, Left, Right };
  Position position = Position::Infix;
  Association association = Association::None;
  std::string symbol, closing;
  unsigned precedence = 0, arity = 0;

  /// Visibility and replacement use the token and syntactic position. Other
  /// fields must agree when declarations contribute to the same environment.
  std::string key() const {
    return std::to_string(static_cast<unsigned>(position)) + ":" + symbol;
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
} // namespace zkc::language

#endif
