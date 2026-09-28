#ifndef ZKC_FRONTEND_SYNTAX_NAMES_H
#define ZKC_FRONTEND_SYNTAX_NAMES_H

#include "zkc/Source/Model.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>

namespace zkc::frontend::syntax {
/// Lexical category of a static root or data slot, independent of its decoded
/// spelling. A quoted atom is an exact identity or datum, never a name to look
/// up; a number is a natural literal; a name is a reference to resolve.
struct Atom : source::Node {
  enum class Kind { Name, Number, String };
  Kind kind = Kind::Name;
  std::string value;
};

/// An authored declaration path: decoded identifier segments in written order.
/// Meaning comes from resolving the segments, never from joining or splitting
/// a spelling.
struct Path : source::Node {
  source::Names segments;
};
/// Diagnostic spelling only.
inline std::string spelling(const Path &path) {
  return llvm::join(path.segments, "::");
}

/// What resolution selected for a reference. Only resolution writes it; later
/// owners read it instead of reinterpreting the authored path.
struct Target {
  enum class Kind {
    Unresolved,
    /// A lexical value or static binder; `symbol` is its identifier.
    Local,
    /// An emitted declaration symbol; `members` select an enum alternative,
    /// component function, dependency path or associated member below it.
    Declaration,
    /// An installed operation contract.
    Operation,
    /// A member function of an interface-bound component parameter.
    Parameter,
    /// A word of the installed static vocabulary, such as a capability.
    Vocabulary,
  };
  Kind kind = Kind::Unresolved;
  std::string symbol;
  source::Names members;
  static Target operation(llvm::StringRef contract) {
    return {Kind::Operation, contract.str(), {}};
  }
  static Target declaration(llvm::StringRef symbol) {
    return {Kind::Declaration, symbol.str(), {}};
  }
  static Target local(llvm::StringRef name) {
    return {Kind::Local, name.str(), {}};
  }
};
/// The one encoding of a resolved reference into the internal dotted symbol
/// namespace. Strict source identifiers contain no dots, so this is injective.
inline std::string encode(const Target &target) {
  auto result = target.symbol;
  for (const auto &member : target.members)
    result += "." + member;
  return result;
}

/// A declaration reference: its authored path and, after resolution, the
/// selected target.
struct Reference : source::Node {
  Path path;
  Target target;
  Reference() = default;
  /// A reference that later compiler stages construct already resolved.
  explicit Reference(Target resolved) : target(std::move(resolved)) {}
};
inline std::string encode(const Reference &reference) {
  return encode(reference.target);
}

/// One selection step of a value place. The kind is kept until a typed owner
/// checks it against the receiver.
struct Projection : source::Node {
  enum class Kind { Field, Product, Index };
  Kind kind = Kind::Field;
  std::string key;
  bool operator==(const Projection &other) const {
    return kind == other.kind && key == other.key;
  }
};
/// A value path with projection steps. It performs no computation.
struct Place : source::Node {
  Reference root;
  std::vector<Projection> steps;
};
using Places = std::vector<Place>;
using PlaceAssignments = std::vector<std::pair<std::string, Place>>;
/// A resolved local place root. Captures and typed checkers only select from
/// lexical values; a declaration root is never a capturable place.
inline const std::string *localRoot(const Place &place) {
  return place.root.target.kind == Target::Kind::Local
             ? &place.root.target.symbol
             : nullptr;
}
inline bool samePlace(const Place &a, const Place &b) {
  return a.root.target.kind == b.root.target.kind &&
         a.root.target.symbol == b.root.target.symbol &&
         a.root.target.members == b.root.target.members && a.steps == b.steps;
}
inline bool ancestor(const Place &parent, const Place &child) {
  return parent.root.target.kind == child.root.target.kind &&
         parent.root.target.symbol == child.root.target.symbol &&
         parent.root.target.members == child.root.target.members &&
         parent.steps.size() <= child.steps.size() &&
         std::equal(parent.steps.begin(), parent.steps.end(),
                    child.steps.begin());
}
/// Add `value` to a set ordered by first use, where `contains(a, b)` says a
/// covers b. A covered value merges into its cover; a covering value takes the
/// position of the first entry it covers and absorbs the others.
template <typename T, typename Contains, typename Merge>
void unite(std::vector<T> &values, T value, Contains contains, Merge merge) {
  for (auto &existing : values)
    if (contains(existing, value)) {
      merge(existing, std::move(value));
      return;
    }
  size_t first = values.size();
  for (size_t i = values.size(); i-- > 0;)
    if (contains(value, values[i])) {
      merge(value, std::move(values[i]));
      values.erase(values.begin() + i);
      first = i;
    }
  values.insert(values.begin() + std::min(first, values.size()),
                std::move(value));
}
inline void unite(Places &places, Place place) {
  unite(places, std::move(place), ancestor, [](Place &, Place &&) {});
}
/// Diagnostic spelling only; never use it to resolve or check a place.
inline std::string spelling(const Place &place) {
  auto result = place.root.path.segments.empty() ? encode(place.root)
                                                 : spelling(place.root.path);
  for (const auto &step : place.steps)
    result += step.kind == Projection::Kind::Index ? "[" + step.key + "]"
                                                   : "." + step.key;
  return result;
}
} // namespace zkc::frontend::syntax
#endif
