#ifndef ZKC_CONTRACTS_REQUIREMENTS_H
#define ZKC_CONTRACTS_REQUIREMENTS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::requirements {

/// Terms are interned in dependency order. A root is a parameter or nominal
/// identity; a projection retains both its parent and associated member name.
/// An application has a head in name and ordered arguments (including zero).
/// Sort checking and installed nominal consistency belong to the caller.
struct Term {
  std::string name;
  std::optional<unsigned> parent = std::nullopt;
  std::optional<std::vector<unsigned>> arguments = std::nullopt;
};

struct Predicate {
  enum class Kind { Equal, Relation };
  Kind kind;
  std::string relation;
  std::vector<unsigned> arguments;

  static Predicate equal(unsigned left, unsigned right);
  static Predicate holds(std::string relation, std::vector<unsigned> arguments);
  bool operator==(const Predicate &other) const;
};

/// Installed implication between unary capabilities, not a cryptographic
/// assurance assertion. Relations with multiple arguments remain explicit.
struct Implication {
  std::string premise, conclusion;
};

enum class Rule {
  Assumption,
  Reflexivity,
  Symmetry,
  Transitivity,
  Projection,
  Transport,
  Implication,
  Application
};

/// Premises always refer to earlier steps, allowing a small independent checker
/// to replay the derivation without trusting the native search algorithm.
struct Step {
  Predicate conclusion;
  Rule rule;
  std::vector<unsigned> premises;
  unsigned declaration = 0;
};

struct Result {
  std::vector<Step> steps;
  /// An absent proof means unresolved, never a proof of negation.
  std::vector<std::optional<unsigned>> goals;
};

/// Decide the finite equality/congruence and relational transport fragment.
/// No terms are invented during closure. No caller-owned declarations mutate.
/// Alternatives are separate queries: their requirements are not conjoined.
llvm::Expected<Result> derive(llvm::ArrayRef<Term> terms,
                              llvm::ArrayRef<Predicate> assumptions,
                              llvm::ArrayRef<Implication> implications,
                              llvm::ArrayRef<Predicate> goals);

/// Replay every step, including unused steps, without trusting proof search.
/// Missing goal indices mean unresolved; all present indices must prove the
/// exact corresponding goal. Invalid formation or derivations are errors.
llvm::Error checkCertificate(llvm::ArrayRef<Term> terms,
                             llvm::ArrayRef<Predicate> assumptions,
                             llvm::ArrayRef<Implication> implications,
                             llvm::ArrayRef<Predicate> goals,
                             const Result &certificate);

} // namespace zkc::requirements

#endif
