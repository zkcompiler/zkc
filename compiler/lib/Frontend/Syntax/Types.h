#ifndef ZKC_FRONTEND_SYNTAX_TYPES_H
#define ZKC_FRONTEND_SYNTAX_TYPES_H
#include "llvm/ADT/StringRef.h"
namespace zkc::frontend {
struct TypeSpelling {
  llvm::StringLiteral surface, constructor;
};
inline constexpr TypeSpelling typeSpellings[] = {
    {"bool", "bool"},
    {"index", "index"},
    {"Indices", "indices"},
    {"Polynomial", "polynomial"},
    {"Table", "table"},
    {"Point", "point"},
    {"Round", "round"},
    {"Rng", "rng"},
    {"Nonce", "nonce"},
    {"Transcript", "transcript"},
    {"Commitment", "commitment"},
    {"Commitments", "commitments"},
    {"OpeningStates", "opening_states"},
    {"Proof", "proof"},
    {"ProverKey", "prover_key"},
    {"VerifierKey", "verifier_key"},
    {"OpeningState", "opening_state"}};
// Vector<Element> selects vector or groups; Matrix<Element> selects matrix.
// All other unary constructors take a nominal domain, not an element type.
} // namespace zkc::frontend
#endif
