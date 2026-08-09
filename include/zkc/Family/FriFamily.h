//===- FriFamily.h - the FRI family template --------------------*- C++ -*-===//
// Family generation: a family template authors concrete reduction contracts
// and the spine that instantiates them; an instance is an ordinary
// content-addressed sealed protocol. This library is the UNJUDGED
// emission half: it turns one declarative instance description into a closed
// ProtocolVocabulary and the PIR spine that the seal battery then judges like
// any hand-written input. Nothing here is a trust boundary — a wrong template
// is refused at seal, and the lit gate sends generated depths through
// vocabulary lint and seal.
//
// The description is a closed point selection: typed scalars and fixed-shape
// objects only, unknown fields refused, and nothing in the file that the
// template can derive. Structure lives here, in the template; pressure to put
// structure in the description is the signal for a separate DSL rather than a
// contract extension.
//===----------------------------------------------------------------------===//
#ifndef ZKC_FAMILY_FRIFAMILY_H
#define ZKC_FAMILY_FRIFAMILY_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <optional>
#include <string>
#include <vector>

namespace zkc {
namespace family {

/// One parameter of a family template: the declaration the JSON
/// validation and the CLI help both render from, so there is exactly
/// one spelling of the parameter surface. Validation is hand-rolled per
/// field beside its semantic checks; the row carries what both renderers
/// read.
struct ParamSpec {
  llvm::StringRef name;
  bool required;
  llvm::StringRef doc;
};

/// The FRI template's parameter surface, in documentation order.
llvm::ArrayRef<ParamSpec> friParamSpecs();

/// A parsed, validated FRI instance description: which member of the
/// family, not how the family is shaped.
struct FriDescription {
  std::string name;       // protocol name
  int64_t k = 0;          // fold depth
  std::string fieldOrder; // fold-challenge space, exact decimal
  int64_t queryLog2 = 0;  // query space is 2^queryLog2
  int64_t ell = 0;        // iid query repetitions
  /// Which analysis parameters the generated reduce declares.  This is
  /// protocol content, not a theorem selection: a derivation later chooses a
  /// rule whose machine conditions read whichever parameters it needs.
  std::string analysis; // "none", "johnson", or "udr"
  // Johnson analysis parameters, declared on the reduce.
  int64_t johnsonM = 0;
  std::string johnsonEta;   // rational, "a/b"
  std::string johnsonDelta; // rational, "a/b"
  // Unique-decoding proximity, declared on the reduce.
  std::string udrTheta;                // rational, "a/b"
  std::optional<int64_t> grindingBits; // pow space is 2^bits
  /// The challenger-value-faithful variant
  /// (evaluation/upstream/plonky3-replay/README.md): final-polynomial coefficient
  /// in the clear, per-round arity binds, a one-word nonce, and the
  /// construction routes that make the prover endpoint derivable.
  bool valueFaithful = false;
  std::string sponge, iv;              // construction profile axes
  std::string extFieldCodec, queryIndexCodec, powValueCodec, rsCodec;
  std::string anchorContract, anchorStatement;

  bool johnson() const { return analysis == "johnson"; }
  bool udr() const { return analysis == "udr"; }
};

/// Parse and validate one instance description. Fail-closed: unknown
/// fields, missing fields, wrong types, and out-of-domain values are
/// named errors phrased in the description's vocabulary.
llvm::Expected<FriDescription> parseFriDescription(llvm::StringRef json,
                                                   llvm::StringRef sourceName);

/// The closed ProtocolVocabulary for this instance: descriptor profiles,
/// transparent check contracts, the depth-k FRI reduction contract, and the
/// grinding contract when requested. Deterministic: same description, same
/// bytes.
std::string emitFriVocabulary(const FriDescription &desc);

/// The PIR spine for this instance. Deterministic; the caller (CLI or
/// sweep) re-parses it through the real dialect before use, and the
/// seal battery is the only authority on whether it denotes.
std::string emitFriSpine(const FriDescription &desc);

} // namespace family
} // namespace zkc

#endif // ZKC_FAMILY_FRIFAMILY_H
