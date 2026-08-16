//===- FriFamily.cpp - the FRI family template ------------------*- C++ -*-===//
// The description parser is the fail-closed half of the descriptor
// table: every field the template accepts is declared once in
// kFriParams, the top-level walk refuses anything else, and every
// refusal is phrased in the description's own vocabulary (which
// parameter, what domain) — the seal battery names IR-level problems,
// this layer names knob-level ones. The emitters are deterministic by
// construction: fixed template strings, loops over validated scalars,
// no container iteration reaches the output.
//===----------------------------------------------------------------------===//

#include "zkc/Family/FriFamily.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/Rational.h"
#include "zkc/Registry/RegistryFile.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::family;

static const ParamSpec kFriParams[] = {
    {"family", true,
     "which family template; this generator carries templates for: fri"},
    {"name", true, "protocol name of the instance"},
    {"k", true, "fold depth (at least 1)"},
    {"field", true, "fold-challenge space cardinality, exact decimal string"},
    {"query_log2", true,
     "the query space is 2^query_log2 (dyadic evaluation domain)"},
    {"log_blowup", false,
     "the rate is 2^-log_blowup; defaults to query_log2 - k - "
     "log_final_poly_len, and an explicit value must satisfy the shape "
     "equation query_log2 = k + log_blowup + log_final_poly_len"},
    {"log_final_poly_len", false,
     "the fold chain stops at a final polynomial of 2^log_final_poly_len "
     "coefficients; defaults to 0 (fold to a constant)"},
    {"ell", true, "iid query repetitions (the vector-mode count)"},
    {"analysis", true,
     "which analysis parameters the reduce declares (none, johnson, "
     "or udr)"},
    {"johnson", false,
     "analysis parameters {m, eta, delta}; required by the "
     "analysis 'johnson'"},
    {"udr", false, "analysis parameter {theta}; required by analysis 'udr'"},
    {"grinding_bits", false,
     "emit a proof-of-work round; the pow space is 2^bits"},
    {"kappa", true,
     "construction profile: {sponge, iv, codecs: {ext_field, query_index, "
     "rs[, pow_value][, word]}}"},
    {"anchors", true,
     "claim anchors: {contract, statement}, each sha256:<64 hex>"},
    {"value_faithful", false,
     "emit the challenger-value-faithful spine "
     "(evaluation/upstream/plonky3-replay/README.md): the final "
     "polynomial's coefficients in the clear, per-round arity binds, a "
     "one-word nonce, and the construction routes that make the prover "
     "endpoint derivable; requires grinding_bits"},
};

ArrayRef<ParamSpec> zkc::family::friParamSpecs() { return kFriParams; }

//===----------------------------------------------------------------------===//
// Description parsing
//===----------------------------------------------------------------------===//

static bool isDecimalCardinality(StringRef s) {
  // The shared canonical-decimal predicate; a space of size < 2 carries
  // nothing.
  return zkc::challenge::isCanonicalPositiveDecimal(s) && s != "1";
}

static bool isRationalString(StringRef s) {
  // Probe the exact downstream parser so this locality gate can never
  // accept a spelling the rule adapter later refuses.
  auto [num, den] = s.split('/');
  llvm::Expected<zkc::registry::Rational> parsed =
      s.contains('/') ? zkc::registry::Rational::fromDecimalPair(num, den)
                      : zkc::registry::Rational::fromDecimal(num);
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return false;
  }
  return true;
}

Expected<FriDescription>
zkc::family::parseFriDescription(StringRef jsonText, StringRef sourceName) {
  auto err = [&](const Twine &message) {
    return createStringError(inconvertibleErrorCode(),
                             sourceName + ": " + message);
  };
  auto parsed = zkc::encoding::parseJsonUniqueKeys(jsonText);
  if (!parsed)
    return err("not valid JSON: " + toString(parsed.takeError()));
  const json::Object *top = parsed->getAsObject();
  if (!top)
    return err("the description must be a JSON object");

  // The closed field set, from the one descriptor table. Unknown keys
  // refuse: the description is a point selection, and pressure to put
  // structure here is the DSL trigger, never a contract extension.
  for (const auto &entry : *top) {
    StringRef key = entry.first;
    if (none_of(kFriParams,
                [&](const ParamSpec &spec) { return spec.name == key; }))
      return err("unknown field '" + key +
                 "' (the description is a closed point selection; structure "
                 "belongs in the family template)");
  }
  for (const ParamSpec &spec : kFriParams)
    if (spec.required && !top->get(spec.name))
      return err("missing field '" + spec.name + "' (" + spec.doc + ")");

  auto stringField = [&](const json::Object &object, StringRef name,
                         const Twine &where) -> Expected<std::string> {
    std::optional<StringRef> value = object.getString(name);
    if (!value)
      return err("'" + where + name + "' must be a string");
    return value->str();
  };

  auto family = stringField(*top, "family", "");
  if (!family)
    return family.takeError();
  if (*family != "fri")
    return err("unknown family '" + *family +
               "' (this generator carries templates for: fri)");

  FriDescription desc;
  auto name = stringField(*top, "name", "");
  if (!name)
    return name.takeError();
  if (name->empty() || !zkc::encoding::inEncodingDomain(*name))
    return err("'name' must be non-empty printable ASCII");
  desc.name = std::move(*name);

  // A template rule, not error locality: this generator only describes
  // instances that fold at least once. Nothing downstream re-judges it.
  std::optional<int64_t> k = top->getInteger("k");
  if (!k || *k <= 0)
    return err("'k' must be a positive integer (a fold depth of 0 is not a "
               "FRI instance)");
  desc.k = *k;

  auto field = stringField(*top, "field", "");
  if (!field)
    return field.takeError();
  if (!isDecimalCardinality(*field))
    return err("'field' must be a decimal integer string (exact cardinality, "
               "at least 2, no leading zeros)");
  desc.fieldOrder = std::move(*field);

  std::optional<int64_t> queryLog2 = top->getInteger("query_log2");
  if (!queryLog2 || *queryLog2 <= 0 || *queryLog2 > 1024)
    return err("'query_log2' must be a positive integer (at most 1024)");
  desc.queryLog2 = *queryLog2;

  bool explicitBlowup = top->get("log_blowup") != nullptr;
  if (explicitBlowup) {
    std::optional<int64_t> value = top->getInteger("log_blowup");
    if (!value || *value < 1 || *value > 1024)
      return err("'log_blowup' must be a positive integer (at most 1024)");
    desc.logBlowup = *value;
  }
  if (top->get("log_final_poly_len")) {
    // The final polynomial rides one counted slot, so 2^log_final_poly_len
    // lives in the shared count domain (at most 2^20); naming the cap
    // here keeps the refusal at the knob rather than an IR-level count
    // grammar error three tools later.
    std::optional<int64_t> value = top->getInteger("log_final_poly_len");
    if (!value || *value < 0 || *value > 20)
      return err("'log_final_poly_len' must be an integer from 0 through 20 "
                 "(2^log_final_poly_len coefficients ride one counted slot "
                 "in the shared count domain)");
    desc.logFinalPolyLen = *value;
  }

  std::optional<int64_t> ell = top->getInteger("ell");
  // The carrier's vector mode floors the count at 2 (a one-draw
  // "vector" would price as repetition without being one); name that
  // domain here, at the knob, not at the parse of the emitted spine.
  if (!ell || *ell < 2 ||
      static_cast<uint64_t>(*ell) > zkc::challenge::kMaxCount)
    return err("'ell' must be an integer from 2 through 2^20 (the shared "
               "vector challenge count domain)");
  desc.ell = *ell;

  auto analysis = stringField(*top, "analysis", "");
  if (!analysis)
    return analysis.takeError();
  if (*analysis != "none" && *analysis != "johnson" && *analysis != "udr")
    return err("unknown analysis '" + *analysis +
               "' (the fri template declares: none, johnson, udr)");
  desc.analysis = std::move(*analysis);

  const json::Object *johnson = top->getObject("johnson");
  if (desc.johnson() && !johnson)
    return err("analysis 'johnson' needs the 'johnson' block (m, eta, delta)");
  if (!desc.johnson() && top->get("johnson"))
    return err("only analysis 'johnson' takes a 'johnson' block");
  if (johnson) {
    for (const auto &entry : *johnson) {
      StringRef key = entry.first;
      if (key != "m" && key != "eta" && key != "delta")
        return err("unknown field 'johnson." + key + "'");
    }
    std::optional<int64_t> m = johnson->getInteger("m");
    // The proximity-gaps theorem quantifies over m >= 3; the row's
    // validity side condition would refuse at dispatch — name the
    // knob here instead.
    if (!m || *m < 3)
      return err("'johnson.m' must be an integer of at least 3 (the "
                 "proximity-gaps fold parameter)");
    desc.johnsonM = *m;
    for (StringRef key : {"eta", "delta"}) {
      auto value = stringField(*johnson, key, "johnson.");
      if (!value)
        return value.takeError();
      if (!isRationalString(*value))
        return err("'johnson." + key + "' must be a rational string 'a/b'");
      (key == "eta" ? desc.johnsonEta : desc.johnsonDelta) = std::move(*value);
    }
  }

  const json::Object *udr = top->getObject("udr");
  if (desc.udr() && !udr)
    return err("analysis 'udr' needs the 'udr' block (theta)");
  if (!desc.udr() && top->get("udr"))
    return err("only analysis 'udr' takes a 'udr' block");
  if (udr) {
    for (const auto &entry : *udr) {
      StringRef key = entry.first;
      if (key != "theta")
        return err("unknown field 'udr." + key + "'");
    }
    auto theta = stringField(*udr, "theta", "udr.");
    if (!theta)
      return theta.takeError();
    if (!isRationalString(*theta))
      return err("'udr.theta' must be a rational string 'a/b'");
    desc.udrTheta = std::move(*theta);
  }

  if (top->get("grinding_bits")) {
    std::optional<int64_t> bits = top->getInteger("grinding_bits");
    if (!bits || *bits <= 0 || *bits > 1024)
      return err("'grinding_bits' must be a positive integer (at most 1024)");
    desc.grindingBits = *bits;
  }

  if (top->get("value_faithful")) {
    std::optional<bool> flag = top->getBoolean("value_faithful");
    if (!flag)
      return err("'value_faithful' must be a boolean");
    if (*flag && !desc.grindingBits)
      return err("'value_faithful' requires grinding_bits: the pinned "
                 "challenger semantics carry a grinding round");
    desc.valueFaithful = *flag;
  }

  const json::Object *kappa = top->getObject("kappa");
  if (!kappa)
    return err("'kappa' must be an object {sponge, iv, codecs}");
  for (const auto &entry : *kappa) {
    StringRef key = entry.first;
    if (key != "sponge" && key != "iv" && key != "codecs")
      return err("unknown field 'kappa." + key + "'");
  }
  for (StringRef key : {"sponge", "iv"}) {
    auto value = stringField(*kappa, key, "kappa.");
    if (!value)
      return value.takeError();
    if (value->empty() || !zkc::encoding::inEncodingDomain(*value))
      return err("'kappa." + key + "' must be non-empty printable ASCII");
    (key == "sponge" ? desc.sponge : desc.iv) = std::move(*value);
  }
  const json::Object *codecs = kappa->getObject("codecs");
  if (!codecs)
    return err("'kappa.codecs' must be an object {ext_field, query_index, rs" +
               Twine(desc.grindingBits ? ", pow_value}" : "}"));
  for (const auto &entry : *codecs) {
    StringRef key = entry.first;
    bool admitted = key == "ext_field" || key == "query_index" || key == "rs" ||
                    (desc.grindingBits && key == "pow_value") ||
                    (desc.valueFaithful && key == "word");
    if (!admitted)
      return err("unknown field 'kappa.codecs." + key +
                 "' (the fri template routes semantic payload classes)");
  }
  SmallVector<StringRef, 5> required{"ext_field", "query_index", "rs"};
  if (desc.grindingBits)
    required.push_back("pow_value");
  // The value-faithful spine reads the queried trace rows in the clear;
  // `word` is their payload class — one base-field word per row.
  if (desc.valueFaithful)
    required.push_back("word");
  for (StringRef key : required) {
    auto value = stringField(*codecs, key, "kappa.codecs.");
    if (!value)
      return value.takeError();
    if (value->empty() || !zkc::encoding::inEncodingDomain(*value))
      return err("'kappa.codecs." + key +
                 "' must be non-empty printable "
                 "ASCII");
    if (key == "ext_field")
      desc.extFieldCodec = std::move(*value);
    else if (key == "query_index")
      desc.queryIndexCodec = std::move(*value);
    else if (key == "pow_value")
      desc.powValueCodec = std::move(*value);
    else if (key == "word")
      desc.wordCodec = std::move(*value);
    else
      desc.rsCodec = std::move(*value);
  }

  const json::Object *anchors = top->getObject("anchors");
  if (!anchors)
    return err("'anchors' must be an object {contract, statement}");
  for (const auto &entry : *anchors) {
    StringRef key = entry.first;
    if (key != "contract" && key != "statement")
      return err("unknown field 'anchors." + key + "'");
  }
  for (StringRef key : {"contract", "statement"}) {
    auto value = stringField(*anchors, key, "anchors.");
    if (!value)
      return value.takeError();
    if (!zkc::encoding::isSha256Ref(*value))
      return err("'anchors." + key + "' must be sha256:<64 lowercase hex>");
    (key == "contract" ? desc.anchorContract : desc.anchorStatement) =
        std::move(*value);
  }

  // Cross-parameter domains the instance would otherwise fail at
  // dispatch (the shape side condition; space embedding): named at the
  // knobs, so a sweep sees which parameter to move, not an IR-level
  // refusal three tools later.
  //
  // The shape equation query_log2 = k + log_blowup + log_final_poly_len
  // is the family's one geometric fact: the evaluation domain covers
  // the message at rate 2^-log_blowup and the fold chain stops at a
  // final polynomial of 2^log_final_poly_len coefficients. An omitted
  // log_blowup is derived from it; an explicit one must satisfy it.
  // log_blowup >= 1 subsumes rate-below-one.
  if (!explicitBlowup)
    desc.logBlowup = desc.queryLog2 - desc.k - desc.logFinalPolyLen;
  if (explicitBlowup &&
      desc.queryLog2 != desc.k + desc.logBlowup + desc.logFinalPolyLen)
    return err("'log_blowup' contradicts the shape equation query_log2 = "
               "k + log_blowup + log_final_poly_len (move whichever knob "
               "the sweep owns)");
  if (desc.logBlowup < 1)
    return err("'query_log2' must equal k + log_blowup + "
               "log_final_poly_len with log_blowup at least 1 (rate below "
               "one: the evaluation domain covers the message and the fold "
               "chain stops at the final polynomial)");
  APInt fieldValue(/*numBits=*/unsigned(4 * desc.fieldOrder.size() + 8),
                   desc.fieldOrder, /*radix=*/10);
  unsigned width = std::max<unsigned>(fieldValue.getBitWidth(),
                                      unsigned(desc.queryLog2 + 2));
  APInt querySpace(width, 1);
  querySpace <<= unsigned(desc.queryLog2);
  if (fieldValue.zext(width).ult(querySpace))
    return err("the query space 2^query_log2 must embed in 'field' "
               "(index draws are reduced into the field)");
  return std::move(desc);
}

//===----------------------------------------------------------------------===//
// Emission
//===----------------------------------------------------------------------===//

/// 2^n as an exact decimal string (spaces are always spelled as exact
/// cardinalities in the carrier).
static std::string pow2Decimal(int64_t n) {
  APInt value(static_cast<unsigned>(n + 2), 1);
  value <<= static_cast<unsigned>(n);
  SmallString<64> str;
  value.toString(str, 10, /*Signed=*/false);
  return std::string(str);
}

/// Role naming follows the hand-written fixtures exactly: unindexed at
/// depth one (fold/g, the main-registry shape), indexed from depth two
/// (fold1../g1..) — role names are identity content, SSA names are not.
static std::string foldRole(const FriDescription &desc, int64_t i) {
  return desc.k == 1 ? "fold" : ("fold" + std::to_string(i));
}
static std::string msgRole(const FriDescription &desc, int64_t i) {
  return desc.k == 1 ? "g" : ("g" + std::to_string(i));
}
static std::string reduceLabel(const FriDescription &desc) {
  if (desc.johnson())
    return "frij";
  return desc.udr() ? "friu" : "fri";
}

/// One exact operand segment for the query-phase check contracts —
/// shared between each contract and its predicate-spec ABI, so the two
/// can never disagree.
static llvm::json::Object checkSegment(StringRef role, StringRef valueClass,
                                       int64_t exact) {
  return llvm::json::Object{
      {"class", valueClass},
      {"multiplicity", llvm::json::Object{{"exact", exact}}},
      {"role", role}};
}

/// The query-phase counts, all constants of the family instance: the
/// input tree has height 2^query_log2, round i's tree height
/// 2^(query_log2 - i), and every path runs leaf to a capless root.
struct QueryShape {
  int64_t ell, k, queryLog2, finalLen;
  int64_t inputPaths() const { return ell * queryLog2; }
  int64_t siblings() const { return ell * k; }
  int64_t roundPaths() const {
    return ell * (k * queryLog2 - k * (k + 1) / 2);
  }
};

/// Mint one opaque predicate spec: the canonical content digest is
/// derived here from the same JSON the vocabulary emits, so the
/// fail-closed key check at load can never see a mismatch.
struct MintedSpec {
  std::string digest;
  llvm::json::Object body;
};
static MintedSpec mintSpec(StringRef title,
                           std::initializer_list<StringRef> references,
                           std::initializer_list<StringRef> acceptance,
                           std::initializer_list<StringRef> parameters,
                           llvm::json::Array operands) {
  llvm::json::Array acceptanceJson;
  for (StringRef line : acceptance)
    acceptanceJson.push_back(line);
  llvm::json::Array parameterJson;
  for (StringRef name : parameters)
    parameterJson.push_back(name);
  llvm::json::Object entry{{"acceptance", std::move(acceptanceJson)},
                           {"operands", std::move(operands)},
                           {"parameters", std::move(parameterJson)},
                           {"semantic_parameters", llvm::json::Array{}}};
  llvm::json::Object spec{
      {"entrypoints", llvm::json::Object{{"accept", std::move(entry)}}},
      {"format", "zkc-check-predicate-spec"},
      {"title", title}};
  llvm::json::Array referenceJson;
  for (StringRef reference : references)
    referenceJson.push_back(reference);
  if (!referenceJson.empty())
    spec["references"] = std::move(referenceJson);
  auto digest = zkc::registry::RegistryFile::digestEntry(
      "zkc/check-predicate-spec\n", llvm::json::Value(llvm::json::Object(spec)));
  if (!digest)
    llvm::report_fatal_error("family predicate spec did not canonicalize");
  return {std::move(*digest), std::move(spec)};
}

/// The two query-phase predicate specs and contracts, instance-baked
/// (the pow-zero precedent: family-emitted vocabulary, exact counts).
/// The Merkle contract authenticates the input layer over wire and
/// statement values alone; round-tree authentication lives inside the
/// consistency contract because round leaves contain the verifier's own
/// folded values, and index-dependent fold arithmetic is deliberately
/// not expressible as carrier rows.
static llvm::json::Array merkleOperands(const QueryShape &shape) {
  llvm::json::Array operands;
  operands.push_back(checkSegment("root", "rs", 1));
  operands.push_back(checkSegment("indices", "query_index", shape.ell));
  operands.push_back(checkSegment("leaves", "word", shape.ell));
  operands.push_back(checkSegment("paths", "rs", shape.inputPaths()));
  return operands;
}
static llvm::json::Array consistencyOperands(const QueryShape &shape) {
  llvm::json::Array operands;
  operands.push_back(checkSegment("zeta", "ext_field", 1));
  operands.push_back(checkSegment("opened", "ext_field", 1));
  operands.push_back(checkSegment("alpha", "ext_field", 1));
  operands.push_back(checkSegment("betas", "ext_field", shape.k));
  operands.push_back(
      checkSegment("final_coefficients", "ext_field", shape.finalLen));
  operands.push_back(checkSegment("indices", "query_index", shape.ell));
  operands.push_back(checkSegment("leaves", "word", shape.ell));
  operands.push_back(checkSegment("roots", "rs", shape.k));
  operands.push_back(checkSegment("siblings", "ext_field", shape.siblings()));
  operands.push_back(checkSegment("round_paths", "rs", shape.roundPaths()));
  return operands;
}

std::string zkc::family::emitFriVocabulary(const FriDescription &desc) {
  std::string out;
  raw_string_ostream os(out);
  StringRef nonceClass = desc.valueFaithful ? "pow_value" : "rs";
  QueryShape shape{desc.ell, desc.k, desc.queryLog2,
                 int64_t(1) << desc.logFinalPolyLen};
  os << "{\n"
     << "  \"registry\": \"zkc.protocol_vocabulary\",\n"
     << "  \"claim_profiles\": {\n"
     << "    \"opaque_relation\": {\"kind\": \"relation\", "
        "\"anchors\": [\"contract\", \"statement\"]},\n"
     << "    \"fri_query_consistent\": {\"kind\": \"evaluation\", "
        "\"anchors\": [\"statement\"]}\n"
     << "  },\n";
  if (desc.valueFaithful) {
    MintedSpec merkle = mintSpec(
        "FRI input-layer Merkle multi-opening predicate",
        {"Ben-Sasson-Chiesa-Spooner, TCC 2016, ePrint 2016/116 (vector "
         "commitments in the BCS transformation)"},
        {"Interpret the paths operand as, per query index in order, one "
         "authentication path of tree-height sibling digests, leaf to "
         "capless root, over the codec's digest words.",
         "For each query index, hash the paired leaf row and compress "
         "along the path selected by the index bits; accept exactly when "
         "every derived root equals the root operand.",
         "The tree height is the per-query path length, which is the "
         "paths element count divided by the indices element count; an "
         "index outside the tree rejects.",
         "The predicate performs no transcript, proof-stream, sponge, "
         "route, or ambient protocol effects."},
        {}, merkleOperands(shape));
    MintedSpec consistency = mintSpec(
        "FRI query fold-consistency predicate",
        {"ethSTARK documentation v1.2, ePrint 2021/582 (query-phase "
         "consistency)"},
        {"Reconstruct, per query index, the reduced opening "
         "(opened - leaf(x)) / (zeta - x) over the bit-reversed shifted "
         "coset, batch-weighted by powers of alpha; a query point equal "
         "to an opening point rejects.",
         "Fold arity-2 rounds in order: each round interpolates the "
         "index pair at its beta, authenticates the pair row against "
         "that round's root operand with its segment of round_paths, "
         "and halves the index.",
         "Accept exactly when every query's folded value equals the "
         "final polynomial (final_coefficients, low degree first) "
         "evaluated at the query's domain point, under the declared "
         "log_blowup and log_final_poly_len.",
         "Element counts bind the shape: betas and roots carry one "
         "element per round, siblings one per query per round, and "
         "round_paths the per-round tree heights; any other count "
         "rejects.",
         "The predicate performs no transcript, proof-stream, sponge, "
         "route, or ambient protocol effects."},
        {"log_blowup", "log_final_poly_len"}, consistencyOperands(shape));
    os << "  \"predicate_specs\": {\n    \"" << merkle.digest << "\": "
       << llvm::json::Value(llvm::json::Object(merkle.body)) << ",\n    \""
       << consistency.digest << "\": "
       << llvm::json::Value(llvm::json::Object(consistency.body)) << "\n  },\n"
       << "  \"check_contracts\": {\n    \"zkc.check.merkle-multi-opening\": "
       << llvm::json::Value(llvm::json::Object{
              {"mode", "opaque"},
              {"predicate",
               llvm::json::Object{{"format", "zkc-opaque-predicate-spec"},
                                  {"content_digest", merkle.digest},
                                  {"entrypoint", "accept"}}},
              {"parameters", llvm::json::Array{}},
              {"semantic_parameters", llvm::json::Array{}},
              {"operands", merkleOperands(shape)}})
       << ",\n    \"zkc.check.fri-query-consistency\": "
       << llvm::json::Value(llvm::json::Object{
              {"mode", "opaque"},
              {"predicate",
               llvm::json::Object{{"format", "zkc-opaque-predicate-spec"},
                                  {"content_digest", consistency.digest},
                                  {"entrypoint", "accept"}}},
              {"parameters",
               llvm::json::Array{"log_blowup", "log_final_poly_len"}},
              {"semantic_parameters", llvm::json::Array{}},
              {"operands", consistencyOperands(shape)}})
       << "";
  } else {
    os << "  \"predicate_specs\": {},\n"
       << "  \"check_contracts\": {";
  }
  bool firstCheck = !desc.valueFaithful;
  if (!desc.valueFaithful) {
    os << "\n    \"zkc.check.rs-equality\": {\"mode\": \"transparent\", "
          "\"predicate\": {\"format\": "
          "\"zkc-transparent-expression\"}, \"parameters\": [], "
          "\"semantic_parameters\": [], \"operands\": "
          "[{\"role\": \"lhs\", \"class\": \"rs\", \"multiplicity\": "
          "{\"exact\": 1}}, {\"role\": \"rhs\", \"class\": \"rs\", "
          "\"multiplicity\": {\"exact\": 1}}]}";
    firstCheck = false;
  }
  if (desc.grindingBits) {
    os << (firstCheck ? "\n" : ",\n")
       << "    \"zkc.check.pow-zero\": {\"mode\": \"transparent\", "
          "\"predicate\": {\"format\": "
          "\"zkc-transparent-expression\"}, \"parameters\": [], "
          "\"semantic_parameters\": [], \"operands\": "
          "[{\"role\": \"nonce\", \"class\": \""
       << nonceClass
       << "\", \"multiplicity\": "
          "{\"exact\": 1}}, {\"role\": \"challenge\", \"class\": "
          "\"pow_value\", "
          "\"multiplicity\": {\"exact\": 1}}]}";
  }
  os << "\n  },\n";
  if (desc.valueFaithful) {
    // The prover's compute holes (docs/spec/vocabularies.md §5.1;
    // docs/spec/endpoints.md §6.2):
    // backend-neutral decomposition contracts the routes cite; the
    // pow-search hole alone peeks the transcript. The witness
    // payload and the derived codeword are separate handle classes:
    // they are different objects, and naming them apart is what
    // lets a supplier binding refuse a route that feeds one where
    // the other belongs.
    os << "  \"hole_contracts\": {\n"
       << "    \"zkc.hole.fri-commit\": {\"kind\": \"commit\", "
          "\"operands\": [{\"sort\": \"handle\", \"role\": "
          "\"codeword\", \"class\": \"fri-codeword\"}], "
          "\"results\": [{\"sort\": \"value\", \"role\": \"cap\", "
          "\"class\": \"rs\", \"count\": \"1\"}, {\"sort\": "
          "\"handle\", \"role\": \"codeword\", \"class\": "
          "\"fri-codeword\"}], \"parameters\": [], "
          "\"semantic_parameters\": []},\n"
       << "    \"zkc.hole.fri-final\": {\"kind\": \"evaluate\", "
          "\"operands\": [{\"sort\": \"handle\", \"role\": "
          "\"codeword\", \"class\": \"fri-codeword\"}], "
          "\"results\": [{\"sort\": \"value\", \"role\": "
          "\"coefficient\", \"class\": \"ext_field\", \"count\": \""
       << shape.finalLen
       << "\"}, {\"sort\": \"handle\", \"role\": \"codeword\", "
          "\"class\": \"fri-codeword\"}], \"parameters\": [], "
          "\"semantic_parameters\": []},\n"
       << "    \"zkc.hole.fri-openval\": {\"kind\": \"evaluate\", "
          "\"operands\": [{\"sort\": \"value\", \"role\": \"zeta\", "
          "\"class\": \"ext_field\", \"count\": \"1\"}, {\"sort\": "
          "\"handle\", \"role\": \"codeword\", \"class\": "
          "\"fri-trace\"}], \"results\": [{\"sort\": \"value\", "
          "\"role\": \"opened\", \"class\": \"ext_field\", "
          "\"count\": \"1\"}, {\"sort\": \"handle\", \"role\": "
          "\"codeword\", \"class\": \"fri-codeword\"}], "
          "\"parameters\": [\"log_blowup\", \"log_final_poly_len\"], "
          "\"semantic_parameters\": []},\n"
       << "    \"zkc.hole.fri-reduce\": {\"kind\": \"extend\", "
          "\"operands\": [{\"sort\": \"value\", \"role\": \"alpha\", "
          "\"class\": \"ext_field\", \"count\": \"1\"}, {\"sort\": "
          "\"handle\", \"role\": \"codeword\", \"class\": "
          "\"fri-codeword\"}], \"results\": [{\"sort\": \"handle\", "
          "\"role\": \"codeword\", \"class\": \"fri-codeword\"}], "
          "\"parameters\": [], \"semantic_parameters\": []},\n"
       << "    \"zkc.hole.fri-fold\": {\"kind\": \"fold\", "
          "\"operands\": [{\"sort\": \"value\", \"role\": \"beta\", "
          "\"class\": \"ext_field\", \"count\": \"1\"}, {\"sort\": "
          "\"handle\", \"role\": \"codeword\", \"class\": "
          "\"fri-codeword\"}], \"results\": [{\"sort\": \"handle\", "
          "\"role\": \"codeword\", \"class\": \"fri-codeword\"}], "
          "\"parameters\": [], \"semantic_parameters\": []},\n"
       << "    \"zkc.hole.fri-pow\": {\"kind\": \"pow_search\", "
          "\"operands\": [{\"sort\": \"sponge\", \"role\": "
          "\"transcript\"}], \"results\": [{\"sort\": \"value\", "
          "\"role\": \"nonce\", \"class\": \"pow_value\", "
          "\"count\": \"1\"}, {\"sort\": \"sponge\", \"role\": "
          "\"transcript\"}], \"parameters\": [\"bits\"], "
          "\"semantic_parameters\": []},\n";
    // The query-answering hole: the reserved `open` kind's first use.
    // It consumes the codeword handle (the retained trees), the sampled
    // indices, and the statement root — so a witness that does not
    // commit to the statement is refused by the fill, by name, before
    // any opening reaches the wire. Results ride in wire order.
    os << "    \"zkc.hole.fri-answer\": {\"kind\": \"open\", "
          "\"operands\": [{\"sort\": \"value\", \"role\": \"indices\", "
          "\"class\": \"query_index\", \"count\": \""
       << desc.ell
       << "\"}, {\"sort\": \"value\", \"role\": \"root\", \"class\": "
          "\"rs\", \"count\": \"1\"}, {\"sort\": \"handle\", \"role\": "
          "\"codeword\", \"class\": \"fri-codeword\"}], \"results\": "
          "[{\"sort\": \"value\", \"role\": \"leaves\", \"class\": "
          "\"word\", \"count\": \""
       << desc.ell
       << "\"}, {\"sort\": \"value\", \"role\": \"input_paths\", "
          "\"class\": \"rs\", \"count\": \""
       << shape.inputPaths() << "\"}";
    for (int64_t i = 1; i <= desc.k; ++i)
      os << ", {\"sort\": \"value\", \"role\": \"sib" << i
         << "\", \"class\": \"ext_field\", \"count\": \"" << desc.ell
         << "\"}, {\"sort\": \"value\", \"role\": \"path" << i
         << "\", \"class\": \"rs\", \"count\": \""
         << desc.ell * (desc.queryLog2 - i) << "\"}";
    os << "], \"parameters\": [], \"semantic_parameters\": []}\n"
       << "  },\n";
  } else {
    os << "  \"hole_contracts\": {},\n";
  }
  os << ""
     << "  \"reduction_contracts\": {\n"
     << "    \"fri\": {\n"
     << "      \"consumes\": [\"opaque_relation\"],\n"
     << "      \"dep_slots\": [\n";
  if (desc.valueFaithful)
    os << "        {\"role\": \"zeta\", \"source\": "
          "\"challenge_capability\", \"class\": \"ext_field\"},\n"
       << "        {\"role\": \"alpha\", \"source\": "
          "\"challenge_capability\", \"class\": \"ext_field\"},\n";
  for (int64_t i = 1; i <= desc.k; ++i)
    os << "        {\"role\": \"" << foldRole(desc, i)
       << "\", \"source\": \"challenge_capability\", \"class\": "
          "\"ext_field\"},\n";
  os << "        {\"role\": \"query\", \"source\": "
        "\"challenge_capability\", \"class\": \"query_index\"}\n"
     << "      ],\n"
     << "      \"rounds\": [\n";
  if (desc.valueFaithful) {
    // The stripped harness's own order: the opening point and batch
    // challenge first, then commit-then-sample rounds, then the final
    // coefficient in the query round.
    // The opening point and batch challenge are the PCS opening phase,
    // not fold rounds: the kind keeps the fold-count projection honest
    // (a soundness rule counting fold rounds must see exactly k).
    os << "        {\"challenge_use\": {\"role\": \"zeta\"}, "
          "\"messages\": [], \"kind\": \"opening\"},\n"
       << "        {\"challenge_use\": {\"role\": \"alpha\"}, "
          "\"messages\": [{\"role\": \"opened\", \"count\": "
          "{\"exact\": 1}}], \"kind\": \"opening\"},\n";
    for (int64_t i = 1; i <= desc.k; ++i)
      os << "        {\"challenge_use\": {\"role\": \"" << foldRole(desc, i)
         << "\"}, \"messages\": [{\"role\": \"" << msgRole(desc, i)
         << "\", \"count\": {\"exact\": 1}}], \"kind\": \"fold\"},\n";
    os << "        {\"challenge_use\": {\"role\": \"query\", "
          "\"count\": "
       << desc.ell
       << "}, \"messages\": [{\"role\": \"final\", \"count\": "
          "{\"exact\": "
       << shape.finalLen
       << "}}], \"kind\": \"query\"}\n"
       << "      ],\n";
  } else {
    for (int64_t i = 1; i <= desc.k; ++i) {
      os << "        {\"challenge_use\": {\"role\": \"" << foldRole(desc, i)
         << "\"}, \"messages\": [";
      if (i > 1)
        os << "{\"role\": \"" << msgRole(desc, i - 1)
           << "\", \"count\": {\"exact\": 1}}";
      os << "], \"kind\": \"fold\"},\n";
    }
    os << "        {\"challenge_use\": {\"role\": \"query\", \"count\": "
       << desc.ell << "}, \"messages\": [{\"role\": \"" << msgRole(desc, desc.k)
       << "\", \"count\": {\"exact\": 1}}], \"kind\": \"query\"}\n"
       << "      ],\n";
  }
  // The shape knobs ride the reduction parameters so a soundness rule
  // reads the declared rate directly (the analysis-parameter precedent);
  // the shape side condition ties them to the realized fold count.
  os << ""
     << "      \"parameters\": {";
  if (desc.johnson())
    os << "\"johnson_delta\": \"atom\", \"johnson_eta\": \"atom\", "
          "\"johnson_m\": \"atom\", ";
  os << "\"log_blowup\": \"atom\", \"log_final_poly_len\": \"atom\"";
  if (desc.udr())
    os << ", \"udr_theta\": \"atom\"";
  os << "},\n";
  if (desc.valueFaithful) {
    // The query phase's two obligations, bound to this contract. The
    // openings themselves are response material, not round messages —
    // they follow the query challenge unabsorbed — so the attachments
    // pin what the round structure already carries: the sampled
    // dependencies and the absorbed pre-challenge messages.
    os << "      \"checks\": {\n"
       << "        \"merkle\": {\n"
       << "          \"contract\": \"zkc.check.merkle-multi-opening\",\n"
       << "          \"parameters\": {},\n"
       << "          \"attachments\": [\n"
       << "            {\"kind\": \"material_ref_equality\", \"source\": "
          "{\"kind\": \"input_anchor\", \"input\": 0, \"anchor\": "
          "\"statement\"}, \"target_role\": \"root\"},\n"
       << "            {\"kind\": \"value_identity_vector\", \"source\": "
          "{\"kind\": \"dependency\", \"role\": \"query\"}, "
          "\"target_role\": \"indices\"}\n"
       << "          ]\n"
       << "        },\n"
       << "        \"consistency\": {\n"
       << "          \"contract\": \"zkc.check.fri-query-consistency\",\n"
       << "          \"parameters\": {\"log_blowup\": \""
       << desc.logBlowup << "\", \"log_final_poly_len\": \""
       << desc.logFinalPolyLen << "\"},\n"
       << "          \"attachments\": [\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"dependency\", \"role\": \"zeta\"}, "
          "\"target_role\": \"zeta\"},\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"message\", \"role\": \"opened\", "
          "\"occurrence\": 0}, \"target_role\": \"opened\"},\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"dependency\", \"role\": \"alpha\"}, "
          "\"target_role\": \"alpha\"},\n"
       << "            {\"kind\": \""
       << (shape.finalLen > 1 ? "value_identity_vector" : "value_identity")
       << "\", \"source\": "
          "{\"kind\": \"message\", \"role\": \"final\", "
          "\"occurrence\": 0}, \"target_role\": "
          "\"final_coefficients\"},\n"
       << "            {\"kind\": \"value_identity_vector\", \"source\": "
          "{\"kind\": \"dependency\", \"role\": \"query\"}, "
          "\"target_role\": \"indices\"},\n"
       << "            {\"kind\": \"value_identity_list\", \"source\": "
          "{\"kind\": \"list\", \"items\": [";
    for (int64_t i = 1; i <= desc.k; ++i)
      os << "{\"kind\": \"dependency\", \"role\": \"" << foldRole(desc, i)
         << "\"}" << (i == desc.k ? "" : ", ");
    os << "]}, \"target_role\": \"betas\"},\n"
       << "            {\"kind\": \"value_identity_list\", \"source\": "
          "{\"kind\": \"list\", \"items\": [";
    for (int64_t i = 1; i <= desc.k; ++i)
      os << "{\"kind\": \"message\", \"role\": \"" << msgRole(desc, i)
         << "\", \"occurrence\": 0}" << (i == desc.k ? "" : ", ");
    os << "]}, \"target_role\": \"roots\"}\n"
       << "          ]\n"
       << "        }\n"
       << "      },\n";
  } else {
    os << "      \"checks\": {\n"
       << "        \"consistency\": {\n"
       << "          \"contract\": \"zkc.check.rs-equality\",\n"
       << "          \"parameters\": {},\n"
       << "          \"transparent_predicate\": [\"eq\", [\"role\", "
          "\"lhs\"], [\"role\", \"rhs\"]],\n"
       << "          \"attachments\": [\n"
       << "            {\"kind\": \"material_ref_equality\", \"source\": "
          "{\"kind\": \"input_anchor\", \"input\": 0, \"anchor\": "
          "\"statement\"}, \"target_role\": \"lhs\"},\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"message\", \"role\": \""
       << msgRole(desc, desc.k)
       << "\", \"occurrence\": 0}, \"target_role\": \"rhs\"}\n"
       << "          ]\n"
       << "        }\n"
       << "      },\n";
  }
  os << "      \"constraints\": [],\n"
     << "      \"outputs\": [{\"profile\": \"fri_query_consistent\", "
        "\"anchors\": {\"statement\": {\"kind\": \"input_anchor\", "
        "\"input\": 0, \"anchor\": \"statement\"}}}]\n"
     << "    }";
  if (desc.grindingBits) {
    // Grinding is a separate local implication: exact shape, exact pow-pin
    // premise, and one anchor-free evaluation output.
    os << ",\n"
       << "    \"grinding\": {\n"
       << "      \"consumes\": [\"fri_query_consistent\"],\n"
       << "      \"dep_slots\": [\n"
       << "        {\"role\": \"pow\", \"source\": "
          "\"challenge_capability\", \"class\": \"pow_value\"}\n"
       << "      ],\n"
       << "      \"rounds\": [\n"
       << "        {\"challenge_use\": {\"role\": \"pow\"}, "
          "\"messages\": [{\"role\": \"nonce\", \"count\": "
          "{\"exact\": 1}}], \"kind\": \"pow\"}\n"
       << "      ],\n"
       << "      \"parameters\": {},\n"
       << "      \"checks\": {\n"
       << "        \"pow_pin\": {\n"
       << "          \"contract\": \"zkc.check.pow-zero\",\n"
       << "          \"parameters\": {},\n"
       << "          \"transparent_predicate\": [\"eq\", [\"role\", "
          "\"challenge\"], [\"const\", \"zero\"]],\n"
       << "          \"attachments\": [\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"message\", \"role\": \"nonce\", "
          "\"occurrence\": 0}, \"target_role\": \"nonce\"},\n"
       << "            {\"kind\": \"value_identity\", \"source\": "
          "{\"kind\": \"dependency\", \"role\": \"pow\"}, "
          "\"target_role\": \"challenge\"}\n"
       << "          ]\n"
       << "        }\n"
       << "      },\n"
       << "      \"constraints\": [],\n"
       << "      \"outputs\": [{\"profile\": \"fri_query_consistent\", "
          "\"anchors\": {\"statement\": {\"kind\": \"input_anchor\", "
          "\"input\": 0, \"anchor\": \"statement\"}}}]\n"
       << "    }";
  }
  os << "\n  },\n"
     << "  \"terminal_rules\": {}\n"
     << "}\n";
  return out;
}

/// The challenger-value-faithful spine
/// (evaluation/upstream/plonky3-replay/README.md): the stripped pinned
/// harness's own transcript — sizes and input commitment bound, the opening
/// point and batch challenge sampled, commit-then-sample rounds, the final
/// coefficients in the clear, arities in their own segment, a one-word grind —
/// with the construction routes that derive the prover.
static std::string emitValueFaithfulSpine(const FriDescription &desc) {
  std::string out;
  raw_string_ostream os(out);
  std::string label = reduceLabel(desc);
  int64_t k = desc.k;

  os << "pir.protocol \"" << desc.name << "\" kappa {codecs = {query_index = \""
     << desc.queryIndexCodec << "\", rs = \"" << desc.rsCodec
     << "\", ext_field = \"" << desc.extFieldCodec << "\", pow_value = \""
     << desc.powValueCodec << "\", word = \"" << desc.wordCodec
     << "\"}, constants = {zero = {class = \"pow_value\", value = "
        "\"0\"}}, iv = \""
     << desc.iv << "\", sponge = \"" << desc.sponge << "\"}";

  // The pinned harness's rate expansion and final-polynomial length.
  // They are the shape the opening fill builds the extension from, so
  // the artifact declares them rather than leaving a supplier to assume
  // them.
  os << " routes {instances = {openval = {contract = "
        "\"zkc.hole.fri-openval\", params = {log_blowup = \""
     << desc.logBlowup << "\", log_final_poly_len = \""
     << desc.logFinalPolyLen
     << "\"}, inputs = [\"chal:zeta\", "
        "\"witness:codeword\"]}, reduce = {contract = "
        "\"zkc.hole.fri-reduce\", inputs = [\"chal:alpha\", "
        "\"openval.1\"]}, ";
  for (int64_t i = 1; i <= k; ++i) {
    std::string commitSource = i == 1 ? std::string("reduce.0")
                                      : ("fold" + std::to_string(i - 1) + ".0");
    os << "commit" << i << " = {contract = \"zkc.hole.fri-commit\", "
       << "inputs = [\"" << commitSource << "\"]}, ";
    os << "fold" << i << " = {contract = \"zkc.hole.fri-fold\", inputs "
       << "= [\"chal:" << foldRole(desc, i) << "\", \"commit" << i
       << ".1\"]}, ";
  }
  os << "final = {contract = \"zkc.hole.fri-final\", inputs = [\"fold" << k
     << ".0\"]}, grind = {contract = \"zkc.hole.fri-pow\", "
     << "params = {bits = \"" << *desc.grindingBits
     << "\"}, inputs = []}, answer = {contract = \"zkc.hole.fri-answer\", "
        "inputs = [\"chal:query\", \"bind:f_root\", \"final.1\"]}}, "
        "witnesses = [[\"codeword\", \"fri-trace\"]]}";
  // Arity binds live past the sampling rounds: a second declared phase
  // (kernel.md §5.3), so the per-segment statement-binding default is
  // met rather than bypassed.
  os << " segments [" << (6 + 2 * k) << "]";
  os << " policy \"analysis_only_artifact\" {\n";
  os << "  %c = pir.instantiate \"prox\" anchors {contract = \""
     << desc.anchorContract << "\", statement = \"" << desc.anchorStatement
     << "\"} : !pir.claim<\"opaque_relation\">\n";
  os << "  %t0 = pir.begin\n";
  // The pinned harness binds the input log-size before anything else;
  // the trace height is the evaluation domain shrunk by the rate,
  // query_log2 - log_blowup.
  os << "  %t1, %size = pir.bind %t0 \"log_size\" : \"pow_value\" stage "
        "seal = \""
     << (desc.queryLog2 - desc.logBlowup) << "\"\n";
  os << "  %t2, %f = pir.bind %t1 \"f_root\" : \"rs\" stage instance\n";
  os << "  %t3, %zeta = pir.chal %t2 deps(%f : !pir.val<\"rs\">) "
        "\"zeta\" : \"ext_field\" domain \"fri.zeta\" space \""
     << desc.fieldOrder << "\"\n";
  // The opened evaluation rides in the clear before the batch
  // challenge, exactly as the pinned pcs absorbs it.
  os << "  %t4, %openval = pir.slot %t3 \"opened_value\" : "
        "\"ext_field\" in \""
     << label << "\" as \"opened\" binding \"openval.0\"\n";
  os << "  %t5, %alpha = pir.chal %t4 deps(%openval : "
        "!pir.val<\"ext_field\">) "
        "\"alpha\" : \"ext_field\" domain \"fri.alpha\" space \""
     << desc.fieldOrder << "\"\n";
  int64_t token = 5;
  auto nextToken = [&]() { return "%t" + std::to_string(++token); };
  std::string prevToken = "%t5";
  for (int64_t i = 1; i <= k; ++i) {
    std::string slotToken = nextToken();
    os << "  " << slotToken << ", %g" << i << " = pir.slot " << prevToken
       << " \"" << msgRole(desc, i) << "_root\" : \"rs\" in \"" << label
       << "\" as \"" << msgRole(desc, i) << "\" binding \"commit" << i
       << ".0\"\n";
    std::string chalToken = nextToken();
    os << "  " << chalToken << ", %fold" << i << " = pir.chal " << slotToken
       << " deps(%g" << i << " : !pir.val<\"rs\">) \"" << foldRole(desc, i)
       << "\" : \"ext_field\" domain \"fri." << foldRole(desc, i)
       << "\" space \"" << desc.fieldOrder << "\"\n";
    prevToken = chalToken;
  }
  std::string finalToken = nextToken();
  os << "  " << finalToken << ", %final = pir.slot " << prevToken
     << " \"final_poly\" : \"ext_field\" count \""
     << (int64_t(1) << desc.logFinalPolyLen) << "\" in \"" << label
     << "\" as \"final\" binding \"final.0\"\n";
  prevToken = finalToken;
  for (int64_t i = 1; i <= k; ++i) {
    std::string bindToken = nextToken();
    os << "  " << bindToken << ", %arity" << i << " = pir.bind " << prevToken
       << " \"arity" << i << "\" : \"pow_value\" stage seal = \"1\"\n";
    prevToken = bindToken;
  }
  std::string nonceToken = nextToken();
  os << "  " << nonceToken << ", %nonce = pir.slot " << prevToken
     << " \"nonce\" : \"pow_value\" in \"grind\" as \"nonce\" "
        "binding \"grind.0\"\n";
  std::string powToken = nextToken();
  os << "  " << powToken << ", %pow = pir.chal " << nonceToken
     << " deps(%nonce : !pir.val<\"pow_value\">) \"pow\" : "
        "\"pow_value\" domain \"grind.pow\" space \""
     << pow2Decimal(*desc.grindingBits) << "\"\n";
  os << "  pir.check \"pow_pin\" contract \"zkc.check.pow-zero\" "
        "(%nonce, %pow : !pir.val<\"pow_value\">, "
        "!pir.val<\"pow_value\">) expr [\"eq\", [\"in\", 1], "
        "[\"const\", \"zero\"]]\n";
  std::string queryToken = nextToken();
  os << "  " << queryToken << ", %query = pir.chal " << powToken
     << " deps(%final : !pir.val<\"ext_field\">) \"query\" : "
        "\"query_index\" domain \"fri.query\" space \""
     << pow2Decimal(desc.queryLog2) << "\" mode [\"vector\", \"" << desc.ell
     << "\", \"uniform_independent\"]\n";
  // The query openings: response material, read after the last
  // challenge without absorption (the Frozen-Heart default is met, not
  // relaxed — nothing samples after these), one counted slot per wire
  // field in the pinned proof's own order.
  prevToken = queryToken;
  auto countedSlot = [&](StringRef name, StringRef ssa, StringRef cls,
                         int64_t count, int64_t resultIndex) {
    std::string slotToken = nextToken();
    os << "  " << slotToken << ", %" << ssa << " = pir.slot " << prevToken
       << " \"" << name << "\" : \"" << cls << "\" count \"" << count
       << "\" unabsorbed binding \"answer." << resultIndex << "\"\n";
    prevToken = slotToken;
  };
  countedSlot("query_leaves", "leaves", "word", desc.ell, 0);
  countedSlot("input_paths", "ipaths", "rs", desc.ell * desc.queryLog2, 1);
  for (int64_t i = 1; i <= k; ++i) {
    countedSlot(("sib" + std::to_string(i)), ("sib" + std::to_string(i)),
                "ext_field", desc.ell, 2 * i);
    countedSlot(("path" + std::to_string(i)), ("path" + std::to_string(i)),
                "rs", desc.ell * (desc.queryLog2 - i), 2 * i + 1);
  }
  os << "  pir.check \"merkle_open\" contract "
        "\"zkc.check.merkle-multi-opening\" (%f, %query, %leaves, "
        "%ipaths : !pir.val<\"rs\">, !pir.val<\"query_index\">, "
        "!pir.val<\"word\">, !pir.val<\"rs\">)\n";
  os << "  pir.check \"query_consistency\" contract "
        "\"zkc.check.fri-query-consistency\" params {log_blowup = \""
     << desc.logBlowup << "\", log_final_poly_len = \""
     << desc.logFinalPolyLen << "\"} (%zeta, %openval, %alpha, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "%fold" << i << ", ";
  os << "%final, %query, %leaves, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "%g" << i << ", ";
  for (int64_t i = 1; i <= k; ++i)
    os << "%sib" << i << ", ";
  for (int64_t i = 1; i <= k; ++i)
    os << "%path" << i << (i == k ? " : " : ", ");
  os << "!pir.val<\"ext_field\">, !pir.val<\"ext_field\">, "
        "!pir.val<\"ext_field\">, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "!pir.val<\"ext_field\">, ";
  os << "!pir.val<\"ext_field\">, !pir.val<\"query_index\">, "
        "!pir.val<\"word\">, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "!pir.val<\"rs\">, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "!pir.val<\"ext_field\">, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "!pir.val<\"rs\">" << (i == k ? ")\n" : ", ");
  os << "  pir.end " << prevToken << "\n";

  os << "  %e = pir.reduce \"" << label
     << "\" contract \"fri\" "
        "(%c : !pir.claim<\"opaque_relation\">) "
        "deps(%zeta, %alpha, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "%fold" << i << ", ";
  os << "%query : !pir.val<\"ext_field\">, !pir.val<\"ext_field\">, ";
  for (int64_t i = 1; i <= k; ++i)
    os << "!pir.val<\"ext_field\">, ";
  os << "!pir.val<\"query_index\">) checks {merkle = \"merkle_open\", "
        "consistency = \"query_consistency\"}";
  os << " params {";
  if (desc.johnson())
    os << "johnson_m = \"" << desc.johnsonM << "\", johnson_eta = \""
       << desc.johnsonEta << "\", johnson_delta = \"" << desc.johnsonDelta
       << "\", ";
  os << "log_blowup = \"" << desc.logBlowup << "\", log_final_poly_len = \""
     << desc.logFinalPolyLen << "\"";
  if (desc.udr())
    os << ", udr_theta = \"" << desc.udrTheta << "\"";
  os << "}";
  os << " anchors [{statement = \"" << desc.anchorStatement
     << "\"}] -> !pir.claim<\"fri_query_consistent\">\n";
  os << "  %s = pir.reduce \"grind\" contract \"grinding\" "
        "(%e : !pir.claim<\"fri_query_consistent\">) "
        "deps(%pow : !pir.val<\"pow_value\">) checks {pow_pin = "
        "\"pow_pin\"} anchors [{statement = \""
     << desc.anchorStatement
     << "\"}] -> !pir.claim<\"fri_query_consistent\">\n";
  os << "  pir.material_bind %f to \"" << desc.anchorStatement
     << "\" : !pir.val<\"rs\">\n";
  os << "  pir.residual %s : !pir.claim<\"fri_query_consistent\"> "
        "route \"fri-terminal-not-modeled\"\n";
  os << "}\n";
  return out;
}

std::string zkc::family::emitFriSpine(const FriDescription &desc) {
  std::string out;
  raw_string_ostream os(out);
  std::string label = reduceLabel(desc);

  os << "pir.protocol \"" << desc.name << "\" kappa {codecs = {query_index = \""
     << desc.queryIndexCodec << "\", rs = \"" << desc.rsCodec
     << "\", ext_field = \"" << desc.extFieldCodec << "\"";
  if (desc.grindingBits)
    os << ", pow_value = \"" << desc.powValueCodec << "\"";
  os << "}";
  if (desc.grindingBits)
    os << ", constants = {zero = {class = \"pow_value\", value = \"0\"}}";
  os << ", iv = \"" << desc.iv << "\", sponge = \"" << desc.sponge << "\"}";
  if (desc.valueFaithful)
    return emitValueFaithfulSpine(desc);
  os << " policy \"analysis_only_artifact\" {\n";
  os << "  %c = pir.instantiate \"prox\" anchors {contract = \""
     << desc.anchorContract << "\", statement = \"" << desc.anchorStatement
     << "\"} : !pir.claim<\"opaque_relation\">\n";

  int64_t token = 1;
  auto nextToken = [&]() { return "%t" + std::to_string(++token); };
  os << "  %t0 = pir.begin\n";
  os << "  %t1, %f = pir.bind %t0 \"f_root\" : \"rs\" stage instance\n";
  std::string prevToken = "%t1";

  std::string prevMsg = "%f";
  for (int64_t i = 1; i <= desc.k; ++i) {
    std::string chalToken = nextToken();
    os << "  " << chalToken << ", %fold" << i << " = pir.chal " << prevToken
       << " deps(" << prevMsg << " : !pir.val<\"rs\">) \"" << foldRole(desc, i)
       << "\" : \"ext_field\" domain \"fri." << foldRole(desc, i)
       << "\" space \"" << desc.fieldOrder << "\"\n";
    std::string slotToken = nextToken();
    os << "  " << slotToken << ", %g" << i << " = pir.slot " << chalToken
       << " \"" << msgRole(desc, i) << "_root\" : \"rs\" in \"" << label
       << "\" as \"" << msgRole(desc, i) << "\"\n";
    prevToken = slotToken;
    prevMsg = "%g" + std::to_string(i);
  }

  if (desc.grindingBits) {
    // The pow round immediately precedes the query challenge (the
    // adjacency the grinding row's side condition checks), and a
    // transparent check pins the challenge to the zero constant.
    std::string nonceToken = nextToken();
    os << "  " << nonceToken << ", %nonce = pir.slot " << prevToken
       << " \"nonce\" : \"rs\" in \"grind\" as \"nonce\"\n";
    std::string powToken = nextToken();
    os << "  " << powToken << ", %pow = pir.chal " << nonceToken
       << " deps(%nonce : !pir.val<\"rs\">) \"pow\" : \"pow_value\" "
          "domain \"grind.pow\" "
          "space \""
       << pow2Decimal(*desc.grindingBits) << "\"\n";
    os << "  pir.check \"pow_pin\" contract \"zkc.check.pow-zero\" "
          "(%nonce, %pow : "
          "!pir.val<\"rs\">, !pir.val<\"pow_value\">) expr [\"eq\", [\"in\", "
          "1], "
          "[\"const\", \"zero\"]]\n";
    prevToken = powToken;
  }

  std::string queryToken = nextToken();
  os << "  " << queryToken << ", %query = pir.chal " << prevToken << " deps("
     << prevMsg
     << " : !pir.val<\"rs\">) \"query\" : \"query_index\" domain \"fri.query\" "
        "space \""
     << pow2Decimal(desc.queryLog2) << "\" mode [\"vector\", \"" << desc.ell
     << "\", \"uniform_independent\"]\n";
  os << "  pir.check \"consistency\" contract "
        "\"zkc.check.rs-equality\" (%f, "
     << prevMsg
     << " : !pir.val<\"rs\">, !pir.val<\"rs\">) expr [\"eq\", [\"in\", 0], "
        "[\"in\", 1]]\n";
  os << "  pir.end " << queryToken << "\n";

  os << "  %e = pir.reduce \"" << label << "\" contract \"fri\""
     << " (%c : !pir.claim<\"opaque_relation\">) deps(";
  for (int64_t i = 1; i <= desc.k; ++i)
    os << "%fold" << i << ", ";
  os << "%query : ";
  for (int64_t i = 1; i <= desc.k; ++i)
    os << "!pir.val<\"ext_field\">, ";
  os << "!pir.val<\"query_index\">)";
  os << " checks {consistency = \"consistency\"}";
  os << " params {";
  if (desc.johnson())
    os << "johnson_m = \"" << desc.johnsonM << "\", johnson_eta = \""
       << desc.johnsonEta << "\", johnson_delta = \"" << desc.johnsonDelta
       << "\", ";
  os << "log_blowup = \"" << desc.logBlowup << "\", log_final_poly_len = \""
     << desc.logFinalPolyLen << "\"";
  if (desc.udr())
    os << ", udr_theta = \"" << desc.udrTheta << "\"";
  os << "}";
  os << " anchors [{statement = \"" << desc.anchorStatement
     << "\"}] -> !pir.claim<\"fri_query_consistent\">\n";

  std::string finalClaim = "%e";
  if (desc.grindingBits) {
    os << "  %s = pir.reduce \"grind\" contract \"grinding\" (%e : "
          "!pir.claim<\"fri_query_consistent\">) deps(%pow : "
          "!pir.val<\"pow_value\">) checks {pow_pin = \"pow_pin\"} anchors "
          "[{statement = \""
       << desc.anchorStatement
       << "\"}] -> !pir.claim<\"fri_query_consistent\">\n";
    finalClaim = "%s";
  }
  os << "  pir.material_bind %f to \"" << desc.anchorStatement
     << "\" : !pir.val<\"rs\">\n";
  os << "  pir.residual " << finalClaim
     << " : !pir.claim<\"fri_query_consistent\"> route "
        "\"fri-terminal-not-modeled\"\n";
  os << "}\n";
  return out;
}
