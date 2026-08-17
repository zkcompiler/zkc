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

#include "zkc/Family/FriShape.h"
#include "zkc/Relation/AnchorProjection.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/Rational.h"
#include "zkc/Registry/RegistryFile.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FormatVariadic.h"
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
    {"preamble", false,
     "authored seal-stage bindings emitted at the head of the spine, each "
     "{label, class} with either a 'value' (decimal, canonical for the "
     "class) or an 'anchor' naming a claim anchor whose transcript "
     "projection becomes the value"},
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

/// The codec this description declares for a payload class, or empty
/// when it declares none.
static llvm::StringRef codecFor(const FriDescription &desc,
                                llvm::StringRef payloadClass) {
  if (payloadClass == "ext_field")
    return desc.extFieldCodec;
  if (payloadClass == "query_index")
    return desc.queryIndexCodec;
  if (payloadClass == "pow_value")
    return desc.powValueCodec;
  if (payloadClass == "rs")
    return desc.rsCodec;
  if (payloadClass == "word")
    return desc.wordCodec;
  return {};
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

  if (const json::Value *preambleValue = top->get("preamble")) {
    const json::Array *entries = preambleValue->getAsArray();
    if (!entries)
      return err("'preamble' must be an array of seal-stage bindings");
    for (const json::Value &entryValue : *entries) {
      const json::Object *entry = entryValue.getAsObject();
      if (!entry)
        return err("each 'preamble' entry must be an object");
      for (const auto &field : *entry) {
        StringRef key = field.first;
        if (key != "label" && key != "class" && key != "value" &&
            key != "anchor")
          return err("unknown field 'preamble." + key + "'");
      }
      FriDescription::PreambleEntry parsed;
      auto label = stringField(*entry, "label", "preamble.");
      if (!label)
        return label.takeError();
      parsed.label = std::move(*label);
      auto payloadClass = stringField(*entry, "class", "preamble.");
      if (!payloadClass)
        return payloadClass.takeError();
      parsed.payloadClass = std::move(*payloadClass);
      // A binding's class keys its codec, so a class this instance's
      // kappa does not carry is refused where the author wrote it
      // rather than at seal, which could only name generated IR.
      if (codecFor(desc, parsed.payloadClass).empty())
        return err("'preamble' entry '" + parsed.label + "' names class '" +
                   parsed.payloadClass +
                   "', which this instance's kappa carries no codec for");

      // The label namespace is global across every member of the
      // spine, so a collision is refused here rather than at seal,
      // where the diagnostic would name an operation the author never
      // wrote.
      for (StringRef reserved :
           {"log_size", "f_root", "opened_value", "final_poly", "nonce",
            "prox", "frij", "pow_pin", "merkle_open", "query_consistency"})
        if (parsed.label == reserved)
          return err("'preamble' label '" + parsed.label +
                     "' is a label this family already emits");
      for (const FriDescription::PreambleEntry &earlier : desc.preamble)
        if (earlier.label == parsed.label)
          return err("'preamble' label '" + parsed.label + "' appears twice");

      const json::Value *value = entry->get("value");
      const json::Value *anchor = entry->get("anchor");
      if (!value && !anchor)
        return err("'preamble' entry '" + parsed.label +
                   "' needs a 'value' or an 'anchor'");
      if (value && anchor)
        return err("'preamble' entry '" + parsed.label +
                   "' names an 'anchor' and a 'value'; an anchored entry's "
                   "value is the anchor's transcript projection and is "
                   "never authored");
      if (anchor) {
        auto anchorName = stringField(*entry, "anchor", "preamble.");
        if (!anchorName)
          return anchorName.takeError();
        parsed.anchor = std::move(*anchorName);
        if (parsed.anchor != "contract")
          return err("'preamble' entry '" + parsed.label + "' cites anchor '" +
                     parsed.anchor +
                     "'; only 'contract' may be cited, because this family "
                     "already binds the statement anchor to its own value "
                     "and a semantic reference is bound once");
        auto projected =
            zkc::relation::anchorProjectionValue(desc.anchorContract);
        if (!projected)
          return projected.takeError();
        parsed.value = std::move(*projected);
      } else {
        auto literal = stringField(*entry, "value", "preamble.");
        if (!literal)
          return literal.takeError();
        parsed.value = std::move(*literal);
        if (parsed.value.empty() ||
            !llvm::all_of(parsed.value, [](char c) { return c >= '0' && c <= '9'; }) ||
            (parsed.value.size() > 1 && parsed.value[0] == '0'))
          return err("'preamble' entry '" + parsed.label +
                     "' needs an exact decimal value");
        // An authored value is a scalar. A class framing several field
        // elements is canonical only element by element, which is a
        // fact about the execution profile's field rather than about
        // this description, so a wide binding states an 'anchor' and
        // carries its transcript projection (docs/spec/relations.md
        // section 2.8) instead of a hand-written number no author can
        // check.
        if (parsed.payloadClass == "rs" || parsed.payloadClass == "ext_field")
          return err("'preamble' entry '" + parsed.label + "' has class '" +
                     parsed.payloadClass +
                     "', which frames several field elements; such a binding "
                     "states an 'anchor' and carries its transcript "
                     "projection rather than an authored value");
        if (parsed.value.size() > 19)
          return err("'preamble' entry '" + parsed.label +
                     "' has a value wider than its class frames");
      }
      desc.preamble.push_back(std::move(parsed));
    }
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
  if (!friShapeHolds(desc.queryLog2, desc.k, desc.logBlowup,
                     desc.logFinalPolyLen))
    return err("'query_log2' must equal k + log_blowup + "
               "log_final_poly_len with log_blowup at least 1 (rate below "
               "one: the evaluation domain covers the message and the fold "
               "chain stops at the final polynomial); move whichever knob "
               "the sweep owns");
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
static llvm::json::Object checkSegment(std::string role,
                                       std::string valueClass, int64_t exact) {
  return llvm::json::Object{
      {"class", std::move(valueClass)},
      {"multiplicity", llvm::json::Object{{"exact", exact}}},
      {"role", std::move(role)}};
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

//===----------------------------------------------------------------------===//
// The vocabulary document
//
// Every section is a value the assembly names, rather than a run of
// text spelled into a stream in the order it happens to be written.
// The reason is not tidiness. Two sections share the minted predicate
// digests — `predicate_specs` files each spec under its digest and
// `check_contracts` cites the same digest — and a stream forces that
// shared state to be computed where the first section needs it and
// carried by hand to the second, which is what makes the two sections
// hard to separate. Named values let the mint happen once, above both.
//
// Spelling reaches nothing here: the digests are taken over the
// canonical form, so key order and whitespace are the writer's
// business. `test/Family/generator-output.test` pins the canonical
// form and the sealed identity, not these bytes, which is what makes
// the arrangement of this file free to change and a change of content
// loud.
//===----------------------------------------------------------------------===//

/// The two claim profiles every instance carries: what the relation
/// input is, and what the reduction concludes about it.
static llvm::json::Object claimProfiles() {
  return llvm::json::Object{
      {"opaque_relation",
       llvm::json::Object{{"kind", "relation"},
                          {"anchors", llvm::json::Array{"contract",
                                                        "statement"}}}},
      {"fri_query_consistent",
       llvm::json::Object{{"kind", "evaluation"},
                          {"anchors", llvm::json::Array{"statement"}}}}};
}

/// The query-phase specs, minted once for both of the sections that
/// name them. A spec's digest is the key `predicate_specs` files it
/// under and the value `check_contracts` cites, so a second mint would
/// be a second chance for the two to disagree.
struct QueryPhaseSpecs {
  MintedSpec merkle;
  MintedSpec consistency;
};

static QueryPhaseSpecs mintQueryPhaseSpecs(const QueryShape &shape) {
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
  return {std::move(merkle), std::move(consistency)};
}

static llvm::json::Object
predicateSpecs(const std::optional<QueryPhaseSpecs> &specs) {
  llvm::json::Object entries;
  if (!specs)
    return entries;
  entries[specs->merkle.digest] = llvm::json::Object(specs->merkle.body);
  entries[specs->consistency.digest] =
      llvm::json::Object(specs->consistency.body);
  return entries;
}

/// A check contract whose predicate is an opaque spec, cited by the
/// digest under which `predicate_specs` files it.
static llvm::json::Object opaqueContract(const MintedSpec &spec,
                                         llvm::json::Array parameters,
                                         llvm::json::Array operands) {
  return llvm::json::Object{
      {"mode", "opaque"},
      {"predicate",
       llvm::json::Object{{"format", "zkc-opaque-predicate-spec"},
                          {"content_digest", spec.digest},
                          {"entrypoint", "accept"}}},
      {"parameters", std::move(parameters)},
      {"semantic_parameters", llvm::json::Array{}},
      {"operands", std::move(operands)}};
}

/// A check contract the carrier evaluates itself; the expression rides
/// the citing reduction, not the contract.
static llvm::json::Object transparentContract(llvm::json::Array operands) {
  return llvm::json::Object{
      {"mode", "transparent"},
      {"predicate",
       llvm::json::Object{{"format", "zkc-transparent-expression"}}},
      {"parameters", llvm::json::Array{}},
      {"semantic_parameters", llvm::json::Array{}},
      {"operands", std::move(operands)}};
}

static llvm::json::Object
checkContracts(const FriDescription &desc, const QueryShape &shape,
               const std::optional<QueryPhaseSpecs> &specs) {
  llvm::json::Object contracts;
  if (desc.valueFaithful) {
    contracts["zkc.check.merkle-multi-opening"] = opaqueContract(
        specs->merkle, llvm::json::Array{}, merkleOperands(shape));
    contracts["zkc.check.fri-query-consistency"] = opaqueContract(
        specs->consistency,
        llvm::json::Array{"log_blowup", "log_final_poly_len"},
        consistencyOperands(shape));
  } else {
    contracts["zkc.check.rs-equality"] = transparentContract(llvm::json::Array{
        checkSegment("lhs", "rs", 1), checkSegment("rhs", "rs", 1)});
  }
  if (desc.grindingBits) {
    // The nonce is a one-word value in the value-faithful variant and a
    // digest in the base form, which is the one place the two spellings
    // of the same round differ.
    const char *nonceClass = desc.valueFaithful ? "pow_value" : "rs";
    contracts["zkc.check.pow-zero"] = transparentContract(
        llvm::json::Array{checkSegment("nonce", nonceClass, 1),
                          checkSegment("challenge", "pow_value", 1)});
  }
  return contracts;
}

//===----------------------------------------------------------------------===//
// Hole contracts
//===----------------------------------------------------------------------===//

static llvm::json::Object valueSlot(std::string role, std::string valueClass,
                                    int64_t count) {
  return llvm::json::Object{{"sort", "value"},
                            {"role", std::move(role)},
                            {"class", std::move(valueClass)},
                            {"count", std::to_string(count)}};
}
static llvm::json::Object handleSlot(std::string role,
                                     std::string handleClass) {
  return llvm::json::Object{{"sort", "handle"},
                            {"role", std::move(role)},
                            {"class", std::move(handleClass)}};
}
static llvm::json::Object spongeSlot(std::string role) {
  return llvm::json::Object{{"sort", "sponge"}, {"role", std::move(role)}};
}
static llvm::json::Object holeContract(std::string kind,
                                       llvm::json::Array operands,
                                       llvm::json::Array results,
                                       llvm::json::Array parameters) {
  return llvm::json::Object{{"kind", std::move(kind)},
                            {"operands", std::move(operands)},
                            {"results", std::move(results)},
                            {"parameters", std::move(parameters)},
                            {"semantic_parameters", llvm::json::Array{}}};
}

/// The prover's compute holes (docs/spec/vocabularies.md §5.1;
/// docs/spec/endpoints.md §6.2): backend-neutral decomposition
/// contracts the routes cite; the pow-search hole alone peeks the
/// transcript. The witness payload and the derived codeword are
/// separate handle classes: they are different objects, and naming them
/// apart is what lets a supplier binding refuse a route that feeds one
/// where the other belongs.
static llvm::json::Object holeContracts(const FriDescription &desc,
                                        const QueryShape &shape) {
  llvm::json::Object holes;
  if (!desc.valueFaithful)
    return holes;

  holes["zkc.hole.fri-commit"] = holeContract(
      "commit", llvm::json::Array{handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{valueSlot("cap", "rs", 1),
                        handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{});
  holes["zkc.hole.fri-final"] = holeContract(
      "evaluate", llvm::json::Array{handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{valueSlot("coefficient", "ext_field", shape.finalLen),
                        handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{});
  holes["zkc.hole.fri-openval"] = holeContract(
      "evaluate",
      llvm::json::Array{valueSlot("zeta", "ext_field", 1),
                        handleSlot("codeword", "fri-trace")},
      llvm::json::Array{valueSlot("opened", "ext_field", 1),
                        handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{"log_blowup", "log_final_poly_len"});
  holes["zkc.hole.fri-reduce"] = holeContract(
      "extend",
      llvm::json::Array{valueSlot("alpha", "ext_field", 1),
                        handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{});
  holes["zkc.hole.fri-fold"] = holeContract(
      "fold",
      llvm::json::Array{valueSlot("beta", "ext_field", 1),
                        handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{handleSlot("codeword", "fri-codeword")},
      llvm::json::Array{});
  holes["zkc.hole.fri-pow"] = holeContract(
      "pow_search", llvm::json::Array{spongeSlot("transcript")},
      llvm::json::Array{valueSlot("nonce", "pow_value", 1),
                        spongeSlot("transcript")},
      llvm::json::Array{"bits"});

  // The query-answering hole: the reserved `open` kind's first use. It
  // consumes the codeword handle (the retained trees), the sampled
  // indices, and the statement root — so a witness that does not commit
  // to the statement is refused by the fill, by name, before any
  // opening reaches the wire. Results ride in wire order.
  llvm::json::Array answers{valueSlot("leaves", "word", desc.ell),
                            valueSlot("input_paths", "rs", shape.inputPaths())};
  for (int64_t i = 1; i <= desc.k; ++i) {
    answers.push_back(
        valueSlot("sib" + std::to_string(i), "ext_field", desc.ell));
    answers.push_back(valueSlot("path" + std::to_string(i), "rs",
                                desc.ell * (desc.queryLog2 - i)));
  }
  holes["zkc.hole.fri-answer"] = holeContract(
      "open",
      llvm::json::Array{valueSlot("indices", "query_index", desc.ell),
                        valueSlot("root", "rs", 1),
                        handleSlot("codeword", "fri-codeword")},
      std::move(answers), llvm::json::Array{});
  return holes;
}

//===----------------------------------------------------------------------===//
// Reduction contracts
//===----------------------------------------------------------------------===//

static llvm::json::Object depSlot(std::string role, std::string slotClass) {
  return llvm::json::Object{{"role", std::move(role)},
                            {"source", "challenge_capability"},
                            {"class", std::move(slotClass)}};
}
static llvm::json::Object message(std::string role, int64_t exact) {
  return llvm::json::Object{
      {"role", std::move(role)},
      {"count", llvm::json::Object{{"exact", exact}}}};
}
static llvm::json::Object round(llvm::json::Object challengeUse,
                                llvm::json::Array messages,
                                std::string kind) {
  return llvm::json::Object{{"challenge_use", std::move(challengeUse)},
                            {"messages", std::move(messages)},
                            {"kind", std::move(kind)}};
}

static llvm::json::Array friDepSlots(const FriDescription &desc) {
  llvm::json::Array slots;
  if (desc.valueFaithful) {
    slots.push_back(depSlot("zeta", "ext_field"));
    slots.push_back(depSlot("alpha", "ext_field"));
  }
  for (int64_t i = 1; i <= desc.k; ++i)
    slots.push_back(depSlot(foldRole(desc, i), "ext_field"));
  slots.push_back(depSlot("query", "query_index"));
  return slots;
}

static llvm::json::Array friRounds(const FriDescription &desc,
                                   const QueryShape &shape) {
  llvm::json::Array rounds;
  if (desc.valueFaithful) {
    // The stripped harness's own order: the opening point and batch
    // challenge first, then commit-then-sample rounds, then the final
    // coefficient in the query round.
    // The opening point and batch challenge are the PCS opening phase,
    // not fold rounds: the kind keeps the fold-count projection honest
    // (a soundness rule counting fold rounds must see exactly k).
    rounds.push_back(round(llvm::json::Object{{"role", "zeta"}},
                           llvm::json::Array{}, "opening"));
    rounds.push_back(round(llvm::json::Object{{"role", "alpha"}},
                           llvm::json::Array{message("opened", 1)}, "opening"));
    for (int64_t i = 1; i <= desc.k; ++i)
      rounds.push_back(round(llvm::json::Object{{"role", foldRole(desc, i)}},
                             llvm::json::Array{message(msgRole(desc, i), 1)},
                             "fold"));
    rounds.push_back(
        round(llvm::json::Object{{"role", "query"}, {"count", desc.ell}},
              llvm::json::Array{message("final", shape.finalLen)}, "query"));
    return rounds;
  }
  for (int64_t i = 1; i <= desc.k; ++i) {
    llvm::json::Array messages;
    if (i > 1)
      messages.push_back(message(msgRole(desc, i - 1), 1));
    rounds.push_back(round(llvm::json::Object{{"role", foldRole(desc, i)}},
                           std::move(messages), "fold"));
  }
  rounds.push_back(
      round(llvm::json::Object{{"role", "query"}, {"count", desc.ell}},
            llvm::json::Array{message(msgRole(desc, desc.k), 1)}, "query"));
  return rounds;
}

/// The shape knobs ride the reduction parameters so a soundness rule
/// reads the declared rate directly (the analysis-parameter precedent);
/// the shape side condition ties them to the realized fold count.
static llvm::json::Object friParameters(const FriDescription &desc) {
  llvm::json::Object parameters{{"log_blowup", "atom"},
                                {"log_final_poly_len", "atom"}};
  if (desc.johnson()) {
    parameters["johnson_delta"] = "atom";
    parameters["johnson_eta"] = "atom";
    parameters["johnson_m"] = "atom";
  }
  if (desc.udr())
    parameters["udr_theta"] = "atom";
  return parameters;
}

static llvm::json::Object attachment(std::string kind,
                                     llvm::json::Object source,
                                     std::string targetRole) {
  return llvm::json::Object{{"kind", std::move(kind)},
                            {"source", std::move(source)},
                            {"target_role", std::move(targetRole)}};
}
static llvm::json::Object fromDependency(std::string role) {
  return llvm::json::Object{{"kind", "dependency"},
                            {"role", std::move(role)}};
}
static llvm::json::Object fromMessage(std::string role) {
  return llvm::json::Object{{"kind", "message"},
                            {"role", std::move(role)},
                            {"occurrence", 0}};
}
static llvm::json::Object fromInputAnchor(int64_t input, std::string anchor) {
  return llvm::json::Object{{"kind", "input_anchor"},
                            {"input", input},
                            {"anchor", std::move(anchor)}};
}
static llvm::json::Object fromList(llvm::json::Array items) {
  return llvm::json::Object{{"kind", "list"}, {"items", std::move(items)}};
}

/// The query phase's obligations, bound to this contract. In the
/// value-faithful variant the openings themselves are response
/// material, not round messages — they follow the query challenge
/// unabsorbed — so the attachments pin what the round structure already
/// carries: the sampled dependencies and the absorbed pre-challenge
/// messages.
static llvm::json::Object friChecks(const FriDescription &desc,
                                    const QueryShape &shape) {
  if (!desc.valueFaithful)
    return llvm::json::Object{
        {"consistency",
         llvm::json::Object{
             {"contract", "zkc.check.rs-equality"},
             {"parameters", llvm::json::Object{}},
             {"transparent_predicate",
              llvm::json::Array{"eq", llvm::json::Array{"role", "lhs"},
                                llvm::json::Array{"role", "rhs"}}},
             {"attachments",
              llvm::json::Array{
                  attachment("material_ref_equality",
                             fromInputAnchor(0, "statement"), "lhs"),
                  attachment("value_identity",
                             fromMessage(msgRole(desc, desc.k)), "rhs")}}}}};

  llvm::json::Array betas, roots;
  for (int64_t i = 1; i <= desc.k; ++i) {
    betas.push_back(fromDependency(foldRole(desc, i)));
    roots.push_back(fromMessage(msgRole(desc, i)));
  }
  return llvm::json::Object{
      {"merkle",
       llvm::json::Object{
           {"contract", "zkc.check.merkle-multi-opening"},
           {"parameters", llvm::json::Object{}},
           {"attachments",
            llvm::json::Array{
                attachment("material_ref_equality",
                           fromInputAnchor(0, "statement"), "root"),
                attachment("value_identity_vector", fromDependency("query"),
                           "indices")}}}},
      {"consistency",
       llvm::json::Object{
           {"contract", "zkc.check.fri-query-consistency"},
           {"parameters",
            llvm::json::Object{
                {"log_blowup", std::to_string(desc.logBlowup)},
                {"log_final_poly_len",
                 std::to_string(desc.logFinalPolyLen)}}},
           {"attachments",
            llvm::json::Array{
                attachment("value_identity", fromDependency("zeta"), "zeta"),
                attachment("value_identity", fromMessage("opened"), "opened"),
                attachment("value_identity", fromDependency("alpha"), "alpha"),
                attachment(shape.finalLen > 1 ? "value_identity_vector"
                                              : "value_identity",
                           fromMessage("final"), "final_coefficients"),
                attachment("value_identity_vector", fromDependency("query"),
                           "indices"),
                attachment("value_identity_list", fromList(std::move(betas)),
                           "betas"),
                attachment("value_identity_list", fromList(std::move(roots)),
                           "roots")}}}}};
}

/// The one conclusion both reductions reach, over the statement anchor
/// the relation input carries.
static llvm::json::Object queryConsistentOutput() {
  return llvm::json::Object{
      {"profile", "fri_query_consistent"},
      {"anchors",
       llvm::json::Object{{"statement", fromInputAnchor(0, "statement")}}}};
}

static llvm::json::Object friReduction(const FriDescription &desc,
                                       const QueryShape &shape) {
  return llvm::json::Object{
      {"consumes", llvm::json::Array{"opaque_relation"}},
      {"dep_slots", friDepSlots(desc)},
      {"rounds", friRounds(desc, shape)},
      {"parameters", friParameters(desc)},
      {"checks", friChecks(desc, shape)},
      {"constraints", llvm::json::Array{}},
      {"outputs", llvm::json::Array{queryConsistentOutput()}}};
}

/// Grinding is a separate local implication: exact shape, exact pow-pin
/// premise, and one anchor-free evaluation output.
static llvm::json::Object grindingReduction() {
  return llvm::json::Object{
      {"consumes", llvm::json::Array{"fri_query_consistent"}},
      {"dep_slots", llvm::json::Array{depSlot("pow", "pow_value")}},
      {"rounds",
       llvm::json::Array{round(llvm::json::Object{{"role", "pow"}},
                               llvm::json::Array{message("nonce", 1)}, "pow")}},
      {"parameters", llvm::json::Object{}},
      {"checks",
       llvm::json::Object{
           {"pow_pin",
            llvm::json::Object{
                {"contract", "zkc.check.pow-zero"},
                {"parameters", llvm::json::Object{}},
                {"transparent_predicate",
                 llvm::json::Array{"eq",
                                   llvm::json::Array{"role", "challenge"},
                                   llvm::json::Array{"const", "zero"}}},
                {"attachments",
                 llvm::json::Array{
                     attachment("value_identity", fromMessage("nonce"),
                                "nonce"),
                     attachment("value_identity", fromDependency("pow"),
                                "challenge")}}}}}},
      {"constraints", llvm::json::Array{}},
      {"outputs", llvm::json::Array{queryConsistentOutput()}}};
}

std::string zkc::family::emitFriVocabulary(const FriDescription &desc) {
  QueryShape shape{desc.ell, desc.k, desc.queryLog2,
                   int64_t(1) << desc.logFinalPolyLen};
  std::optional<QueryPhaseSpecs> specs;
  if (desc.valueFaithful)
    specs = mintQueryPhaseSpecs(shape);

  llvm::json::Object reductions{{"fri", friReduction(desc, shape)}};
  if (desc.grindingBits)
    reductions["grinding"] = grindingReduction();

  llvm::json::Object document{
      {"registry", "zkc.protocol_vocabulary"},
      {"claim_profiles", claimProfiles()},
      {"predicate_specs", predicateSpecs(specs)},
      {"check_contracts", checkContracts(desc, shape, specs)},
      {"hole_contracts", holeContracts(desc, shape)},
      {"reduction_contracts", std::move(reductions)},
      {"terminal_rules", llvm::json::Object{}}};

  std::string out;
  raw_string_ostream os(out);
  os << llvm::formatv("{0:2}", llvm::json::Value(std::move(document))) << "\n";
  return out;
}

/// Emit the authored preamble after `pir.begin` and return the token
/// the family's own first event chains from. The preamble uses its own
/// token names so adding one changes no other line of the spine.
static std::string emitPreamble(llvm::raw_ostream &os,
                                const FriDescription &desc) {
  std::string token = "%t0";
  for (size_t index = 0; index < desc.preamble.size(); ++index) {
    const FriDescription::PreambleEntry &entry = desc.preamble[index];
    std::string next = "%p" + std::to_string(index + 1);
    os << "  " << next << ", %pre" << (index + 1) << " = pir.bind " << token
       << " \"" << entry.label << "\" : \"" << entry.payloadClass
       << "\" stage seal = \"" << entry.value << "\"\n";
    token = next;
  }
  return token;
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
  os << " segments [" << (6 + 2 * k + (int64_t)desc.preamble.size())
     << "]";
  os << " policy \"analysis_only_artifact\" {\n";
  os << "  %c = pir.instantiate \"prox\" anchors {contract = \""
     << desc.anchorContract << "\", statement = \"" << desc.anchorStatement
     << "\"} : !pir.claim<\"opaque_relation\">\n";
  os << "  %t0 = pir.begin\n";
  std::string head = emitPreamble(os, desc);
  // The pinned harness binds the input log-size before anything else;
  // the trace height is the evaluation domain shrunk by the rate,
  // query_log2 - log_blowup.
  os << "  %t1, %size = pir.bind " << head << " \"log_size\" : \"pow_value\" stage "
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
  std::string head = emitPreamble(os, desc);
  os << "  %t1, %f = pir.bind " << head
     << " \"f_root\" : \"rs\" stage instance\n";
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
