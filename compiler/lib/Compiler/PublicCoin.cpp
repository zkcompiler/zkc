#include "zkc/Compiler/PublicCoin.h"
#include "PublicCoin.h"
#include "PublicCoinGraph.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
constexpr unsigned maxPorts = 1024, maxDraws = 64;
constexpr unsigned maxWork = 1000000;
struct Requirement {
  std::string entry, prover, verifier, subject;
  SmallVector<std::string> entries;
  unsigned service = 0, decision = 0;
  SmallVector<unsigned> bound;
  SmallVector<std::pair<std::string, std::string>> draws;
};
bool keys(const json::Object &o, ArrayRef<StringRef> names) {
  return o.size() == names.size() &&
         all_of(names, [&](StringRef name) { return o.get(name); });
}
bool name(const json::Object &o, StringRef key, std::string &out) {
  auto s = o.getString(key);
  if (!s || s->empty() || s->size() > 4096 || s->contains('\0'))
    return false;
  out = s->str();
  return true;
}
bool index(const json::Object &o, StringRef key, unsigned &out) {
  auto *value = o.get(key);
  auto n = value ? value->getAsUINT64() : std::nullopt;
  if (!n || *n >= maxPorts)
    return false;
  out = *n;
  return true;
}
Expected<Requirement> parseRequirement(StringRef text) {
  auto parsed = parseNaturalJson(
      text, 1024 * 1024, 64, "public-coin-requirement", "public-coin-limit");
  if (!parsed)
    return parsed.takeError();
  auto *o = parsed->getAsObject();
  Requirement r;
  if (!o ||
      !keys(*o, {"format", "entry", "prover", "verifier", "service", "decision",
                 "bound_inputs", "draws", "subject", "deployment_entries"}) ||
      o->getString("format") != "zkc.public-coin-requirement/0" ||
      !name(*o, "subject", r.subject) ||
      (r.subject != "authored" && r.subject != "realized") ||
      !name(*o, "entry", r.entry) || !name(*o, "prover", r.prover) ||
      !name(*o, "verifier", r.verifier) || r.prover == r.verifier ||
      !index(*o, "service", r.service) || !index(*o, "decision", r.decision))
    return error("public-coin-requirement");
  auto *entries = o->getArray("deployment_entries");
  if (!entries || entries->empty() || entries->size() > maxPorts)
    return error("public-coin-requirement");
  std::set<std::string> uniqueEntries;
  for (const auto &entry : *entries) {
    auto name = entry.getAsString();
    if (!name || name->empty() || name->size() > 4096 || name->contains('\0') ||
        !uniqueEntries.insert(name->str()).second)
      return error("public-coin-requirement");
    r.entries.push_back(name->str());
  }
  if (!uniqueEntries.count(r.entry))
    return error("public-coin-requirement");
  auto *inputs = o->getArray("bound_inputs"), *draws = o->getArray("draws");
  if (!inputs || inputs->size() > maxPorts || !draws || draws->empty() ||
      draws->size() > maxDraws)
    return error("public-coin-requirement");
  std::set<unsigned> unique;
  for (auto &input : *inputs) {
    auto n = input.getAsUINT64();
    if (!n || *n >= maxPorts || !unique.insert(*n).second)
      return error("public-coin-requirement");
    r.bound.push_back(*n);
  }
  std::set<std::string> sites;
  for (auto &draw : *draws) {
    auto *d = draw.getAsObject();
    std::string query, delivery;
    if (!d || !keys(*d, {"query_site", "delivery_site"}) ||
        !name(*d, "query_site", query) ||
        !name(*d, "delivery_site", delivery) || !sites.insert(query).second ||
        !sites.insert(delivery).second)
      return error("public-coin-requirement");
    r.draws.emplace_back(std::move(query), std::move(delivery));
  }
  return r;
}
std::string digest(StringRef value) {
  return toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
}
// Stream the identity rather than retaining another complete copy of the IR.
class Fingerprint : public raw_ostream {
  SHA256 hash;
  uint64_t bytes = 0;
  void write_impl(const char *data, size_t size) override {
    bytes += size;
    if (bytes <= 16 * 1024 * 1024)
      hash.update(StringRef(data, size));
  }
  uint64_t current_pos() const override { return bytes; }

public:
  Fingerprint() { SetBufferSize(4096); }
  ~Fingerprint() override { flush(); }
  Expected<std::string> finish() {
    flush();
    if (bytes > 16 * 1024 * 1024)
      return error("public-coin-limit");
    return toHex(hash.final(), true);
  }
};
Expected<std::string> fingerprint(ModuleOp module) {
  Fingerprint stream;
  module.print(stream);
  return stream.finish();
}
template <typename T> std::string spelling(T type) {
  std::string text;
  raw_string_ostream(text) << type;
  return text;
}
bool owns(ArrayAttr roles, StringRef role) {
  return any_of(roles, [&](Attribute a) {
    return cast<StringAttr>(a).getValue() == role;
  });
}
json::Array ports(const BitVector &bits) {
  json::Array result;
  for (int port : bits.set_bits())
    result.push_back(port);
  return result;
}
Expected<json::Object> interface(pir::MathematicalOp program,
                                 const Requirement &r,
                                 SymbolTableCollection &symbols) {
  auto signature = program.getFunctionType();
  if (signature.getNumInputs() > maxPorts ||
      signature.getNumResults() > maxPorts || program.getRoles().size() != 2 ||
      !owns(program.getRoles(), r.prover) ||
      !owns(program.getRoles(), r.verifier) ||
      r.service >= signature.getNumInputs() ||
      r.decision >= signature.getNumResults() ||
      !signature.getResult(r.decision).isSignlessInteger(1) ||
      !owns(cast<ArrayAttr>(program.getOutputRoles()[r.decision]), r.verifier))
    return error("public-coin-interface");
  auto service =
      dyn_cast<pir::ServiceReferenceType>(signature.getInput(r.service));
  auto serviceRoles = cast<ArrayAttr>(program.getInputRoles()[r.service]);
  if (!service || protocol::randomServiceField(service.getContract()).empty() ||
      serviceRoles.size() != 1 || !owns(serviceRoles, r.verifier))
    return error("public-coin-service");
  BitVector bound(signature.getNumInputs()), statement(bound.size()),
      privateInputs(bound.size());
  for (unsigned port : r.bound) {
    if (port >= bound.size() ||
        !owns(cast<ArrayAttr>(program.getInputRoles()[port]), r.verifier))
      return error("public-coin-interface");
    auto policy = mathematical::nativeTypePolicy(signature.getInput(port));
    if (!policy || !policy->wire ||
        isa<pir::ServiceReferenceType>(signature.getInput(port)))
      return error("public-coin-interface");
    bound.set(port);
    if (!owns(cast<ArrayAttr>(program.getInputRoles()[port]), r.prover))
      privateInputs.set(port);
  }
  for (auto use : program.getBody().front().getOps<pir::StatementOp>()) {
    auto relation = symbols.lookupNearestSymbolFrom<relation::DeclareOp>(
        use, use.getRelationAttr());
    if (!relation || relation.getPurposes().size() != use.getNumOperands())
      return error("public-coin-module");
    for (auto [input, selector, purpose] :
         zip(use.getInputs(), use.getSelectors(), relation.getPurposes())) {
      if (cast<StringAttr>(selector).getValue() != r.verifier)
        continue;
      auto formal = dyn_cast<BlockArgument>(input);
      if (!formal || formal.getOwner() != &program.getBody().front())
        return error("public-coin-statement");
      if (!bound.test(formal.getArgNumber()))
        return error("public-coin-statement");
      if (cast<StringAttr>(purpose).getValue() != "witness")
        statement.set(formal.getArgNumber());
    }
  }
  // Binding obligations cover every verifier data input, not just the ones
  // the current decision happens to depend on. Services are separate authority.
  for (unsigned port = 0; port < bound.size(); ++port)
    if (owns(cast<ArrayAttr>(program.getInputRoles()[port]), r.verifier) &&
        !isa<pir::ServiceReferenceType>(signature.getInput(port)) &&
        !bound.test(port))
      return error("public-coin-unbound-input",
                   Twine("verifier input ") + Twine(port));
  json::Array inputs, outputs;
  for (auto [i, type] : enumerate(signature.getInputs()))
    inputs.push_back(json::Object{
        {"port", i},
        {"type", spelling(type)},
        {"roles", spelling(cast<ArrayAttr>(program.getInputRoles()[i]))}});
  for (auto [i, type] : enumerate(signature.getResults()))
    outputs.push_back(json::Object{
        {"port", i},
        {"type", spelling(type)},
        {"roles", spelling(cast<ArrayAttr>(program.getOutputRoles()[i]))}});
  auto nonStatement = bound;
  nonStatement.reset(statement);
  return json::Object{
      {"inputs", std::move(inputs)},
      {"outputs", std::move(outputs)},
      {"statement_inputs", ports(statement)},
      {"bound_non_statement_inputs", ports(nonStatement)},
      {"prover_unavailable_bound_inputs", ports(privateInputs)}};
}
} // namespace
Expected<json::Value>
detail::analyzePublicCoin(const mathematical::RealizedProtocol &owner,
                          StringRef text) {
  auto requirement = parseRequirement(text);
  if (!requirement)
    return requirement.takeError();
  const auto &r = *requirement;
  auto authored = owner.authoredSnapshot();
  auto prepared = owner.preparedSnapshot();
  auto realized = owner.observationSnapshot();
  if (!authored || !prepared || !realized) {
    if (!realized)
      return realized.takeError();
    return error("public-coin-module");
  }
  std::set<std::string> roots;
  auto unit = *prepared->getOps<pir::ProtocolModuleOp>().begin();
  for (auto program : unit.getBody().front().getOps<pir::MathematicalOp>())
    roots.insert(program.getSymName().str());
  if (roots != std::set<std::string>(r.entries.begin(), r.entries.end()))
    return error("public-coin-interface",
                 "deployment entries differ from the checked owner");
  ModuleOp subject = r.subject == "authored" ? *authored : *realized->module;
  auto sourceHash = fingerprint(*authored);
  if (!sourceHash)
    return sourceHash.takeError();
  auto preparedHash = fingerprint(*prepared);
  if (!preparedHash)
    return preparedHash.takeError();
  auto realizedHash = fingerprint(*realized->module);
  if (!realizedHash)
    return realizedHash.takeError();
  auto root = *subject.getOps<pir::ProtocolModuleOp>().begin();
  SymbolTable symbols(root);
  auto program = symbols.lookup<pir::MathematicalOp>(r.entry);
  if (!program)
    return error("public-coin-interface");
  SymbolTableCollection tables;
  auto boundary = interface(program, r, tables);
  if (!boundary)
    return boundary.takeError();
  uint64_t remaining = maxWork;
  facts::Work work(remaining);
  ArrayRef<Operation *> transports;
  if (r.subject == "realized")
    transports = realized->dataExchanges;
  ProtocolObservationAnalysis analysis(subject, transports);
  auto checked = analysis.get(program, r.verifier, work);
  if (!checked)
    return error(work.exhausted() ? "public-coin-limit"
                                  : "public-coin-dependence",
                 toString(checked.takeError()));
  const auto &summary = **checked;
  using Pending = ProtocolPendingTransfer;
  if (summary.pending.input == Pending::Input::Formal ||
      summary.pending.output == Pending::Output::Query)
    return error("public-coin-delivery");
  for (int service : summary.services.set_bits())
    if (unsigned(service) != r.service)
      return error("public-coin-service");
  if (r.decision >= summary.results.size() ||
      summary.results[r.decision].empty())
    return error("public-coin-dependence");
  auto graph = publicCoinGraph(subject, analysis, summary, work, r.draws);
  if (!graph)
    return graph.takeError();
  auto policy = owner.mathematicalPolicy();
  auto oraclePolicy =
      protocol::encodeOracleRealizationPolicy(owner.oraclePolicy());
  if (!oraclePolicy)
    return oraclePolicy.takeError();
  auto record = parseNaturalJson(owner.realizationRecord(), 8 * 1024 * 1024, 64,
                                 "public-coin-report", "public-coin-limit");
  if (!record)
    return record.takeError();
  auto selection = json::parse(owner.normalizedSelection());
  if (!selection)
    return selection.takeError();
  json::Array entries;
  for (const auto &entry : roots)
    entries.push_back(entry);
  json::Object result{{"format", "zkc.public-coin-view/0"},
                      {"subject", r.subject},
                      {"entry", r.entry},
                      {"deployment_entries", std::move(entries)},
                      {"prover", r.prover},
                      {"verifier", r.verifier},
                      {"service", r.service},
                      {"decision", r.decision},
                      {"interface", std::move(*boundary)},
                      {"graph", std::move(*graph)},
                      {"analyzed_ir_sha256",
                       r.subject == "authored" ? *sourceHash : *realizedHash},
                      {"source_ir_sha256", std::move(*sourceHash)},
                      {"prepared_ir_sha256", std::move(*preparedHash)},
                      {"realized_ir_sha256", std::move(*realizedHash)},
                      {"requirement_sha256", digest(text)},
                      {"finite_bulk", policy.finiteBulk},
                      {"fuse_vector_reductions", policy.vectorReductionFusion},
                      {"fuse_collect_fold", policy.collectFoldFusion},
                      {"calculation_batching", policy.calculationBatching},
                      {"oracle_policy", std::move(*oraclePolicy)},
                      {"oracle_selection", std::move(*selection)},
                      {"realization", std::move(*record)}};
  // Count without retaining another serialized copy, including the checked
  // realization record and interface outside the graph's own byte allowance.
  class Counter : public raw_ostream {
    uint64_t count = 0;
    void write_impl(const char *, size_t size) override { count += size; }
    uint64_t current_pos() const override { return count; }

  public:
    Counter() { SetUnbuffered(); }
  } stream;
  stream << json::Value(json::Object(result));
  if (stream.tell() > 8 * 1024 * 1024)
    return error("public-coin-limit");
  return json::Value(std::move(result));
}
Expected<json::Value>
analyzePublicCoin(ModuleOp original, StringRef text,
                  MathematicalSelectionPolicy policy,
                  const protocol::OracleRealizationPolicy &oraclePolicy) {
  auto requirement = parseRequirement(text);
  if (!requirement)
    return requirement.takeError();
  if (!original || failed(zkc::admitStage(original)) ||
      !hasSingleElement(*original.getBody()))
    return error("public-coin-module");
  auto root = dyn_cast<pir::ProtocolModuleOp>(original.getBody()->front());
  if (!root || root.getProfile() != pir::Profile::Protocol)
    return error("public-coin-module");
  if (!SymbolTable::lookupSymbolIn(root, requirement->entry))
    return error("public-coin-interface");
  auto prepared = mathematical::PreparedProtocol::prepare(original, policy);
  if (!prepared)
    return error("public-coin-module");
  SmallVector<StringRef> entries;
  for (const auto &entry : requirement->entries)
    entries.push_back(entry);
  if (failed(prepared->selectEntries(entries)))
    return error("public-coin-interface");
  auto realized = mathematical::RealizedProtocol::realize(std::move(*prepared),
                                                          oraclePolicy);
  if (!realized)
    return realized.takeError();
  return detail::analyzePublicCoin(*realized, text);
}
Error checkPublicCoin(ModuleOp original, StringRef requirement, StringRef text,
                      MathematicalSelectionPolicy policy,
                      const protocol::OracleRealizationPolicy &oraclePolicy) {
  auto candidate = parseNaturalJson(text, 8 * 1024 * 1024, 64,
                                    "public-coin-report", "public-coin-limit");
  if (!candidate)
    return candidate.takeError();
  auto checked = analyzePublicCoin(original, requirement, policy, oraclePolicy);
  if (!checked)
    return checked.takeError();
  if (!zkc::equalNaturalJson(*candidate, *checked))
    return error("public-coin-report");
  return Error::success();
}
} // namespace zkc
