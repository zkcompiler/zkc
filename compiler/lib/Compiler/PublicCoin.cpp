#include "zkc/Compiler/PublicCoin.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
constexpr unsigned maxPorts = 1024, maxActions = 2048, maxDraws = 64;
constexpr unsigned maxDependencies = 65536, maxWork = 1000000;
struct Requirement {
  std::string entry, prover, verifier;
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
                 "bound_inputs", "draws"}) ||
      o->getString("format") != "zkc.public-coin-requirement/1" ||
      !name(*o, "entry", r.entry) || !name(*o, "prover", r.prover) ||
      !name(*o, "verifier", r.verifier) || r.prover == r.verifier ||
      !index(*o, "service", r.service) || !index(*o, "decision", r.decision))
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
std::string spelling(Type type) {
  std::string text;
  raw_string_ostream(text) << type;
  return text;
}
bool owns(ArrayAttr roles, StringRef role) {
  return any_of(roles, [&](Attribute a) {
    return cast<StringAttr>(a).getValue() == role;
  });
}
Value unrestricted(Value value) {
  while (auto restriction = value.getDefiningOp<pir::RestrictRolesOp>())
    value = restriction.getInput();
  return value;
}

// Retain authored paths as diagnostic identity, not a cryptographic domain.
// No expression graph is copied: only bounded ordered action occurrences.
struct Occurrences {
  StringMap<json::Array> paths;
  unsigned remainingBytes = 1024 * 1024;
  Error collect(pir::MathematicalOp function, SymbolTable &symbols,
                ArrayRef<std::string> prefix = {}, StringRef expanded = {}) {
    if (prefix.size() > 64)
      return error("public-coin-limit");
    for (auto &op : function.getBody().front()) {
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site)
        continue;
      std::string id = expanded.empty()
                           ? site.getValue().str()
                           : (Twine("apply_") + Twine(expanded.size()) + "_" +
                              expanded + "_" + site.getValue())
                                 .str();
      SmallVector<std::string> path(prefix);
      path.push_back(site.getValue().str());
      if (auto call = dyn_cast<pir::ApplyOp>(op)) {
        auto callee = symbols.lookup<pir::MathematicalOp>(call.getCallee());
        if (!callee)
          return error("public-coin-module");
        if (auto e = collect(callee, symbols, path, id))
          return e;
        continue;
      }
      if (paths.size() >= maxActions || id.size() > remainingBytes)
        return error("public-coin-limit");
      remainingBytes -= id.size();
      json::Array parts;
      for (auto &part : path) {
        if (part.size() > remainingBytes)
          return error("public-coin-limit");
        remainingBytes -= part.size();
        parts.push_back(part);
      }
      if (!paths.try_emplace(id, std::move(parts)).second)
        return error("public-coin-occurrence");
    }
    return Error::success();
  }
  Expected<json::Object> action(StringRef site) {
    auto found = paths.find(site);
    if (found == paths.end())
      return error("public-coin-occurrence");
    return json::Object{{"site", site.str()},
                        {"path", json::Array(found->second)}};
  }
};

class View {
  pir::MathematicalOp program;
  const Requirement &requirement;
  Occurrences &occurrences;
  mathematical::Availability availability;
  llvm::DenseMap<Value, BitVector> dependencies;
  BitVector bound, statement, unavailableToProver;
  unsigned verifier = 0, anchorsCount = 0, work = maxWork;
  unsigned reportWork = maxDependencies;
  json::Array anchors, events, draws, guards;
  // Entry input anchors occupy their actual port number, including unbound
  // ports. Only bound ports enter the view; unused ports grant no premise.
  bool available(Value value) {
    auto found = availability.values.find(value);
    return found != availability.values.end() && found->second.test(verifier);
  }
  Error charge(unsigned count) {
    if (count > work)
      return error("public-coin-limit");
    work -= count;
    return Error::success();
  }
  Error set(Value value, BitVector deps) {
    if (auto e = charge((deps.size() + 63) / 64 + 1))
      return e;
    dependencies.try_emplace(value, std::move(deps));
    return Error::success();
  }
  Error atom(Value value, unsigned index) {
    BitVector deps(anchorsCount);
    deps.set(index);
    return set(value, std::move(deps));
  }
  Expected<json::Array> checkedDependencies(Value value) {
    auto found = dependencies.find(value);
    if (found == dependencies.end())
      return error("public-coin-dependence");
    json::Array result;
    for (int bit : found->second.set_bits()) {
      if (unsigned(bit) < bound.size() && !bound.test(bit))
        return error("public-coin-unbound-input",
                     Twine("verifier component at input ") + Twine(bit));
      if (!reportWork)
        return error("public-coin-limit");
      --reportWork;
      result.push_back(bit);
    }
    return result;
  }
  json::Array ports(const BitVector &bits) {
    json::Array result;
    for (int index : bits.set_bits())
      result.push_back(index);
    return result;
  }

public:
  View(pir::MathematicalOp p, const Requirement &r, Occurrences &o)
      : program(p), requirement(r), occurrences(o) {}
  Expected<json::Object> run(SymbolTableCollection &tables) {
    auto &r = requirement;
    auto &block = program.getBody().front();
    auto signature = program.getFunctionType();
    if (signature.getNumInputs() > maxPorts ||
        signature.getNumResults() > maxPorts ||
        program.getRoles().size() != 2 || !owns(program.getRoles(), r.prover) ||
        !owns(program.getRoles(), r.verifier) ||
        r.service >= signature.getNumInputs() ||
        r.decision >= signature.getNumResults() ||
        !signature.getResult(r.decision).isSignlessInteger(1) ||
        !owns(cast<ArrayAttr>(program.getOutputRoles()[r.decision]),
              r.verifier))
      return error("public-coin-interface");
    auto service =
        dyn_cast<pir::ServiceReferenceType>(signature.getInput(r.service));
    auto serviceRoles = cast<ArrayAttr>(program.getInputRoles()[r.service]);
    if (!service ||
        protocol::randomServiceField(service.getContract()).empty() ||
        serviceRoles.size() != 1 || !owns(serviceRoles, r.verifier))
      return error("public-coin-service");
    verifier = cast<StringAttr>(program.getRoles()[0]).getValue() == r.verifier
                   ? 0
                   : 1;
    if (failed(mathematical::analyze(program, availability, tables)))
      return error("public-coin-module");
    bound.resize(signature.getNumInputs());
    statement.resize(bound.size());
    unavailableToProver.resize(bound.size());
    for (unsigned input : r.bound) {
      if (input >= bound.size() || !available(block.getArgument(input)))
        return error("public-coin-interface");
      auto policy = mathematical::nativeTypePolicy(signature.getInput(input));
      if (!policy || !policy->wire)
        return error("public-coin-interface");
      bound.set(input);
      if (!owns(cast<ArrayAttr>(program.getInputRoles()[input]), r.prover))
        unavailableToProver.set(input);
    }
    unsigned actions = 0;
    anchorsCount = signature.getNumInputs();
    for (auto &op : block) {
      if (op.hasAttr("site") && ++actions > maxActions)
        return error("public-coin-limit");
      if (isa<pir::QueryOp>(op))
        ++anchorsCount;
      if (auto exchange = dyn_cast<pir::ExchangeOp>(op);
          exchange && exchange.getReceiver() == r.verifier)
        ++anchorsCount;
    }
    for (auto arg : block.getArguments()) {
      unsigned input = arg.getArgNumber();
      anchors.push_back(json::Object{{"kind", "input"},
                                     {"port", input},
                                     {"type", spelling(arg.getType())}});
      if (available(arg))
        if (auto e = atom(arg, input))
          return e;
    }
    for (unsigned input : r.bound)
      events.push_back(input);
    pir::QueryOp pending;
    unsigned nextDraw = 0;
    for (auto &op : block) {
      if (auto use = dyn_cast<pir::StatementOp>(op)) {
        // Ordinary admission fixes these operands to selected entry components.
        auto relation = tables.lookupNearestSymbolFrom<relation::DeclareOp>(
            use, use.getRelationAttr());
        if (!relation || relation.getPurposes().size() != use.getNumOperands())
          return error("public-coin-module");
        for (auto [input, selector, purpose] :
             zip(use.getInputs(), use.getSelectors(), relation.getPurposes())) {
          if (cast<StringAttr>(selector).getValue() != r.verifier)
            continue;
          unsigned port = cast<BlockArgument>(input).getArgNumber();
          if (!bound.test(port))
            return error("public-coin-statement");
          if (cast<StringAttr>(purpose).getValue() != "witness")
            statement.set(port);
        }
        continue;
      }
      if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        if (call.getRole() == r.verifier)
          return error("public-coin-verifier-local");
        continue;
      }
      if (auto query = dyn_cast<pir::QueryOp>(op)) {
        if (query.getOwner() != r.verifier ||
            query.getReference() != block.getArgument(r.service))
          return error("public-coin-service");
        if (pending || nextDraw >= r.draws.size() ||
            query.getSite() != r.draws[nextDraw].first)
          return error("public-coin-delivery");
        auto record = occurrences.action(query.getSite());
        if (!record)
          return record.takeError();
        (*record)["prefix_length"] = events.size();
        draws.push_back(std::move(*record));
        auto anchor = occurrences.action(query.getSite());
        if (!anchor)
          return anchor.takeError();
        (*anchor)["kind"] = "draw";
        (*anchor)["type"] = spelling(query.getResult(0).getType());
        unsigned id = anchors.size();
        anchors.push_back(std::move(*anchor));
        events.push_back(id);
        if (auto e = atom(query.getResult(0), id))
          return e;
        pending = query;
        ++nextDraw;
        continue;
      }
      if (auto exchange = dyn_cast<pir::ExchangeOp>(op)) {
        if (exchange.getReceiver() == r.verifier) {
          if (pending)
            return error("public-coin-delivery");
          auto anchor = occurrences.action(exchange.getSite());
          if (!anchor)
            return anchor.takeError();
          (*anchor)["kind"] = "receive";
          (*anchor)["type"] = spelling(exchange.getOutput().getType());
          unsigned id = anchors.size();
          anchors.push_back(std::move(*anchor));
          events.push_back(id);
          // The verifier's received component is independent of the sender's
          // expression, including when that expression is also available at V.
          if (auto e = atom(exchange.getOutput(), id))
            return e;
        } else {
          if (!pending || exchange.getSite() != r.draws[nextDraw - 1].second ||
              unrestricted(exchange.getInput()) != pending.getResult(0))
            return error("public-coin-delivery");
          auto delivery = occurrences.action(exchange.getSite());
          if (!delivery)
            return delivery.takeError();
          (*draws.back().getAsObject())["delivery"] = std::move(*delivery);
          auto found = dependencies.find(exchange.getInput());
          if (found == dependencies.end())
            return error("public-coin-dependence");
          if (auto e = set(exchange.getOutput(), found->second))
            return e;
          pending = {};
        }
        continue;
      }
      if (auto guard = dyn_cast<pir::GuardOp>(op)) {
        if (guard.getOwner() == r.verifier) {
          auto deps = checkedDependencies(guard.getCondition());
          if (!deps)
            return deps.takeError();
          auto action = occurrences.action(guard.getSite());
          if (!action)
            return action.takeError();
          (*action)["dependencies"] = std::move(*deps);
          (*action)["prefix_length"] = events.size();
          guards.push_back(std::move(*action));
        }
        continue;
      }
      if (isa<pir::MathematicalReturnOp>(op))
        continue;
      bool restriction = isa<pir::RestrictRolesOp>(op);
      auto semantics = mathematical::classify(&op);
      if (!restriction &&
          (!semantics || semantics->category != mathematical::Category::Total))
        return error("public-coin-dependence");
      for (auto result : op.getResults()) {
        if (!available(result))
          continue;
        BitVector deps(anchorsCount);
        auto operands =
            restriction
                ? FailureOr<SmallVector<unsigned>>(SmallVector<unsigned>{0})
                : mathematical::operandDependencies(&op,
                                                    result.getResultNumber());
        if (failed(operands))
          return error("public-coin-dependence");
        for (unsigned index : *operands) {
          auto found = dependencies.find(op.getOperand(index));
          if (found == dependencies.end())
            return error("public-coin-dependence");
          if (auto e = charge((deps.size() + 63) / 64 + 1))
            return e;
          deps |= found->second;
        }
        if (auto e = set(result, std::move(deps)))
          return e;
      }
    }
    if (pending || nextDraw != r.draws.size())
      return error("public-coin-delivery");
    auto decision = checkedDependencies(block.back().getOperand(r.decision));
    if (!decision)
      return decision.takeError();
    auto nonStatement = bound;
    nonStatement.reset(statement);
    return json::Object{
        {"format", "zkc.public-coin-view/1"},
        {"entry", r.entry},
        {"prover", r.prover},
        {"verifier", r.verifier},
        {"service", r.service},
        {"decision", r.decision},
        {"anchors", std::move(anchors)},
        {"events", std::move(events)},
        {"draws", std::move(draws)},
        {"guards", std::move(guards)},
        {"decision_dependencies", std::move(*decision)},
        {"statement_inputs", ports(statement)},
        {"bound_non_statement_inputs", ports(nonStatement)},
        {"prover_unavailable_bound_inputs", ports(unavailableToProver)}};
  }
};
} // namespace
Expected<json::Value> analyzePublicCoin(ModuleOp original, StringRef text) {
  auto requirement = parseRequirement(text);
  if (!requirement)
    return requirement.takeError();
  if (!original || failed(verify(original)) ||
      !hasSingleElement(*original.getBody()))
    return error("public-coin-module");
  auto root = dyn_cast<pir::ProtocolModuleOp>(original.getBody()->front());
  if (!root || root.getProfile() != pir::Profile::Protocol)
    return error("public-coin-module");
  SymbolTable symbols(root);
  auto entry = symbols.lookup<pir::MathematicalOp>(requirement->entry);
  if (!entry)
    return error("public-coin-interface");
  auto sourceHash = fingerprint(original);
  if (!sourceHash)
    return sourceHash.takeError();
  OwningOpRef<ModuleOp> prepared(cast<ModuleOp>(original->clone()));
  PassManager pipeline(original.getContext());
  pipeline.addPass(protocol::createPrepareProtocolPass(false));
  if (failed(pipeline.run(*prepared)))
    return error("public-coin-module");
  auto preparedHash = fingerprint(*prepared);
  if (!preparedHash)
    return preparedHash.takeError();
  auto preparedRoot = cast<pir::ProtocolModuleOp>(prepared->getBody()->front());
  SymbolTable preparedSymbols(preparedRoot);
  auto program =
      preparedSymbols.lookup<pir::MathematicalOp>(requirement->entry);
  if (!program)
    return error("public-coin-module");
  // Ordinary admission already budgets the whole application tree, including
  // action-free callees. Collect only after bounded preparation also succeeds.
  Occurrences occurrences;
  if (auto e = occurrences.collect(entry, symbols))
    return e;
  SymbolTableCollection tables;
  View analysis(program, *requirement, occurrences);
  auto view = analysis.run(tables);
  if (!view)
    return view.takeError();
  (*view)["source_ir_sha256"] = std::move(*sourceHash);
  (*view)["prepared_ir_sha256"] = std::move(*preparedHash);
  (*view)["requirement_sha256"] = digest(text);
  return json::Value(std::move(*view));
}
Error checkPublicCoin(ModuleOp original, StringRef requirement,
                      StringRef text) {
  auto candidate = parseNaturalJson(text, 8 * 1024 * 1024, 64,
                                    "public-coin-report", "public-coin-limit");
  if (!candidate)
    return candidate.takeError();
  auto checked = analyzePublicCoin(original, requirement);
  if (!checked)
    return checked.takeError();
  if (*candidate != *checked)
    return error("public-coin-report");
  return Error::success();
}
} // namespace zkc
