#include "zkc/Compiler/NativeProof.h"
#include "NativeProofVerification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include <map>
#include <set>
using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
namespace pir = protocol_ir;
constexpr unsigned maxPorts = 1024, maxActions = 2048;
bool name(StringRef s) {
  return !s.empty() && s.size() <= 4096 &&
         all_of(s, [](unsigned char c) { return c >= 33 && c <= 126; });
}
std::optional<unsigned> number(const json::Value &v) {
  auto s = v.getAsString();
  unsigned n;
  if (!s || s->empty() || s->size() > 4 ||
      (s->size() > 1 && s->front() == '0') || s->getAsInteger(10, n) ||
      n >= maxPorts || !all_of(*s, [](char c) { return c >= '0' && c <= '9'; }))
    return {};
  return n;
}
Expected<protocol::BoundType> wire(Type type, bool input = false) {
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical)
    return logical.takeError();
  if (protocol::nativeMessageData(*logical) ||
      (input && logical->kind == "table" &&
       logical->identity == "bls12-381.fr") ||
      (input && logical->kind == "verifier_key" &&
       logical->identity == "multilinear.kzg.bls12-381/0"))
    return *logical;
  return error("native-proof-wire-type");
}
StringRef wireCodec(const protocol::BoundType &type) {
  if (protocol::nativeDataFrame(type))
    return "zkc.native-data/0";
  if (type.kind == "verifier_key")
    return "zkc.native-verifier-key/0";
  return type.kind == "field_array" ? "zkc.native-field-array/0"
                                    : protocol::defaultCodec(type);
}
bool owns(ArrayAttr set, StringRef role) {
  return is_contained(set, StringAttr::get(set.getContext(), role));
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return {};
  return dyn_cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
bool admittedOperation(Operation &op, bool beforePreparation) {
  return !op.getNumRegions() &&
         (isa<pir::QueryOp, pir::ExchangeOp, pir::StatementOp, pir::GuardOp,
              pir::LocalCallOp, pir::MathematicalReturnOp, pir::FinishIfOp,
              pir::RestrictRolesOp>(op) ||
          // Verified pure helpers contain no protocol events. The ordinary
          // preparation pass expands both kinds of static call under its
          // bounds.
          (beforePreparation && isa<pir::ApplyOp, func::CallOp>(op)) ||
          mathematical::isTotal(&op));
}
struct Origin {
  std::string protocol, site;
  std::vector<std::string> event;
  std::vector<std::array<std::string, 3>> steps;
};
// Borrowed services pass through isolated repeat captures without acquiring a
// new authority. Return the argument in its original mathematical definition.
BlockArgument sourcePort(Value value) {
  while (auto argument = dyn_cast<BlockArgument>(value)) {
    auto repeat = dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
    if (!repeat)
      return argument;
    if (!argument.getArgNumber())
      return {};
    value = repeat.getInputs()[argument.getArgNumber()];
  }
  return {};
}
Expected<StringMap<Origin>> origins(pir::MathematicalOp entry,
                                    SymbolTable &symbols) {
  StringMap<Origin> out;
  unsigned remaining = 100000;
  auto collect = [&](auto &&self, pir::MathematicalOp function, Block &body,
                     ArrayRef<std::array<std::string, 3>> steps,
                     StringRef expanded,
                     const StringMap<std::string> &roles) -> Error {
    if (steps.size() > 64)
      return error("native-proof-origin-limit");
    for (auto &op : body) {
      if (!remaining--)
        return error("native-proof-origin-limit");
      auto repeat = dyn_cast<pir::RepeatOp>(op);
      if (!admittedOperation(op, true) && !repeat &&
          !isa<pir::ProtocolYieldOp>(op))
        return error("native-proof-operation");
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site)
        continue;
      auto id = expanded.empty() ? site.str()
                                 : mathematical::expandedApplicationSite(
                                       expanded, site.getValue());
      if (auto apply = dyn_cast<pir::ApplyOp>(op)) {
        auto callee = symbols.lookup<pir::MathematicalOp>(apply.getCallee());
        if (!callee || !hasSingleElement(callee.getBody()))
          return error("native-proof-source");
        std::vector<std::array<std::string, 3>> childSteps(steps.begin(),
                                                           steps.end());
        childSteps.push_back(
            {"apply", function.getSymName().str(), site.str()});
        StringMap<std::string> childRoles;
        for (auto [source, target] : zip(callee.getRoles(), apply.getRoles()))
          childRoles[cast<StringAttr>(source).getValue()] =
              roles.lookup(cast<StringAttr>(target).getValue());
        if (auto e = self(self, callee, callee.getBody().front(), childSteps,
                          id, childRoles))
          return e;
        continue;
      }
      if (repeat || isa<pir::QueryOp, pir::ExchangeOp>(op)) {
        Origin origin{function.getSymName().str(),
                      site.str(),
                      {},
                      {steps.begin(), steps.end()}};
        if (auto query = dyn_cast<pir::QueryOp>(op)) {
          auto port = sourcePort(query.getReference());
          if (!port || port.getOwner() != &function.getBody().front())
            return error("native-proof-service-alias");
          auto service = cast<pir::ServiceReferenceType>(port.getType());
          origin.event = {"query",
                          origin.protocol,
                          origin.site,
                          "input_" + std::to_string(port.getArgNumber()),
                          service.getContract().str(),
                          query.getMethod().str(),
                          roles.lookup(query.getOwner())};
        } else if (auto message = dyn_cast<pir::ExchangeOp>(op)) {
          origin.event = {"message",
                          origin.protocol,
                          origin.site,
                          origin.site,
                          roles.lookup(message.getSender()),
                          roles.lookup(message.getReceiver())};
        } else {
          origin.event = {"repeat", origin.protocol, origin.site};
        }
        if (out.size() >= maxActions)
          return error("native-proof-origin-limit");
        if (!out.try_emplace(id, origin).second)
          return error("native-proof-origin");
        if (repeat) {
          auto child = origin.steps;
          child.push_back({"repeat", origin.protocol, origin.site});
          if (auto e = self(self, function, repeat.getBody().front(), child,
                            expanded, roles))
            return e;
        }
      }
    }
    return Error::success();
  };
  StringMap<std::string> roles;
  for (auto role : entry.getRoles()) {
    auto name = cast<StringAttr>(role).getValue();
    roles[name] = name.str();
  }
  if (auto e = collect(collect, entry, entry.getBody().front(), {}, {}, roles))
    return std::move(e);
  return out;
}
using Event = detail::NativeTranscriptEvent;
struct Admitted {
  std::vector<Event> events;
  json::Array publicBindings, messages, wireSites, sequence;
  std::vector<std::pair<std::string, std::string>> draws;
};
enum class DrawSelection { Explicit, Service };
Expected<Admitted>
admit(pir::MathematicalOp source, const NativeProofPolicy &policy,
      const StringMap<Origin> &sourceOrigins,
      DrawSelection selection = DrawSelection::Explicit,
      const protocol::ConstructionPlan *construction = nullptr) {
  if (!source)
    return error("native-proof-entry");
  auto signature = source.getFunctionType();
  auto roles = source.getRoles();
  if (roles.size() != 2 || !owns(roles, policy.producer) ||
      !owns(roles, policy.validator) || signature.getNumInputs() > maxPorts ||
      signature.getNumResults() > maxPorts ||
      policy.acceptance >= signature.getNumResults() ||
      !signature.getResult(policy.acceptance).isSignlessInteger(1) ||
      !owns(cast<ArrayAttr>(source.getOutputRoles()[policy.acceptance]),
            policy.validator))
    return error("native-proof-interface");
  Admitted admitted;
  StringRef challengeField = protocol::nativeChallengeField(policy.suite);
  if (construction) {
    if (!policy.service || *policy.service >= signature.getNumInputs())
      return error("native-proof-verifier-service");
    auto reference = dyn_cast<pir::ServiceReferenceType>(
        signature.getInput(*policy.service));
    if (!reference)
      return error("native-proof-verifier-service");
    challengeField = protocol::randomServiceField(reference.getContract());
    if (challengeField.empty())
      return error("native-proof-verifier-service");
  }
  std::vector<unsigned> required;
  for (auto [i, type] : enumerate(signature.getInputs())) {
    auto owners = cast<ArrayAttr>(source.getInputRoles()[i]);
    if (!owns(owners, policy.validator))
      continue;
    if (auto service = dyn_cast<pir::ServiceReferenceType>(type)) {
      if (policy.service != i ||
          protocol::randomServiceField(service.getContract()) !=
              challengeField ||
          owners.size() != 1)
        return error("native-proof-verifier-service");
      continue;
    }
    auto logical = wire(type, true);
    if (!logical)
      return logical.takeError();
    required.push_back(i);
    admitted.publicBindings.push_back(
        json::Array{policy.validator, std::to_string(i), logical->spelling(),
                    wireCodec(*logical).str()});
  }
  {
    unsigned keys = 0;
    bool needsKey = false;
    auto inspect = [&](Type type) {
      auto logical = protocol::encodeBoundType(type, false);
      if (!logical) {
        consumeError(logical.takeError());
        return;
      }
      needsKey |= protocol::nativeSetupType(*logical);
    };
    for (auto [i, type] : llvm::enumerate(signature.getInputs())) {
      inspect(type);
      auto logical = protocol::encodeBoundType(type, false);
      if (!logical) {
        consumeError(logical.takeError());
        continue;
      }
      if (logical->kind == "verifier_key" &&
          !owns(cast<ArrayAttr>(source.getInputRoles()[i]), policy.validator))
        return error("native-proof-verifier-key-port");
    }
    source.walk([&](Operation *op) {
      for (auto type : llvm::concat<const Type>(op->getOperandTypes(),
                                                op->getResultTypes()))
        inspect(type);
    });
    for (auto i : required) {
      auto logical = protocol::encodeBoundType(signature.getInput(i), false);
      if (!logical)
        return logical.takeError();
      keys += logical->kind == "verifier_key";
    }
    if (keys > 64 || (needsKey && !keys))
      return error("native-proof-setup-coverage");
  }
  if (required != policy.publicInputs)
    return error("native-proof-public-bindings");
  if (policy.service &&
      (*policy.service >= signature.getNumInputs() ||
       !isa<pir::ServiceReferenceType>(signature.getInput(*policy.service)) ||
       !owns(cast<ArrayAttr>(source.getInputRoles()[*policy.service]),
             policy.validator)))
    return error("native-proof-verifier-service");
  llvm::StringSet<> consumedOrigins;
  auto consume = [&](StringRef site,
                     StringRef kind) -> Expected<const Origin *> {
    auto found = sourceOrigins.find(site);
    if (found == sourceOrigins.end() || found->second.event.empty() ||
        found->second.event.front() != kind ||
        !consumedOrigins.insert(site).second)
      return error("native-proof-origin");
    return &found->second;
  };
  auto append = [&](Operation *op, bool query, Type payload,
                    json::Array &sequence,
                    std::optional<uint64_t> bound = {}) -> Error {
    auto site = op->getAttrOfType<StringAttr>("site").str();
    auto found = consume(site, query ? "query" : "message");
    if (!found)
      return found.takeError();
    const auto &origin = **found;
    if (query) {
      auto action = cast<pir::QueryOp>(op);
      if (origin.event.size() != 7 || origin.event[6] != action.getOwner())
        return error("native-proof-origin");
    } else {
      auto action = cast<pir::ExchangeOp>(op);
      if (origin.event.size() != 6 || origin.event[4] != action.getSender() ||
          origin.event[5] != action.getReceiver())
        return error("native-proof-origin");
    }
    auto encoded = protocol::encodeNativeOriginTemplate(
        policy.entry, origin.steps, origin.event);
    if (!encoded)
      return encoded.takeError();
    auto type = wire(payload);
    if (!type)
      return type.takeError();
    admitted.events.push_back(
        {site, *encoded, payload, query,
         static_cast<unsigned>(count_if(
             origin.steps, [](const auto &s) { return s[0] == "repeat"; })),
         bound});
    if (bound)
      sequence.push_back(
          json::Array{"index", *encoded, std::to_string(*bound)});
    else
      sequence.push_back(json::Array{query ? "query" : "message", *encoded});
    if (!query) {
      admitted.messages.push_back(
          json::Array{*encoded, type->spelling(), wireCodec(*type).str()});
      if (cast<pir::ExchangeOp>(op).getSender() == policy.producer)
        admitted.wireSites.push_back(json::Array{*encoded, site});
    }
    return Error::success();
  };
  SymbolTable symbols(source->getParentOp());
  unsigned draw = 0, actions = 0;
  auto block = [&](auto &&self, Block &body, json::Array &sequence,
                   unsigned depth) -> Error {
    if (depth > 64)
      return error("native-proof-origin-limit");
    pir::QueryOp pending;
    for (auto &op : body) {
      if (op.hasAttr("site") && ++actions > maxActions)
        return error("native-proof-action-limit");
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        if (pending)
          return error("native-proof-loop-prefix");
        auto found = consume(repeat.getSite(), "repeat");
        if (!found)
          return found.takeError();
        json::Array children;
        if (auto e = self(self, repeat.getBody().front(), children, depth + 1))
          return e;
        // Both roles must execute every loop containing transcript events. Pure
        // local loops may remain owner-local and have an empty event subtree.
        if (!children.empty() && repeat.getRoles().size() != 2)
          return error("native-proof-loop-participants");
        for (auto &child : children)
          sequence.push_back(std::move(child));
        continue;
      }
      if (!admittedOperation(op, false) && !isa<pir::ProtocolYieldOp>(op))
        return error("native-proof-operation");
      if (auto statement = dyn_cast<pir::StatementOp>(op)) {
        auto declaration =
            symbols.lookup<relation::DeclareOp>(statement.getRelation());
        if (!declaration ||
            statement.getInputs().size() != declaration.getPurposes().size())
          return error("native-proof-statement");
        // This two-role deployment selects one validator observation. A
        // retained relation must designate that same original result.
        if (statement.getAcceptance() != policy.acceptance)
          return error("native-proof-statement-acceptance");
        for (auto [input, purpose] :
             zip(statement.getInputs(), declaration.getPurposes())) {
          // Formation binds statements to entry arguments. Availability at the
          // validator matters even when the statement selects another role.
          auto port = dyn_cast<BlockArgument>(input);
          if (!port || port.getOwner() != &source.getBody().front())
            return error("native-proof-statement");
          auto owners =
              cast<ArrayAttr>(source.getInputRoles()[port.getArgNumber()]);
          if (cast<StringAttr>(purpose).getValue() == "witness" &&
              owns(owners, policy.validator))
            return error("native-proof-private-verifier-witness");
          if (cast<StringAttr>(purpose).getValue() != "witness" &&
              !owns(owners, policy.validator))
            return error("native-proof-statement-public-input");
        }
      }
      if (isa<pir::FinishIfOp>(op) && pending)
        return error("native-proof-prefix");
      if (auto query = dyn_cast<pir::QueryOp>(op)) {
        if (pending)
          return error("native-proof-prefix");
        if (query.getOwner() == policy.producer) {
          if (policy.service &&
              sourcePort(query.getReference()) ==
                  source.getBody().front().getArgument(*policy.service))
            return error("native-proof-draw-selection");
          auto origin = consume(query.getSite(), "query");
          if (!origin)
            return origin.takeError();
          continue;
        }
        // A selected query is a field draw or a UniformIndex query. Both
        // become transitions of the same transcript at this occurrence.
        bool index = query.getMethod() == "index";
        if (!policy.service ||
            sourcePort(query.getReference()) !=
                source.getBody().front().getArgument(*policy.service) ||
            query.getNumOperands() != (index ? 2u : 1u) ||
            query.getNumResults() != 1 ||
            query.getResult(0).getType() !=
                (index ? Type(IntegerType::get(source.getContext(), 64,
                                               IntegerType::Unsigned))
                       : Type(algebra::FieldType::get(source.getContext(),
                                                      challengeField))) ||
            (!index && query.getMethod() != "draw") || draw >= 64 ||
            (selection == DrawSelection::Explicit &&
             (draw >= policy.draws.size() ||
              query.getSite() != policy.draws[draw].first)))
          return error("native-proof-draw-selection");
        // Formation already fixes an index domain to a power-of-two constant;
        // its value becomes part of the transcript event. The suite's
        // IndexTranscript fact is checked when the transition is bound.
        std::optional<uint64_t> bound;
        if (index) {
          auto constant =
              query.getInputs().front().getDefiningOp<data::IndexOp>();
          if (!constant ||
              !(bound = protocol::parseUniformIndexBound(constant.getValue())))
            return error("native-proof-draw-selection");
        }
        if (auto e = append(query, true, query.getResult(0).getType(), sequence,
                            bound))
          return e;
        pending = query;
      }
      if (auto message = dyn_cast<pir::ExchangeOp>(op)) {
        if (message.getSender() == policy.producer) {
          if (message.getReceiver() != policy.validator)
            return error("native-proof-reverse-message");
          if (pending)
            return error("native-proof-prefix");
        } else {
          if (!pending || message.getInput() != pending.getResult(0) ||
              (selection == DrawSelection::Explicit &&
               message.getSite() != policy.draws[draw].second) ||
              message.getReceiver() != policy.producer)
            return error("native-proof-reverse-message");
          admitted.draws.emplace_back(pending.getSite().str(),
                                      message.getSite().str());
          pending = {};
          ++draw;
        }
        if (auto e =
                append(message, false, message.getInput().getType(), sequence))
          return e;
      }
    }
    if (pending)
      return error("native-proof-draw-selection");
    return Error::success();
  };
  if (auto e = block(block, source.getBody().front(), admitted.sequence, 0))
    return std::move(e);
  if (selection == DrawSelection::Explicit && draw != policy.draws.size())
    return error("native-proof-draw-selection");
  if (consumedOrigins.size() != sourceOrigins.size())
    return error("native-proof-origin-coverage");
  if (policy.format == protocol::ProofFormat::RawBytes) {
    if (!policy.suite.empty() || admitted.events.size() != 1 ||
        admitted.events.front().query || admitted.events.front().depth)
      return error("native-proof-format");
    auto type =
        protocol::encodeBoundType(admitted.events.front().payload, false);
    if (!type)
      return type.takeError();
    if (type->kind != "bytes")
      return error("native-proof-format");
  }
  return admitted;
}
Error admitConstruction(pir::MathematicalOp source,
                        const protocol::ConstructionPlan &plan,
                        ArrayRef<Event> events) {
  StringMap<unsigned> indices;
  for (auto [i, event] : enumerate(events))
    indices[event.site] = i;
  StringMap<Operation *> operations;
  source.walk([&](Operation *op) {
    if (auto site = op->getAttrOfType<StringAttr>("site"))
      operations[site.getValue()] = op;
  });
  SymbolTable symbols(source->getParentOp());
  llvm::StringSet<> covered;
  for (const auto &rule : plan.rules) {
    if (rule.kind == protocol::ConstructionRule::Kind::Start)
      continue;
    std::optional<unsigned> previous;
    Operation *previousOperation = nullptr;
    for (auto [leaf, site] : enumerate(rule.sites)) {
      auto found = indices.find(site);
      if (found == indices.end() || !covered.insert(site).second)
        return error("native-proof-construction-coverage");
      auto &event = events[found->second];
      bool query = rule.kind == protocol::ConstructionRule::Kind::Query;
      if (event.query != query || event.payload != rule.payload[leaf])
        return error("native-proof-construction-signature");
      auto *operation = operations.lookup(site);
      // Projection may restrict each tuple leaf to its sender separately.
      // Those total calculations do not split one logical message; a guard,
      // local action, query or another exchange does.
      auto *next =
          previousOperation ? previousOperation->getNextNode() : nullptr;
      while (next && next != operation &&
             (mathematical::isTotal(next) || isa<pir::RestrictRolesOp>(next)))
        next = next->getNextNode();
      if (!operation ||
          (previous && (*previous + 1 != found->second || next != operation)))
        return error("native-proof-construction-message-group");
      if (query) {
        auto handler = symbols.lookup<local::FuncOp>(rule.handler.getValue());
        if (!handler ||
            handler.getFunctionType().getNumInputs() !=
                plan.state.size() + unsigned(event.bound.has_value()))
          return error("native-proof-construction-request");
      }
      if (previous) {
        auto before = dyn_cast<pir::ExchangeOp>(previousOperation);
        auto after = dyn_cast<pir::ExchangeOp>(operation);
        if (!before || !after || before.getSender() != after.getSender() ||
            before.getReceiver() != after.getReceiver())
          return error("native-proof-construction-message-group");
      }
      previous = found->second;
      previousOperation = operation;
    }
  }
  if (!plan.nativeBase && covered.size() != events.size())
    return error("native-proof-construction-coverage");
  return Error::success();
}
} // namespace
json::Value encodeNativeProofPolicy(const NativeProofPolicy &p) {
  json::Array inputs, draws;
  for (auto port : p.publicInputs)
    inputs.push_back(std::to_string(port));
  for (const auto &[query, delivery] : p.draws)
    draws.push_back(json::Array{query, delivery});
  return json::Array{"zkc.native-proof-policy/0",
                     p.entry,
                     p.producer,
                     p.validator,
                     std::to_string(p.acceptance),
                     p.suite,
                     p.service ? std::to_string(*p.service) : "",
                     std::move(inputs),
                     std::move(draws),
                     protocol::proofFormatName(p.format),
                     p.construction};
}
namespace {
Expected<NativeProofPolicy> readProofPolicy(StringRef text, bool selectDraws) {
  if (text.size() > 1024 * 1024 || !mlirNestingWithinLimit(text))
    return error("native-proof-policy-limit");
  auto parsed = parseJson(text);
  if (!parsed)
    return parsed.takeError();
  auto *a = parsed->getAsArray();
  if (!a || a->size() != 11 ||
      (*a)[0].getAsString() != "zkc.native-proof-policy/0")
    return error("native-proof-policy");
  NativeProofPolicy p;
  auto formatName = (*a)[9].getAsString();
  auto format =
      formatName ? protocol::parseProofFormat(*formatName) : std::nullopt;
  if (!format)
    return error("native-proof-format");
  p.format = *format;
  for (auto [i, target] : {std::pair{1u, &p.entry},
                           {2u, &p.producer},
                           {3u, &p.validator},
                           {5u, &p.suite},
                           {10u, &p.construction}}) {
    auto s = (*a)[i].getAsString();
    bool optional = i == 5 || (i == 10 && s && s->empty());
    if (!s || (!optional && !name(*s)))
      return error("native-proof-policy");
    if (!optional && (s->size() > 128 || !all_of(*s, [](unsigned char c) {
                        return llvm::isAlnum(c) || c == '_' || c == '.' ||
                               c == '-';
                      })))
      return error("native-proof-policy");
    *target = s->str();
  }
  auto acceptance = number((*a)[4]);
  auto service = (*a)[6].getAsString();
  auto *inputs = (*a)[7].getAsArray(), *draws = (*a)[8].getAsArray();
  if (!acceptance || !service || !inputs || inputs->size() > maxPorts ||
      !draws || draws->size() > 64 || (selectDraws && !draws->empty()) ||
      p.producer == p.validator)
    return error("native-proof-policy");
  p.acceptance = *acceptance;
  if (!service->empty()) {
    p.service = number((*a)[6]);
    if (!p.service)
      return error("native-proof-policy");
  }
  if (p.format == protocol::ProofFormat::RawBytes &&
      (!p.suite.empty() || !p.construction.empty()))
    return error("native-proof-format");
  if (!p.construction.empty()
          ? !p.service || (!p.suite.empty() &&
                           protocol::nativeChallengeField(p.suite).empty())
      : p.suite.empty() ? p.service.has_value() || !draws->empty()
                        : protocol::nativeChallengeField(p.suite).empty() ||
                              !p.service || (!selectDraws && draws->empty()))
    return error("native-proof-policy");
  for (const auto &input : *inputs) {
    auto port = number(input);
    if (!port || (!p.publicInputs.empty() && p.publicInputs.back() >= *port))
      return error("native-proof-policy");
    p.publicInputs.push_back(*port);
  }
  std::set<std::string> sites;
  for (const auto &item : *draws) {
    auto *d = item.getAsArray();
    if (!d || d->size() != 2)
      return error("native-proof-policy");
    auto query = (*d)[0].getAsString(), delivery = (*d)[1].getAsString();
    if (!query || !delivery || !name(*query) || !name(*delivery) ||
        !sites.insert(query->str()).second ||
        !sites.insert(delivery->str()).second)
      return error("native-proof-policy");
    p.draws.emplace_back(query->str(), delivery->str());
  }
  return p;
}
} // namespace
Expected<NativeProofPolicy> parseNativeProofPolicy(StringRef text) {
  return readProofPolicy(text, false);
}
namespace {
class Emitter {
  pir::ProtocolModuleOp module;
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan *plan;
  StringMap<const protocol::ConstructionRule *> rules;
  SmallVector<Attribute> invokedHelpers;
  OpBuilder builder;
  SymbolTable symbols;
  unsigned freshIndex = 0;
  std::map<std::string, FlatSymbolRefAttr> helpers;
  llvm::StringSet<> occupied;
  llvm::DenseMap<std::pair<StringAttr, ArrayAttr>, FlatSymbolRefAttr> bindings;
  std::string fresh() {
    std::string value;
    do {
      value = "_transcript_" + std::to_string(freshIndex++);
    } while (symbols.lookup(value) || !occupied.insert(value).second);
    return value;
  }
  FlatSymbolRefAttr binding(StringRef contract, ArrayRef<Attribute> arguments) {
    auto parameters = builder.getArrayAttr(arguments);
    auto key = std::make_pair(builder.getStringAttr(contract), parameters);
    auto found = bindings.find(key);
    if (found != bindings.end())
      return found->second;
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&module.getBody().front());
    auto operation = local::OperationBindingOp::create(
        builder, module.getLoc(), fresh(), contract, parameters, "");
    symbols.insert(operation);
    auto ref = FlatSymbolRefAttr::get(operation);
    bindings.try_emplace(key, ref);
    return ref;
  }
  Operation *kernel(StringRef contract, FlatSymbolRefAttr binding,
                    ValueRange inputs, TypeRange outputs, StringRef site,
                    ArrayRef<Attribute> parameters = {}) {
    OperationState state(module.getLoc(),
                         protocol::boundOperationName(contract));
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttribute("binding", binding);
    state.addAttribute("site", builder.getStringAttr(site));
    state.addAttribute("parameters", builder.getArrayAttr(parameters));
    return builder.create(state);
  }
  Expected<FlatSymbolRefAttr> helper(const Event &event, TypeRange stateTypes) {
    if (auto *rule = rules.lookup(event.site)) {
      auto source = symbols.lookup<local::FuncOp>(rule->handler.getValue());
      if (!source || !source.getBody().hasOneBlock())
        return error("native-proof-construction-handler");
      SmallVector<Type> inputs(stateTypes), outputs;
      if (event.query)
        outputs.push_back(event.payload);
      else
        append_range(inputs, rule->payload);
      unsigned dataInputs = inputs.size();
      inputs.append(event.depth, builder.getIntegerType(64, false));
      append_range(outputs, stateTypes);
      builder.setInsertionPointToEnd(&module.getBody().front());
      auto function =
          local::FuncOp::create(builder, module.getLoc(), fresh(),
                                builder.getFunctionType(inputs, outputs));
      symbols.insert(function);
      function->setAttr(
          "logical_origin",
          builder.getArrayAttr({builder.getStringAttr(function.getSymName()),
                                builder.getArrayAttr({})}));
      auto *body = function.addEntryBlock();
      builder.setInsertionPointToEnd(body);
      llvm::StringSet<> sites;
      source.walk([&](Operation *op) {
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          sites.insert(site.getValue());
      });
      auto site = [&](StringRef prefix) {
        std::string selected = prefix.str();
        for (unsigned i = 0; !sites.insert(selected).second; ++i)
          selected = (prefix + "_" + Twine(i)).str();
        return selected;
      };
      SmallVector<Value> arguments(body->getArguments().take_front(dataInputs));
      if (event.bound)
        arguments.push_back(
            kernel("index.constant", binding("index.constant", {}), {},
                   {event.payload}, site("bound"),
                   {builder.getStringAttr(std::to_string(*event.bound))})
                ->getResult(0));
      IRMapping mapping;
      mapping.map(source.getBody().front().getArguments(), arguments);
      for (auto &op : source.getBody().front()) {
        if (auto returned = dyn_cast<local::ReturnOp>(op)) {
          SmallVector<Value> values;
          if (event.query)
            values.push_back(mapping.lookup(returned.getInputs().back()));
          for (Value value : returned.getInputs().take_front(stateTypes.size()))
            values.push_back(mapping.lookup(value));
          if (event.bound) {
            auto valid = kernel("index.less", binding("index.less", {}),
                                {values.front(), arguments.back()},
                                {builder.getI1Type()}, site("range"));
            kernel("control.require", binding("control.require", {}),
                   {valid->getResult(0)}, {}, site("require_range"));
          }
          local::ReturnOp::create(builder, module.getLoc(), values);
        } else {
          builder.clone(op, mapping);
        }
      }
      return FlatSymbolRefAttr::get(function);
    }
    auto type = wire(event.payload);
    if (!type)
      return type.takeError();
    std::string contract =
        !event.query  ? "transcript.native.indexed.observe.data"
        : event.bound ? "transcript.native.indexed.index"
                      : "transcript.native.indexed.challenge";
    SmallVector<Attribute> args{builder.getStringAttr(policy.suite)};
    if (!event.query)
      args.push_back(builder.getStringAttr(type->spelling()));
    auto selected = binding(contract, args);
    SmallVector<Type> inputs(stateTypes), outputs;
    if (event.query)
      outputs.push_back(event.payload);
    else
      inputs.push_back(event.payload);
    auto dataInputs = inputs.size();
    inputs.append(event.depth, builder.getIntegerType(64, false));
    append_range(outputs, stateTypes);
    builder.setInsertionPointToEnd(&module.getBody().front());
    auto function =
        local::FuncOp::create(builder, module.getLoc(), fresh(),
                              builder.getFunctionType(inputs, outputs));
    symbols.insert(function);
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr(function.getSymName()),
                              builder.getArrayAttr({})}));
    auto *body = function.addEntryBlock();
    builder.setInsertionPointToEnd(body);
    SmallVector<Value> operands(body->getArguments().take_front(dataInputs));
    if (event.bound)
      operands.push_back(
          kernel("index.constant", binding("index.constant", {}), {},
                 {event.payload}, "bound",
                 {builder.getStringAttr(std::to_string(*event.bound))})
              ->getResult(0));
    {
      auto indices = RankedTensorType::get({ShapedType::kDynamic},
                                           builder.getIntegerType(64, false));
      auto empty = binding("indices.empty", {});
      Value coordinates =
          kernel("indices.empty", empty, {}, {indices}, "coordinates")
              ->getResult(0);

      for (auto [i, argument] :
           enumerate(body->getArguments().drop_front(dataInputs)))
        coordinates = kernel("indices.append", binding("indices.append", {}),
                             {coordinates, argument}, {indices},
                             "coordinate_" + std::to_string(i))
                          ->getResult(0);
      operands.push_back(coordinates);
    }
    auto *operation =
        kernel(contract, selected, operands, outputs, "transition",
               {builder.getStringAttr(event.origin)});
    local::ReturnOp::create(builder, module.getLoc(), operation->getResults());
    return FlatSymbolRefAttr::get(function);
  }

public:
  Emitter(pir::ProtocolModuleOp module, const NativeProofPolicy &policy,
          const protocol::ConstructionPlan *plan)
      : module(module), policy(policy), plan(plan),
        builder(module.getContext()), symbols(module) {
    if (plan)
      for (const auto &rule : plan->rules)
        for (const auto &site : rule.sites)
          rules[site] = &rule;
    module.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        occupied.insert(site.getValue());
    });
  }
  Error run(const Admitted &admitted, json::Array &exportedPlan) {
    auto records = module.getBody().front().getOps<pir::ProjectionOp>();
    if (!hasSingleElement(records))
      return error("native-proof-entry");
    auto record = *records.begin();
    if (record.getInterfaces().size() != 1)
      return error("native-proof-entry");
    auto original = cast<DictionaryAttr>(record.getInterfaces()[0]);
    auto stateType = local::CapabilityType::get(module.getContext(),
                                                "transcript:" + policy.suite);
    SmallVector<Type> stateTypes;
    if (plan)
      stateTypes = plan->state;
    else
      stateTypes.push_back(stateType);
    bool hostRoot =
        !plan || plan->root == protocol::ConstructionPlan::Root::Host;
    if (plan) {
      if (plan->initializer &&
          !symbols.lookup<local::FuncOp>(plan->initializer.getValue()))
        return error("native-proof-construction-handler");
      for (const auto &rule : plan->rules)
        if (!symbols.lookup<local::FuncOp>(rule.handler.getValue()))
          return error("native-proof-construction-handler");
    }
    // Source admission bounds the original program. Charge repeated handler
    // copies separately before generating adapters or threading participants.
    uint64_t remaining = 1000000;
    llvm::DenseMap<Operation *, uint64_t> bodyCosts;
    for (const auto &event : admitted.events) {
      const auto *rule = rules.lookup(event.site);
      uint64_t cost = 16 * (1 + stateTypes.size() + event.depth +
                            (rule ? rule->payload.size() : 1));
      if (rule && rule->sites.back() == event.site) {
        auto function = symbols.lookup<local::FuncOp>(rule->handler.getValue());
        if (!function)
          return error("native-proof-construction-handler");
        auto found = bodyCosts.find(function);
        if (found == bodyCosts.end()) {
          uint64_t bodyCost = 0;
          function.walk([&](Operation *op) {
            bodyCost += 1 + op->getNumOperands() + op->getNumResults() +
                        op->getAttrs().size();
            for (auto &region : op->getRegions())
              for (auto &block : region)
                bodyCost += block.getNumArguments();
          });
          found = bodyCosts.try_emplace(function, bodyCost).first;
        }
        cost += found->second;
      }
      if (cost > remaining)
        return error("native-proof-construction-limit");
      remaining -= cost;
    }
    json::Array adapters;
    std::map<std::string, const Event *> events;
    for (const auto &event : admitted.events) {
      events.emplace(event.site, &event);
      auto *rule = rules.lookup(event.site);
      if (rule && rule->sites.back() != event.site)
        continue;
      auto result = helper(event, stateTypes);
      if (!result)
        return result.takeError();
      helpers.emplace(event.site, *result);
      invokedHelpers.push_back(*result);
      if (plan) {
        json::Array origins;
        if (rule) {
          for (const auto &site : rule->sites) {
            auto selected = find_if(admitted.events, [&](const Event &e) {
              return e.site == site;
            });
            if (selected == admitted.events.end())
              return error("native-proof-construction-handler");
            origins.push_back(selected->origin);
          }
        } else {
          origins.push_back(event.origin);
        }
        adapters.push_back(json::Array{result->getValue().str(),
                                       rule ? "local" : "native",
                                       std::move(origins)});
      }
    }
    if (plan) {
      json::Array slots, startInputs;
      std::string start;
      for (Type type : stateTypes) {
        auto logical = protocol::encodeBoundType(type, false);
        if (!logical)
          return logical.takeError();
        slots.push_back(logical->spelling());
      }
      for (const auto &rule : plan->rules)
        if (rule.kind == protocol::ConstructionRule::Kind::Start) {
          start = rule.handler.getValue().str();
          for (unsigned input : rule.inputs)
            startInputs.push_back(std::to_string(input));
        }
      exportedPlan = json::Array{
          "zkc.construction-plan/0",
          plan->symbol.getValue().str(),
          hostRoot ? "host" : "local",
          std::move(slots),
          plan->initializer ? plan->initializer.getValue().str() : "",
          json::Array{start, std::move(startInputs)},
          std::move(adapters)};
    }
    std::map<std::string, std::string> deliveries;
    std::set<std::string> queries;
    for (auto &[query, delivery] : policy.draws) {
      deliveries.emplace(delivery, query);
      queries.insert(query);
    }
    std::map<std::string, SmallVector<Attribute>> addedActions;
    for (auto participant :
         module.getBody().front().getOps<pir::ParticipantOp>()) {
      auto &body = participant.getBody().front();
      auto type = participant.getFunctionType();
      SmallVector<Type> inputs(type.getInputs()), outputs(type.getResults());
      if (hostRoot)
        append_range(inputs, stateTypes);
      append_range(outputs, stateTypes);
      participant.setFunctionType(builder.getFunctionType(inputs, outputs));
      SmallVector<Value> state;
      if (hostRoot)
        for (Type slot : stateTypes)
          state.push_back(body.addArgument(slot, participant.getLoc()));
      if (participant.getRole() == policy.validator)
        participant->removeAttr("service_ports");
      SmallVector<StringRef> reached;
      SmallVector<Value> coordinates;
      auto invoke = [&](FlatSymbolRefAttr reference, ValueRange operands,
                        StringRef anchor) -> local::CallOp {
        auto function = symbols.lookup<local::FuncOp>(reference.getValue());
        auto invocation = local::CallOp::create(
            builder, participant.getLoc(), function.getResultTypes(), operands,
            reference, builder.getStringAttr(fresh()));
        state.clear();
        append_range(state,
                     invocation.getResults().take_back(stateTypes.size()));
        auto target = builder.getDictionaryAttr(
            {builder.getNamedAttr("participant",
                                  FlatSymbolRefAttr::get(participant)),
             builder.getNamedAttr("operation",
                                  builder.getStringAttr("local.call"))});
        addedActions[anchor.str()].push_back(builder.getDictionaryAttr(
            {builder.getNamedAttr("site", invocation.getSiteAttr()),
             builder.getNamedAttr("kind",
                                  builder.getStringAttr("protocol.local_call")),
             builder.getNamedAttr("callee", reference),
             builder.getNamedAttr("targets", builder.getArrayAttr({target}))}));
        return invocation;
      };
      auto call = [&](const Event &event, StringRef anchor,
                      ValueRange payload = {}) -> local::CallOp {
        reached.push_back(event.origin);
        SmallVector<Value> operands(state);
        append_range(operands, payload);
        append_range(operands, coordinates);
        return invoke(helpers.at(event.site), operands, anchor);
      };
      if (plan) {
        builder.setInsertionPointToStart(&body);
        if (!hostRoot) {
          invoke(plan->initializer, {}, "");
          if (!is_contained(invokedHelpers, plan->initializer))
            invokedHelpers.push_back(plan->initializer);
        }
        for (const auto &rule : plan->rules) {
          if (rule.kind != protocol::ConstructionRule::Kind::Start)
            continue;
          SmallVector<Value> operands(state);
          auto participants = original.getAs<ArrayAttr>("participants");
          for (auto item : participants) {
            auto ports = cast<DictionaryAttr>(item);
            if (ports.getAs<FlatSymbolRefAttr>("participant") !=
                FlatSymbolRefAttr::get(participant))
              continue;
            auto originalInputs = ports.getAs<ArrayAttr>("inputs");
            for (unsigned input : rule.inputs) {
              auto found =
                  llvm::find(originalInputs, builder.getI64IntegerAttr(input));
              if (found == originalInputs.end())
                return error("native-proof-construction-start");
              operands.push_back(
                  body.getArgument(found - originalInputs.begin()));
            }
          }
          invoke(rule.handler, operands, "");
          if (!is_contained(invokedHelpers, rule.handler))
            invokedHelpers.push_back(rule.handler);
        }
      }
      SmallVector<Value> payloadGroup;
      auto observe = [&](const Event &event, StringRef anchor, Value payload) {
        payloadGroup.push_back(payload);
        auto *rule = rules.lookup(event.site);
        if (rule && rule->sites.back() != event.site) {
          reached.push_back(event.origin);
          return;
        }
        call(event, anchor, payloadGroup);
        payloadGroup.clear();
      };
      auto thread = [&](auto &&self, Block &block) -> Error {
        for (auto &op : make_early_inc_range(block)) {
          if (auto loop = dyn_cast<pir::ProtocolLoopOp>(op)) {
            bool observed = false;
            loop.walk([&](Operation *nested) {
              // Completion returns the current constructed state even if this
              // isolated loop has no transcript event of its own.
              observed |= isa<pir::FinishIfOp>(nested);
              if (auto site = nested->getAttrOfType<StringAttr>("site"))
                observed |= events.count(site.str()) != 0;
            });
            if (!observed)
              continue;
            if (!loop.getMaximum())
              return error("native-proof-loop-profile");
            unsigned carried = loop.getCarried();
            SmallVector<Value> operands(loop.getInputs().begin(),
                                        loop.getInputs().end());
            operands.insert(operands.begin() + 1 + carried, state.begin(),
                            state.end());
            SmallVector<Type> results(loop.getResultTypes());
            append_range(results, stateTypes);
            // Fresh captures keep the source operands untouched. Normal later
            // simplification may deduplicate them; admission follows capture
            // SSA.
            append_range(operands, coordinates);
            builder.setInsertionPoint(loop);
            auto replacement = pir::ProtocolLoopOp::create(
                builder, loop.getLoc(), results, operands, loop.getSiteAttr(),
                builder.getI64IntegerAttr(carried + stateTypes.size()),
                loop.getCountAttr(), loop.getParameterAttr(),
                loop.getMaximumAttr());
            replacement.getBody().takeBody(loop.getBody());
            auto &child = replacement.getBody().front();
            state.clear();
            for (auto [index, slot] : enumerate(stateTypes))
              state.push_back(child.insertArgument(1 + carried + index, slot,
                                                   loop.getLoc()));
            SmallVector<Value> outer = coordinates;
            coordinates.clear();
            for (Value coordinate : outer)
              coordinates.push_back(
                  child.addArgument(coordinate.getType(), loop.getLoc()));
            coordinates.push_back(child.getArgument(0));
            if (auto e = self(self, child))
              return e;
            coordinates = std::move(outer);
            for (auto [oldValue, newValue] :
                 zip(loop.getResults(), replacement.getResults()))
              oldValue.replaceAllUsesWith(newValue);
            state.clear();
            append_range(state,
                         replacement.getResults().take_back(stateTypes.size()));
            loop.erase();
            continue;
          }
          if (auto yielded = dyn_cast<pir::ProtocolYieldOp>(op)) {
            yielded->insertOperands(yielded.getNumOperands(), state);
            continue;
          }
          if (auto completion = dyn_cast<pir::FinishIfOp>(op)) {
            SmallVector<Value> inputs(completion.getValues());
            append_range(inputs, state);
            SmallVector<Type> results(completion.getResultTypes());
            append_range(results, stateTypes);
            builder.setInsertionPoint(completion);
            auto replacement = pir::FinishIfOp::create(
                builder, completion.getLoc(), results,
                completion.getCondition(), inputs, completion.getSite(),
                completion.getOwner());
            for (auto [oldValue, newValue] :
                 zip(completion.getResults(), replacement.getResults()))
              oldValue.replaceAllUsesWith(newValue);
            state.clear();
            append_range(state,
                         replacement.getResults().take_back(stateTypes.size()));
            completion.erase();
            continue;
          }
          if (auto finish = dyn_cast<pir::FinishOp>(op)) {
            finish->insertOperands(finish.getNumOperands(), state);
            continue;
          }
          auto site = op.getAttrOfType<StringAttr>("site");
          if (!site)
            continue;
          auto found = events.find(site.str());
          if (found == events.end())
            continue;
          auto &event = *found->second;
          if (isa<pir::ParticipantQueryOp>(op)) {
            if (!event.query || participant.getRole() != policy.validator)
              return error("native-proof-projected-event");
            builder.setInsertionPoint(&op);
            auto replacement = call(event, site.getValue());
            op.getResult(0).replaceAllUsesWith(replacement.getResult(0));
            op.erase();
          } else if (auto receive = dyn_cast<pir::AwaitOp>(op)) {
            if (event.query)
              return error("native-proof-projected-event");
            auto delivery = deliveries.find(site.str());
            if (delivery != deliveries.end()) {
              if (participant.getRole() != policy.producer)
                return error("native-proof-projected-event");
              builder.setInsertionPoint(&op);
              auto challenge =
                  call(*events.at(delivery->second), site.getValue());
              receive.getOutput().replaceAllUsesWith(challenge.getResult(0));
              observe(event, site.getValue(), challenge.getResult(0));
              op.erase();
            } else {
              if (participant.getRole() != policy.validator)
                return error("native-proof-projected-event");
              builder.setInsertionPointAfter(&op);
              observe(event, site.getValue(), receive.getOutput());
            }
          } else if (auto send = dyn_cast<pir::EmitOp>(op)) {
            if (event.query || (deliveries.count(site.str())
                                    ? participant.getRole() != policy.validator
                                    : participant.getRole() != policy.producer))
              return error("native-proof-projected-event");
            builder.setInsertionPointAfter(&op);
            observe(event, site.getValue(), send.getInput());
            if (deliveries.count(site.str()))
              op.erase();
          } else
            return error("native-proof-projected-event");
        }
        return Error::success();
      };
      if (auto e = thread(thread, body))
        return e;
      if (reached.size() != admitted.events.size() ||
          !all_of(zip(reached, admitted.events), [](auto pair) {
            return std::get<0>(pair) == std::get<1>(pair).origin;
          }))
        return error("native-proof-event-chain");
    }
    auto rewrite = [&](auto &&self, ArrayAttr source) -> ArrayAttr {
      SmallVector<Attribute> actions;
      for (auto item : source) {
        auto action = cast<DictionaryAttr>(item);
        auto site = action.getAs<StringAttr>("site").str();
        if (auto body = action.getAs<ArrayAttr>("body")) {
          NamedAttrList edited(action);
          edited.set("body", self(self, body));
          action = edited.getDictionary(module.getContext());
        }
        if (!queries.count(site) && !deliveries.count(site))
          actions.push_back(action);
        append_range(actions, addedActions[site]);
      }
      return builder.getArrayAttr(actions);
    };
    SmallVector<Attribute> actionList(addedActions[""]);
    append_range(actionList,
                 rewrite(rewrite, original.getAs<ArrayAttr>("actions")));
    auto actions = builder.getArrayAttr(actionList);
    SmallVector<Attribute> states;
    for (Type type : stateTypes)
      states.push_back(TypeAttr::get(type));
    auto construction = builder.getDictionaryAttr(
        {builder.getNamedAttr(
             "format", builder.getStringAttr("zkc.native-construction/0")),
         builder.getNamedAttr("state", builder.getArrayAttr(states)),
         builder.getNamedAttr(
             "root", builder.getStringAttr(hostRoot ? "host" : "local")),
         builder.getNamedAttr("plan",
                              builder.getStringAttr(policy.construction)),
         builder.getNamedAttr("helpers", builder.getArrayAttr(invokedHelpers)),
         builder.getNamedAttr("removed_services",
                              builder.getArrayAttr({builder.getI64IntegerAttr(
                                  *policy.service)})),
         builder.getNamedAttr("actions", actions)});
    NamedAttrList updated(original);
    updated.append("construction", construction);
    record.setInterfacesAttr(
        builder.getArrayAttr({updated.getDictionary(module.getContext())}));
    return Error::success();
  }
};
} // namespace
namespace {
struct PreparedProof {
  OwningOpRef<ModuleOp> module;
  StringMap<Origin> origins;
  std::optional<protocol::ConstructionPlan> construction;
};
Expected<PreparedProof> prepareProof(ModuleOp source,
                                     const NativeProofPolicy &policy,
                                     bool fuseVectorReductions) {
  if (!source || failed(verify(source)))
    return error("native-proof-source");
  auto original = unit(source);
  if (!original || original.getProfile() != pir::Profile::Protocol)
    return error("native-proof-source");
  std::optional<protocol::ConstructionPlan> construction;
  SymbolTableCollection constructionSymbols;
  for (auto record : original.getBody().front().getOps<pir::ConstructionOp>()) {
    if (construction || record.getSymName() != policy.construction)
      return error("native-proof-construction-selection");
    auto checked = protocol::readConstructionPlan(record, constructionSymbols);
    if (!checked)
      return checked.takeError();
    if (checked->target.getValue() != policy.entry ||
        checked->suite != policy.suite || checked->service != policy.service)
      return error("native-proof-construction-selection");
    construction = std::move(*checked);
  }
  if (construction.has_value() != !policy.construction.empty())
    return error("native-proof-construction-selection");
  SymbolTable originalSymbols(original);
  auto entry = originalSymbols.lookup<pir::MathematicalOp>(policy.entry);
  if (!entry)
    return error("native-proof-entry");
  auto occurrenceMap = origins(entry, originalSymbols);
  if (!occurrenceMap)
    return occurrenceMap.takeError();
  // Only the selected construction closure can consume the managed root.
  // Protocol data ports and unrelated Local code cannot introduce one.
  llvm::DenseSet<Operation *> authorized;
  if (construction &&
      construction->root == protocol::ConstructionPlan::Root::Host) {
    SmallVector<local::FuncOp> pending;
    for (const auto &rule : construction->rules)
      pending.push_back(
          originalSymbols.lookup<local::FuncOp>(rule.handler.getValue()));
    while (!pending.empty()) {
      auto function = pending.pop_back_val();
      if (!function || !authorized.insert(function).second)
        continue;
      function.walk([&](local::ApplyOp apply) {
        pending.push_back(
            originalSymbols.lookup<local::FuncOp>(apply.getCallee()));
      });
    }
  }
  bool transcript = false;
  bool allowed = false;
  auto checkType = [&](Type type) {
    type.walk([&](Type nested) {
      if (auto cap = dyn_cast<local::CapabilityType>(nested))
        transcript |=
            cap.getKind().starts_with("transcript:") &&
            (!allowed || cap.getKind() != "transcript:" + policy.suite);
    });
  };
  original.walk([&](Operation *op) {
    auto function = dyn_cast<local::FuncOp>(op);
    if (!function)
      function = op->getParentOfType<local::FuncOp>();
    allowed = (function && authorized.contains(function)) ||
              (isa<pir::ConstructionOp>(op) && construction &&
               construction->root == protocol::ConstructionPlan::Root::Host);
    for (auto type : op->getOperandTypes())
      checkType(type);
    for (auto type : op->getResultTypes())
      checkType(type);
    for (auto &region : op->getRegions())
      for (auto &block : region)
        for (auto type : block.getArgumentTypes())
          checkType(type);
    for (auto attr : op->getAttrs())
      attr.getValue().walk([&](Type type) { checkType(type); });
    if (auto binding = dyn_cast<local::OperationBindingOp>(op)) {
      if (binding.getContract().starts_with("transcript.")) {
        auto *effects = protocol::operationContracts(binding.getContract());
        auto arguments = binding.getArguments();
        transcript |=
            !construction ||
            construction->root != protocol::ConstructionPlan::Root::Host ||
            !effects || !effects->managedHistory || arguments.empty() ||
            arguments[0] != StringAttr::get(source.getContext(), policy.suite);
      }
    }
  });
  if (transcript)
    return error("native-proof-authored-transcript");
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  PassManager passes(source.getContext());
  passes.addPass(
      protocol::createPrepareProtocolPass(false, fuseVectorReductions));
  if (failed(passes.run(*candidate)))
    return error("native-proof-preparation");
  if (!unit(*candidate))
    return error("native-proof-preparation");
  return PreparedProof{std::move(candidate), std::move(*occurrenceMap),
                       std::move(construction)};
}
} // namespace
Expected<NativeProofPolicy>
selectNativeProofDraws(ModuleOp source, const NativeProofPolicy &selection,
                       bool fuseVectorReductions) {
  auto policy =
      readProofPolicy(printJson(encodeNativeProofPolicy(selection)), true);
  if (!policy)
    return policy.takeError();
  auto prepared = prepareProof(source, *policy, fuseVectorReductions);
  if (!prepared)
    return prepared.takeError();
  SymbolTable symbols(unit(*prepared->module));
  auto program = symbols.lookup<pir::MathematicalOp>(policy->entry);
  auto admitted =
      admit(program, *policy, prepared->origins, DrawSelection::Service,
            prepared->construction ? &*prepared->construction : nullptr);
  if (!admitted)
    return admitted.takeError();
  if (prepared->construction)
    if (auto e = admitConstruction(program, *prepared->construction,
                                   admitted->events))
      return std::move(e);
  policy->draws = std::move(admitted->draws);
  return parseNativeProofPolicy(printJson(encodeNativeProofPolicy(*policy)));
}
Expected<NativeProofConstruction>
constructNativeProof(ModuleOp source, const NativeProofPolicy &policy,
                     bool fuseVectorReductions) {
  // Validate public API callers too; policy structs are not admission tokens.
  auto checked =
      parseNativeProofPolicy(printJson(encodeNativeProofPolicy(policy)));
  if (!checked)
    return checked.takeError();
  auto preparedSource = prepareProof(source, policy, fuseVectorReductions);
  if (!preparedSource)
    return preparedSource.takeError();
  auto candidate = std::move(preparedSource->module);
  auto prepared = unit(*candidate);
  SymbolTable preparedSymbols(prepared);
  auto program = preparedSymbols.lookup<pir::MathematicalOp>(policy.entry);
  auto admitted = admit(
      program, policy, preparedSource->origins, DrawSelection::Explicit,
      preparedSource->construction ? &*preparedSource->construction : nullptr);
  if (!admitted)
    return admitted.takeError();
  if (preparedSource->construction)
    if (auto e = admitConstruction(program, *preparedSource->construction,
                                   admitted->events))
      return std::move(e);
  auto allDefinitions =
      OwningOpRef<ModuleOp>(cast<ModuleOp>((*candidate)->clone()));
  // Applications have already expanded. Export only the selected entry; local
  // symbols remain owned and checked by the normal native module verifier.
  for (auto function : make_early_inc_range(
           prepared.getBody().front().getOps<pir::MathematicalOp>()))
    if (function != program)
      function.erase();
  if (auto e = detail::verifyNativeEntrySelection(*allDefinitions, *candidate,
                                                  policy.entry))
    return std::move(e);
  allDefinitions = {};
  for (auto record : make_early_inc_range(
           prepared.getBody().front().getOps<pir::ConstructionOp>()))
    record.erase();
  PassManager passes(source.getContext());
  passes.addPass(protocol::createProjectProtocolPass(false));
  if (failed(passes.run(*candidate)))
    return error("native-proof-projection");
  auto projected = OwningOpRef<ModuleOp>(cast<ModuleOp>((*candidate)->clone()));
  auto *plan =
      preparedSource->construction ? &*preparedSource->construction : nullptr;
  json::Array exportedPlan;
  if (!policy.suite.empty() || plan)
    if (auto e = Emitter(unit(*candidate), policy, plan)
                     .run(*admitted, exportedPlan))
      return std::move(e);
  if (failed(verify(*candidate)))
    return error("native-proof-construction");
  if (auto e = detail::verifyNativeTranscript(*projected, *candidate, policy,
                                              admitted->events, plan))
    return std::move(e);
  json::Value descriptor(json::Array{
      "zkc.native-proof-descriptor/0", encodeNativeProofPolicy(policy),
      "zkc.native-origin/0", std::move(admitted->sequence),
      std::move(admitted->publicBindings), std::move(admitted->messages),
      std::move(exportedPlan)});
  return NativeProofConstruction{std::move(candidate), std::move(descriptor),
                                 std::move(admitted->wireSites)};
}
Error checkNativeProof(ModuleOp source, ModuleOp candidate,
                       const NativeProofPolicy &policy,
                       bool fuseVectorReductions) {
  if (!source || !candidate || candidate.getContext() != source.getContext() ||
      failed(verify(candidate)))
    return error("native-proof-candidate");
  auto expected = constructNativeProof(source, policy, fuseVectorReductions);
  if (!expected)
    return expected.takeError();
  if (!OperationEquivalence::isEquivalentTo(
          expected->module->getOperation(), candidate,
          OperationEquivalence::IgnoreLocations))
    return error("native-proof-correspondence");
  return Error::success();
}
} // namespace zkc
