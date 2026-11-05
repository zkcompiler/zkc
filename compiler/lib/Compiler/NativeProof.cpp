#include "zkc/Compiler/NativeProof.h"
#include "../Transforms/PreparedProtocol.h"
#include "../Transforms/RealizedProtocol.h"
#include "ConstructionBinding.h"
#include "IRFingerprint.h"
#include "NativeCodec.h"
#include "NativeConstructionPreparation.h"
#include "NativeProofOrigins.h"
#include "NativeProofVerification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>
#include <type_traits>
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
bool verifierKey(const protocol::BoundType &type) {
  return protocol::setupKey(type.kind) == protocol::SetupKey::Verifier;
}
// The catalog's input-only frames: a codec frame of layout Table, the
// standalone public table input.
bool inputOnlyFrame(const protocol::BoundType &type) {
  const auto *codec =
      protocol::installedDomains().defaultCodec(type.kind, type.identity);
  const auto *row =
      codec ? protocol::instances::codec(codec->identity) : nullptr;
  const auto *tag = row && row->frame
                        ? protocol::instances::frameTag(row->frame->tag)
                        : nullptr;
  return tag && tag->layout == protocol::instances::FrameLayout::Table;
}
Expected<protocol::BoundType> wire(Type type, bool input = false) {
  auto logical = protocol::encodeBoundType(type, false);
  if (!logical)
    return logical.takeError();
  // Inputs also admit the catalog's input-only frames and verifier keys,
  // which exist only over commitments whose scheme requires a setup.
  if (protocol::nativeMessageData(*logical) ||
      (input && (inputOnlyFrame(*logical) || verifierKey(*logical))))
    return *logical;
  return error("native-proof-wire-type");
}
StringRef wireCodec(const protocol::BoundType &type) {
  if (protocol::nativeDataFrame(type))
    return "zkc.native-data/0";
  if (verifierKey(type))
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
bool oracleOperation(Operation &op) {
  return isa<pir::OracleSendOp, pir::OracleQueryOp, pir::OracleVirtualOp,
             pir::OracleInputOp, pir::OracleComponentsOp, pir::OracleShapeOp,
             pir::OracleForgetShapeOp, pir::OracleContentsOp,
             pir::OracleSequenceEmptyOp, pir::OracleSequenceAppendOp,
             pir::OracleSequenceAtOp, pir::OracleSequenceLengthOp>(op);
}
bool admittedOperation(Operation &op, bool beforePreparation) {
  // Formed total mathematics includes closed selected regions. Their complete
  // bodies were admitted as mathematics and cannot contain Protocol events.
  return mathematical::isTotal(&op) ||
         (!op.getNumRegions() &&
          (isa<pir::QueryOp, pir::ExchangeOp, pir::StatementOp, pir::GuardOp,
               pir::LocalCallOp, pir::MathematicalReturnOp, pir::FinishIfOp,
               pir::RestrictRolesOp, pir::AssembleRolesOp>(op) ||
           // Preparation expands verified pure and Protocol applications.
           (beforePreparation &&
            (isa<pir::ApplyOp, func::CallOp>(op) || oracleOperation(op))) ||
           (!beforePreparation && isa<pir::ConstructionStartOp>(op))));
}

using Origin = detail::NativeSourceOrigin;
// Borrowed services pass through isolated repeat and branch captures without
// acquiring a new authority. Return the argument in its original mathematical
// definition.
BlockArgument sourcePort(Value value) {
  while (value) {
    if (auto restriction = value.getDefiningOp<pir::RestrictRolesOp>()) {
      value = restriction.getInput();
      continue;
    }
    auto argument = dyn_cast<BlockArgument>(value);
    if (!argument)
      return {};
    if (isSelectedControl(argument.getOwner()->getParentOp())) {
      value = selectedCapture(argument);
      continue;
    }
    auto repeat = dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
    if (!repeat)
      return argument;
    if (!argument.getArgNumber())
      return {};
    value = repeat.getInputs()[argument.getArgNumber()];
  }
  return {};
}
Expected<StringMap<Origin>>
origins(pir::MathematicalOp entry, SymbolTable &symbols,
        ArrayRef<protocol::ConstructionInvocation> invocations) {
  StringMap<Origin> out;
  llvm::StringSet<> starts;
  for (const auto &invocation : invocations)
    starts.insert(invocation.site);
  unsigned remaining = 100000;
  auto collect = [&](auto &&self, pir::MathematicalOp function, Block &body,
                     ArrayRef<protocol::NativeOriginStep> steps,
                     StringRef expanded,
                     const StringMap<std::string> &roles) -> Error {
    if (steps.size() > 64)
      return error("native-proof-origin-limit");
    if (function.getSymName().starts_with("zkc.oracle."))
      return error("native-proof-reserved-origin");
    for (auto &op : body) {
      if (!remaining--)
        return error("native-proof-origin-limit");
      auto repeat = dyn_cast<pir::RepeatOp>(op);
      auto branch = dyn_cast<pir::BranchOp>(op);
      if (!admittedOperation(op, true) && !repeat && !branch &&
          !isa<pir::ProtocolYieldOp>(op))
        return error("native-proof-operation", op.getName().getStringRef());
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site)
        continue;
      auto id = expanded.empty() ? site.str()
                                 : mathematical::expandedApplicationSite(
                                       expanded, site.getValue());
      if (auto apply = dyn_cast<pir::ApplyOp>(op)) {
        if (starts.contains(id)) {
          Origin origin{function.getSymName().str(),
                        site.str(),
                        protocol::NativeStartOrigin{function.getSymName().str(),
                                                    site.str()},
                        {steps.begin(), steps.end()}};
          if (out.size() >= maxActions || !out.try_emplace(id, origin).second)
            return error("native-proof-origin");
        }
        auto callee = symbols.lookup<pir::MathematicalOp>(apply.getCallee());
        if (!callee || !hasSingleElement(callee.getBody()))
          return error("native-proof-source");
        std::vector<protocol::NativeOriginStep> childSteps(steps.begin(),
                                                           steps.end());
        childSteps.push_back({protocol::NativeOriginStep::Kind::Apply,
                              function.getSymName().str(), site.str()});
        StringMap<std::string> childRoles;
        for (auto [source, target] : zip(callee.getRoles(), apply.getRoles()))
          childRoles[cast<StringAttr>(source).getValue()] =
              roles.lookup(cast<StringAttr>(target).getValue());
        if (auto e = self(self, callee, callee.getBody().front(), childSteps,
                          id, childRoles))
          return e;
        continue;
      }
      if (repeat || branch || isa<pir::QueryOp, pir::ExchangeOp>(op) ||
          oracleOperation(op)) {
        Origin origin{function.getSymName().str(),
                      site.str(),
                      {},
                      {steps.begin(), steps.end()}};
        if (auto query = dyn_cast<pir::QueryOp>(op)) {
          auto port = sourcePort(query.getReference());
          if (!port || port.getOwner() != &function.getBody().front())
            return error("native-proof-service-alias");
          auto service = cast<pir::ServiceReferenceType>(port.getType());
          origin.event = protocol::NativeQueryOrigin{
              origin.protocol,         origin.site,
              port.getArgNumber(),     service.getContract().str(),
              query.getMethod().str(), roles.lookup(query.getOwner())};
        } else if (auto message = dyn_cast<pir::ExchangeOp>(op)) {
          origin.event = protocol::NativeMessageOrigin{
              origin.protocol, origin.site, origin.site,
              roles.lookup(message.getSender()),
              roles.lookup(message.getReceiver())};
        } else if (oracleOperation(op)) {
          origin.event = detail::NativeOracleOrigin{};
        } else if (branch) {
          origin.event = detail::NativeBranchOrigin{};
        } else {
          origin.event = detail::NativeRepeatOrigin{};
        }
        if (out.size() >= maxActions)
          return error("native-proof-origin-limit");
        if (!out.try_emplace(id, origin).second)
          return error("native-proof-origin");
        if (repeat) {
          auto child = origin.steps;
          child.push_back({protocol::NativeOriginStep::Kind::Repeat,
                           origin.protocol, origin.site});
          if (auto e = self(self, function, repeat.getBody().front(), child,
                            expanded, roles))
            return e;
        } else if (branch) {
          // Formation fixes the arm order and labels. Inventory every arm once;
          // branch alternatives are static origin components, not coordinates.
          for (auto [index, arm] : enumerate(branch.getArms())) {
            auto child = origin.steps;
            child.push_back({protocol::NativeOriginStep::Kind::Branch,
                             origin.protocol, origin.site,
                             cast<StringAttr>(branch.getAlternatives()[index])
                                 .getValue()
                                 .str()});
            if (auto e =
                    self(self, function, arm.front(), child, expanded, roles))
              return e;
          }
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
  json::Array publicBindings, messages, wireSites, sequence, witnesses;
  std::vector<std::pair<std::string, std::string>> draws;
};
enum class DrawSelection { Explicit, Service };
Expected<Admitted>
admitInterface(pir::MathematicalOp source, const NativeProofPolicy &policy,
               const protocol::ConstructionPlan *construction) {
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
  std::vector<unsigned> required;
  for (auto [i, type] : enumerate(signature.getInputs())) {
    auto owners = cast<ArrayAttr>(source.getInputRoles()[i]);
    if (!owns(owners, policy.validator))
      continue;
    if (auto service = dyn_cast<pir::ServiceReferenceType>(type)) {
      auto field = protocol::randomServiceField(service.getContract());
      if (field.empty() || owners.size() != 1 ||
          (!construction && is_contained(policy.services, i) &&
           field != challengeField))
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
      if (verifierKey(*logical) &&
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
      keys += verifierKey(*logical);
    }
    if (keys > 64 || (needsKey && !keys))
      return error("native-proof-setup-coverage");
  }
  if (required != policy.publicInputs)
    return error("native-proof-public-bindings");
  for (auto service : policy.services)
    if (service >= signature.getNumInputs() ||
        !isa<pir::ServiceReferenceType>(signature.getInput(service)) ||
        !owns(cast<ArrayAttr>(source.getInputRoles()[service]),
              policy.validator))
      return error("native-proof-verifier-service");
  return admitted;
}
Expected<Admitted>
admit(pir::MathematicalOp source, const NativeProofPolicy &policy,
      const StringMap<Origin> &sourceOrigins,
      DrawSelection selection = DrawSelection::Explicit,
      const protocol::ConstructionPlan *construction = nullptr) {
  auto interface = admitInterface(source, policy, construction);
  if (!interface)
    return interface.takeError();
  auto admitted = std::move(*interface);
  StringRef challengeField = protocol::nativeChallengeField(policy.suite);
  struct ControlFrame {
    protocol::NativeOriginStep::Kind kind;
    std::string site, alternative;
  };
  SmallVector<ControlFrame> frames;
  uint64_t originWork = 100000;
  auto chargeOrigin = [&](uint64_t amount) {
    if (amount > originWork) {
      originWork = 0;
      return false;
    }
    originWork -= amount;
    return true;
  };
  llvm::StringSet<> consumedOrigins;
  auto consume = [&](StringRef site, auto event) -> Expected<const Origin *> {
    using SourceEvent = std::decay_t<decltype(event)>;
    auto found = sourceOrigins.find(site);
    if (found == sourceOrigins.end() ||
        !std::holds_alternative<SourceEvent>(found->second.event) ||
        !consumedOrigins.insert(site).second)
      return error("native-proof-origin");
    // Compare the typed provenance with the actual enclosing control stack.
    // Application frames expand names; branch labels never add coordinates.
    const auto &origin = found->second;
    std::string prefix;
    unsigned frame = 0;
    auto expand = [&](StringRef name, StringRef protocol) {
      return prefix.empty() || protocol.starts_with("zkc.oracle.")
                 ? name.str()
                 : mathematical::expandedApplicationSite(prefix, name);
    };
    for (const auto &step : origin.steps) {
      if (!chargeOrigin(1 + prefix.size() + step.site.size() +
                        step.protocol.size() + step.alternative.size()))
        return error("native-proof-origin-limit");
      if (step.kind == protocol::NativeOriginStep::Kind::Apply) {
        prefix = expand(step.site, step.protocol);
        if (prefix.size() > 4096)
          return error("native-proof-origin-limit");
        continue;
      }
      if (frame >= frames.size() || frames[frame].kind != step.kind ||
          frames[frame].site != expand(step.site, step.protocol) ||
          frames[frame].alternative != step.alternative)
        return error("native-proof-origin");
      ++frame;
    }
    if (!chargeOrigin(1 + prefix.size() + origin.site.size()) ||
        frame != frames.size() || expand(origin.site, origin.protocol) != site)
      return error(originWork ? "native-proof-origin"
                              : "native-proof-origin-limit");
    return &origin;
  };
  auto append = [&](Operation *op, bool query, Type payload,
                    json::Array &sequence, std::optional<uint64_t> bound = {},
                    std::optional<uint64_t> count = {},
                    bool reconstructed = false) -> Error {
    auto site = op->getAttrOfType<StringAttr>("site").str();
    auto found = query ? consume(site, protocol::NativeQueryOrigin{})
                       : consume(site, protocol::NativeMessageOrigin{});
    if (!found)
      return found.takeError();
    const auto &origin = **found;
    if (query) {
      auto action = cast<pir::QueryOp>(op);
      if (std::get<protocol::NativeQueryOrigin>(origin.event).owner !=
          action.getOwner())
        return error("native-proof-origin");
    } else {
      auto action = cast<pir::ExchangeOp>(op);
      const auto &message =
          std::get<protocol::NativeMessageOrigin>(origin.event);
      if (message.sender != action.getSender() ||
          message.receiver != action.getReceiver())
        return error("native-proof-origin");
    }
    auto typed = detail::exportNativeSourceOrigin(policy.entry, origin);
    if (!typed)
      return typed.takeError();
    auto encoded = protocol::encodeNativeOriginTemplate(*typed);
    if (!encoded)
      return encoded.takeError();
    auto type = wire(payload);
    if (!type)
      return type.takeError();
    admitted.events.push_back(
        {site, *encoded, payload, query,
         static_cast<unsigned>(count_if(
             origin.steps,
             [](const auto &s) {
               return s.kind == protocol::NativeOriginStep::Kind::Repeat;
             })),
         bound, std::nullopt});
    auto &event = admitted.events.back();
    event.count = count;
    event.reconstructed = reconstructed;
    if (count) {
      auto gate = find_if(policy.gates,
                          [&](const auto &gate) { return gate.first == site; });
      if (gate != policy.gates.end()) {
        event.difficulty = gate->second;
        event.witnessSite = "gate." + site;
        if (sourceOrigins.contains(event.witnessSite))
          return error("native-proof-gate-selection");
        admitted.witnesses.push_back(json::Array{*encoded, event.witnessSite,
                                                 "index", "native.index/0"});
        admitted.wireSites.push_back(json::Array{*encoded, event.witnessSite});
        sequence.push_back(json::Array{
            "gated-indices", *encoded, std::to_string(*bound),
            std::to_string(*count), std::to_string(*event.difficulty)});
      } else {
        sequence.push_back(json::Array{"indices", *encoded,
                                       std::to_string(*bound),
                                       std::to_string(*count)});
      }
    } else if (bound)
      sequence.push_back(
          json::Array{"index", *encoded, std::to_string(*bound)});
    else
      sequence.push_back(json::Array{query           ? "query"
                                     : reconstructed ? "reconstructed-message"
                                                     : "message",
                                     *encoded});
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
        auto found = consume(repeat.getSite(), detail::NativeRepeatOrigin{});
        if (!found)
          return found.takeError();
        json::Array children;
        frames.push_back({protocol::NativeOriginStep::Kind::Repeat,
                          repeat.getSite().str(),
                          {}});
        auto failure =
            self(self, repeat.getBody().front(), children, depth + 1);
        frames.pop_back();
        if (failure)
          return failure;
        // Both roles must execute every loop containing transcript events. Pure
        // local loops may remain owner-local and have an empty event subtree.
        if (!children.empty() && repeat.getRoles().size() != 2)
          return error("native-proof-loop-participants");
        for (auto &child : children)
          sequence.push_back(std::move(child));
        continue;
      }
      if (auto branch = dyn_cast<pir::BranchOp>(op)) {
        if (pending)
          return error("native-proof-branch-prefix");
        auto found = consume(branch.getSite(), detail::NativeBranchOrigin{});
        if (!found)
          return found.takeError();
        bool observed = false;
        for (auto [index, arm] : enumerate(branch.getArms())) {
          frames.push_back(
              {protocol::NativeOriginStep::Kind::Branch, branch.getSite().str(),
               cast<StringAttr>(branch.getAlternatives()[index]).str()});
          json::Array children;
          auto failure = self(self, arm.front(), children, depth + 1);
          frames.pop_back();
          if (failure)
            return failure;
          observed |= !children.empty();
          for (auto &child : children)
            sequence.push_back(std::move(child));
        }
        if (observed && branch.getRoles().size() != 2)
          return error("native-proof-branch-participants");
        continue;
      }
      if (!admittedOperation(op, false) && !isa<pir::ProtocolYieldOp>(op))
        return error("native-proof-operation", op.getName().getStringRef());
      if (auto start = dyn_cast<pir::ConstructionStartOp>(op)) {
        if (pending)
          return error("native-proof-prefix");
        auto found = consume(start.getSite(), protocol::NativeStartOrigin{});
        if (!found)
          return found.takeError();
        const auto &origin = **found;
        auto typed = detail::exportNativeSourceOrigin(policy.entry, origin);
        if (!typed)
          return typed.takeError();
        auto encoded = protocol::encodeNativeOriginTemplate(*typed);
        if (!encoded)
          return encoded.takeError();
        SmallVector<Type> inputs(start.getOperandTypes());
        json::Array types;
        for (Type input : inputs) {
          auto logical = protocol::encodeBoundType(input, false);
          if (!logical)
            return logical.takeError();
          types.push_back(logical->spelling());
        }
        admitted.events.push_back(
            {start.getSite().str(),
             *encoded,
             {},
             false,
             static_cast<unsigned>(count_if(
                 origin.steps,
                 [](const auto &s) {
                   return s.kind == protocol::NativeOriginStep::Kind::Repeat;
                 })),
             std::nullopt,
             std::move(inputs)});
        sequence.push_back(json::Array{"start", *encoded, std::move(types)});
      }
      if (auto statement = dyn_cast<pir::StatementOp>(op)) {
        auto declaration =
            symbols.lookup<relation::DeclareOp>(statement.getRelation());
        if (!declaration ||
            statement.getInputs().size() != declaration.getPurposes().size())
          return error("native-proof-statement");
        // This two-role deployment selects one validator observation. A
        // retained selection must designate that same role-local result.
        if (statement.getAcceptance() != policy.acceptance)
          return error("native-proof-statement-acceptance");
        if (statement.getTargetAttr()) {
          auto target = pir::getStatementTarget(statement);
          auto decision = target ? dyn_cast<ArrayAttr>(target[4]) : ArrayAttr();
          auto role = decision && decision.size() == 3
                          ? dyn_cast<StringAttr>(decision[2])
                          : StringAttr();
          if (!role || role.getValue() != policy.validator)
            return error("native-proof-statement-acceptance");
        }
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
        auto authority = sourcePort(query.getReference());
        bool selected = authority &&
                        is_contained(policy.services, authority.getArgNumber());
        if (!selected) {
          // Placement keeps this service and its results owner-local. Request
          // reconstruction cannot use an unselected query as a seed, so private
          // entropy cannot become a producer-visible request.
          auto origin = consume(query.getSite(), protocol::NativeQueryOrigin{});
          if (!origin)
            return origin.takeError();
          continue;
        }
        if (query.getOwner() != policy.validator)
          return error("native-proof-draw-selection");
        // A selected query is a field draw or a UniformIndex query. Both
        // become transitions of the same transcript at this occurrence.
        bool index = query.getMethod() == "index",
             block = query.getMethod() == "indices";
        if (query.getNumOperands() != (block   ? 3u
                                       : index ? 2u
                                               : 1u) ||
            query.getNumResults() != 1 ||
            (!construction &&
             query.getResult(0).getType() !=
                 (block   ? Type(data::IndicesType::get(source.getContext()))
                  : index ? Type(IntegerType::get(source.getContext(), 64,
                                                  IntegerType::Unsigned))
                          : Type(algebra::FieldType::get(source.getContext(),
                                                         challengeField)))) ||
            (!index && !block && query.getMethod() != "draw") || draw >= 64 ||
            (selection == DrawSelection::Explicit &&
             (draw >= policy.draws.size() ||
              query.getSite() != policy.draws[draw].first)))
          return error("native-proof-draw-selection");
        // Formation already fixes an index domain to a positive u64 constant;
        // its value becomes part of the transcript event. The suite's
        // IndexTranscript fact is checked when the transition is bound.
        std::optional<uint64_t> bound;
        std::optional<uint64_t> count;
        if (index || block) {
          auto constant =
              query.getInputs().front().getDefiningOp<data::IndexOp>();
          if (!constant || !protocol::uniformIndexBound(constant.getValue()))
            return error("native-proof-draw-selection");
          bound = constant.getValue();
          if (block) {
            auto amount = query.getInputs()[1].getDefiningOp<data::IndexOp>();
            if (!amount || !amount.getValue() || amount.getValue() > 1048576 ||
                !isPowerOf2_64(*bound) || *bound > (uint64_t(1) << 63) ||
                !protocol::installedDomains().hasFact("IndexBlockTranscript",
                                                      {policy.suite}) ||
                construction)
              return error("native-proof-index-block");
            count = amount.getValue();
          }
        }
        if (auto e = append(query, true, query.getResult(0).getType(), sequence,
                            bound, count))
          return e;
        pending = query;
      }
      if (auto message = dyn_cast<pir::ExchangeOp>(op)) {
        bool reconstructed = false;
        if (message.getSender() == policy.producer) {
          if (message.getReceiver() != policy.validator)
            return error("native-proof-reverse-message");
          if (pending)
            return error("native-proof-prefix");
        } else {
          if (message.getSender() != policy.validator ||
              message.getReceiver() != policy.producer)
            return error("native-proof-reverse-message");
          if (pending) {
            // Application expansion preserves role-local components through
            // explicit restrictions/assemblies. Read only the validator's
            // actual component; a computed value never aliases the draw.
            Value payload = message.getInput();
            while (payload) {
              if (!chargeOrigin(1))
                return error("native-proof-origin-limit");
              if (auto restriction =
                      payload.getDefiningOp<pir::RestrictRolesOp>()) {
                if (!chargeOrigin(restriction.getRoles().size()))
                  return error("native-proof-origin-limit");
                if (!owns(restriction.getRoles(), policy.validator))
                  break;
                payload = restriction.getInput();
              } else if (auto assembly =
                             payload.getDefiningOp<pir::AssembleRolesOp>()) {
                if (!chargeOrigin(assembly.getRoles().size()))
                  return error("native-proof-origin-limit");
                payload = assembly.getComponent(policy.validator);
              } else {
                break;
              }
            }
            if (payload != pending.getResult(0) ||
                (selection == DrawSelection::Explicit &&
                 message.getSite() != policy.draws[draw].second))
              return error("native-proof-reverse-message");
            admitted.draws.emplace_back(pending.getSite().str(),
                                        message.getSite().str());
            pending = {};
            ++draw;
          } else {
            // Occurrence selection is not a reconstruction certificate. The
            // participant reader must establish the actual value relation
            // before this message can lose its transport.
            if (construction || policy.suite.empty())
              return error("native-proof-request-profile");
            reconstructed = true;
          }
        }
        if (auto e = append(message, false, message.getInput().getType(),
                            sequence, {}, {}, reconstructed))
          return e;
      }
    }
    if (pending)
      return error(isa<pir::BranchOp>(body.getParentOp())
                       ? "native-proof-branch-prefix"
                       : "native-proof-draw-selection");
    return Error::success();
  };
  if (auto e = block(block, source.getBody().front(), admitted.sequence, 0))
    return std::move(e);
  for (const auto &gate : policy.gates) {
    auto event = find_if(admitted.events, [&](const auto &event) {
      return event.site == gate.first;
    });
    if (event == admitted.events.end() || !event->query || !event->count ||
        !event->difficulty)
      return error("native-proof-gate-selection");
  }
  if (selection == DrawSelection::Explicit && draw != policy.draws.size())
    return error("native-proof-draw-selection");
  if (consumedOrigins.size() != sourceOrigins.size())
    return error("native-proof-origin-coverage");
  if (policy.format == protocol::ProofFormat::RawBytes &&
      !(construction && construction->codec)) {
    if (!policy.suite.empty() || admitted.events.size() != 1 ||
        admitted.events.front().query || admitted.events.front().depth)
      return error("native-proof-format");
    auto origin =
        protocol::decodeNativeOriginTemplate(admitted.events.front().origin);
    if (!origin)
      return origin.takeError();
    if (any_of(origin->path, [](const auto &step) {
          return step.kind == protocol::NativeOriginStep::Kind::Branch;
        }))
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
  std::map<protocol::ConstructionRule::Kind, llvm::StringSet<>> covered;
  for (const auto &rule : plan.rules) {
    if (rule.kind == protocol::ConstructionRule::Kind::Start)
      continue;
    std::optional<unsigned> previous;
    Operation *previousOperation = nullptr;
    for (auto [leaf, site] : enumerate(rule.sites)) {
      auto found = indices.find(site);
      if (found == indices.end() || !covered[rule.kind].insert(site).second)
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
        auto handler = symbols.lookup<func::FuncOp>(rule.handler.getValue());
        auto signature = protocol::scopedDataSignature(handler);
        if (!signature ||
            signature.getNumInputs() !=
                plan.state.size() + unsigned(event.bound.has_value()))
          return error("native-proof-construction-request");
      }
      if (protocol::isCodecRule(rule.kind)) {
        auto message = dyn_cast<pir::ExchangeOp>(operation);
        auto owners =
            cast<ArrayAttr>(source.getInputRoles()[plan.services.front()]);
        if (!message || owners.size() != 1 ||
            message.getReceiverAttr() != owners[0] ||
            message.getSenderAttr() == owners[0])
          return error("native-proof-construction-codec-direction");
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
  if (!plan.nativeBase &&
      covered[protocol::ConstructionRule::Kind::Message].size() +
              covered[protocol::ConstructionRule::Kind::Query].size() !=
          size_t(count_if(
              events, [](const auto &event) { return !event.startInputs; })))
    return error("native-proof-construction-coverage");
  if (plan.codec) {
    auto owners =
        cast<ArrayAttr>(source.getInputRoles()[plan.services.front()]);
    for (const auto &event : events) {
      auto message =
          dyn_cast_or_null<pir::ExchangeOp>(operations.lookup(event.site));
      if (message && message.getReceiverAttr() == owners[0])
        for (auto kind : {protocol::ConstructionRule::Kind::Encode,
                          protocol::ConstructionRule::Kind::Receive,
                          protocol::ConstructionRule::Kind::Decode})
          if (!covered[kind].contains(event.site))
            return error("native-proof-construction-coverage");
    }
  }
  return Error::success();
}
} // namespace
json::Value encodeNativeProofPolicy(const NativeProofPolicy &p) {
  json::Array inputs, draws, services, gates;
  for (auto service : p.services)
    services.push_back(std::to_string(service));
  for (auto port : p.publicInputs)
    inputs.push_back(std::to_string(port));
  for (const auto &[query, delivery] : p.draws)
    draws.push_back(json::Array{query, delivery});
  for (const auto &[site, bits] : p.gates)
    gates.push_back(json::Array{site, std::to_string(bits)});
  return json::Array{"zkc.native-proof-policy/0",
                     p.entry,
                     p.producer,
                     p.validator,
                     std::to_string(p.acceptance),
                     p.suite,
                     std::move(services),
                     std::move(inputs),
                     std::move(draws),
                     protocol::proofFormatName(p.format),
                     p.construction,
                     std::move(gates)};
}
Error checkNativeProofPolicy(const NativeProofPolicy &p, bool selection) {
  auto identifier = [](StringRef s) {
    return name(s) && s.size() <= 128 && all_of(s, [](unsigned char c) {
             return llvm::isAlnum(c) || c == '_' || c == '.' || c == '-';
           });
  };
  // The suite is checked below against the installed challenge fields.
  if (!identifier(p.entry) || !identifier(p.producer) ||
      !identifier(p.validator) ||
      (!p.construction.empty() && !identifier(p.construction)))
    return error("native-proof-policy");
  if (p.acceptance >= maxPorts || p.services.size() > maxPorts ||
      p.publicInputs.size() > maxPorts || p.draws.size() > 64 ||
      (selection && !p.draws.empty()) || p.producer == p.validator)
    return error("native-proof-policy");
  auto increasing = [](ArrayRef<unsigned> ports) {
    for (auto [i, port] : enumerate(ports))
      if (port >= maxPorts || (i && ports[i - 1] >= port))
        return false;
    return true;
  };
  if (!increasing(p.services))
    return error("native-proof-policy");
  if (p.format == protocol::ProofFormat::RawBytes && p.construction.empty() &&
      !p.suite.empty())
    return error("native-proof-format");
  if (!p.construction.empty()
          ? p.services.empty() ||
                (!p.suite.empty() &&
                 protocol::nativeChallengeField(p.suite).empty())
      : p.suite.empty()
          ? !p.services.empty() || !p.draws.empty()
          : protocol::nativeChallengeField(p.suite).empty() ||
                p.services.size() != 1 || (!selection && p.draws.empty()))
    return error("native-proof-policy");
  if (!increasing(p.publicInputs))
    return error("native-proof-policy");
  std::set<StringRef> sites;
  for (const auto &[query, delivery] : p.draws)
    if (!name(query) || !name(delivery) || !sites.insert(query).second ||
        !sites.insert(delivery).second)
      return error("native-proof-policy");
  if (p.gates.size() > 64 || (!p.gates.empty() && p.suite.empty()))
    return error("native-proof-policy");
  std::set<StringRef> gatedSites;
  for (const auto &[site, bits] : p.gates)
    if (!name(site) || bits > 64 || !gatedSites.insert(site).second)
      return error("native-proof-policy");
  return Error::success();
}
namespace {
// Decode the JSON shape only; every policy rule is the typed check's.
Expected<NativeProofPolicy> readProofPolicy(StringRef text, bool selection) {
  if (text.size() > 1024 * 1024 || !mlirNestingWithinLimit(text))
    return error("native-proof-policy-limit");
  auto parsed = parseJson(text);
  if (!parsed)
    return parsed.takeError();
  auto *a = parsed->getAsArray();
  if (!a || a->size() != 12 ||
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
    if (!s)
      return error("native-proof-policy");
    *target = s->str();
  }
  auto acceptance = number((*a)[4]);
  auto *services = (*a)[6].getAsArray(), *inputs = (*a)[7].getAsArray();
  auto *draws = (*a)[8].getAsArray(), *gates = (*a)[11].getAsArray();
  if (!acceptance || !services || !inputs || !draws || !gates)
    return error("native-proof-policy");
  p.acceptance = *acceptance;
  auto ports = [](const json::Array &values, std::vector<unsigned> &out) {
    for (const auto &value : values) {
      auto port = number(value);
      if (!port)
        return false;
      out.push_back(*port);
    }
    return true;
  };
  if (!ports(*services, p.services) || !ports(*inputs, p.publicInputs))
    return error("native-proof-policy");
  auto pair = [](const json::Value &value) -> const json::Array * {
    auto *items = value.getAsArray();
    return items && items->size() == 2 ? items : nullptr;
  };
  for (const auto &item : *draws) {
    auto *draw = pair(item);
    auto query = draw ? (*draw)[0].getAsString() : std::nullopt;
    auto delivery = draw ? (*draw)[1].getAsString() : std::nullopt;
    if (!query || !delivery)
      return error("native-proof-policy");
    p.draws.emplace_back(query->str(), delivery->str());
  }
  for (const auto &item : *gates) {
    auto *gate = pair(item);
    auto site = gate ? (*gate)[0].getAsString() : std::nullopt;
    auto bits = gate ? number((*gate)[1]) : std::nullopt;
    if (!site || !bits)
      return error("native-proof-policy");
    p.gates.emplace_back(site->str(), *bits);
  }
  if (auto e = checkNativeProofPolicy(p, selection))
    return std::move(e);
  return p;
}
} // namespace
Expected<NativeProofPolicy> parseNativeProofPolicy(StringRef text) {
  return readProofPolicy(text, false);
}
namespace {
using ActionPositions =
    llvm::DenseMap<std::pair<Attribute, Attribute>, unsigned>;

// Generated actions can join endpoints at different source positions. Order
// their metadata from the actual participant bodies, retaining the global order
// of source actions. This changes neither body nor its ordered failure
// behavior.
Expected<ArrayAttr> orderConstructedActions(Builder &builder,
                                            const ActionPositions &positions,
                                            ArrayRef<Attribute> actions,
                                            ArrayAttr source) {
  llvm::DenseMap<Attribute, unsigned> bySite;
  llvm::DenseMap<Attribute, SmallVector<std::pair<unsigned, unsigned>>>
      byParticipant;
  SmallVector<SmallVector<unsigned>> successors(actions.size());
  SmallVector<unsigned> incoming(actions.size(), 0);
  auto edge = [&](unsigned before, unsigned after) {
    successors[before].push_back(after);
    ++incoming[after];
  };
  for (auto [index, item] : enumerate(actions)) {
    auto action = cast<DictionaryAttr>(item);
    auto site = action.getAs<StringAttr>("site");
    if (!bySite.try_emplace(site, index).second)
      return error("native-proof-construction-order");
    for (auto target : action.getAs<ArrayAttr>("targets")) {
      auto participant = cast<DictionaryAttr>(target).get("participant");
      auto found = positions.find({participant, site});
      if (found == positions.end())
        return error("native-proof-construction-order");
      byParticipant[participant].emplace_back(found->second, index);
    }
  }
  std::optional<unsigned> previous;
  for (auto item : source) {
    auto found = bySite.find(cast<DictionaryAttr>(item).get("site"));
    if (found == bySite.end())
      continue;
    if (previous)
      edge(*previous, found->second);
    previous = found->second;
  }
  for (auto &[participant, occurrences] : byParticipant) {
    llvm::sort(occurrences);
    for (unsigned i = 1; i < occurrences.size(); ++i) {
      if (occurrences[i - 1].first == occurrences[i].first)
        return error("native-proof-construction-order");
      edge(occurrences[i - 1].second, occurrences[i].second);
    }
  }
  // Prefer the existing order whenever the constraints leave a choice.
  std::set<unsigned> ready;
  for (auto [index, count] : enumerate(incoming))
    if (!count)
      ready.insert(index);
  SmallVector<Attribute> ordered;
  while (!ready.empty()) {
    unsigned next = *ready.begin();
    ready.erase(ready.begin());
    ordered.push_back(actions[next]);
    for (unsigned successor : successors[next])
      if (!--incoming[successor])
        ready.insert(successor);
  }
  if (ordered.size() != actions.size())
    return error("native-proof-construction-order");
  return builder.getArrayAttr(ordered);
}

class Emitter {
  pir::ProtocolModuleOp module;
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan *plan;
  StringMap<const protocol::ConstructionRule *> rules;
  std::map<std::string, protocol::ConstructionRule> startRules;
  SmallVector<Attribute> invokedHelpers;
  OpBuilder builder;
  SymbolTable symbols;
  unsigned freshIndex = 0;
  std::map<std::string, FlatSymbolRefAttr> helpers, searches;
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
    auto operation = runtime::BindingOp::create(
        builder, module.getLoc(), fresh(), contract, parameters, "");
    symbols.insert(operation);
    auto ref = FlatSymbolRefAttr::get(operation);
    bindings.try_emplace(key, ref);
    return ref;
  }
  SmallVector<Value> kernel(exec::ScopedExecutionBuilder &control,
                            FlatSymbolRefAttr selected, ValueRange inputs,
                            TypeRange outputs, StringRef site,
                            ArrayRef<Attribute> parameters = {}) {
    return control.invoke(
        "exec.apply", outputs, control.scoped(inputs),
        {builder.getNamedAttr("binding", selected),
         builder.getNamedAttr("site", builder.getStringAttr(site)),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters))});
  }
  Expected<FlatSymbolRefAttr> helper(const Event &event, TypeRange stateTypes,
                                     bool search = false) {
    auto *rule = rules.lookup(event.site);
    auto source = rule ? symbols.lookup<func::FuncOp>(rule->handler.getValue())
                       : func::FuncOp();
    auto signature = protocol::scopedDataSignature(source);
    if (rule && !signature)
      return error("native-proof-construction-handler");
    if (!rule) {
      if (event.startInputs)
        return error("native-proof-construction-start");
      if (event.query && !event.bound &&
          event.payload != algebra::FieldType::get(
                               module.getContext(),
                               protocol::nativeChallengeField(policy.suite)))
        return error("native-proof-construction-signature",
                     "native query domain differs from the transcript suite");
      if (event.bound && !isPowerOf2_64(*event.bound))
        return error("native-proof-index-bound",
                     "native sampling requires a power-of-two bound");
    }
    SmallVector<Type> inputs{runtime::ScopeType::get(module.getContext())};
    append_range(inputs, stateTypes);
    SmallVector<Type> outputs;
    if (event.query)
      outputs.push_back(event.payload);
    else if (event.startInputs)
      append_range(inputs, *event.startInputs);
    else if (rule)
      append_range(inputs, rule->payload);
    else
      inputs.push_back(event.payload);
    if (event.difficulty && !search)
      inputs.push_back(builder.getIntegerType(64, false));
    if (event.difficulty && search)
      outputs.push_back(builder.getIntegerType(64, false));
    unsigned dataInputs = inputs.size() - 1;
    inputs.append(event.depth, builder.getIntegerType(64, false));
    append_range(outputs, stateTypes);
    builder.setInsertionPointToEnd(&module.getBody().front());
    auto function = func::FuncOp::create(
        builder, module.getLoc(), fresh(),
        builder.getFunctionType(
            inputs, {exec::OutcomeType::get(module.getContext(), outputs)}));
    function.setPrivate();
    function->setAttr("no_inline", builder.getUnitAttr());
    function->setAttr(
        "runtime.origin",
        builder.getArrayAttr({builder.getStringAttr(function.getSymName()),
                              builder.getArrayAttr({})}));
    symbols.insert(function);
    auto *body = function.addEntryBlock();
    builder.setInsertionPointToEnd(body);
    exec::ScopedExecutionBuilder control(builder, function);
    auto data = function.getArguments().drop_front();
    SmallVector<Value> operands(data.take_front(dataInputs));
    if (event.bound && !event.count)
      operands.push_back(kernel(
          control, binding("index.constant", {}), {}, {event.payload}, "bound",
          {builder.getIntegerAttr(builder.getIntegerType(64, false),
                                  *event.bound)})[0]);
    if (rule) {
      // Preserve the original handler as an ordinary borrowed-scope call.
      // Checked helper substitution consumes its actual control later.
      auto values = control.invoke(
          "func.call", signature.getResults(), control.scoped(operands),
          {builder.getNamedAttr("callee", rule->handler),
           builder.getNamedAttr("runtime.site",
                                builder.getStringAttr("handler"))});
      SmallVector<Value> results;
      if (event.query)
        results.push_back(values.back());
      append_range(results, ArrayRef(values).take_front(stateTypes.size()));
      if (event.bound) {
        auto valid = kernel(control, binding("index.less", {}),
                            {results.front(), operands.back()},
                            {builder.getI1Type()}, "range");
        kernel(control, binding("control.require", {}), valid, {},
               "require_range");
      }
      control.returned(results);
    } else {
      auto type = wire(event.payload);
      if (!type)
        return type.takeError();
      std::string contract =
          !event.query ? "transcript.native.indexed.observe.data"
          : event.count
              ? (event.difficulty
                     ? (search ? "transcript.native.indexed.indices.search"
                               : "transcript.native.indexed.indices.gated")
                     : "transcript.native.indexed.indices")
          : event.bound ? "transcript.native.indexed.index"
                        : "transcript.native.indexed.challenge";
      SmallVector<Attribute> arguments{builder.getStringAttr(policy.suite)};
      if (!event.query)
        arguments.push_back(TypeAttr::get(event.payload));
      auto indices = data::IndicesType::get(builder.getContext());
      Value coordinates = kernel(control, binding("indices.empty", {}), {},
                                 {indices}, "coordinates")[0];
      for (auto [i, argument] : enumerate(data.drop_front(dataInputs)))
        coordinates = kernel(control, binding("indices.append", {}),
                             {coordinates, argument}, {indices},
                             "coordinate_" + std::to_string(i))[0];
      operands.push_back(coordinates);
      auto origin = protocol::decodeNativeOriginTemplate(event.origin);
      if (!origin)
        return origin.takeError();
      auto parameter =
          runtime::importNativeOrigin(builder.getContext(), *origin);
      if (!parameter)
        return parameter.takeError();
      SmallVector<Attribute> parameters{*parameter};
      if (event.count) {
        parameters.push_back(builder.getIntegerAttr(
            builder.getIntegerType(64, false), *event.bound));
        parameters.push_back(builder.getIntegerAttr(
            builder.getIntegerType(64, false), *event.count));
        if (event.difficulty)
          parameters.push_back(builder.getIntegerAttr(
              builder.getIntegerType(64, false), *event.difficulty));
      }
      auto values = kernel(control, binding(contract, arguments), operands,
                           outputs, "transition", parameters);
      control.returned(values);
    }
    return FlatSymbolRefAttr::get(function);
  }

public:
  Emitter(pir::ProtocolModuleOp module, const NativeProofPolicy &policy,
          const protocol::ConstructionPlan *plan,
          ArrayRef<protocol::ConstructionInvocation> invocations)
      : module(module), policy(policy), plan(plan),
        builder(module.getContext()), symbols(module) {
    if (plan)
      for (const auto &rule : plan->rules)
        if (!protocol::isCodecRule(rule.kind))
          for (const auto &site : rule.sites)
            rules[site] = &rule;
    for (const auto &invocation : invocations) {
      auto inserted = startRules.emplace(
          invocation.site,
          protocol::ConstructionRule{protocol::ConstructionRuleKind::Start,
                                     invocation.handler,
                                     {invocation.site},
                                     invocation.inputs,
                                     {},
                                     {}});
      rules[invocation.site] = &inserted.first->second;
    }
    module.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        occupied.insert(site.getValue());
    });
  }
  Error run(const Admitted &admitted, json::Array &exportedPlan,
            const detail::NativeRequestPlan &requests,
            const detail::NativeConstructionPreparation &joint) {
    if (!joint.complete())
      return error("native-construction-preparation-replica");
    auto emittedRequests =
        detail::emitNativeRequests(requests, module, [&] { return fresh(); });
    if (!emittedRequests)
      return emittedRequests.takeError();
    auto replace = [&](Value from, Value to) {
      from.replaceAllUsesWith(to);
      for (auto &item : emittedRequests->requests)
        if (item.second == from)
          item.second = to;
    };
    auto records = module.getBody().front().getOps<pir::ProjectionOp>();
    if (!hasSingleElement(records))
      return error("native-proof-entry");
    auto record = *records.begin();
    if (record.getInterfaces().size() != 1)
      return error("native-proof-entry");
    auto original = cast<DictionaryAttr>(record.getInterfaces()[0]);
    SmallVector<Type> stateTypes;
    if (plan)
      stateTypes = plan->state;
    else
      stateTypes.push_back(runtime::CapabilityType::get(
          module.getContext(), zkc::runtime::CapabilityKind::Transcript,
          policy.suite));
    bool hostRoot =
        !plan || plan->root == protocol::ConstructionPlan::Root::Host;
    if (plan) {
      if (plan->initializer &&
          !symbols.lookup<func::FuncOp>(plan->initializer.getValue()))
        return error("native-proof-construction-handler");
      for (const auto &rule : plan->rules)
        if (!symbols.lookup<func::FuncOp>(rule.handler.getValue()))
          return error("native-proof-construction-handler");
    }
    // Source admission bounds the original program. Charge repeated handler
    // expansion work separately before generating adapters or threading
    // participants.
    uint64_t remaining = 1000000;
    llvm::DenseMap<Operation *, uint64_t> bodyCosts;
    for (const auto &event : admitted.events) {
      const auto *rule = rules.lookup(event.site);
      uint64_t cost = 16 * (1 + stateTypes.size() + event.depth +
                            (event.startInputs ? event.startInputs->size()
                             : rule            ? rule->payload.size()
                                               : 1));
      if (rule && rule->sites.back() == event.site) {
        auto function = symbols.lookup<func::FuncOp>(rule->handler.getValue());
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
      if (event.difficulty) {
        auto search = helper(event, stateTypes, true);
        if (!search)
          return search.takeError();
        searches.emplace(event.site, *search);
        invokedHelpers.push_back(*search);
      }
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
    for (const auto &action : emittedRequests->actions) {
      auto call = action.call;
      auto participant = call->getParentOfType<pir::ParticipantOp>();
      auto target = builder.getDictionaryAttr(
          {builder.getNamedAttr("participant",
                                FlatSymbolRefAttr::get(participant)),
           builder.getNamedAttr("operation",
                                builder.getStringAttr("protocol.local_call"))});
      addedActions[action.anchor].push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr("site", call.getSiteAttr()),
           builder.getNamedAttr("kind",
                                builder.getStringAttr("protocol.local_call")),
           builder.getNamedAttr("callee", call.getCalleeAttr()),
           builder.getNamedAttr("targets", builder.getArrayAttr({target}))}));
    }
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
      if (participant.getRole() == policy.validator) {
        SmallVector<unsigned> selected;
        auto owners = original.getAs<ArrayAttr>("input_roles");
        unsigned ingress = 0;
        for (auto [i, roles] : enumerate(owners)) {
          if (!owns(cast<ArrayAttr>(roles), policy.validator))
            continue;
          if (is_contained(policy.services, i))
            selected.push_back(ingress);
          ++ingress;
        }
        SmallVector<Attribute> retained;
        if (auto ports = participant->getAttrOfType<ArrayAttr>("service_ports"))
          for (auto port : ports)
            if (auto row = cast<ArrayAttr>(port);
                !is_contained(selected, cast<IntegerAttr>(row[2]).getInt())) {
              auto ingress = cast<IntegerAttr>(row[2]).getInt();
              retained.push_back(builder.getArrayAttr(
                  {row[0], row[1],
                   builder.getI64IntegerAttr(
                       ingress - llvm::count_if(selected, [&](unsigned port) {
                         return port < ingress;
                       }))}));
            }
        if (retained.empty())
          participant->removeAttr("service_ports");
        else
          participant->setAttr("service_ports", builder.getArrayAttr(retained));
      }
      SmallVector<StringRef> reached;
      SmallVector<Value> coordinates;
      auto invoke = [&](FlatSymbolRefAttr reference, ValueRange operands,
                        StringRef anchor) -> pir::LocalCallOp {
        auto function = symbols.lookup<func::FuncOp>(reference.getValue());
        auto invocation = pir::LocalCallOp::create(
            builder, participant.getLoc(),
            protocol::scopedDataSignature(function).getResults(), operands,
            reference, builder.getStringAttr(fresh()),
            participant.getRoleAttr());
        state.clear();
        append_range(state,
                     invocation.getResults().take_back(stateTypes.size()));
        auto target = builder.getDictionaryAttr(
            {builder.getNamedAttr("participant",
                                  FlatSymbolRefAttr::get(participant)),
             builder.getNamedAttr(
                 "operation", builder.getStringAttr("protocol.local_call"))});
        addedActions[anchor.str()].push_back(builder.getDictionaryAttr(
            {builder.getNamedAttr("site", invocation.getSiteAttr()),
             builder.getNamedAttr("kind",
                                  builder.getStringAttr("protocol.local_call")),
             builder.getNamedAttr("callee", reference),
             builder.getNamedAttr("targets", builder.getArrayAttr({target}))}));
        return invocation;
      };
      auto call = [&](const Event &event, StringRef anchor,
                      ValueRange payload = {}) -> pir::LocalCallOp {
        reached.push_back(event.origin);
        SmallVector<Value> operands(state);
        append_range(operands, payload);
        append_range(operands, coordinates);
        bool search =
            event.difficulty && participant.getRole() == policy.producer;
        return invoke(search ? searches.at(event.site) : helpers.at(event.site),
                      operands,
                      event.difficulty ? StringRef(event.site) : anchor);
      };
      auto witness = [&](const Event &event, StringRef anchor,
                         Value value = {}) -> Value {
        auto slot = builder.getStringAttr(event.witnessSite);
        Value result;
        bool send = participant.getRole() == policy.producer;
        if (send) {
          pir::EmitOp::create(builder, participant.getLoc(), value,
                              event.witnessSite, event.witnessSite,
                              policy.validator);
        } else {
          result = pir::AwaitOp::create(builder, participant.getLoc(),
                                        builder.getIntegerType(64, false),
                                        event.witnessSite, event.witnessSite,
                                        policy.producer)
                       .getOutput();
        }
        if (!send) {
          SmallVector<Attribute> targets;
          for (auto endpoint :
               module.getBody().front().getOps<pir::ParticipantOp>())
            targets.push_back(builder.getDictionaryAttr(
                {builder.getNamedAttr("participant",
                                      FlatSymbolRefAttr::get(endpoint)),
                 builder.getNamedAttr(
                     "operation",
                     builder.getStringAttr(endpoint.getRole() == policy.producer
                                               ? "protocol.send"
                                               : "protocol.receive"))}));
          addedActions[anchor.str()].push_back(builder.getDictionaryAttr(
              {builder.getNamedAttr("site", slot),
               builder.getNamedAttr("kind",
                                    builder.getStringAttr("protocol.exchange")),
               builder.getNamedAttr("targets",
                                    builder.getArrayAttr(targets))}));
        }
        return result;
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
      uint64_t threadWork = 1000000;
      auto chargeThread = [&](uint64_t amount) {
        if (amount > threadWork)
          return false;
        threadWork -= amount;
        return true;
      };
      auto thread = [&](auto &&self, Block &block, unsigned depth) -> Error {
        if (depth > 64)
          return error("native-proof-construction-limit");
        for (auto &op : make_early_inc_range(block)) {
          if (!chargeThread(1))
            return error("native-proof-construction-limit");
          if (auto branch = dyn_cast<pir::ParticipantBranchOp>(op)) {
            if (!payloadGroup.empty())
              return error("native-proof-construction-message-group");
            bool observed = false, exhausted = false;
            branch.walk([&](Operation *nested) {
              if (!chargeThread(1)) {
                exhausted = true;
                return WalkResult::interrupt();
              }
              observed |= isa<pir::FinishIfOp>(nested);
              if (auto site = nested->getAttrOfType<StringAttr>("site"))
                observed |= events.count(site.str()) != 0;
              return WalkResult::advance();
            });
            if (exhausted)
              return error("native-proof-construction-limit");
            if (!observed)
              continue;
            if (!chargeThread(branch.getNumOperands() + branch.getNumResults() +
                              state.size() + coordinates.size()))
              return error("native-proof-construction-limit");
            SmallVector<Value> operands(branch.getInputs());
            SmallVector<unsigned> coordinateSlots;
            SmallVector<Value> addedCoordinates;
            for (Value coordinate : coordinates) {
              if (!chargeThread(operands.size()))
                return error("native-proof-construction-limit");
              // The selector is not a capture and cannot supply a coordinate.
              auto captures = ArrayRef<Value>(operands).drop_front();
              auto found = llvm::find(captures, coordinate);
              if (found != captures.end())
                coordinateSlots.push_back(1 + (found - captures.begin()));
              else {
                if (!chargeThread(addedCoordinates.size()))
                  return error("native-proof-construction-limit");
                auto added = llvm::find(addedCoordinates, coordinate);
                coordinateSlots.push_back(branch.getNumOperands() +
                                          stateTypes.size() +
                                          (added - addedCoordinates.begin()));
                if (added == addedCoordinates.end())
                  addedCoordinates.push_back(coordinate);
              }
            }
            append_range(operands, state);
            append_range(operands, addedCoordinates);
            SmallVector<Type> results(branch.getResultTypes());
            append_range(results, stateTypes);
            builder.setInsertionPoint(branch);
            OperationState description(
                branch.getLoc(), pir::ParticipantBranchOp::getOperationName());
            description.addOperands(operands);
            description.addTypes(results);
            description.addAttributes(branch->getAttrs());
            for (unsigned i = 0; i < branch.getNumRegions(); ++i)
              description.addRegion();
            auto replacement =
                cast<pir::ParticipantBranchOp>(builder.create(description));
            SmallVector<Value> outerCoordinates(coordinates);
            for (auto [index, arm] : enumerate(branch.getArms())) {
              auto payload = selectedPayloadTypes(branch, index);
              if (!payload)
                return payload.takeError();
              if (!chargeThread(arm.front().getNumArguments() +
                                stateTypes.size() + addedCoordinates.size() +
                                coordinates.size()))
                return error("native-proof-construction-limit");
              replacement->getRegion(index).takeBody(arm);
              auto &child = replacement->getRegion(index).front();
              state.clear();
              for (Type type : stateTypes)
                state.push_back(child.addArgument(type, branch.getLoc()));
              for (Value coordinate : addedCoordinates)
                child.addArgument(coordinate.getType(), branch.getLoc());
              coordinates.clear();
              for (unsigned slot : coordinateSlots)
                coordinates.push_back(
                    child.getArgument(payload->size() + slot - 1));
              if (auto e = self(self, child, depth + 1))
                return e;
              if (!payloadGroup.empty())
                return error("native-proof-construction-message-group");
            }
            coordinates = std::move(outerCoordinates);
            for (auto [oldValue, newValue] :
                 zip(branch.getResults(), replacement.getResults()))
              replace(oldValue, newValue);
            state.assign(
                replacement.getResults().take_back(stateTypes.size()).begin(),
                replacement.getResults().take_back(stateTypes.size()).end());
            branch.erase();
            continue;
          }
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
            // Reuse an exact invariant capture for an administrative coordinate
            // when the source already forwards it. Preserve every original
            // capture and its multiplicity; only new coordinate slots are
            // shared. A carried slot is not an invariant capture.
            unsigned captureStart = 1 + carried + stateTypes.size();
            SmallVector<unsigned> coordinateSlots;
            SmallVector<Value> addedCoordinates;
            for (Value coordinate : coordinates) {
              auto captures =
                  ArrayRef<Value>(operands).drop_front(captureStart);
              auto found = llvm::find(captures, coordinate);
              unsigned slot = captureStart + (found - captures.begin());
              if (found == captures.end()) {
                addedCoordinates.push_back(coordinate);
                operands.push_back(coordinate);
              }
              coordinateSlots.push_back(slot);
            }
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
            for (Value coordinate : addedCoordinates)
              child.addArgument(coordinate.getType(), loop.getLoc());
            SmallVector<Value> outer = coordinates;
            coordinates.clear();
            for (unsigned slot : coordinateSlots)
              coordinates.push_back(child.getArgument(slot));
            coordinates.push_back(child.getArgument(0));
            if (auto e = self(self, child, depth + 1))
              return e;
            coordinates = std::move(outer);
            for (auto [oldValue, newValue] :
                 zip(loop.getResults(), replacement.getResults()))
              replace(oldValue, newValue);
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
            bool affineState =
                !plan || plan->root == protocol::ConstructionPlan::Root::Host;
            if (affineState)
              append_range(results, stateTypes);
            builder.setInsertionPoint(completion);
            auto replacement = pir::FinishIfOp::create(
                builder, completion.getLoc(), results,
                completion.getCondition(), inputs, completion.getSite(),
                completion.getOwner());
            for (auto [oldValue, newValue] :
                 zip(completion.getResults(), replacement.getResults()))
              replace(oldValue, newValue);
            if (affineState) {
              state.clear();
              append_range(
                  state, replacement.getResults().take_back(stateTypes.size()));
            }
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
          if (auto start = dyn_cast<pir::ConstructionStartOp>(op)) {
            if (!event.startInputs || !payloadGroup.empty())
              return error("native-proof-construction-start");
            builder.setInsertionPoint(&op);
            call(event, site.getValue(), start.getInputs());
            op.erase();
          } else if (isa<pir::ParticipantQueryOp>(op)) {
            if (!event.query || participant.getRole() != policy.validator)
              return error("native-proof-projected-event");
            builder.setInsertionPoint(&op);
            SmallVector<Value> payload;
            if (event.difficulty)
              payload.push_back(witness(event, site.getValue()));
            auto replacement = call(event, site.getValue(), payload);
            replace(op.getResult(0), replacement.getResult(0));
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
              if (auto &query = *events.at(delivery->second); query.difficulty)
                witness(query, site.getValue(), challenge.getResult(1));
              replace(receive.getOutput(), challenge.getResult(0));
              observe(event, site.getValue(), challenge.getResult(0));
              op.erase();
            } else if (event.reconstructed) {
              Value payload = emittedRequests->requests.lookup(&op);
              if (participant.getRole() != policy.producer || !payload)
                return error("native-request-emission");
              builder.setInsertionPoint(&op);
              replace(receive.getOutput(), payload);
              observe(event, site.getValue(), payload);
              op.erase();
            } else {
              if (participant.getRole() != policy.validator)
                return error("native-proof-projected-event");
              builder.setInsertionPointAfter(&op);
              observe(event, site.getValue(), receive.getOutput());
            }
          } else if (auto send = dyn_cast<pir::EmitOp>(op)) {
            if (event.query ||
                (deliveries.count(site.str()) || event.reconstructed
                     ? participant.getRole() != policy.validator
                     : participant.getRole() != policy.producer))
              return error("native-proof-projected-event");
            builder.setInsertionPointAfter(&op);
            observe(event, site.getValue(), send.getInput());
            if (deliveries.count(site.str()) || event.reconstructed)
              op.erase();
          } else
            return error("native-proof-projected-event");
        }
        return Error::success();
      };
      if (auto e = thread(thread, body, 0))
        return e;
      if (reached.size() != admitted.events.size() ||
          !all_of(zip(reached, admitted.events), [](auto pair) {
            return std::get<0>(pair) == std::get<1>(pair).origin;
          }))
        return error("native-proof-event-chain");
    }
    ActionPositions positions;
    for (auto participant :
         module.getBody().front().getOps<pir::ParticipantOp>()) {
      unsigned next = 0;
      auto reference = FlatSymbolRefAttr::get(participant);
      participant.walk<WalkOrder::PreOrder>([&](Operation *op) {
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          positions.try_emplace({reference, site}, next++);
      });
    }
    auto rewrite = [&](auto &&self, ArrayAttr source) -> Expected<ArrayAttr> {
      SmallVector<Attribute> actions;
      for (auto item : source) {
        auto action = cast<DictionaryAttr>(item);
        auto site = action.getAs<StringAttr>("site").str();
        if (auto body = action.getAs<ArrayAttr>("body")) {
          NamedAttrList edited(action);
          auto nested = self(self, body);
          if (!nested)
            return nested.takeError();
          edited.set("body", *nested);
          action = edited.getDictionary(module.getContext());
        }
        if (auto arms = action.getAs<ArrayAttr>("arms")) {
          NamedAttrList edited(action);
          SmallVector<Attribute> rewrittenArms;
          for (Attribute item : arms) {
            auto arm = cast<DictionaryAttr>(item);
            auto nested = self(self, arm.getAs<ArrayAttr>("body"));
            if (!nested)
              return nested.takeError();
            NamedAttrList updated(arm);
            updated.set("body", *nested);
            rewrittenArms.push_back(updated.getDictionary(module.getContext()));
          }
          edited.set("arms", builder.getArrayAttr(rewrittenArms));
          action = edited.getDictionary(module.getContext());
        }
        bool reconstructed =
            events.count(site) && events.at(site)->reconstructed;
        if (!queries.count(site) && !deliveries.count(site) && !reconstructed &&
            !startRules.count(site))
          actions.push_back(action);
        append_range(actions, addedActions[site]);
      }
      return orderConstructedActions(builder, positions, actions, source);
    };
    SmallVector<Attribute> actionList(addedActions[""]);
    auto rewritten = rewrite(rewrite, original.getAs<ArrayAttr>("actions"));
    if (!rewritten)
      return rewritten.takeError();
    append_range(actionList, *rewritten);
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
         builder.getNamedAttr(
             "removed_services",
             builder.getI64ArrayAttr(SmallVector<int64_t>(
                 policy.services.begin(), policy.services.end()))),
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
// Charge the immutable original copy before allocating it. Admission and
// checked realization have their own existing budgets; the new joint phase
// shares this remaining allowance through source analysis and both discharges.
bool reserveConstructionSource(Operation *op, uint64_t &remaining,
                               unsigned depth = 0) {
  auto charge = [&](uint64_t work) {
    if (work > remaining)
      return false;
    remaining -= work;
    return true;
  };
  if (depth > 64 || !charge(1) || !charge(op->getNumOperands()) ||
      !charge(op->getNumResults()) || !charge(op->getNumRegions()) ||
      !charge(op->getAttrs().size()))
    return false;
  unsigned nestedDepth =
      depth +
      !isa<ModuleOp, func::FuncOp, pir::ProtocolModuleOp, pir::MathematicalOp>(
          op);
  for (Region &region : op->getRegions())
    for (Block &block : region) {
      if (!charge(1) || !charge(block.getNumArguments()))
        return false;
      for (Operation &child : block)
        if (!reserveConstructionSource(&child, remaining, nestedDepth))
          return false;
    }
  return true;
}
// A grouped message is one directional exchange in the original admitted
// source. Check this fixed structural fact before logical-only preparation:
// an invalid group must not be reported as an unresolved request closure.
// Full event, payload, adjacency and coverage checking remains in
// admitConstruction on the independently prepared subject.
Error checkConstructionMessageDirections(pir::MathematicalOp entry,
                                         const protocol::ConstructionPlan &plan,
                                         uint64_t &remaining) {
  StringMap<pir::ExchangeOp> exchanges;
  bool exhausted = false;
  entry.walk([&](Operation *op) {
    if (remaining < 1 + op->getAttrs().size()) {
      exhausted = true;
      return WalkResult::interrupt();
    }
    remaining -= 1 + op->getAttrs().size();
    auto exchange = dyn_cast<pir::ExchangeOp>(op);
    auto site = op->getAttrOfType<StringAttr>("site");
    if (exchange && site) {
      if (remaining < site.getValue().size()) {
        exhausted = true;
        return WalkResult::interrupt();
      }
      remaining -= site.getValue().size();
      exchanges[site.getValue()] = exchange;
    }
    return WalkResult::advance();
  });
  if (exhausted)
    return error("native-construction-preparation-capacity");
  for (const auto &rule : plan.rules) {
    pir::ExchangeOp previous;
    for (const auto &site : rule.sites) {
      if (remaining < 1 + site.size())
        return error("native-construction-preparation-capacity");
      remaining -= 1 + site.size();
      auto current = exchanges.lookup(site);
      if (previous && current &&
          (previous.getSender() != current.getSender() ||
           previous.getReceiver() != current.getReceiver()))
        return error("native-proof-construction-message-group");
      previous = current;
    }
  }
  return Error::success();
}
struct PreparedProof {
  // Destruction order keeps both original owners alive until after the borrow.
  // Realization owns its independent copies; it never mutates this subject.
  OwningOpRef<ModuleOp> original;
  std::shared_ptr<const protocol::SourceExecutionClosure> originalExecution;
  OwningOpRef<ModuleOp> module;
  std::shared_ptr<const protocol::SourceExecutionClosure> realizedExecution;
  detail::NativeConstructionPreparation joint;
  StringMap<Origin> origins;
  std::optional<protocol::ConstructionPlan> construction;
  SmallVector<protocol::ConstructionInvocation> invocations;
  std::shared_ptr<const mathematical::RealizedProtocol> realization;
};
Expected<PreparedProof>
prepareProof(ModuleOp source, const NativeProofPolicy &policy,
             MathematicalSelectionPolicy mathematicalSelection,
             const protocol::OracleRealizationPolicy &oracleSelection) {
  if (!source || failed(zkc::admitStage(source)))
    return error("native-proof-source");
  uint64_t preparationAllowance = 1000000;
  if (!reserveConstructionSource(source, preparationAllowance))
    return error("native-construction-preparation-capacity");
  auto originalOwner = OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
  source = *originalOwner;
  auto original = unit(source);
  if (!original || original.getProfile() != pir::Profile::Protocol)
    return error("native-proof-source");
  // The selected entry and construction execute; unrelated declarations,
  // such as an uncalled helper or protocol, do not take part in this check.
  auto entry = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(original, policy.entry));
  if (!entry)
    return error("native-proof-entry");
  std::optional<protocol::ConstructionPlan> construction;
  SmallVector<protocol::ConstructionInvocation> invocations;
  SymbolTableCollection constructionSymbols;
  auto records = original.getBody().front().getOps<pir::ConstructionOp>();
  if (!policy.construction.empty()) {
    auto record =
        constructionSymbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
            original,
            StringAttr::get(source.getContext(), policy.construction));
    if (!record)
      return error("native-proof-construction-selection");
    auto resolved =
        protocol::resolveConstructionPlan(record, constructionSymbols);
    if (!resolved)
      return resolved.takeError();
    auto &checked = resolved->plan;
    if (resolved->definitions.size() !=
            size_t(std::distance(records.begin(), records.end())) ||
        checked.target.getValue() != policy.entry ||
        checked.suite != policy.suite ||
        !llvm::equal(checked.services, policy.services))
      return error("native-proof-construction-selection");
    if (bool(checked.codec) !=
        (policy.format == protocol::ProofFormat::RawBytes))
      return error("native-proof-format");
    construction = std::move(checked);
    invocations = std::move(resolved->invocations);
  } else if (!records.empty())
    return error("native-proof-construction-selection");
  SymbolTable originalSymbols(original);
  auto occurrenceMap = origins(entry, originalSymbols, invocations);
  if (!occurrenceMap)
    return occurrenceMap.takeError();
  // Only the selected construction closure can consume the managed root.
  // Protocol data ports and unrelated scoped functions cannot introduce one.
  llvm::DenseSet<Operation *> authorized;
  if (construction &&
      construction->root == protocol::ConstructionPlan::Root::Host) {
    SmallVector<func::FuncOp> pending;
    for (const auto &rule : construction->rules)
      pending.push_back(
          originalSymbols.lookup<func::FuncOp>(rule.handler.getValue()));
    for (const auto &invocation : invocations)
      pending.push_back(
          originalSymbols.lookup<func::FuncOp>(invocation.handler.getValue()));
    while (!pending.empty()) {
      auto function = pending.pop_back_val();
      if (!function || !authorized.insert(function).second)
        continue;
      function.walk([&](func::CallOp apply) {
        pending.push_back(
            originalSymbols.lookup<func::FuncOp>(apply.getCallee()));
      });
    }
  }
  bool transcript = false;
  bool allowed = false;
  auto checkType = [&](Type type) {
    type.walk([&](Type nested) {
      if (auto cap = dyn_cast<runtime::CapabilityType>(nested))
        transcript |= cap.getKind() == runtime::CapabilityKind::Transcript &&
                      (!allowed || cap.getIdentity() != policy.suite);
    });
  };
  original.walk([&](Operation *op) {
    auto function = dyn_cast<func::FuncOp>(op);
    if (!function)
      function = op->getParentOfType<func::FuncOp>();
    allowed = (function && authorized.contains(function)) ||
              (isa<pir::ConstructionOp>(op) && construction &&
               construction->root == protocol::ConstructionPlan::Root::Host);
    if (auto binding = dyn_cast<runtime::BindingOp>(op)) {
      auto *effects = protocol::operationContracts(binding.getContract());
      auto arguments = binding.getArguments();
      // A declaration exposes its callable ABI without owning a transcript.
      // Every use still has to occur in an authorized handler below. Merely
      // declaring a managed operation must not authorize an unselected body.
      allowed =
          construction &&
          construction->root == protocol::ConstructionPlan::Root::Host &&
          effects && effects->managedHistory && !arguments.empty() &&
          arguments[0] == StringAttr::get(source.getContext(), policy.suite);
    }
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
  });
  if (transcript)
    return error("native-proof-authored-transcript");
  SmallVector<mathematical::ApplicationStart> starts;
  for (const auto &invocation : invocations)
    starts.push_back({policy.entry, invocation.site, invocation.inputs});
  // Keep original root ports stable: native proof bindings refer to authored
  // data, not imported logical oracle graphs or appended realization stores.
  bool logicalPort = false;
  entry.getFunctionType().walk([&](Type type) {
    logicalPort |= isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
  });
  if (logicalPort)
    return error("native-proof-oracle-interface");
  // Policy/interface refusals precede selected dependency analysis. The same
  // checks run again on the independently prepared subject in admit().
  auto interface =
      admitInterface(entry, policy, construction ? &*construction : nullptr);
  if (!interface)
    return interface.takeError();
  auto execution = protocol::readSourceExecutionClosure(original);
  if (!execution)
    return execution.takeError();
  auto originalExecution =
      std::make_shared<const protocol::SourceExecutionClosure>(
          std::move(*execution));
  if (construction)
    if (auto e = checkConstructionMessageDirections(entry, *construction,
                                                    preparationAllowance))
      return std::move(e);
  auto joint = detail::prepareNativeConstruction(
      source, entry, *originalExecution, policy,
      construction ? &*construction : nullptr, invocations,
      preparationAllowance);
  if (!joint)
    return joint.takeError();
  auto preparation = mathematical::PreparedProtocol::prepare(
      source, mathematicalSelection, nullptr, starts);
  if (!preparation ||
      failed(preparation->consumeConstruction(policy.construction)) ||
      failed(preparation->selectEntries({policy.entry})))
    return error("native-proof-preparation");
  auto realization = mathematical::RealizedProtocol::realize(
      std::move(*preparation), oracleSelection);
  if (!realization)
    return realization.takeError();
  auto owner =
      std::make_shared<mathematical::RealizedProtocol>(std::move(*realization));
  auto actualOrigins =
      detail::realizedNativeOrigins(*owner, policy.entry, *occurrenceMap);
  if (!actualOrigins)
    return actualOrigins.takeError();
  auto candidate = std::move(actualOrigins->candidate);
  if (!candidate || !unit(*candidate))
    return error("native-proof-preparation");
  std::shared_ptr<const protocol::SourceExecutionClosure> realizedExecution;
  if (joint->needsRealization()) {
    auto actualExecution =
        protocol::readSourceExecutionClosure(unit(*candidate));
    if (!actualExecution)
      return actualExecution.takeError();
    realizedExecution =
        std::make_shared<const protocol::SourceExecutionClosure>(
            std::move(*actualExecution));
    auto actualEntry =
        SymbolTable(unit(*candidate)).lookup<pir::MathematicalOp>(policy.entry);
    if (auto e = joint->resolveRealization(
            *candidate, actualEntry, *realizedExecution, policy,
            construction ? &*construction : nullptr, invocations))
      return std::move(e);
  }
  return PreparedProof{
      std::move(originalOwner), std::move(originalExecution),
      std::move(candidate),     std::move(realizedExecution),
      std::move(*joint),        std::move(actualOrigins->origins),
      std::move(construction),  std::move(invocations),
      std::move(owner)};
}
} // namespace
Expected<NativeProofPolicy> selectNativeProofDraws(
    ModuleOp source, const NativeProofPolicy &selection,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  if (auto e = checkNativeProofPolicy(selection, true))
    return std::move(e);
  auto policy = selection;
  auto prepared =
      prepareProof(source, policy, mathematicalSelection, oracleSelection);
  if (!prepared)
    return prepared.takeError();
  SymbolTable symbols(unit(*prepared->module));
  auto program = symbols.lookup<pir::MathematicalOp>(policy.entry);
  auto admitted =
      admit(program, policy, prepared->origins, DrawSelection::Service,
            prepared->construction ? &*prepared->construction : nullptr);
  if (!admitted)
    return admitted.takeError();
  if (prepared->construction)
    if (auto e = admitConstruction(program, *prepared->construction,
                                   admitted->events))
      return std::move(e);
  policy.draws = std::move(admitted->draws);
  // Every paired loop needs actual count correspondence, including loops
  // without events. Reverse requests additionally need a deterministic
  // source relation. Construction checks the emitted candidate separately;
  // selecting an occurrence never certifies its payload or iteration count.
  auto projected = prepared->realization->project(false);
  if (!projected)
    return error("native-proof-projection");
  auto requests = detail::planNativeRequests(
      unit(*projected), policy, admitted->events, prepared->realization.get());
  if (!requests)
    return requests.takeError();
  if (auto e = prepared->joint.dischargeRequests(*requests))
    return std::move(e);
  if (auto e = checkNativeProofPolicy(policy))
    return std::move(e);
  return policy;
}
static Expected<NativeProofConstruction> constructNativeProofChecked(
    ModuleOp source, const NativeProofPolicy &policy,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection,
    ModuleOp supplied = {}, json::Value *bindingView = nullptr,
    NativeProofBindingProfile bindingProfile =
        NativeProofBindingProfile::NativeHistory) {
  // Validate public API callers too; policy structs are not admission tokens.
  if (auto e = checkNativeProofPolicy(policy))
    return std::move(e);
  auto preparedSource =
      prepareProof(source, policy, mathematicalSelection, oracleSelection);
  if (!preparedSource)
    return preparedSource.takeError();
  // Binding analysis borrows this immutable prepared source through the final
  // candidate check. Keep its owner distinct from the mutable projection.
  auto &sourceSnapshot = preparedSource->module;
  auto prepared = unit(*sourceSnapshot);
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
  SmallVector<Type> bindingInputs(program.getFunctionType().getInputs());
  // Consume the same checked edge used by ordinary execution. Projection
  // checks an independent copy while the source/realization owner stays alive.
  auto candidate = preparedSource->realization->project(false);
  if (!candidate)
    return error("native-proof-projection");
  auto projected = OwningOpRef<ModuleOp>(cast<ModuleOp>((*candidate)->clone()));
  auto *plan =
      preparedSource->construction ? &*preparedSource->construction : nullptr;
  // This projection came from the same immutable checked realization of the
  // original used by joint preparation. actualOrigins/admit checked its event
  // associations. The actual request planner now closes every reverse-value,
  // branch and recurrence obligation before Emitter can mutate the candidate.
  auto requests =
      detail::planNativeRequests(unit(*projected), policy, admitted->events,
                                 preparedSource->realization.get());
  if (!requests)
    return requests.takeError();
  if (auto e = preparedSource->joint.dischargeRequests(*requests))
    return std::move(e);
  json::Array exportedPlan;
  if (!policy.suite.empty() || plan)
    if (auto e =
            Emitter(unit(*candidate), policy, plan, preparedSource->invocations)
                .run(*admitted, exportedPlan, *requests, preparedSource->joint))
      return std::move(e);
  if (failed(zkc::admitStage(*candidate)))
    return error("native-proof-construction");
  if (auto e = detail::verifyNativeTranscript(
          *projected, *candidate, policy, admitted->events, plan,
          preparedSource->invocations, preparedSource->realization.get()))
    return std::move(e);
  if (supplied && !(plan && plan->codec))
    if (auto e = detail::verifyNativeTranscript(
            *projected, supplied, policy, admitted->events, plan,
            preparedSource->invocations, preparedSource->realization.get()))
      return error("native-proof-correspondence", toString(std::move(e)));
  json::Array codecPlan;
  if (plan && plan->codec) {
    auto beforeCodec =
        OwningOpRef<ModuleOp>(cast<ModuleOp>((*candidate)->clone()));
    auto encoded = detail::constructNativeCodec(*candidate, policy, *plan,
                                                admitted->events, exportedPlan);
    if (!encoded)
      return encoded.takeError();
    if (auto e =
            detail::verifyNativeCodec(*beforeCodec, *candidate, policy, *plan,
                                      admitted->events, exportedPlan, *encoded))
      return std::move(e);
    if (supplied)
      if (auto e = detail::verifyNativeCodec(*beforeCodec, supplied, policy,
                                             *plan, admitted->events,
                                             exportedPlan, *encoded))
        return error("native-proof-correspondence", toString(std::move(e)));
    codecPlan = std::move(*encoded);
    admitted->wireSites.clear();
  }
  if (plan)
    exportedPlan.push_back(std::move(codecPlan));
  json::Value descriptor(json::Array{
      "zkc.native-proof-descriptor/0", encodeNativeProofPolicy(policy),
      "zkc.native-origin/0", std::move(admitted->sequence),
      std::move(admitted->publicBindings), std::move(admitted->messages),
      std::move(exportedPlan), std::move(admitted->witnesses),
      preparedSource->realization->normalizedSelection().str()});
  if (bindingView) {
    auto view = detail::analyzeConstructionBinding(
        supplied ? supplied : *candidate, program, bindingInputs, policy,
        bindingProfile, admitted->events, plan);
    if (!view)
      return view.takeError();
    (*view->getAsObject())["descriptor"] = descriptor;
    *bindingView = std::move(*view);
  }
  return NativeProofConstruction{std::move(candidate), std::move(descriptor),
                                 std::move(admitted->wireSites),
                                 std::move(preparedSource->realization)};
}
Expected<NativeProofConstruction>
constructNativeProof(ModuleOp source, const NativeProofPolicy &policy,
                     MathematicalSelectionPolicy mathematicalSelection,
                     const protocol::OracleRealizationPolicy &oracleSelection) {
  return constructNativeProofChecked(source, policy, mathematicalSelection,
                                     oracleSelection);
}
Error checkNativeProof(
    ModuleOp source, ModuleOp candidate, const NativeProofPolicy &policy,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  if (!source || !candidate || candidate.getContext() != source.getContext() ||
      failed(zkc::admitStage(candidate)))
    return error("native-proof-candidate");
  auto expected = constructNativeProofChecked(
      source, policy, mathematicalSelection, oracleSelection, candidate);
  if (!expected)
    return expected.takeError();
  if (!OperationEquivalence::isEquivalentTo(
          expected->module->getOperation(), candidate,
          OperationEquivalence::IgnoreLocations))
    return error("native-proof-correspondence");
  return Error::success();
}
Expected<json::Value> analyzeNativeProofBinding(
    ModuleOp source, ModuleOp candidate, const NativeProofPolicy &policy,
    NativeProofBindingProfile profile,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  if (!source || !candidate || candidate.getContext() != source.getContext() ||
      failed(zkc::admitStage(candidate)))
    return error("native-proof-candidate");
  json::Value view(nullptr);
  auto expected =
      constructNativeProofChecked(source, policy, mathematicalSelection,
                                  oracleSelection, candidate, &view, profile);
  if (!expected)
    return expected.takeError();
  if (!OperationEquivalence::isEquivalentTo(
          expected->module->getOperation(), candidate,
          OperationEquivalence::IgnoreLocations))
    return error("native-proof-correspondence");
  auto originalHash =
      detail::fingerprintIR(source, "construction-binding-capacity");
  if (!originalHash)
    return originalHash.takeError();
  auto candidateHash =
      detail::fingerprintIR(candidate, "construction-binding-capacity");
  if (!candidateHash)
    return candidateHash.takeError();
  auto &object = *view.getAsObject();
  object["source_sha256"] = *originalHash;
  object["candidate_sha256"] = *candidateHash;
  auto oracle = protocol::encodeOracleRealizationPolicy(oracleSelection);
  if (!oracle)
    return oracle.takeError();
  object["realization"] = expected->realization->realizationData();
  object["oracle_policy"] = std::move(*oracle);
  object["mathematical_policy"] = json::Object{
      {"finite_bulk", mathematicalSelection.finiteBulk},
      {"calculation_batching", mathematicalSelection.calculationBatching},
      {"fuse_vector_reductions", mathematicalSelection.vectorReductionFusion},
      {"fuse_collect_fold", mathematicalSelection.collectFoldFusion}};
  if (!jsonWithinByteLimit(view, 8 * 1024 * 1024))
    return error("construction-binding-capacity");
  return view;
}
Error checkNativeProofBinding(
    ModuleOp source, ModuleOp candidate, const NativeProofPolicy &policy,
    NativeProofBindingProfile profile, StringRef report,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  auto supplied = parseNaturalJson(report, 8 * 1024 * 1024, 64,
                                   "construction-binding-report",
                                   "construction-binding-capacity");
  if (!supplied)
    return supplied.takeError();
  auto expected =
      analyzeNativeProofBinding(source, candidate, policy, profile,
                                mathematicalSelection, oracleSelection);
  if (!expected)
    return expected.takeError();
  if (!equalNaturalJson(*supplied, *expected))
    return error("construction-binding-report");
  return Error::success();
}
} // namespace zkc

namespace zkc {
namespace {
std::string printedText(Operation *value) {
  std::string text;
  raw_string_ostream out(text);
  value->print(out, OpPrintingFlags().printGenericOpForm());
  return text;
}
std::string sha256Identity(StringRef text) {
  return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(text)), true);
}
// The catalogue identities an exported logical type or binding names: its
// installed domain arguments at any depth and its random-service types, with
// the fields those services sample. Resource slots are not catalogue rows.
void collectIdentities(const json::Value &value, llvm::StringSet<> &domains,
                       llvm::StringSet<> &services) {
  const auto *array = value.getAsArray();
  if (!array)
    return;
  if (array->size() == 3 && (*array)[0].getAsString() == StringRef("domain")) {
    auto sort = (*array)[1].getAsString();
    auto identity = (*array)[2].getAsString();
    if (sort && identity &&
        protocol::installedDomains().identitySort(*identity) == *sort)
      domains.insert(*identity);
    return;
  }
  if (array->size() == 2 && (*array)[0].getAsString() == StringRef("service")) {
    if (auto contract = (*array)[1].getAsString()) {
      services.insert(*contract);
      domains.insert(protocol::randomServiceField(*contract));
    }
    return;
  }
  for (const auto &child : *array)
    collectIdentities(child, domains, services);
}
// Identities of exported instruction rows: bindings, result types and loop
// block arguments, nested bodies included. Attributes are not type positions.
void collectInstructionIdentities(const json::Array &instructions,
                                  llvm::StringSet<> &domains,
                                  llvm::StringSet<> &services) {
  for (const auto &value : instructions) {
    const auto &row = *value.getAsArray();
    collectIdentities(row[2], domains, services);
    collectIdentities(row[4], domains, services);
    for (const auto &region : *row[5].getAsArray()) {
      const auto &parts = *region.getAsArray();
      collectIdentities(parts[0], domains, services);
      collectInstructionIdentities(*parts[1].getAsArray(), domains, services);
    }
  }
}
// Reads the supplied, independently checked candidate. It never reconstructs an
// expected participant or substitutes a mathematical reference. References are
// absolute positions in a scoped environment: inputs first, then every
// operation result in execution order. A loop body extends the environment at
// the loop with its block arguments; after the loop, its results take the place
// of the body's values. Calls to helpers inserted by construction are expanded
// with their formals bound to the actual operands; calls to helpers of the
// original source remain calls.
class ParticipantExporter {
  SymbolTable symbols, sourceSymbols;
  const protocol::SourceExecutionClosure &execution;
  const StringMap<Origin> &sourceOrigins;
  llvm::DenseMap<Value, unsigned> references;
  struct CoordinateAlias {
    Value value;
    unsigned slot;
  };
  using Coordinate = SmallVector<CoordinateAlias>;
  SmallVector<Coordinate> coordinates;
  std::string entryName;
  unsigned next = 0, work = 0, exported = 0;
  size_t encodedBytes = 0, frameWork = 0;

  // Only lexical state is restored. Every arm and expanded helper consumes the
  // same operation, instruction, frame-work and byte allowances.
  struct Frame {
    ParticipantExporter &owner;
    llvm::DenseMap<Value, unsigned> references;
    SmallVector<Coordinate> coordinates;
    unsigned next;
    bool restoreNext;
    Frame(ParticipantExporter &owner, bool restoreNext = true)
        : owner(owner), references(owner.references),
          coordinates(owner.coordinates), next(owner.next),
          restoreNext(restoreNext) {}
    ~Frame() {
      owner.references = std::move(references);
      owner.coordinates = std::move(coordinates);
      if (restoreNext)
        owner.next = next;
    }
  };
  struct Ending {
    StringRef operation;
    SmallVector<unsigned> values;
    SmallVector<Value> forwarded = {};
  };
  Error chargeFrame(size_t amount) {
    if (amount > 100000 - frameWork)
      return error("constructed-participant-limit");
    frameWork += amount;
    return Error::success();
  }
  size_t coordinateSize() const {
    size_t size = coordinates.size();
    for (const auto &coordinate : coordinates)
      size += coordinate.size();
    return size;
  }
  // A slot alone is never evidence of forwarding. Only the actual SSA
  // operand can transfer lineage to a new formal, including duplicate captures.
  Error forwardCoordinate(Value actual, Value formal, unsigned slot,
                          SmallVectorImpl<Coordinate> &target) {
    for (auto [i, coordinate] : enumerate(coordinates)) {
      if (auto e = chargeFrame(1 + coordinate.size() + target[i].size()))
        return e;
      if (any_of(coordinate, [&](const CoordinateAlias &alias) {
            return alias.value == actual;
          }))
        target[i].push_back({formal, slot});
    }
    return Error::success();
  }
  Error chargeBytes(const json::Array &value) {
    size_t amount = printJson(json::Value(json::Array(value))).size();
    if (amount > 1024 * 1024 - encodedBytes)
      return error("constructed-participant-limit");
    encodedBytes += amount;
    return Error::success();
  }
  static json::Array indices(ArrayRef<unsigned> values) {
    json::Array result;
    for (unsigned value : values)
      result.push_back(value);
    return result;
  }

  Expected<unsigned> reference(Value value) {
    auto found = references.find(value);
    if (found == references.end())
      return error("constructed-participant-reference");
    return found->second;
  }
  Expected<json::Array> operands(ValueRange inputs) {
    json::Array result;
    for (Value operand : inputs) {
      auto index = reference(operand);
      if (!index)
        return index.takeError();
      result.push_back(*index);
    }
    return result;
  }
  Expected<json::Value> binding(Operation &op) {
    auto symbol = op.getAttrOfType<FlatSymbolRefAttr>("binding");
    if (!symbol)
      return json::Array{};
    auto declaration =
        dyn_cast_or_null<runtime::BindingOp>(symbols.lookup(symbol.getValue()));
    if (!declaration)
      return error("constructed-participant-binding");
    auto data = exportBindingData(declaration);
    if (!data)
      return data.takeError();
    return std::move(*data);
  }
  Expected<json::Array> attributes(Operation &op) {
    json::Array result;
    for (NamedAttribute attribute : op.getAttrs()) {
      // The admitted CFG reader already consumed these successor segments.
      // step.inputs and step.regions carry the checked logical association.
      if (isa<exec::MatchOp>(op) &&
          attribute.getName() == "successor_operand_segments")
        continue;
      if (attribute.getName() == "parameters" && isa<exec::ApplyOp>(op)) {
        auto declaration = symbols.lookup<runtime::BindingOp>(
            cast<exec::ApplyOp>(op).getBinding());
        if (!declaration)
          return error("constructed-participant-binding");
        auto parameters = exportInvocationParametersData(
            declaration.getContract(), declaration.getArgumentsAttr(),
            cast<exec::ApplyOp>(op).getParametersAttr());
        if (!parameters)
          return parameters.takeError();
        json::Array values;
        for (auto &parameter : *parameters)
          values.push_back(json::Array{"parameter", std::move(parameter)});
        result.push_back(json::Array{attribute.getName().getValue().str(),
                                     json::Array{"array", std::move(values)}});
        continue;
      }
      auto value = exportSemanticAttributeData(attribute.getValue());
      if (!value)
        return value.takeError();
      result.push_back(
          json::Array{attribute.getName().getValue().str(), std::move(*value)});
    }
    return result;
  }
  Expected<SmallVector<unsigned>> terminal(ValueRange values) {
    if (auto e = chargeFrame(values.size()))
      return std::move(e);
    SmallVector<unsigned> returned;
    for (Value value : values) {
      auto index = reference(value);
      if (!index)
        return index.takeError();
      returned.push_back(*index);
    }
    return returned;
  }
  Error emit(Operation &op, ValueRange inputs, TypeRange outputs,
             json::Array &out, json::Array regions) {
    if (++exported > 2048 || inputs.size() > 512 || outputs.size() > 512)
      return error("constructed-participant-limit");
    if (auto e = chargeFrame(inputs.size() + outputs.size()))
      return e;
    auto declaration = binding(op);
    if (!declaration)
      return declaration.takeError();
    auto arguments = operands(inputs);
    if (!arguments)
      return arguments.takeError();
    auto metadata = attributes(op);
    if (!metadata)
      return metadata.takeError();
    auto types = exportLogicalTypesData(outputs);
    if (!types)
      return types.takeError();
    json::Array instruction{op.getName().getStringRef().str(),
                            std::move(*metadata),
                            std::move(*declaration),
                            std::move(*arguments),
                            std::move(*types),
                            json::Array{}};
    if (op.getName().getStringRef() == "protocol.service_query") {
      auto site = op.getAttrOfType<StringAttr>("site");
      auto found =
          site ? sourceOrigins.find(site.getValue()) : sourceOrigins.end();
      if (found == sourceOrigins.end() ||
          !std::holds_alternative<protocol::NativeQueryOrigin>(
              found->second.event))
        return error("constructed-participant-service-origin");
      auto typed = detail::exportNativeSourceOrigin(entryName, found->second);
      if (!typed)
        return typed.takeError();
      auto origin = protocol::encodeNativeOriginTemplate(*typed);
      if (!origin)
        return origin.takeError();
      if (size_t(count_if(typed->path, [](const auto &step) {
            return step.kind == protocol::NativeOriginStep::Kind::Repeat;
          })) != coordinates.size())
        return error("constructed-participant-service-origin");
      json::Array indices;
      for (const auto &coordinate : coordinates) {
        if (coordinate.empty())
          return error("constructed-participant-service-origin");
        indices.push_back(coordinate.front().slot);
      }
      instruction.push_back(json::Array{*origin, std::move(indices)});
    }
    // Child instructions were already charged. Charge this row with an empty
    // region list, then attach the separately charged region headers.
    if (auto e = chargeBytes(instruction))
      return e;
    instruction[5] = std::move(regions);
    out.push_back(std::move(instruction));
    return Error::success();
  }

  // A selected region is closed: only payloads and explicit capture rows are
  // visible. Rebase enclosing induction coordinates through those exact rows,
  // never through equal types or an outer frame's numeric positions.
  Error enterArm(ValueRange arguments, ValueRange captures, unsigned payloads) {
    if (arguments.size() > 512)
      return error("constructed-participant-limit");
    if (arguments.size() != payloads + captures.size())
      return error("constructed-participant-branch");
    if (auto e = chargeFrame(references.size() + arguments.size() +
                             coordinates.size()))
      return e;
    SmallVector<Coordinate> localCoordinates(coordinates.size());
    for (auto [i, capture] : enumerate(captures)) {
      auto index = reference(capture);
      if (!index)
        return index.takeError();
      unsigned slot = payloads + i;
      if (auto e = forwardCoordinate(capture, arguments[slot], slot,
                                     localCoordinates))
        return e;
    }
    references.clear();
    next = 0;
    for (Value argument : arguments)
      references[argument] = next++;
    coordinates = std::move(localCoordinates);
    return Error::success();
  }
  Expected<json::Array> armRecord(TypeRange arguments, json::Array instructions,
                                  Ending ending, StringRef alternative,
                                  TypeRange payloads) {
    auto types = exportLogicalTypesData(arguments);
    if (!types)
      return types.takeError();
    auto payloadTypes = exportLogicalTypesData(payloads);
    if (!payloadTypes)
      return payloadTypes.takeError();
    json::Array result{
        std::move(*types), json::Array{},
        json::Array{ending.operation.str(), indices(ending.values)},
        alternative.str(), std::move(*payloadTypes)};
    if (auto e = chargeBytes(result))
      return std::move(e);
    result[1] = std::move(instructions);
    return result;
  }

  Expected<json::Array> selected(Operation &op, unsigned depth) {
    auto alternatives = op.getAttrOfType<ArrayAttr>("alternatives");
    if (alternatives && alternatives.size() > selectedRegionArmLimit)
      return error("constructed-participant-limit");
    if (!op.getNumOperands() || op.getNumSuccessors() || !alternatives ||
        alternatives.empty() || alternatives.size() != op.getNumRegions())
      return error("constructed-participant-branch");
    json::Array regions;
    for (auto [i, region] : enumerate(op.getRegions())) {
      if (!hasSingleElement(region))
        return error("constructed-participant-branch");
      auto alternative = dyn_cast<StringAttr>(alternatives[i]);
      auto payloads = selectedPayloadTypes(&op, i);
      if (!payloads)
        return payloads.takeError();
      Block &arm = region.front();
      SmallVector<Type> expected(*payloads);
      append_range(expected, op.getOperands().drop_front().getTypes());
      if (!alternative || arm.getArgumentTypes() != TypeRange(expected) ||
          arm.empty() || arm.back().getOperandTypes() != op.getResultTypes())
        return error("constructed-participant-branch");
      if (auto e = chargeFrame(references.size() + coordinateSize()))
        return std::move(e);
      Frame frame(*this);
      if (auto e = enterArm(arm.getArguments(), op.getOperands().drop_front(),
                            payloads->size()))
        return std::move(e);
      json::Array nested;
      StringRef terminator =
          isa<data::BranchOp>(op) ? "data.yield" : "protocol.yield";
      auto yielded = body(arm, terminator, depth + 1, nested);
      if (!yielded)
        return yielded.takeError();
      auto record = armRecord(arm.getArgumentTypes(), std::move(nested),
                              {terminator, std::move(*yielded)},
                              alternative.getValue(), *payloads);
      if (!record)
        return record.takeError();
      regions.push_back(std::move(*record));
    }
    return regions;
  }

  Expected<json::Array>
  selectedHelper(const protocol::SourceExecutionStep &step, unsigned depth) {
    auto &op = *step.operation;
    if (step.regions.size() > selectedRegionArmLimit)
      return error("constructed-participant-limit");
    if (step.inputs.empty() || step.regions.empty())
      return error("constructed-participant-branch");
    auto alternatives = op.getAttrOfType<ArrayAttr>("alternatives");
    bool boolean = isa<exec::TestOp>(op);
    auto variant = dyn_cast<data::VariantType>(step.inputs.front().getType());
    if (boolean ? step.regions.size() != 2 ||
                      !step.inputs.front().getType().isSignlessInteger(1)
                : !variant || !alternatives ||
                      alternatives.size() != step.regions.size() ||
                      variant.getAlternatives().size() != step.regions.size())
      return error("constructed-participant-branch");
    json::Array regions;
    for (auto [i, regionFunction] : enumerate(step.regions)) {
      auto function = regionFunction;
      StringRef label = i ? "else" : "then";
      SmallVector<Type> payloads;
      if (!boolean) {
        auto alternative = variant.getAlternatives()[i];
        label = alternative.getLabel().getValue();
        if (cast<StringAttr>(alternatives[i]).getValue() != label)
          return error("constructed-participant-branch");
        append_range(payloads, alternative.getPayload());
      }
      auto outcome = function.getFunctionType().getNumResults() == 1
                         ? dyn_cast<exec::OutcomeType>(
                               function.getFunctionType().getResult(0))
                         : exec::OutcomeType();
      SmallVector<Type> expected(payloads);
      append_range(expected, ValueRange(step.inputs).drop_front().getTypes());
      if (!function->hasAttr("runtime.region") || !outcome ||
          TypeRange(outcome.getPayload()) !=
              ValueRange(step.outputs).getTypes() ||
          TypeRange(function.getFunctionType().getInputs().drop_front()) !=
              TypeRange(expected))
        return error("constructed-participant-branch");
      if (auto e = chargeFrame(references.size() + coordinateSize()))
        return std::move(e);
      Frame frame(*this);
      auto arguments = function.getArguments().drop_front();
      if (auto e = enterArm(arguments, ValueRange(step.inputs).drop_front(),
                            payloads.size()))
        return std::move(e);
      json::Array nested;
      auto ending = helperBody(function, depth + 1, nested);
      if (!ending)
        return ending.takeError();
      auto record =
          armRecord(ValueRange(arguments).getTypes(), std::move(nested),
                    std::move(*ending), label, payloads);
      if (!record)
        return record.takeError();
      regions.push_back(std::move(*record));
    }
    return regions;
  }

  Error helper(FlatSymbolRefAttr callee, ValueRange inputs, ValueRange outputs,
               unsigned depth, json::Array &out, Operation *invocation) {
    if (depth > 64)
      return error("constructed-participant-limit");
    auto function = symbols.lookup<func::FuncOp>(callee.getValue());
    auto signature = protocol::scopedDataSignature(function);
    if (!signature || signature.getNumInputs() != inputs.size() ||
        TypeRange(signature.getResults()) != outputs.getTypes())
      return error("constructed-participant-helper");
    if (inputs.size() > 512 || signature.getNumResults() > 512)
      return error("constructed-participant-limit");
    if (sourceSymbols.lookup(callee.getValue())) {
      if (auto e = emit(*invocation, inputs, signature.getResults(), out, {}))
        return e;
      for (Value result : outputs)
        references[result] = next++;
      return Error::success();
    }
    if (auto e = chargeFrame(references.size() + coordinateSize() +
                             inputs.size() + outputs.size()))
      return e;
    SmallVector<unsigned> values;
    SmallVector<Coordinate> returnedCoordinates(coordinates.size());
    {
      Frame frame(*this, false);
      // Inline expansion retains actual slots. Only SSA operand/formal and
      // returned-value/result forwarding can add aliases to those slots.
      auto actuals = terminal(inputs);
      if (!actuals)
        return actuals.takeError();
      references.clear();
      for (auto [formal, actual, slot] :
           zip(function.getArguments().drop_front(), inputs, *actuals)) {
        references[formal] = slot;
        if (auto e = forwardCoordinate(actual, formal, slot, coordinates))
          return e;
      }
      auto ending = helperBody(function, depth, out);
      if (!ending)
        return ending.takeError();
      // A stopped helper has no normal values. A nonempty ABI would require a
      // separate call-region carrier; do not manufacture references for it.
      if (ending->operation == "exec.reject" && signature.getNumResults())
        return error("constructed-participant-return");
      if (ending->values.size() != outputs.size() ||
          ending->forwarded.size() != outputs.size())
        return error("constructed-participant-helper");
      values = std::move(ending->values);
      for (auto [actual, result, slot] :
           zip(ending->forwarded, outputs, values))
        if (auto e =
                forwardCoordinate(actual, result, slot, returnedCoordinates))
          return e;
    }
    for (auto [result, slot] : zip(outputs, values))
      references[result] = slot;
    for (auto [coordinate, returned] : zip(coordinates, returnedCoordinates)) {
      if (auto e = chargeFrame(returned.size()))
        return e;
      append_range(coordinate, returned);
    }
    return Error::success();
  }

  Expected<Ending> helperBody(func::FuncOp function, unsigned depth,
                              json::Array &out) {
    if (depth > 64)
      return error("constructed-participant-limit");
    auto found = execution.bodies.find(function.getSymName().str());
    if (found == execution.bodies.end())
      return error("constructed-participant-helper");
    for (const auto &step : found->second) {
      if (++work > 4096)
        return error("constructed-participant-limit");
      auto &op = *step.operation;
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        auto values = terminal(step.inputs);
        if (!values)
          return values.takeError();
        if (auto e = chargeFrame(step.inputs.size()))
          return std::move(e);
        return Ending{op.getName().getStringRef(), std::move(*values),
                      SmallVector<Value>(step.inputs)};
      }
      if (isa<exec::RejectOp>(op)) {
        if (auto e = emit(op, {}, {}, out, {}))
          return std::move(e);
        return Ending{"exec.reject", {}};
      }
      if (isa<exec::TestOp, exec::MatchOp>(op)) {
        auto regions = selectedHelper(step, depth);
        if (!regions)
          return regions.takeError();
        if (auto e = emit(op, step.inputs, ValueRange(step.outputs).getTypes(),
                          out, std::move(*regions)))
          return std::move(e);
        for (Value result : step.outputs)
          references[result] = next++;
        continue;
      }
      if (!step.regions.empty())
        return error("constructed-participant-control",
                     op.getName().getStringRef());
      if (auto call = dyn_cast<func::CallOp>(op)) {
        if (auto e = helper(call.getCalleeAttr(), step.inputs, step.outputs,
                            depth + 1, out, &op))
          return std::move(e);
        continue;
      }
      if (!isa<exec::ApplyOp, exec::BooleanOp, exec::VariantOp>(op))
        return error("constructed-participant-operation",
                     op.getName().getStringRef());
      if (auto e = emit(op, step.inputs, ValueRange(step.outputs).getTypes(),
                        out, {}))
        return std::move(e);
      for (auto result : step.outputs)
        references[result] = next++;
    }
    return error("constructed-participant-return");
  }

public:
  ParticipantExporter(pir::ProtocolModuleOp module,
                      pir::ProtocolModuleOp source,
                      const StringMap<Origin> &sourceOrigins,
                      const protocol::SourceExecutionClosure &execution)
      : symbols(module), sourceSymbols(source), execution(execution),
        sourceOrigins(sourceOrigins) {}

  // Exports one block into `out`. `terminator` names the operation that must
  // end it; its operand references are returned.
  Expected<SmallVector<unsigned>> body(Block &block, StringRef terminator,
                                       unsigned depth, json::Array &out) {
    if (depth > 64)
      return error("constructed-participant-limit");
    for (Operation &op : block) {
      if (++work > 4096)
        return error("constructed-participant-limit");
      StringRef name = op.getName().getStringRef();
      if (name == terminator) {
        if (&op != &block.back())
          return error("constructed-participant-return");
        return terminal(op.getOperands());
      }
      if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        if (auto e = helper(call.getCalleeAttr(), call.getInputs(),
                            op.getResults(), depth + 1, out, &op))
          return std::move(e);
        continue;
      }
      if (name == "protocol.loop") {
        if (op.getNumRegions() != 1 || !hasSingleElement(op.getRegion(0)) ||
            op.getNumSuccessors())
          return error("constructed-participant-control", name);
        Block &loop = op.getRegion(0).front();
        unsigned outer = next;
        auto carried = op.getAttrOfType<IntegerAttr>("carried");
        if (!carried || carried.getInt() < 0 ||
            uint64_t(carried.getInt()) >= loop.getNumArguments() ||
            loop.getNumArguments() != op.getNumOperands())
          return error("constructed-participant-control", name);
        if (loop.getNumArguments() > 512)
          return error("constructed-participant-limit");
        if (auto e = chargeFrame(references.size() + coordinateSize() +
                                 loop.getNumArguments() + 2))
          return std::move(e);
        json::Array nested;
        json::Array yieldedList;
        {
          Frame frame(*this);
          for (BlockArgument argument : loop.getArguments())
            references[argument] = next++;
          // Invariant captures forward their actual operands each iteration.
          // Initial carried values do not: the next yield can replace them.
          unsigned captures = 1 + unsigned(carried.getInt());
          for (unsigned i = captures; i < loop.getNumArguments(); ++i)
            if (auto e =
                    forwardCoordinate(op.getOperand(i), loop.getArgument(i),
                                      outer + i, coordinates))
              return std::move(e);
          coordinates.push_back(Coordinate{{loop.getArgument(0), outer}});
          auto yielded = body(loop, "protocol.yield", depth + 1, nested);
          if (!yielded)
            return yielded.takeError();
          yieldedList = indices(*yielded);
        }
        auto arguments = exportLogicalTypesData(loop.getArgumentTypes());
        if (!arguments)
          return arguments.takeError();
        json::Array region{std::move(*arguments), json::Array{},
                           std::move(yieldedList)};
        if (auto e = chargeBytes(region))
          return std::move(e);
        region[1] = std::move(nested);
        if (auto e = emit(op, op.getOperands(), op.getResultTypes(), out,
                          json::Array{std::move(region)}))
          return std::move(e);
        for (Value result : op.getResults())
          references[result] = next++;
        continue;
      }
      if (isa<pir::ParticipantBranchOp, data::BranchOp>(op)) {
        auto regions = selected(op, depth);
        if (!regions)
          return regions.takeError();
        if (auto e = emit(op, op.getOperands(), op.getResultTypes(), out,
                          std::move(*regions)))
          return std::move(e);
        for (Value result : op.getResults())
          references[result] = next++;
        continue;
      }
      if (op.getNumRegions() || op.getNumSuccessors())
        return error("constructed-participant-control", name);
      if (!(name.starts_with("algebra.") || name.starts_with("arith.") ||
            name.starts_with("crypto.") || name.starts_with("data.") ||
            name == "protocol.receive" || name == "protocol.send" ||
            name == "protocol.service_query" || name == "protocol.guard" ||
            name == "protocol.finish_if"))
        return error("constructed-participant-operation", name);
      if (auto e = emit(op, op.getOperands(), op.getResultTypes(), out,
                        json::Array{}))
        return std::move(e);
      for (Value result : op.getResults())
        references[result] = next++;
    }
    return error("constructed-participant-return");
  }

  Expected<json::Value> run(pir::ParticipantOp participant, StringRef source,
                            StringRef candidate,
                            const NativeProofPolicy &policy) {
    Block &entry = participant.getBody().front();
    entryName = policy.entry;
    auto type = participant.getFunctionType();
    if (entry.getNumArguments() > 512 || type.getNumResults() > 512)
      return error("constructed-participant-limit");
    if (auto e = chargeFrame(entry.getNumArguments()))
      return std::move(e);
    for (BlockArgument argument : entry.getArguments())
      references[argument] = next++;
    json::Array instructions;
    auto returned = body(entry, "protocol.finish", 0, instructions);
    if (!returned)
      return returned.takeError();
    json::Array results;
    for (unsigned index : *returned)
      results.push_back(index);
    json::Array services;
    auto original = sourceSymbols.lookup<pir::MathematicalOp>(policy.entry);
    if (!original)
      return error("constructed-participant-service-interface");
    SmallVector<unsigned> roots;
    for (auto [index, roles] : enumerate(original.getInputRoles()))
      if (owns(cast<ArrayAttr>(roles), participant.getRole()) &&
          !(participant.getRole() == policy.validator &&
            is_contained(policy.services, index)))
        roots.push_back(index);
    if (auto ports = participant->getAttrOfType<ArrayAttr>("service_ports"))
      for (Attribute attribute : ports) {
        auto row = dyn_cast<ArrayAttr>(attribute);
        if (!row || row.size() != 3)
          return error("constructed-participant-service-interface");
        auto port = dyn_cast<StringAttr>(row[0]);
        auto contract = dyn_cast<StringAttr>(row[1]);
        auto input = dyn_cast<IntegerAttr>(row[2]);
        if (!port || !contract || !input || input.getInt() < 0 ||
            uint64_t(input.getInt()) >= roots.size())
          return error("constructed-participant-service-interface");
        unsigned root = roots[input.getInt()];
        auto service = dyn_cast<pir::ServiceReferenceType>(
            original.getFunctionType().getInput(root));
        if (!service || service.getContract() != contract.getValue())
          return error("constructed-participant-service-interface");
        services.push_back(
            json::Array{port.getValue().str(), participant.getRole().str(),
                        std::to_string(root), std::to_string(input.getInt()),
                        contract.getValue().str()});
      }
    auto inputs = exportLogicalTypesData(type.getInputs());
    if (!inputs)
      return inputs.takeError();
    auto outputs = exportLogicalTypesData(type.getResults());
    if (!outputs)
      return outputs.takeError();
    // The rows of every catalogue identity the participant names: its types
    // and bindings, the policy's transcript suite and its ports' services.
    llvm::StringSet<> domains, contracts;
    for (const auto &value : *inputs)
      collectIdentities(value, domains, contracts);
    for (const auto &value : *outputs)
      collectIdentities(value, domains, contracts);
    collectInstructionIdentities(instructions, domains, contracts);
    if (!policy.suite.empty())
      domains.insert(policy.suite);
    for (const auto &port : services) {
      StringRef contract = *(*port.getAsArray())[4].getAsString();
      contracts.insert(contract);
      domains.insert(protocol::randomServiceField(contract));
    }
    json::Value catalogue = protocol::exportCatalogueRows(domains, contracts);
    json::Value record(json::Array{
        "zkc.constructed-participant/0", sha256Identity(source),
        sha256Identity(candidate), encodeNativeProofPolicy(policy),
        participant.getSymName().str(), std::move(*inputs), std::move(*outputs),
        std::move(instructions), std::move(results), std::move(services),
        std::move(catalogue)});
    if (printJson(record).size() > 1024 * 1024)
      return error("constructed-participant-limit");
    return record;
  }
};
Expected<json::Value>
exportCheckedParticipant(ModuleOp source, ModuleOp candidate,
                         StringRef sourceBytes, const NativeProofPolicy &policy,
                         const StringMap<Origin> &sourceOrigins,
                         ConstructedParticipantRole role) {
  auto module = unit(candidate);
  auto original = unit(source);
  if (!module || !original)
    return error("constructed-participant-module");
  pir::ParticipantOp selected;
  StringRef selectedRole = role == ConstructedParticipantRole::Producer
                               ? policy.producer
                               : policy.validator;
  StringRef refusal = role == ConstructedParticipantRole::Producer
                          ? "constructed-participant-producer"
                          : "constructed-participant-validator";
  for (auto participant : module.getBody().front().getOps<pir::ParticipantOp>())
    if (participant.getInstance() == policy.entry &&
        participant.getRole() == selectedRole) {
      if (selected)
        return error(refusal);
      selected = participant;
    }
  if (!selected)
    return error(refusal);
  auto execution = protocol::readSourceExecutionClosure(module);
  if (!execution)
    return execution.takeError();
  return ParticipantExporter(module, original, sourceOrigins, *execution)
      .run(selected, sourceBytes, printedText(candidate.getOperation()),
           policy);
}
} // namespace

Expected<json::Value> exportConstructedParticipant(
    ModuleOp source, ModuleOp candidate, StringRef sourceBytes,
    const NativeProofPolicy &policy,
    MathematicalSelectionPolicy mathematicalSelection,
    ConstructedParticipantRole role,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  if (auto e = checkNativeProof(source, candidate, policy,
                                mathematicalSelection, oracleSelection))
    return std::move(e);
  auto prepared =
      prepareProof(source, policy, mathematicalSelection, oracleSelection);
  if (!prepared)
    return prepared.takeError();
  return exportCheckedParticipant(source, candidate, sourceBytes, policy,
                                  prepared->origins, role);
}

Expected<json::Value> exportConstructedPair(
    ModuleOp source, ModuleOp candidate, StringRef sourceBytes,
    const NativeProofPolicy &policy,
    MathematicalSelectionPolicy mathematicalSelection,
    const protocol::OracleRealizationPolicy &oracleSelection) {
  if (auto e = checkNativeProof(source, candidate, policy,
                                mathematicalSelection, oracleSelection))
    return std::move(e);
  auto prepared =
      prepareProof(source, policy, mathematicalSelection, oracleSelection);
  if (!prepared)
    return prepared.takeError();
  auto producer = exportCheckedParticipant(
      source, candidate, sourceBytes, policy, prepared->origins,
      ConstructedParticipantRole::Producer);
  if (!producer)
    return producer.takeError();
  auto validator = exportCheckedParticipant(
      source, candidate, sourceBytes, policy, prepared->origins,
      ConstructedParticipantRole::Validator);
  if (!validator)
    return validator.takeError();
  return json::Array{"zkc.constructed-pair/0", std::move(*producer),
                     std::move(*validator)};
}
} // namespace zkc
