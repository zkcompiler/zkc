#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<ConstructionPlan>
readConstructionPlan(protocol_ir::ConstructionOp record,
                     SymbolTableCollection &symbols) {
  auto fail = [](StringRef detail) {
    return error("protocol-construction", detail);
  };
  if (!record || failed(record->getName().verifyInvariants(record)))
    return fail("invalid construction record");
  for (auto attr : record->getAttrs())
    if (!is_contained(record.getAttributeNames(), attr.getName().getValue()))
      return fail("unexpected construction attribute");
  auto target = symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
      record, record.getTargetAttr());
  if (!target || failed(target->getName().verifyInvariants(target)))
    return fail("construction target must be a protocol definition");
  auto signature = target.getFunctionType();
  auto service = record.getService();
  if (service < 0 || uint64_t(service) >= signature.getNumInputs() ||
      !isa<protocol_ir::ServiceReferenceType>(signature.getInput(service)) ||
      target.getInputRoles().size() != signature.getNumInputs())
    return fail("replacement must select a protocol service input");
  if (record.getProvider().empty() || record.getProvider().size() > 65536 ||
      record.getState().size() > 1024 || record.getRules().size() > 2048 ||
      record.getApplications().size() > 2048)
    return fail("invalid or oversized construction selection");
  if (record.getRoot() != "local" && record.getRoot() != "host")
    return fail("unknown construction root");
  ConstructionPlan plan{record.getRoot() == "local"
                            ? ConstructionPlan::Root::Local
                            : ConstructionPlan::Root::Host,
                        FlatSymbolRefAttr::get(record),
                        record.getTargetAttr(),
                        record.getInitializerAttr(),
                        record.getProvider().str(),
                        record.getSuite().str(),
                        unsigned(service),
                        record.getNativeBase(),
                        {},
                        {},
                        std::nullopt,
                        {},
                        record.getRootOnly()};
  llvm::StringSet<> calls;
  for (auto item : record.getApplications()) {
    auto application = dyn_cast<DictionaryAttr>(item);
    auto child = application
                     ? application.getAs<FlatSymbolRefAttr>("construction")
                     : FlatSymbolRefAttr{};
    auto site =
        application ? application.getAs<StringAttr>("site") : StringAttr{};
    if (!application || application.size() != 2 || !child || !site ||
        site.empty() || site.size() > 4096 ||
        !calls.insert(site.getValue()).second ||
        !symbols.lookupNearestSymbolFrom<protocol_ir::ConstructionOp>(record,
                                                                      child))
      return fail("invalid or duplicate child construction selection");
    plan.applications.push_back({child, site.getValue().str()});
  }
  mathematical::NativeTypePolicies types(record);
  for (auto attr : record.getState()) {
    auto type = dyn_cast<TypeAttr>(attr);
    if (!type)
      return fail("state slots must be types");
    auto logical = encodeBoundType(type.getValue(), false);
    if (!logical)
      return logical.takeError();
    if (plan.root == ConstructionPlan::Root::Local &&
        (!duplicable(*logical) || !discardable(*logical)))
      return fail("source-created state requires Copy and Drop");
    auto policy = types.get(type.getValue());
    if (!policy || !policy->protocolPort)
      return fail("construction state requires a protocol port representation");
    plan.state.push_back(type.getValue());
  }
  if (plan.root == ConstructionPlan::Root::Local) {
    if (!plan.initializer)
      return fail("local root requires a factory");
    auto factory = symbols.lookupNearestSymbolFrom<local::FuncOp>(
        record, plan.initializer);
    if (!factory || failed(factory->getName().verifyInvariants(factory)) ||
        !factory.getFunctionType().getInputs().empty() ||
        !equal(factory.getResultTypes(), plan.state) || !plan.suite.empty() ||
        plan.nativeBase)
      return fail("local root requires a matching zero-argument factory");
  } else {
    if (plan.initializer || nativeChallengeField(plan.suite).empty() ||
        randomServiceField(
            cast<protocol_ir::ServiceReferenceType>(signature.getInput(service))
                .getContract()) != nativeChallengeField(plan.suite) ||
        plan.state.size() != 1 ||
        plan.state.front() !=
            local::CapabilityType::get(record.getContext(),
                                       "transcript:" + plan.suite))
      return fail("host root requires the selected managed transcript state");
  }
  auto bytes = RankedTensorType::get(
      {ShapedType::kDynamic},
      IntegerType::get(record.getContext(), 8, IntegerType::Unsigned));
  auto index = IntegerType::get(record.getContext(), 64, IntegerType::Unsigned);
  auto sharedInputs = [&](DenseI64ArrayAttr inputs,
                          SmallVectorImpl<unsigned> &ports,
                          SmallVectorImpl<Type> &parameters) -> Error {
    llvm::DenseSet<int64_t> seen;
    for (auto port : inputs.asArrayRef()) {
      if (port < 0 || uint64_t(port) >= signature.getNumInputs() ||
          !seen.insert(port).second)
        return fail("invalid or duplicate original input");
      auto owners = dyn_cast<ArrayAttr>(target.getInputRoles()[port]);
      if (!owners || owners.size() != target.getRoles().size() ||
          !all_of(owners,
                  [&](Attribute owner) {
                    return is_contained(target.getRoles(), owner);
                  }) ||
          isa<protocol_ir::ServiceReferenceType>(signature.getInput(port)))
        return fail("original input must be available at both participants");
      parameters.push_back(signature.getInput(port));
      ports.push_back(port);
    }
    return Error::success();
  };
  auto functionMatches = [&](FlatSymbolRefAttr reference, TypeRange inputs,
                             TypeRange outputs) {
    auto function =
        symbols.lookupNearestSymbolFrom<local::FuncOp>(record, reference);
    return function &&
           succeeded(function->getName().verifyInvariants(function)) &&
           equal(function.getArgumentTypes(), inputs) &&
           equal(function.getResultTypes(), outputs);
  };
  if (auto selected = record.getCodecAttr()) {
    ConstructionCodec codec;
    auto provider = selected.getAs<StringAttr>("provider");
    auto slots = selected.getAs<ArrayAttr>("record");
    auto inputs = selected.getAs<DenseI64ArrayAttr>("inputs");
    codec.initialize = selected.getAs<FlatSymbolRefAttr>("initialize");
    codec.write = selected.getAs<FlatSymbolRefAttr>("write");
    codec.finish = selected.getAs<FlatSymbolRefAttr>("finish");
    if (selected.size() != 6 || !provider || provider.empty() ||
        provider.size() > 65536 || !slots || slots.size() > 1024 || !inputs ||
        inputs.size() > 1024 || !codec.initialize || !codec.write ||
        !codec.finish || target.getRoles().size() != 2)
      return fail("invalid codec selection");
    codec.provider = provider.str();
    for (auto attr : slots) {
      auto slot = dyn_cast<TypeAttr>(attr);
      if (!slot)
        return fail("codec Record slots must be types");
      auto logical = encodeBoundType(slot.getValue(), false);
      if (!logical)
        return logical.takeError();
      auto policy = types.get(slot.getValue());
      if (!duplicable(*logical) || !discardable(*logical) || !policy ||
          !policy->protocolPort)
        return fail("codec Record requires Copy and Drop protocol data");
      codec.record.push_back(slot.getValue());
    }
    SmallVector<Type> layout;
    if (auto e = sharedInputs(inputs, codec.inputs, layout))
      return std::move(e);
    auto finishInputs = codec.record;
    finishInputs.push_back(bytes);
    if (!functionMatches(codec.initialize, layout, codec.record) ||
        !functionMatches(codec.write, codec.record, {bytes}) ||
        !functionMatches(codec.finish, finishInputs, {}))
      return fail("codec method signature differs from its selection");
    plan.codec = std::move(codec);
  }
  bool start = false;
  uint64_t siteBytes = 0;
  uint64_t remaining = 1000000;
  std::map<ConstructionRule::Kind, llvm::StringSet<>> sites;
  for (auto item : record.getRules()) {
    auto rule = dyn_cast<DictionaryAttr>(item);
    if (!rule || rule.size() != 6)
      return fail("invalid construction rule shape");
    auto kind = rule.getAs<StringAttr>("kind");
    auto handler = rule.getAs<FlatSymbolRefAttr>("handler");
    auto selectedSites = rule.getAs<ArrayAttr>("sites");
    auto inputs = rule.getAs<DenseI64ArrayAttr>("inputs");
    auto payload = rule.getAs<ArrayAttr>("payload");
    auto chunks = rule.getAs<ArrayAttr>("chunks");
    if (!kind || !handler || !selectedSites || !inputs || !payload || !chunks ||
        inputs.size() > 1024 || payload.size() > 1024 || chunks.size() > 1024 ||
        selectedSites.size() > 1024)
      return fail("invalid construction rule fields");
    uint64_t work = 1 + 2 * plan.state.size() + selectedSites.size() +
                    inputs.size() + 2 * payload.size() + 3 * chunks.size() +
                    (plan.codec ? 2 * plan.codec->record.size() : 0);
    if (work > remaining)
      return fail("construction signature work limit exceeded");
    remaining -= work;
    ConstructionRule selection;
    auto selectedKind = parseConstructionRuleKind(kind.getValue());
    if (!selectedKind)
      return fail("unknown construction rule kind");
    selection.kind = *selectedKind;
    bool codec = isCodecRule(selection.kind);
    if (codec ? !plan.codec || chunks.empty() : !chunks.empty())
      return fail("byte chunks require a codec rule and record format");
    selection.handler = handler;
    for (auto attr : payload) {
      auto type = dyn_cast<TypeAttr>(attr);
      if (!type)
        return fail("rule payload slots must be types");
      selection.payload.push_back(type.getValue());
    }
    for (auto attr : chunks) {
      auto type = dyn_cast<TypeAttr>(attr);
      if (!type || type.getValue() != bytes)
        return fail("wire chunks must be Bytes");
      selection.chunks.push_back(type.getValue());
    }
    auto &seen = sites[selection.kind];
    for (auto attr : selectedSites) {
      auto site = dyn_cast<StringAttr>(attr);
      if (!site || site.empty() || site.size() > 4096 ||
          !seen.insert(site.getValue()).second)
        return fail("invalid or duplicate construction site");
      siteBytes += site.size();
      if (siteBytes > 16 * 1024 * 1024 || seen.size() > 2048)
        return fail("construction site limit exceeded");
      selection.sites.push_back(site.str());
    }
    SmallVector<Type> parameters(plan.state), results(plan.state);
    if (selection.kind == ConstructionRule::Kind::Start) {
      if (start || !selection.sites.empty() || !selection.payload.empty())
        return fail("start must be unique and select only original inputs");
      start = true;
      if (auto e = sharedInputs(inputs, selection.inputs, parameters))
        return std::move(e);
    } else {
      if (!inputs.empty() || selection.sites.empty())
        return fail("event rules require sites and no entry input selectors");
      if (selection.kind == ConstructionRule::Kind::Query) {
        if (selection.sites.size() != 1 || selection.payload.size() != 1)
          return fail("query must select one result");
        append_range(results, selection.payload);
      } else {
        if (selection.payload.size() != selection.sites.size())
          return fail("message leaves must match the logical payload");
        if (codec) {
          switch (selection.kind) {
          case ConstructionRule::Kind::Encode:
            parameters = plan.codec->record;
            append_range(parameters, selection.payload);
            results = plan.codec->record;
            append_range(results, selection.chunks);
            break;
          case ConstructionRule::Kind::Receive:
            parameters = plan.codec->record;
            parameters.push_back(bytes);
            results = plan.codec->record;
            results.append(2 * selection.chunks.size(), index);
            break;
          case ConstructionRule::Kind::Decode:
            parameters = selection.chunks;
            results = selection.payload;
            break;
          case ConstructionRule::Kind::Wire:
            append_range(parameters, selection.chunks);
            break;
          default:
            llvm_unreachable("checked codec kind");
          }
        } else
          append_range(parameters, selection.payload);
      }
    }
    auto function =
        symbols.lookupNearestSymbolFrom<local::FuncOp>(record, handler);
    if (!function || failed(function->getName().verifyInvariants(function)))
      return fail("construction handler must be an ordinary Local function");
    // UniformIndex also receives the explicit request bound. Occurrence
    // admission checks this argument against the actual query request.
    if (selection.kind == ConstructionRule::Kind::Query &&
        function.getFunctionType().getNumInputs() == parameters.size() + 1)
      parameters.push_back(index);
    if (!functionMatches(handler, parameters, results))
      return fail("construction handler signature differs from its rule");
    plan.rules.push_back(std::move(selection));
  }
  // A codec's associations describe the same complete logical message, never
  // individually compatible leaves drawn from different groups.
  std::map<std::string, const ConstructionRule *> encoded;
  for (const auto &rule : plan.rules)
    if (rule.kind == ConstructionRule::Kind::Encode)
      encoded.emplace(rule.sites.front(), &rule);
  for (const auto &rule : plan.rules) {
    if (!isCodecRule(rule.kind))
      continue;
    auto found = encoded.find(rule.sites.front());
    if (found == encoded.end() || found->second->sites != rule.sites ||
        found->second->payload != rule.payload ||
        found->second->chunks != rule.chunks)
      return fail("codec rules disagree on message or byte shape");
  }
  for (auto kind :
       {ConstructionRule::Kind::Receive, ConstructionRule::Kind::Decode})
    if (sites[kind].size() != sites[ConstructionRule::Kind::Encode].size())
      return fail("codec requires receive and decode for each encoded message");
  if (!start && !plan.nativeBase)
    return fail("a construction without a native base requires start");
  return plan;
}
} // namespace zkc::protocol

mlir::LogicalResult zkc::protocol_ir::ConstructionOp::verifySymbolUses(
    mlir::SymbolTableCollection &symbols) {
  auto plan = protocol::readConstructionPlan(*this, symbols);
  if (!plan)
    return diagnostics::emit(emitOpError(), "protocol-construction",
                             llvm::toString(plan.takeError()));
  return mlir::success();
}
