#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
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
      record.getState().size() > 1024 || record.getRules().size() > 2048)
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
                        {}};
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
  bool start = false;
  uint64_t siteBytes = 0;
  uint64_t remaining = 1000000;
  llvm::StringSet<> sites;
  for (auto item : record.getRules()) {
    auto rule = dyn_cast<DictionaryAttr>(item);
    if (!rule || rule.size() != 5)
      return fail("invalid construction rule shape");
    auto kind = rule.getAs<StringAttr>("kind");
    auto handler = rule.getAs<FlatSymbolRefAttr>("handler");
    auto selectedSites = rule.getAs<ArrayAttr>("sites");
    auto inputs = rule.getAs<DenseI64ArrayAttr>("inputs");
    auto payload = rule.getAs<ArrayAttr>("payload");
    if (!kind || !handler || !selectedSites || !inputs || !payload ||
        inputs.size() > 1024 || payload.size() > 1024 ||
        selectedSites.size() > 1024)
      return fail("invalid construction rule fields");
    uint64_t work = 1 + 2 * plan.state.size() + selectedSites.size() +
                    inputs.size() + 2 * payload.size();
    if (work > remaining)
      return fail("construction signature work limit exceeded");
    remaining -= work;
    ConstructionRule selection;
    if (kind.getValue() == "start")
      selection.kind = ConstructionRule::Kind::Start;
    else if (kind.getValue() == "message")
      selection.kind = ConstructionRule::Kind::Message;
    else if (kind.getValue() == "query")
      selection.kind = ConstructionRule::Kind::Query;
    else
      return fail("unknown construction rule kind");
    selection.handler = handler;
    for (auto attr : payload) {
      auto type = dyn_cast<TypeAttr>(attr);
      if (!type)
        return fail("rule payload slots must be types");
      selection.payload.push_back(type.getValue());
    }
    for (auto attr : selectedSites) {
      auto site = dyn_cast<StringAttr>(attr);
      if (!site || site.empty() || site.size() > 4096 ||
          !sites.insert(site.getValue()).second)
        return fail("invalid or duplicate construction site");
      siteBytes += site.size();
      if (siteBytes > 16 * 1024 * 1024 || sites.size() > 2048)
        return fail("construction site limit exceeded");
      selection.sites.push_back(site.str());
    }
    SmallVector<Type> parameters(plan.state), results(plan.state);
    if (selection.kind == ConstructionRule::Kind::Start) {
      if (start || !selection.sites.empty() || !selection.payload.empty())
        return fail("start must be unique and select only original inputs");
      start = true;
      llvm::DenseSet<int64_t> seen;
      for (auto port : inputs.asArrayRef()) {
        if (port < 0 || uint64_t(port) >= signature.getNumInputs() ||
            !seen.insert(port).second)
          return fail("invalid or duplicate start input");
        auto owners = dyn_cast<ArrayAttr>(target.getInputRoles()[port]);
        if (!owners || !equal(owners, target.getRoles()) ||
            isa<protocol_ir::ServiceReferenceType>(signature.getInput(port)))
          return fail("start input must be available at both participants");
        parameters.push_back(signature.getInput(port));
        selection.inputs.push_back(port);
      }
    } else {
      if (!inputs.empty() || selection.sites.empty())
        return fail("event rules require sites and no entry input selectors");
      if (selection.kind == ConstructionRule::Kind::Message) {
        if (selection.payload.size() != selection.sites.size())
          return fail("message leaves must match the logical payload");
        append_range(parameters, selection.payload);
      } else {
        if (selection.sites.size() != 1 || selection.payload.size() != 1)
          return fail("query must select one result");
        append_range(results, selection.payload);
      }
    }
    auto function =
        symbols.lookupNearestSymbolFrom<local::FuncOp>(record, handler);
    if (!function || failed(function->getName().verifyInvariants(function)))
      return fail("construction handler must be an ordinary Local function");
    // UniformIndex bodies also receive the explicit request bound. Occurrence
    // admission checks this argument against the actual query request.
    if (selection.kind == ConstructionRule::Kind::Query &&
        function.getFunctionType().getNumInputs() == parameters.size() + 1)
      parameters.push_back(
          IntegerType::get(record.getContext(), 64, IntegerType::Unsigned));
    if (!equal(function.getArgumentTypes(), parameters) ||
        !equal(function.getResultTypes(), results))
      return fail("construction handler signature differs from its rule");
    plan.rules.push_back(std::move(selection));
  }
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
