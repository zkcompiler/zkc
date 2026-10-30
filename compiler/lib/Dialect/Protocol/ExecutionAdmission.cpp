#include "../Verification.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/Services.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include <map>
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
bool identifier(StringRef value) {
  return !value.empty() && value.size() <= 128 &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}
// This is native admission after nested operation verification, not a source
// correspondence check or byte parser. The containing symbol table owns every
// mutable dependency. No Program record or type spelling supplies facts.
class ExecutionAdmission {
  protocol_ir::ProtocolModuleOp owner;
  bool physical;
  SymbolTableCollection symbols;
  llvm::DenseMap<Type, LogicalTypePermissions> permissions;
  std::map<std::pair<StringRef, StringRef>, Type> schemas;
  uint64_t remaining = 1000000, instructions = 0;
  unsigned callables = 0, participants = 0, entries = 0, functions = 0;
  std::set<std::pair<StringRef, StringRef>> identities;
  llvm::StringMap<StringRef> services;
  std::string problem, message;
  Operation *site = nullptr;

  bool fail(Operation *op, StringRef code, StringRef detail = {}) {
    if (problem.empty()) {
      site = op;
      problem = code.str();
      message = detail.str();
    }
    return false;
  }
  bool charge(Operation *op, uint64_t amount = 1) {
    if (amount > remaining)
      return fail(op, "execution-analysis-limit", "participant work limit");
    remaining -= amount;
    return true;
  }
  bool attributes(Operation *op, ArrayRef<StringRef> allowed) {
    return all_of(op->getAttrs(),
                  [&](NamedAttribute attr) {
                    return is_contained(allowed, attr.getName().getValue());
                  }) ||
           fail(op, "interactive-unknown-attribute");
  }
  bool type(Operation *op, Type type) {
    if (!charge(op))
      return false;
    if (permissions.contains(type))
      return true;
    auto represented = dyn_cast<runtime::RepresentedType>(type);
    if (physical != bool(represented))
      return fail(op, "binding-type", "value differs from execution stage");
    LogicalTypePermissions facts;
    auto emit = [&] { return op->emitOpError(); };
    if (failed(verifyLogicalType(emit, logicalValueType(type), &facts)) ||
        (physical && failed(verifyValueType(emit, type))) ||
        (represented &&
         isDiagonalRepresentation(represented.getRepresentation())))
      return fail(op, "binding-type", "unsupported participant value");
    permissions.try_emplace(type, facts);
    return true;
  }
  bool ports(Operation *op, TypeRange ports) {
    if (ports.size() > 1024)
      return fail(op, "interactive-port-limit");
    for (Type port : ports)
      if (!type(op, port))
        return false;
    return true;
  }
  bool selectedService(Type actual, const BoundType &expected) {
    if (!physical)
      return true;
    auto selected = dyn_cast<runtime::RepresentedType>(actual);
    // Installed service methods currently have only atomic ports. Select the
    // provider's exact default representation directly from installation data.
    // Logical matching below independently checks constructor and nominal
    // field.
    auto *representation = installedDomains().defaultRepresentation(
        expected.kind, expected.identity);
    return selected && selected.getChildren().empty() && representation &&
           selected.getRepresentation() == representation->identity;
  }
  bool service(protocol_ir::ParticipantQueryOp query) {
    auto contract = services.find(query.getPort());
    auto method = contract == services.end()
                      ? std::optional<ServiceMethod>{}
                      : serviceMethod(contract->second, query.getMethod());
    if (!method || query.getInputs().size() != method->inputs.size() ||
        query.getOutputs().size() != 1)
      return fail(query, "service-query-signature");
    SmallVector<Type> logical;
    for (auto [value, expected] : zip(query.getInputs(), method->inputs)) {
      if (!selectedService(value.getType(), expected))
        return fail(query, "service-query-signature",
                    "input representation differs");
      logical.push_back(logicalValueType(value.getType()));
    }
    auto output = query.getOutputs().front().getType();
    if (!selectedService(output, method->output) ||
        !protocol_ir::matchesServiceSignature(
            logical, {logicalValueType(output)}, *method))
      return fail(query, "service-query-signature",
                  "service data ports differ");
    return true;
  }
  bool body(protocol_ir::ParticipantOp participant, Block &block,
            TypeRange outputs, llvm::StringSet<> &sites, unsigned depth = 0) {
    if (depth >= 64 || block.empty() || !charge(participant))
      return fail(participant, "execution-analysis-limit",
                  "participant control depth");
    llvm::DenseSet<Value> available, consumed;
    if (!ports(participant, block.getArgumentTypes()))
      return false;
    for (Value value : block.getArguments())
      available.insert(value);
    auto consume = [&](Operation *op, ValueRange values,
                       bool invariant = false) {
      if (!charge(op, values.size()))
        return false;
      for (Value value : values) {
        if (!available.contains(value) || consumed.contains(value))
          return fail(op, "interactive-resource-reuse",
                      "unavailable participant value");
        if (!type(op, value.getType()))
          return false;
        if (!permissions.lookup(value.getType()).copy) {
          if (invariant)
            return fail(op, "interactive-loop-capture",
                        "invariant requires Copy");
          // Sending observes a wire value; it does not transfer local custody.
          if (!isa<protocol_ir::EmitOp>(op))
            consumed.insert(value);
        }
      }
      return true;
    };
    for (Operation &operation : block) {
      auto *op = &operation;
      if (!charge(op) || ++instructions > 65536)
        return fail(op, "execution-analysis-limit",
                    "participant instruction limit");
      bool terminal =
          isa<protocol_ir::FinishOp, protocol_ir::ProtocolYieldOp>(op);
      if (terminal != (op == &block.back()))
        return fail(op, "interactive-terminator");
      if (terminal) {
        if (!attributes(op, {}) ||
            isa<protocol_ir::ProtocolYieldOp>(op) != (depth != 0) ||
            op->getOperandTypes() != outputs || !consume(op, op->getOperands()))
          return fail(op, "interactive-return");
        continue;
      }
      auto occurrence = op->getAttrOfType<StringAttr>("site");
      if (!occurrence || !identifier(occurrence.getValue()) ||
          !sites.insert(occurrence.getValue()).second)
        return fail(op, "interactive-site");
      if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(op)) {
        if (!attributes(op,
                        {"site", "carried", "count", "parameter", "maximum"}) ||
            !loop.getBody().hasOneBlock() || !loop.getMaximum() ||
            *loop.getMaximum() > 1048576 ||
            !consume(op, loop.getInputs().take_front(1 + loop.getCarried())) ||
            !consume(op, loop.getInputs().drop_front(1 + loop.getCarried()),
                     true) ||
            !body(participant, loop.getBody().front(), loop.getResultTypes(),
                  sites, depth + 1))
          return fail(op, "interactive-loop-body");
      } else {
        if (!consume(op, op->getOperands()))
          return false;
        if (auto call = dyn_cast<protocol_ir::LocalCallOp>(op)) {
          auto function =
              symbols.lookupSymbolIn<func::FuncOp>(owner, call.getCalleeAttr());
          auto signature = scopedDataSignature(function);
          if (!attributes(op, {"site", "callee", "role"}) ||
              call.getRoleAttr() != participant.getRoleAttr() || !signature ||
              call.getOperandTypes() != signature.getInputs() ||
              call.getResultTypes() != signature.getResults())
            return fail(op, "interactive-local-signature");
        } else if (auto query = dyn_cast<protocol_ir::ParticipantQueryOp>(op)) {
          if (!attributes(op, {"site", "port", "method"}) || !service(query))
            return false;
        } else if (isa<protocol_ir::EmitOp, protocol_ir::AwaitOp>(op)) {
          auto schema = op->getAttrOfType<StringAttr>("schema");
          auto peer = op->getAttrOfType<StringAttr>("peer");
          if (!attributes(op, {"site", "schema", "peer"}) || !schema || !peer ||
              !identifier(schema.getValue()) || !identifier(peer.getValue()) ||
              peer == participant.getRoleAttr())
            return fail(op, "interactive-peer");
          Type payload = isa<protocol_ir::EmitOp>(op)
                             ? op->getOperand(0).getType()
                             : op->getResult(0).getType();
          auto [position, inserted] = schemas.emplace(
              std::make_pair(participant.getInstance(), schema.getValue()),
              payload);
          if (!inserted && position->second != payload)
            return fail(op, "interactive-schema-type");
        } else if (auto finish = dyn_cast<protocol_ir::FinishIfOp>(op)) {
          if (!attributes(op, {"site", "owner"}) || failed(finish.verify()))
            return fail(op, "interactive-return-type");
        } else
          return fail(op, "binding-operation",
                      "operation outside execution profile");
      }
      if (!ports(op, op->getResultTypes()))
        return false;
      for (Value value : op->getResults())
        available.insert(value);
    }
    return true;
  }
  bool participant(protocol_ir::ParticipantOp participant) {
    if (!attributes(participant, {"sym_name", "function_type", "instance",
                                  "role", "service_ports"}) ||
        !identifier(participant.getSymName()) ||
        !identifier(participant.getInstance()) ||
        !identifier(participant.getRole()) ||
        !identities.emplace(participant.getInstance(), participant.getRole())
             .second)
      return fail(participant, "interactive-participant-identity");
    auto signature = participant.getFunctionType();
    if (!ports(participant, signature.getInputs()) ||
        !ports(participant, signature.getResults()))
      return false;
    services.clear();
    auto portsAttr = participant->getAttrOfType<ArrayAttr>("service_ports");
    if (participant->hasAttr("service_ports") && !portsAttr)
      return fail(participant, "service-port-interface");
    unsigned count =
        signature.getNumInputs() + (portsAttr ? portsAttr.size() : 0);
    if (count > 1024)
      return fail(participant, "interactive-port-limit");
    llvm::DenseSet<uint64_t> indices;
    if (portsAttr)
      for (auto item : portsAttr) {
        if (!charge(participant))
          return false;
        auto row = dyn_cast<ArrayAttr>(item);
        if (!row || row.size() != 3 || !isa<StringAttr>(row[0]) ||
            !isa<StringAttr>(row[1]) || !isa<IntegerAttr>(row[2]))
          return fail(participant, "service-port-interface");
        auto name = cast<StringAttr>(row[0]).getValue();
        auto contract = cast<StringAttr>(row[1]).getValue();
        auto index = cast<IntegerAttr>(row[2]);
        if (!identifier(name) || randomServiceField(contract).empty() ||
            !index.getType().isSignlessInteger(64) || index.getInt() < 0 ||
            uint64_t(index.getInt()) >= count ||
            !indices.insert(index.getInt()).second ||
            !services.try_emplace(name, contract).second)
          return fail(participant, "service-port-interface");
      }
    llvm::StringSet<> sites;
    return body(participant, participant.getBody().front(),
                signature.getResults(), sites);
  }
  bool entry(protocol_ir::ProtocolEntryOp entry) {
    if (!attributes(entry, {"sym_name", "targets"}) ||
        !identifier(entry.getSymName()) || entry.getTargets().empty() ||
        entry.getTargets().size() > 4096)
      return fail(entry, "interactive-entry-targets");
    llvm::StringSet<> roles;
    StringAttr instance;
    for (auto item : entry.getTargets()) {
      if (!charge(entry))
        return false;
      auto row = dyn_cast<ArrayAttr>(item);
      if (!row || row.size() != 2 || !isa<StringAttr>(row[0]) ||
          !isa<FlatSymbolRefAttr>(row[1]))
        return fail(entry, "interactive-entry-targets");
      auto role = cast<StringAttr>(row[0]);
      auto target = symbols.lookupSymbolIn<protocol_ir::ParticipantOp>(
          owner, cast<FlatSymbolRefAttr>(row[1]));
      if (!identifier(role.getValue()) ||
          !roles.insert(role.getValue()).second || !target ||
          role != target.getRoleAttr())
        return fail(entry, "interactive-entry-role");
      if (instance && instance != target.getInstanceAttr())
        return fail(entry, "interactive-entry-instance");
      instance = target.getInstanceAttr();
    }
    return true;
  }
  bool check() {
    if (!attributes(owner, {"profile", "source_declarations"}) ||
        (owner->hasAttr("source_declarations") &&
         !owner->getAttrOfType<ArrayAttr>("source_declarations")))
      return fail(owner, "interactive-module");
    auto closure = physical ? readExecutionClosure(owner, true)
                            : readSourceExecutionClosure(owner);
    if (!closure) {
      (void)diagnostics::emit(owner.emitOpError(), closure.takeError());
      return false;
    }
    for (Operation &op : owner.getBody().front()) {
      if (!charge(&op))
        return false;
      if (auto function = dyn_cast<func::FuncOp>(op)) {
        if (!function->hasAttr("runtime.region")) {
          ++callables;
          if (isScopedExecutionFunction(function))
            ++functions;
        }
      } else if (isa<data::DomainOp>(op)) {
        if (physical)
          return fail(&op, "execution-unresolved-domain");
        ++callables;
      } else if (isa<ModuleOp>(op)) {
        if (physical)
          return fail(&op, "computation-profile");
      } else if (isa<runtime::BindingOp, protocol_ir::ProjectionOp,
                     relation::DeclareOp>(op)) {
        continue;
      } else if (auto selected = dyn_cast<protocol_ir::ParticipantOp>(op)) {
        ++participants;
        ++callables;
        if (!participant(selected))
          return false;
      } else if (auto selected = dyn_cast<protocol_ir::ProtocolEntryOp>(op)) {
        ++entries;
        if (!entry(selected))
          return false;
      } else
        return fail(&op, "interactive-top-operation");
      if (callables > 4096)
        return fail(&op, "interactive-definition-limit");
    }
    if ((!entries && (participants || !functions)) ||
        (!participants && entries))
      return fail(owner, "interactive-entry");
    return true;
  }

public:
  explicit ExecutionAdmission(protocol_ir::ProtocolModuleOp owner)
      : owner(owner),
        physical(owner.getProfile() == protocol_ir::Profile::Physical) {}
  LogicalResult run() {
    if (check())
      return success();
    if (problem.empty())
      return failure();
    return diagnostics::emit(
        (site ? site : owner.getOperation())->emitOpError(), problem, message);
  }
};
} // namespace
LogicalResult verifyModule(Operation *root) {
  auto owner = dyn_cast_or_null<protocol_ir::ProtocolModuleOp>(root);
  if (!owner || !protocol_ir::isExecutableProfile(owner.getProfile()))
    return failure();
  return ExecutionAdmission(owner).run();
}
} // namespace zkc::protocol
