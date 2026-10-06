#include "MathematicalSupport.h"
#include "MathematicalValues.h"
#include "ProtocolApplications.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-projection",
                           detail);
}
LogicalResult refuseLocal(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "native-local-policy", detail);
}
bool supportedPreservationEdge(protocol_ir::Profile before,
                               protocol_ir::Profile after) {
  using Profile = protocol_ir::Profile;
  switch (before) {
  case Profile::Protocol:
    return after == Profile::Participant;
  case Profile::Participant:
    return after == Profile::Participant || after == Profile::Exec;
  case Profile::Exec:
    return after == Profile::Exec || after == Profile::Physical;
  case Profile::Physical:
    return after == Profile::Physical;
  case Profile::ProtocolExec:
    return false;
  }
  return false;
}
Type logicalType(Type type) {
  if (auto physical = dyn_cast<plan::DataType>(type))
    return physical.getLogical();
  return type;
}
} // namespace
ArrayAttr statementBindings(zkc::protocol_ir::MathematicalOp program,
                            SymbolTableCollection &symbols) {
  Builder builder(program.getContext());
  SmallVector<Attribute> statements;
  for (auto statement :
       program.getBody().front().getOps<zkc::protocol_ir::StatementOp>()) {
    auto declaration =
        symbols.lookupNearestSymbolFrom<zkc::relation::DeclareOp>(
            statement, statement.getRelationAttr());
    SmallVector<Attribute> ports;
    for (auto input : statement.getInputs())
      ports.push_back(
          builder.getI64IntegerAttr(cast<BlockArgument>(input).getArgNumber()));
    statements.push_back(builder.getDictionaryAttr(
        {builder.getNamedAttr("relation", statement.getRelationAttr()),
         builder.getNamedAttr("relation_type", declaration.getSignatureAttr()),
         builder.getNamedAttr("relation_kind", declaration.getKindAttr()),
         builder.getNamedAttr("relation_key", declaration.getKeyAttr()),
         builder.getNamedAttr("relation_revision",
                              declaration.getRevisionAttr()),
         builder.getNamedAttr("relation_purposes", declaration.getPurposes()),
         builder.getNamedAttr("inputs", builder.getArrayAttr(ports)),
         builder.getNamedAttr("selectors", statement.getSelectors()),
         builder.getNamedAttr("acceptance", statement.getAcceptanceAttr())}));
  }
  return builder.getArrayAttr(statements);
}

LogicalResult verifyProtocolPreparationPreserved(Operation *before,
                                                 Operation *after) {
  bool applications = false;
  before->walk([&](protocol_ir::ApplyOp) { applications = true; });
  if (applications)
    return verifyPreparedValues(cast<protocol_ir::ProtocolModuleOp>(before),
                                cast<protocol_ir::ProtocolModuleOp>(after));
  SymbolTable targetSymbols(after);
  auto significant = [](protocol_ir::MathematicalOp function) {
    SmallVector<Operation *> result;
    function.walk<WalkOrder::PreOrder>([&](Operation *op) {
      auto meaning = classify(op);
      if (meaning && (meaning->category == Category::Action ||
                      meaning->category == Category::Declaration ||
                      isa<protocol_ir::RepeatOp>(op)))
        result.push_back(op);
    });
    return result;
  };
  unsigned count = 0;
  for (auto function :
       before->getRegion(0).front().getOps<protocol_ir::MathematicalOp>()) {
    ++count;
    auto target = dyn_cast_or_null<protocol_ir::MathematicalOp>(
        targetSymbols.lookup(function.getSymName()));
    if (!target || function->getAttrDictionary() != target->getAttrDictionary())
      return refuseLocal(after, "preparation changed a common interface");
    auto lhs = significant(function), rhs = significant(target);
    if (lhs.size() != rhs.size())
      return refuseLocal(after,
                         "preparation changed ordered actions or statements");
    for (auto [a, b] : zip(lhs, rhs)) {
      if (a->getName() != b->getName() ||
          a->getAttrDictionary() != b->getAttrDictionary() ||
          a->getOperandTypes() != b->getOperandTypes() ||
          a->getResultTypes() != b->getResultTypes())
        return refuseLocal(after,
                           "preparation changed ordered actions or statements");
      auto path = [](Operation *op) {
        SmallVector<Attribute> result;
        for (auto *parent = op->getParentOp(); parent;
             parent = parent->getParentOp())
          if (auto loop = dyn_cast<protocol_ir::RepeatOp>(parent))
            result.push_back(loop.getSiteAttr());
        return result;
      };
      if (path(a) != path(b))
        return refuseLocal(
            after, "preparation moved an action across a repeat boundary");
      if (isa<protocol_ir::StatementOp>(a)) {
        if (a->getNumOperands() != b->getNumOperands())
          return refuseLocal(after, "preparation changed statement arity");
        for (auto [x, y] : zip(a->getOperands(), b->getOperands())) {
          auto original = dyn_cast<BlockArgument>(x);
          auto rewritten = dyn_cast<BlockArgument>(y);
          if (!original || !rewritten ||
              original.getOwner() != &function.getBody().front() ||
              rewritten.getOwner() != &target.getBody().front() ||
              original.getArgNumber() != rewritten.getArgNumber())
            return refuseLocal(after,
                               "preparation changed a statement entry binding");
        }
      }
    }
  }
  if (count != std::distance(after->getRegion(0)
                                 .front()
                                 .getOps<protocol_ir::MathematicalOp>()
                                 .begin(),
                             after->getRegion(0)
                                 .front()
                                 .getOps<protocol_ir::MathematicalOp>()
                                 .end()))
    return refuseLocal(after,
                       "preparation changed the common definition count");
  return verifyPreparedValues(cast<protocol_ir::ProtocolModuleOp>(before),
                              cast<protocol_ir::ProtocolModuleOp>(after));
}
LogicalResult verifyAuthoredLocalsPreserved(Operation *before,
                                            Operation *after) {
  SymbolTable sourceSymbols(before), targetSymbols(after);
  auto profile = cast<protocol_ir::ProtocolModuleOp>(after).getProfile();
  // Projection and mathematical simplification cannot invent executable work.
  // Lowering may add generated calculations while preserving every authored
  // one.
  if (profile == protocol_ir::Profile::Protocol ||
      profile == protocol_ir::Profile::Participant) {
    for (auto &op : after->getRegion(0).front())
      if (isa<local::FuncOp, local::OperationBindingOp>(op) &&
          !sourceSymbols.lookup(SymbolTable::getSymbolName(&op)))
        return refuseLocal(after,
                           "mathematical pass added an executable definition");
  }
  for (auto &op : before->getRegion(0).front()) {
    if (!isa<local::FuncOp, local::OperationBindingOp>(op))
      continue;
    auto name = SymbolTable::getSymbolName(&op);
    auto *target = targetSymbols.lookup(name);
    if (!target || !OperationEquivalence::isEquivalentTo(
                       &op, target, OperationEquivalence::IgnoreLocations))
      return refuseLocal(
          after, "mathematical pass changed an authored executable definition");
  }
  return success();
}

namespace {
protocol_ir::ProtocolModuleOp protocolUnit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return {};
  return dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
protocol_ir::ProjectionOp projection(protocol_ir::ProtocolModuleOp unit) {
  if (!unit)
    return {};
  auto records = unit.getBody().front().getOps<protocol_ir::ProjectionOp>();
  return records.empty() ? protocol_ir::ProjectionOp() : *records.begin();
}
OwningOpRef<protocol_ir::ParticipantOp>
logicalParticipant(protocol_ir::ParticipantOp participant) {
  OwningOpRef<protocol_ir::ParticipantOp> copy(
      cast<protocol_ir::ParticipantOp>(participant->clone()));
  SmallVector<Type> inputs, results;
  for (auto type : participant.getFunctionType().getInputs())
    inputs.push_back(logicalType(type));
  for (auto type : participant.getFunctionType().getResults())
    results.push_back(logicalType(type));
  copy->setFunctionType(
      FunctionType::get(participant.getContext(), inputs, results));
  copy->walk([&](Operation *op) {
    for (auto &region : op->getRegions())
      for (auto &block : region)
        for (auto argument : block.getArguments())
          argument.setType(logicalType(argument.getType()));
    for (auto value : op->getResults())
      value.setType(logicalType(value.getType()));
  });
  return copy;
}
} // namespace

// Structural validation alone deliberately allows supplied executable programs
// without source metadata. Compiler passes also compare against their frozen
// input, so losing a projected interface cannot turn a derived result into
// an unrelated supplied program. This is a compiler postcondition, not an
// independent source/candidate proof.
LogicalResult verifyProjectionPreserved(ModuleOp original, ModuleOp candidate) {
  auto before = protocolUnit(original), after = protocolUnit(candidate);
  if (!before || !after)
    return refuse(candidate, "projected compilation lost its protocol unit");
  if (!supportedPreservationEdge(before.getProfile(), after.getProfile()))
    return refuse(candidate, "unsupported preservation profile edge");
  // Same-profile executable checking recognizes structural identity only.
  // Local bodies, bindings, representations and provenance are part of that
  // subject; comparing participant calls alone would miss changed callees.
  if (before.getProfile() == after.getProfile() &&
      (before.getProfile() == protocol_ir::Profile::Exec ||
       before.getProfile() == protocol_ir::Profile::Physical)) {
    if (!OperationEquivalence::isEquivalentTo(
            before, after, OperationEquivalence::IgnoreLocations))
      return refuse(candidate,
                    "same-profile executable check changed the module");
    return success();
  }
  SymbolTable targetSymbols(after);
  SymbolTableCollection symbolTables;
  // Adjacent executable data flow must agree even for supplied programs or
  // the older source route, which carry no mathematical projection record.
  if (before.getProfile() == protocol_ir::Profile::Exec ||
      before.getProfile() == protocol_ir::Profile::Physical) {
    auto sourceParticipants =
        before.getBody().front().getOps<protocol_ir::ParticipantOp>();
    auto targetParticipants =
        after.getBody().front().getOps<protocol_ir::ParticipantOp>();
    if (llvm::range_size(sourceParticipants) !=
        llvm::range_size(targetParticipants))
      return refuse(candidate, "compilation changed the participant count");
    for (auto participant :
         before.getBody().front().getOps<protocol_ir::ParticipantOp>()) {
      auto target = dyn_cast_or_null<protocol_ir::ParticipantOp>(
          targetSymbols.lookup(participant.getSymName()));
      if (!target)
        return refuse(candidate, "compilation lost a participant");
      auto lhs = logicalParticipant(participant),
           rhs = logicalParticipant(target);
      if (!OperationEquivalence::isEquivalentTo(
              lhs->getOperation(), rhs->getOperation(),
              OperationEquivalence::IgnoreLocations))
        return refuse(candidate, "compilation changed participant "
                                 "execution order or data flow");
    }
  }
  auto prior = projection(before), result = projection(after);
  if (!prior && result && before.getProfile() != protocol_ir::Profile::Protocol)
    return refuse(candidate,
                  "compilation added an ungrounded projection record");
  if (prior) {
    if (before.getProfile() == protocol_ir::Profile::Participant &&
        failed(verifyAuthoredLocalsPreserved(before, after)))
      return failure();
    if (before.getProfile() == protocol_ir::Profile::Participant &&
        after.getProfile() == protocol_ir::Profile::Participant &&
        failed(verifyParticipantValues(before, after)))
      return failure();
    if (!result || prior.getInterfaces() != result.getInterfaces())
      return refuse(candidate,
                    "projected compilation changed or lost a frozen interface");
    if (before.getProfile() == protocol_ir::Profile::Participant &&
        after.getProfile() != protocol_ir::Profile::Participant &&
        failed(verifyMathLowering(before, after)))
      return failure();
    if (before.getProfile() == protocol_ir::Profile::Exec ||
        before.getProfile() == protocol_ir::Profile::Physical) {
      if (prior.getCalculations() != result.getCalculations())
        return refuse(candidate,
                      "compilation changed generated calculation origins");
    }
    return success();
  }
  if (before.getProfile() != protocol_ir::Profile::Protocol)
    return success();
  // Raw application-bearing inputs compose an independently checked
  // substitution edge with projection. Already prepared pass inputs are used
  // directly, so the producer's actual adjacent subject is retained.
  OwningOpRef<protocol_ir::ProtocolModuleOp> expanded;
  bool applications = false;
  before.walk([&](protocol_ir::ApplyOp) { applications = true; });
  if (applications) {
    expanded = cast<protocol_ir::ProtocolModuleOp>(before->clone());
    if (failed(expandApplications(*expanded)) ||
        failed(verifyPreparedValues(before, *expanded)))
      return failure();
    before = *expanded;
  }
  if (!result)
    return refuse(candidate, "role projection lost its source interface");
  llvm::StringMap<DictionaryAttr> interfaces;
  for (auto item : result.getInterfaces()) {
    auto interface = cast<DictionaryAttr>(item);
    if (!interfaces
             .try_emplace(interface.getAs<StringAttr>("source").getValue(),
                          interface)
             .second)
      return refuse(result, "duplicate projected source interface");
  }
  unsigned count = 0;
  for (auto program :
       before.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    ++count;
    auto interface = interfaces.lookup(program.getSymName());
    if (!interface ||
        interface.get("original_type") != program.getFunctionTypeAttr() ||
        interface.get("roles") != program.getRoles() ||
        interface.get("input_roles") != program.getInputRoles() ||
        interface.get("output_roles") != program.getOutputRoles())
      return refuse(result,
                    "role projection changed a declared source interface");
    if (interface.get("statements") != statementBindings(program, symbolTables))
      return refuse(result,
                    "role projection changed statement inputs or acceptance");
    auto compare = [&](auto &&self, Block &block, ArrayAttr mapped,
                       unsigned depth) -> LogicalResult {
      if (depth > 64 || !mapped)
        return refuse(result, "invalid projected action nesting");
      SmallVector<Operation *> actions;
      for (auto &op : block)
        if (auto meaning = classify(&op);
            meaning && (meaning->category == Category::Action ||
                        isa<protocol_ir::RepeatOp>(op)))
          actions.push_back(&op);
      if (mapped.size() != actions.size())
        return refuse(result,
                      "role projection changed the source action count");
      for (auto [action, item] : zip(actions, mapped)) {
        auto map = cast<DictionaryAttr>(item);
        if (map.get("site") != action->getAttr("site") ||
            map.getAs<StringAttr>("kind").getValue() !=
                action->getName().getStringRef())
          return refuse(result,
                        "role projection changed a source action occurrence");
        if (isa<protocol_ir::LocalCallOp>(action) &&
            map.get("callee") != action->getAttr("callee"))
          return refuse(result, "role projection changed an authored callee");
        llvm::DenseSet<Attribute> owners;
        for (auto targetItem : map.getAs<ArrayAttr>("targets")) {
          auto target = cast<DictionaryAttr>(targetItem);
          auto participant =
              symbolTables.lookupNearestSymbolFrom<protocol_ir::ParticipantOp>(
                  result, target.getAs<FlatSymbolRefAttr>("participant"));
          owners.insert(participant.getRoleAttr());
          if (isa<protocol_ir::RepeatOp>(action))
            continue;
          auto operation = target.getAs<StringAttr>("operation").getValue();
          auto owner = action->getAttrOfType<StringAttr>(
              operation == "protocol.send"            ? "sender"
              : operation == "protocol.receive"       ? "receiver"
              : isa<protocol_ir::LocalCallOp>(action) ? "role"
                                                      : "owner");
          if (participant.getRoleAttr() != owner)
            return refuse(result, "role projection changed an action owner");
        }
        if (auto loop = dyn_cast<protocol_ir::RepeatOp>(action)) {
          if (map.get("maximum") != loop.getMaximumAttr() ||
              owners.size() != loop.getRoles().size() ||
              !all_of(loop.getRoles(),
                      [&](Attribute role) { return owners.contains(role); }))
            return refuse(
                result,
                "role projection changed repeat bounds or participants");
          if (failed(self(self, loop.getBody().front(),
                          map.getAs<ArrayAttr>("body"), depth + 1)))
            return failure();
        }
      }
      return success();
    };
    if (failed(compare(compare, program.getBody().front(),
                       interface.getAs<ArrayAttr>("actions"), 0)))
      return failure();
  }
  return count == interfaces.size()
             ? verifyProjectedValues(before, after)
             : refuse(result, "role projection added a source interface");
}

} // namespace zkc::mathematical
