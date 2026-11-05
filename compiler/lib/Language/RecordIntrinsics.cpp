#include "RecordIntrinsics.h"
#include "BindingWitness.h"
#include "BodyCheck.h"
#include "ManagedServices.h"
#include "ScopedWitness.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
std::optional<ValuePlacement>
unpackedPlacement(Semantics &types, const Value &source, const Type &payload,
                  unsigned participants, Span span) {
  const auto *nominal = types.typeDeclaration(source.type);
  if (source.type.kind != Type::Kind::LogicalRecord || !nominal ||
      nominal->roles.empty() || !source.placement ||
      !std::holds_alternative<ProductPlacement>(source.placement->value)) {
    types.fail(
        "source.call",
        "protocol record operation requires a distributed nominal wrapper",
        span);
    return {};
  }
  auto exact =
      types.placement(source.type, *source.placement, participants, span);
  if (!exact || *exact != *source.placement ||
      source.components != placementRoles(*exact)) {
    if (!types.diagnostic)
      types.fail("source.placement",
                 "record operation requires the exact wrapper placement", span);
    return {};
  }
  const auto &root = std::get<ProductPlacement>(exact->value);
  auto roles = placementRoles(*exact);
  if (root.fields.empty())
    return DataPlacement{std::move(roles)};
  if (!types.chargeIdentity(payload, span))
    return {};
  return types.placement(
      payload,
      ProductPlacement{typeIdentity(payload), std::move(roles), root.fields},
      participants, span);
}
} // namespace
bool isRecordIntrinsic(protocol::FrontendSignature rule) {
  using S = protocol::FrontendSignature;
  return rule == S::RecordUnpack || rule == S::RecordInspect ||
         rule == S::RecordRepack;
}
bool isRecordIntrinsic(const protocol::FrontendDeclaration *row) {
  return row && row->rule && isRecordIntrinsic(*row->rule);
}
bool Checker::indexDeclarations() {
  for (const auto &decl : output.declarations)
    if (!types.charge(decl.qualifiedName.size() + decl.members.size() + 1,
                      decl.span))
      return false;
  if (!types.charge(formingIndex->bindingCount(), {}))
    return false;
  formingIndex->finish(output.declarations, *output.sources);
  output.declarationIndex = formingIndex;
  for (const auto &row : protocol::frontendDeclarations()) {
    auto id = output.declarationIndex->canonical(row.module + "::" + row.name);
    if (!id || output.declarationIndex->association(*id) != &row)
      return types.fail("source.installation",
                        "missing installed declaration association", {});
  }
  return true;
}
bool Checker::checkInstalledSignatures() {
  return checkDeclarationAssociations(
      types, output.declarations, *output.declarationIndex, *output.sources);
}
bool checkDeclarationAssociations(Semantics &types,
                                  ArrayRef<Declaration> declarations,
                                  const DeclarationIndex &index,
                                  ArrayRef<SourceBuffer> sources) {
  uint64_t identityWork = declarations.size();
  for (const auto &decl : declarations)
    identityWork += decl.name.size() + decl.qualifiedName.size();
  if (!types.charge(identityWork, {}))
    return false;
  if (!index.matchesInstallation(declarations, sources))
    return types.fail("source.installation",
                      "installed declaration identity or ownership differs",
                      {});
  for (const auto &decl : declarations) {
    if (auto *method = index.serviceAssociation(decl.id)) {
      auto refuse = [&] {
        return types.fail(
            "source.installation",
            "installed managed method differs from its catalog signature",
            decl.span);
      };
      const auto *constructor =
          decl.parent ? index.ruleAssociation(*decl.parent) : nullptr;
      if (!constructor || constructor->identity != method->constructor ||
          decl.name != method->name ||
          decl.qualifiedName != declarations[decl.parent->index].qualifiedName +
                                    "::" + method->name ||
          constructor->rule != protocol::FrontendSignature::RandomConstructor ||
          decl.kind != Declaration::Kind::Local || !decl.isPublic ||
          decl.abstract || decl.primitive || decl.body ||
          decl.finiteDefinition || !decl.members.empty() ||
          !decl.inputs.empty() || !decl.inputOrder.empty() ||
          !decl.roles.empty() || !decl.services.empty() ||
          !decl.scopedInputs.empty() || !decl.descriptorInputs.empty() ||
          !decl.permissionBounds.empty() || !decl.capabilityBounds.empty() ||
          !decl.bounds.empty() || !decl.dataPreconditions.empty() ||
          decl.effectAllowance ||
          decl.parameters.size() != 1 + serviceStaticCount(method->signature) ||
          decl.parameters.front().sort != Parameter::Sort::Domain ||
          decl.parameters.front().domainSort != "Field" ||
          declarations[decl.parent->index].parameters.size() != 1 ||
          parameterType(decl.parameters.front()) !=
              parameterType(
                  declarations[decl.parent->index].parameters.front()) ||
          decl.outputs.size() != 1 ||
          decl.outputs.front().type !=
              serviceResult(method->signature,
                            parameterType(decl.parameters.front())))
        return refuse();
      for (unsigned i = 1; i < decl.parameters.size(); ++i)
        if (decl.parameters[i].sort != Parameter::Sort::Natural)
          return refuse();
      continue;
    }
    auto *row = index.association(decl.id);
    if (!row)
      continue;
    auto refuse = [&] {
      return types.fail("source.installation",
                        "installed signature differs from its catalog rule",
                        decl.span);
    };
    // A primitive association keeps the primitive path, whose agreement with
    // its operation or intrinsic is checked with every primitive declaration.
    // Checking completes the definition after this check; a checked
    // declaration must define exactly the associated primitive.
    if (!row->rule) {
      if ((decl.primitive && decl.primitive->identity != row->primitive) ||
          decl.kind != (row->kind == protocol::SourceDeclarationKind::Math
                            ? Declaration::Kind::Math
                            : Declaration::Kind::Local) ||
          !decl.isPublic || decl.abstract)
        return refuse();
      continue;
    }
    if (!decl.isPublic || decl.abstract || decl.primitive ||
        decl.finiteDefinition || !decl.roles.empty() ||
        !decl.services.empty() || !decl.scopedInputs.empty() ||
        !decl.descriptorInputs.empty() || !decl.permissionBounds.empty() ||
        !decl.capabilityBounds.empty() || !decl.consumerRequirements.empty() ||
        !decl.admissions.empty() || !decl.bounds.empty() ||
        !decl.dataPreconditions.empty())
      return refuse();
    if (row->rule == protocol::FrontendSignature::NativeMessage) {
      if (row->kind != protocol::SourceDeclarationKind::Requirement ||
          decl.kind != Declaration::Kind::Requirement ||
          decl.parameters.size() != 1 ||
          decl.parameters.front().sort != Parameter::Sort::Type ||
          !(decl.parameters.front().permissions == Permissions{}) ||
          !decl.inputs.empty() || !decl.outputs.empty() ||
          !decl.members.empty())
        return refuse();
      continue;
    }
    if (row->rule == protocol::FrontendSignature::RandomConstructor) {
      if (decl.kind != Declaration::Kind::Interface ||
          decl.parameters.size() != 1 ||
          decl.parameters.front().sort != Parameter::Sort::Domain ||
          decl.parameters.front().domainSort != "Field" ||
          !decl.inputs.empty() || !decl.outputs.empty())
        return refuse();
      unsigned expected = 0;
      for (const auto &method : protocol::serviceMethodDeclarations()) {
        if (method.constructor != row->identity)
          continue;
        ++expected;
        auto selected =
            index.member(SourceAccess{decl.id}, decl.id, method.name);
        auto *ref = std::get_if<ResolvedReference>(&selected);
        if (!ref || ref->category != ResolutionCategory::ServiceMethod ||
            index.serviceAssociation(ref->target) != &method ||
            !llvm::any_of(decl.members, [&](auto id) {
              return id.index == ref->target.index;
            }))
          return refuse();
      }
      if (decl.members.size() != expected)
        return refuse();
      continue;
    }
    unsigned count =
        row->rule == protocol::FrontendSignature::RecordRepack ? 2 : 1;
    if (decl.kind != Declaration::Kind::Local ||
        decl.parameters.size() != count || decl.inputs.size() != count ||
        decl.outputs.size() != 1 || decl.inputOrder.size() != count ||
        decl.effectAllowance)
      return refuse();
    for (unsigned i = 0; i < count; ++i)
      if (decl.parameters[i].sort != Parameter::Sort::Type ||
          decl.parameters[i].permissions.copy ||
          decl.parameters[i].permissions.drop ||
          decl.inputs[i].type != parameterType(decl.parameters[i]) ||
          decl.inputOrder[i].kind != Declaration::InputSlot::Kind::Data ||
          decl.inputOrder[i].index != i)
        return refuse();
    if (decl.outputs.front().type != parameterType(decl.parameters.front()))
      return refuse();
  }
  return true;
}
std::optional<Type> recordPayload(Semantics &types, const Declaration &caller,
                                  const Type &source,
                                  protocol::FrontendSignature rule, Span span) {
  if (!isRecordIntrinsic(rule)) {
    types.fail("source.installation", "unknown record signature rule", span);
    return {};
  }
  if (!types.constructorAllowed(caller, source)) {
    types.fail("source.private",
               "record operation requires constructor authority", span);
    return {};
  }
  if (source.kind == Type::Kind::Variant) {
    types.fail("source.type", "variants are unpacked by exhaustive match",
               span);
    return {};
  }
  auto fields = types.fields(source, span);
  if (!fields)
    return {};
  if (rule != protocol::FrontendSignature::RecordUnpack) {
    auto *nominal = types.typeDeclaration(source);
    if ((source.kind != Type::Kind::Record &&
         source.kind != Type::Kind::LogicalRecord) ||
        !nominal || !nominal->resource ||
        (source.kind == Type::Kind::LogicalRecord && nominal->roles.empty())) {
      types.fail("source.type",
                 "custody succession requires an explicitly restricted "
                 "ordinary or fixed-roster distributed record",
                 span);
      return {};
    }
    for (const auto &field : *fields)
      for (Usage permission : {Usage::Copy, Usage::Drop})
        if (!types.requireUsage(
                field.type, permission, span, &caller, "source.permission",
                "custody succession requires Copy and Drop payload fields"))
          return {};
  }
  Type result(fields->empty() ? Type::Kind::Unit : Type::Kind::Tuple);
  for (const auto &field : *fields)
    result.arguments.push_back(field.type);
  if (source.kind == Type::Kind::Associated)
    result = fields->front().type;
  return result;
}
std::optional<ValueId> BodyChecker::recordCall(const Expression &expr,
                                               const CallableReference &target,
                                               protocol::FrontendSignature rule,
                                               unsigned depth) {
  using S = protocol::FrontendSignature;
  bool repack = rule == S::RecordRepack, inspect = rule == S::RecordInspect;
  if ((!local() && !protocol()) ||
      ((inspect || repack) && body.stage == Body::Stage::Host) ||
      expr.children.size() != (repack ? 2u : 1u) || !expr.arguments.empty() ||
      !expr.callLabels.empty() || !expr.staticLabels.empty() || expr.roles) {
    fail("source.call",
         "record operation requires authorized positional values", expr.span);
    return {};
  }
  auto value = expression(expr.children.front(), {}, depth + 1);
  if (!value)
    return {};
  const auto source = body.values[value->index].type;
  auto payloadType =
      recordPayload(checker.types, decl, source, rule, expr.span);
  if (!payloadType || !use(*value, expr.span))
    return {};
  std::optional<ValuePlacement> payloadPlacement;
  if (protocol()) {
    payloadPlacement =
        unpackedPlacement(checker.types, body.values[value->index],
                          *payloadType, decl.roles.size(), expr.span);
    if (!payloadPlacement ||
        !active(body.values[value->index].components, expr.span))
      return {};
  }
  std::vector<ValueId> operands{*value};
  Type result = *payloadType;
  auto kind = Construct::Kind::Unpack;
  if (inspect) {
    result = Type(Type::Kind::Tuple);
    result.arguments = {source, *payloadType};
    kind = Construct::Kind::Inspect;
  } else if (repack) {
    auto payload = expression(expr.children[1], *payloadType, depth + 1, false,
                              payloadPlacement);
    if (!payload || !use(*payload, expr.span))
      return {};
    if (protocol() &&
        body.values[payload->index].placement != payloadPlacement) {
      fail("source.placement", "repack requires the exact payload placement",
           expr.span);
      return {};
    }
    operands.push_back(*payload);
    result = source;
    kind = Construct::Kind::Repack;
  }
  std::optional<ValuePlacement> placed;
  std::vector<unsigned> roles;
  if (protocol()) {
    const auto &wrapper = *body.values[value->index].placement;
    if (inspect) {
      if (!checker.types.chargeIdentity(result, expr.span))
        return {};
      placed = ProductPlacement{typeIdentity(result),
                                placementRoles(wrapper),
                                {wrapper, *payloadPlacement}};
    } else
      placed = repack ? wrapper : *payloadPlacement;
    roles = placementRoles(*placed);
  }
  auto output =
      emit(Construct{operands, {}, kind}, result, roles, expr.span, placed);
  if (!output)
    return {};
  CallBinding binding{target, {source}, operands, {}, {}, {}, {}};
  if (repack)
    binding.arguments.push_back(*payloadType);
  binding.lexicalOwner = decl.id;
  binding.installedSignature = rule;
  for (unsigned i = 0; i < operands.size(); ++i)
    binding.argumentOrder.push_back(i);
  auto &operation = body.operations.back();
  binding.intrinsicSource = witnesses.intrinsics.size();
  witnesses.intrinsics.push_back(std::make_shared<IntrinsicCallSource>(
      IntrinsicCallSource{decl.id,
                          target.declaration,
                          uint32_t(&expr - syntax.expressions.data()),
                          {},
                          target.module,
                          binding.arguments,
                          target.reference}));
  operation.binding = std::move(binding);
  if (!checkCallAction(checker.types, checker.output.declarations, body,
                       operation, checker.output.declarationIndex.get()))
    return {};
  return output;
}
bool checkRecordInvocation(Semantics &types, ArrayRef<Declaration> declarations,
                           const DeclarationIndex &index, const Body &body,
                           const Operation &operation) {
  auto refuse = [&] {
    return types.fail(
        "source.binding-witness",
        "record invocation differs from its association or lexical authority",
        operation.span);
  };
  const auto &binding = *operation.binding;
  auto *row = index.association(binding.target.declaration);
  if (!row || !binding.installedSignature ||
      row->rule != *binding.installedSignature || !isRecordIntrinsic(row) ||
      !binding.lexicalOwner || !binding.intrinsicSource ||
      binding.lexicalOwner->index >= declarations.size() ||
      binding.target.module ||
      (body.mode != Body::Mode::Local && body.mode != Body::Mode::Protocol) ||
      (row->rule != protocol::FrontendSignature::RecordUnpack &&
       body.stage == Body::Stage::Host) ||
      operation.results.size() != 1 ||
      operation.results.front().index >= body.values.size() ||
      binding.notation || !binding.symbol.empty() || !binding.family.empty() ||
      binding.origin || binding.filteredReduction || binding.scopedSource ||
      !binding.roles.empty() || !binding.services.empty() ||
      !binding.scopedArguments.empty() || !binding.descriptorArguments.empty())
    return refuse();
  bool repack = row->rule == protocol::FrontendSignature::RecordRepack;
  unsigned count = repack ? 2 : 1;
  if (binding.operands.size() != count || binding.arguments.size() != count ||
      binding.argumentOrder.size() != count)
    return refuse();
  for (unsigned i = 0; i < count; ++i)
    if (binding.argumentOrder[i] != i ||
        binding.operands[i].index >= body.values.size() ||
        binding.arguments[i] != body.values[binding.operands[i].index].type)
      return refuse();
  auto source = body.values[binding.operands.front().index].type;
  auto payload = recordPayload(types, declarations[binding.lexicalOwner->index],
                               source, *row->rule, operation.span);
  if (!payload)
    return false;
  const auto *action = std::get_if<Construct>(&operation.action);
  if (!action || !action->alternative.empty() ||
      action->operands.size() != count)
    return refuse();
  for (unsigned i = 0; i < count; ++i)
    if (action->operands[i].index != binding.operands[i].index)
      return refuse();
  Type result = *payload;
  auto kind = Construct::Kind::Unpack;
  if (repack) {
    if (binding.arguments[1] != *payload)
      return refuse();
    kind = Construct::Kind::Repack;
    result = source;
  } else if (row->rule == protocol::FrontendSignature::RecordInspect) {
    kind = Construct::Kind::Inspect;
    result = Type(Type::Kind::Tuple);
    result.arguments = {source, *payload};
  }
  if (body.mode == Body::Mode::Protocol) {
    const auto &input = body.values[binding.operands.front().index];
    const auto &output = body.values[operation.results.front().index];
    auto payloadPlacement = unpackedPlacement(
        types, input, *payload,
        declarations[binding.lexicalOwner->index].roles.size(), operation.span);
    if (!payloadPlacement)
      return refuse();
    ValuePlacement placed = *payloadPlacement;
    if (repack) {
      const auto &replacement = body.values[binding.operands[1].index];
      if (replacement.placement != payloadPlacement ||
          replacement.components != placementRoles(*payloadPlacement))
        return refuse();
      placed = *input.placement;
    } else if (row->rule == protocol::FrontendSignature::RecordInspect) {
      if (!types.chargeIdentity(result, operation.span))
        return false;
      placed = ProductPlacement{typeIdentity(result),
                                input.components,
                                {*input.placement, *payloadPlacement}};
    }
    if (output.placement != placed ||
        output.components != placementRoles(placed))
      return refuse();
  }
  return (action->kind == kind &&
          body.values[operation.results.front().index].type == result) ||
         refuse();
}
} // namespace zkc::language::detail
