#include "ManagedServices.h"
#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::language::detail {
unsigned serviceStaticCount(protocol::ServiceSignature signature) {
  switch (signature) {
  case protocol::ServiceSignature::RandomDraw:
    return 0;
  case protocol::ServiceSignature::RandomIndex:
    return 1;
  case protocol::ServiceSignature::RandomIndices:
    return 2;
  }
  llvm_unreachable("unknown managed signature");
}
Type serviceResult(protocol::ServiceSignature signature, const Type &field) {
  switch (signature) {
  case protocol::ServiceSignature::RandomDraw:
    return field;
  case protocol::ServiceSignature::RandomIndex:
    return Type(Type::Kind::Index);
  case protocol::ServiceSignature::RandomIndices:
    return cantFail(builtinType("indices", {}));
  }
  llvm_unreachable("unknown managed signature");
}
std::optional<CallableReference>
resolveServiceMethod(Semantics &types, const DeclarationIndex &index,
                     DeclarationId owner, const ResolvedReference &constructor,
                     StringRef name, Span span) {
  auto *association = index.ruleAssociation(constructor.target);
  if (constructor.category != ResolutionCategory::ServiceConstructor ||
      !association ||
      association->rule != protocol::FrontendSignature::RandomConstructor) {
    types.fail("source.service", "receiver has no managed constructor", span);
    return {};
  }
  auto selected = index.member(SourceAccess{owner}, constructor.target, name,
                               {[&] { return types.charge(1, span); }, {}});
  auto *member = std::get_if<ResolvedReference>(&selected);
  auto *row = member ? index.serviceAssociation(member->target) : nullptr;
  if (!member || member->category != ResolutionCategory::ServiceMethod ||
      !row || row->constructor != association->identity) {
    if (!types.diagnostic)
      types.fail("source.service", "unknown installed service member", span);
    return {};
  }
  auto reference = constructor;
  reference.target = member->target;
  reference.category = member->category;
  reference.path.insert(reference.path.end(), member->path.begin(),
                        member->path.end());
  return CallableReference{member->target, {}, std::move(reference)};
}
bool checkServiceInvocation(Semantics &types,
                            ArrayRef<Declaration> declarations,
                            const DeclarationIndex &index, const Body &body,
                            const Operation &op) {
  auto refuse = [&] {
    return types.fail("source.binding-witness",
                      "managed invocation differs from its selected method",
                      op.span);
  };
  if (!op.binding)
    return refuse();
  const auto &binding = *op.binding;
  auto *row = index.serviceAssociation(binding.target.declaration);
  const auto *query = std::get_if<ServiceQuery>(&op.action);
  if (!row || !query || body.mode != Body::Mode::Protocol ||
      binding.target.reference.category != ResolutionCategory::ServiceMethod ||
      binding.target.reference.target.index !=
          binding.target.declaration.index ||
      binding.target.declaration.index >= declarations.size() ||
      binding.target.module || binding.services.size() != 1 ||
      binding.services.front().index != query->service.index ||
      query->service.index >= body.services.size() ||
      binding.arguments.size() != 1 + serviceStaticCount(row->signature) ||
      !binding.operands.empty() || !binding.argumentOrder.empty() ||
      !binding.scopedArguments.empty() || !binding.domainArguments.empty() ||
      binding.notation || binding.origin || !binding.symbol.empty() ||
      !binding.family.empty() || binding.filteredReduction ||
      binding.installedSignature || binding.intrinsicSource ||
      binding.lexicalOwner || !binding.scopedSource || op.results.size() != 1 ||
      op.results.front().index >= body.values.size())
    return refuse();
  const auto &port = body.services[query->service.index];
  auto *constructor = index.ruleAssociation(port.constructor.target);
  const auto &decl = declarations[binding.target.declaration.index];
  if (!constructor || constructor->identity != row->constructor ||
      !decl.parent || decl.parent->index != port.constructor.target.index ||
      port.constructor.category != ResolutionCategory::ServiceConstructor ||
      binding.arguments.front() != port.field ||
      port.field.kind != Type::Kind::Field ||
      binding.roles != std::vector<unsigned>{port.owner})
    return refuse();
  auto selected = resolveServiceMethod(types, index, decl.id, port.constructor,
                                       decl.name, op.span);
  if (!selected || selected->reference != binding.target.reference)
    return refuse();
  unsigned count = serviceStaticCount(row->signature);
  if (bool(query->bound) != (count >= 1) || bool(query->count) != (count == 2))
    return refuse();
  for (unsigned i = 0; i < count; ++i) {
    const auto &term = binding.arguments[i + 1];
    if (term.kind != Type::Kind::Natural ||
        (term.dimension.isClosed() &&
         !protocol::uniformIndexBound(term.dimension.closedValue())) ||
        term.dimension != (i == 0 ? *query->bound : *query->count))
      return refuse();
  }
  const auto &value = body.values[op.results.front().index];
  return (value.type == serviceResult(row->signature, port.field) &&
          value.components == std::vector<unsigned>{port.owner}) ||
         refuse();
}
bool Checker::classifyServices() {
  for (auto &decl : output.declarations) {
    if (decl.kind != Declaration::Kind::Protocol)
      continue;
    auto &written = *sources[decl.id.index];
    auto inputs = std::move(written.inputs);
    written.inputs.clear();
    for (auto &slot : written.inputOrder) {
      if (slot.kind != Declaration::InputSlot::Kind::Data)
        continue;
      auto port = std::move(inputs[slot.index]);
      if (!types.charge(1, port.span))
        return false;
      const protocol::FrontendDeclaration *service = nullptr;
      if (port.type.kind == SyntaxType::Kind::Name) {
        // A static binder shadows an installed prelude constructor.
        bool bound = false;
        for (auto scope = std::optional(decl.id); scope;
             scope = output.declarations[scope->index].parent)
          for (const auto &parameter : sources[scope->index]->parameters) {
            if (!types.charge(1, port.span))
              return false;
            bound |=
                parameter.name == StringRef(port.type.name).split("::").first;
          }
        if (!bound) {
          // A data port's type records its own route when the signature
          // resolves it, so this classification records only a service.
          auto reference = select(decl, port.type.name, port.type.span, false);
          if (types.diagnostic)
            return false;
          if (reference) {
            const auto &constructor =
                output.declarations[reference->target.index];
            service = index().association(reference->target);
            if (reference->category != ResolutionCategory::ServiceConstructor)
              service = nullptr;
            if (service) {
              port.serviceConstructor = constructor.qualifiedName;
              port.serviceReference = *reference;
              SaveAndRestore site(referenceSite, port.type.referenceSite);
              if (!recordReference(decl, ReferenceRoute::Service, *reference,
                                   port.type.name, port.type.span))
                return false;
            }
          }
        }
      }
      auto &destination = service ? written.services : written.inputs;
      slot.kind = service ? Declaration::InputSlot::Kind::Service
                          : Declaration::InputSlot::Kind::Data;
      slot.index = destination.size();
      destination.push_back(std::move(port));
    }
    decl.inputOrder = written.inputOrder;
  }
  return true;
}
} // namespace zkc::language::detail
