#include "Checker.h"
#include "zkc/Contracts/Services.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::language::detail {
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
        // A static binder shadows an implicit installed source constructor.
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
