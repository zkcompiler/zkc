#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Diagnostics.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<ResolvedReference>
Checker::constructionMember(const Declaration &owner, const Type &provider,
                            StringRef name, Span span,
                            std::optional<ResolvedReference> selectedProvider) {
  const Declaration *contract = nullptr;
  std::optional<ResolvedReference> reference = std::move(selectedProvider);
  auto binderOwner = owner.id;
  uint32_t slot = UINT32_MAX;
  if (provider.symbolic) {
    auto *parameter = types.parameter(provider.domain);
    if (parameter && parameter->interface) {
      contract = &output.declarations[parameter->interface->index];
      auto found = moduleParameterReferences.find(parameter->atom);
      if (found != moduleParameterReferences.end()) {
        reference = found->second.reference;
        binderOwner = found->second.owner;
        slot = found->second.slot;
      }
    }
  } else if (auto *module = types.typeDeclaration(provider);
             module && module->implementation) {
    contract = types.typeDeclaration(*module->implementation);
    if (!reference) {
      auto selected =
          index().lookup(accessFor(owner), "::" + module->qualifiedName,
                         {[&] { return types.charge(1, span); }, {}});
      if (auto *ref = std::get_if<ResolvedReference>(&selected))
        reference = *ref;
      else if (!acceptFailure(std::get<LookupFailure>(selected), span, true))
        return {};
    }
  }
  if (!contract || contract->kind != Declaration::Kind::Interface ||
      !reference) {
    types.fail("source.construction", "provider must implement an interface",
               span);
    return {};
  }
  auto selected = index().member(accessFor(owner), contract->id, name,
                                 {[&] { return types.charge(1, span); }, {}});
  if (auto *failure = std::get_if<LookupFailure>(&selected)) {
    if (failure->kind != LookupFailureKind::NotFound)
      acceptFailure(*failure, span, true);
    else
      types.fail("source.construction", "provider interface requires " + name,
                 span);
    return {};
  }
  const auto &member = std::get<ResolvedReference>(selected);
  reference->target = member.target;
  reference->category = member.category;
  reference->path.insert(reference->path.end(), member.path.begin(),
                         member.path.end());
  // Concrete providers also retain the exact module term; the binder slot is
  // absent (UINT32_MAX), rather than inferred later from a display string.
  reference->abstract =
      AbstractMemberContext{provider, contract->id, binderOwner, slot};
  if (!signature(member.target) ||
      !recordReference(owner, ReferenceRoute::Construction, *reference, name,
                       span))
    return {};
  return reference;
}
bool Checker::constructionCodec(Declaration &decl,
                                const SyntaxConstruction &syntax,
                                ConstructionDefinition &result,
                                const Substitution &substitution) {
  if (!syntax.codec)
    return true;
  if (result.codec)
    return types.fail("source.construction",
                      "an inherited record format cannot be replaced",
                      syntax.codec->span);
  SaveAndRestore site(referenceSite, syntax.codec->referenceSite);
  auto provider = type(decl, *syntax.codec);
  if (!provider)
    return false;
  if (provider->kind != Type::Kind::Module)
    return types.fail("source.construction", "record format requires a module",
                      syntax.codec->span);
  auto member = constructionMember(
      decl, *provider, "Record", syntax.codec->span,
      typeReferences.count(syntax.codec->referenceSite)
          ? std::optional(typeReferences.at(syntax.codec->referenceSite))
          : std::nullopt);
  if (!member)
    return false;
  auto record = types.associated(*provider, member->target, syntax.codec->span);
  if (!record || !types.executableType(*record, syntax.codec->span))
    return false;
  auto permissions = types.permissions(*record, decl.span, &decl);
  if (!permissions)
    return false;
  if (!permissions->copy || !permissions->drop)
    return types.fail("source.construction",
                      "codec Record requires Copy and Drop", decl.span);
  ConstructionCodec codec;
  codec.provider = *provider;
  codec.record = *record;
  const auto &protocol = output.declarations[decl.target->index];
  Type layout(Type::Kind::Tuple);
  for (const auto &input : syntax.layout) {
    if (!types.charge(protocol.inputs.size(), input.span))
      return false;
    auto found = find_if(protocol.inputs, [&](const Port &port) {
      return port.name == input.name;
    });
    if (found == protocol.inputs.end() ||
        found->roles.size() != protocol.roles.size())
      return types.fail("source.construction",
                        "format layout selects only shared protocol inputs",
                        input.span);
    unsigned index = found - protocol.inputs.begin();
    if (is_contained(codec.inputs, index))
      return types.fail("source.construction", "duplicate format layout input",
                        input.span);
    auto selected = types.substitute(found->type, substitution, input.span);
    if (!selected || !types.executableType(*selected, input.span))
      return false;
    layout.arguments.push_back(std::move(*selected));
    codec.inputs.push_back(index);
  }
  if (layout.arguments.empty())
    layout = Type(Type::Kind::Unit);
  else if (layout.arguments.size() == 1) {
    Type single = layout.arguments.front();
    layout = std::move(single);
  }
  auto method = [&](StringRef name, ArrayRef<Type> inputs,
                    ArrayRef<Type> outputs, ConstructionMethod &selected) {
    auto found = constructionMember(
        decl, *provider, name, decl.span,
        typeReferences.count(syntax.codec->referenceSite)
            ? std::optional(typeReferences.at(syntax.codec->referenceSite))
            : std::nullopt);
    if (!found)
      return false;
    const auto &function = output.declarations[found->target.index];
    if (function.kind != Declaration::Kind::Local ||
        function.parameters.size() !=
            output.declarations[function.parent->index].parameters.size() ||
        function.inputOrder.size() != function.inputs.size() ||
        function.inputs.size() != inputs.size() ||
        function.outputs.size() != outputs.size())
      return types.fail("source.construction",
                        "codec method signature differs: " + name.str(),
                        decl.span);
    auto bindings =
        types.boundMemberSubstitution(function, *provider, decl.span);
    if (!bindings)
      return false;
    for (const auto &[ports, expected] :
         {std::pair<ArrayRef<Port>, ArrayRef<Type>>{function.inputs, inputs},
          {function.outputs, outputs}})
      for (auto [port, value] : zip(ports, expected)) {
        auto actual = types.substitute(port.type, *bindings, decl.span);
        if (!actual)
          return false;
        if (*actual != value)
          return types.fail("source.construction",
                            "codec method type differs: " + name.str(),
                            decl.span);
      }
    selected.target = {found->target, *provider, *found};
    for (const auto &parameter : function.parameters)
      selected.arguments.push_back(bindings->at(parameter.atom));
    return true;
  };
  auto bytes = builtinType("bytes", {});
  if (!bytes)
    return types.accept(bytes.takeError(), decl.span);
  if (!method("initialize", {layout}, {*record}, codec.initialize) ||
      !method("write", {*record}, {*bytes}, codec.write) ||
      !method("finish", {*record, *bytes}, {Type(Type::Kind::Unit)},
              codec.finish))
    return false;
  result.codec = std::move(codec);
  return true;
}
} // namespace zkc::language::detail
