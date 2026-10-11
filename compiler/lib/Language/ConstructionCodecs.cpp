#include "Checker.h"
#include "zkc/Language/Builtins.h"
using namespace llvm;
namespace zkc::language::detail {
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
  auto provider = type(decl, *syntax.codec);
  if (!provider)
    return false;
  if (provider->kind != Type::Kind::Component)
    return types.fail("source.construction",
                      "record format requires a component", syntax.codec->span);
  auto record = types.associated(*provider, "Record", syntax.codec->span);
  if (!record)
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
    if (!selected)
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
  const Declaration *owner =
      provider->symbolic
          ? &output.declarations[types.parameter(provider->domain)
                                     ->interface->index]
          : types.typeDeclaration(*provider);
  auto method = [&](StringRef name, ArrayRef<Type> inputs,
                    ArrayRef<Type> outputs, ConstructionMethod &selected) {
    if (!types.charge(owner->members.size(), decl.span))
      return false;
    auto found = find_if(owner->members, [&](DeclarationId member) {
      return output.declarations[member.index].name == name;
    });
    if (found == owner->members.end())
      return types.fail("source.construction", "codec requires " + name.str(),
                        decl.span);
    const auto &function = output.declarations[found->index];
    if (function.kind != Declaration::Kind::Local ||
        function.parameters.size() != owner->parameters.size() ||
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
    selected.target = {*found, *provider};
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
