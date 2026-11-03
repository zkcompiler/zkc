#include "Internal.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::language::detail {
namespace {
Error refuse(const Twine &message, Span span) {
  return failure("source.installation", message, span);
}
SyntaxType named(StringRef name, Span span) {
  SyntaxType type;
  type.kind = SyntaxType::Kind::Name;
  type.name = name.str();
  type.span = span;
  return type;
}
/// A catalog type term in the spelling its declaration would be written with.
Expected<SyntaxType> term(const protocol::SourceTerm &value,
                          ArrayRef<SyntaxParameter> statics, Span span) {
  if (!value.index)
    return named(value.constructor, span);
  if (*value.index >= statics.size())
    return refuse("installed type names an absent static parameter", span);
  auto name = statics[*value.index].name;
  if (!value.member.empty())
    name += "::" + value.member;
  return named(name, span);
}
Expected<SyntaxDeclaration>
declaration(const protocol::FrontendDeclaration &row, Span span, Work &work) {
  if (auto error = work.count(work.declarations, work.limits.declarations,
                              "declaration count", span))
    return std::move(error);
  if (auto error =
          work.charge(1 + row.statics.size() + row.inputs.size(), span))
    return std::move(error);
  SyntaxDeclaration result;
  result.kind = row.kind == protocol::SourceDeclarationKind::Math
                    ? Declaration::Kind::Math
                : row.kind == protocol::SourceDeclarationKind::Local
                    ? Declaration::Kind::Local
                    : Declaration::Kind::Interface;
  result.name = row.name;
  result.isPublic = result.explicitPublic = true;
  result.span = span;
  for (const auto &value : row.statics) {
    SyntaxParameter parameter;
    parameter.name = value.name;
    parameter.span = span;
    if (value.kind == "Domain")
      parameter.constraint = named(value.sort, span);
    else if (value.kind == "Type")
      parameter.constraint = named("Type", span);
    else
      return refuse("installed static parameter kind has no source form", span);
    result.parameters.push_back(std::move(parameter));
  }
  for (const auto &value : row.inputs) {
    auto type = term(value.type, result.parameters, span);
    if (!type)
      return type.takeError();
    result.inputOrder.push_back(
        {Declaration::InputSlot::Kind::Data, unsigned(result.inputs.size())});
    SyntaxPort port;
    port.name = value.name;
    port.type = std::move(*type);
    port.span = span;
    result.inputs.push_back(std::move(port));
  }
  if (row.output) {
    auto type = term(*row.output, result.parameters, span);
    if (!type)
      return type.takeError();
    SyntaxPort port;
    port.name = "result";
    port.type = std::move(*type);
    port.span = span;
    result.outputs.push_back(std::move(port));
  }
  // A primitive declaration keeps the primitive path and its agreement checks;
  // a rule association has no body.
  if (!row.rule)
    result.primitive = row.primitive;
  return result;
}
Expected<SyntaxOperator> notation(const protocol::FrontendNotation &row,
                                  SourceId source, Span span) {
  if (!admittedOperatorSymbol(row.symbol))
    return refuse("installed notation symbol is not an operator", span);
  SyntaxOperator result;
  result.symbol = row.symbol;
  result.target = named(row.target, span);
  result.isPublic = row.isPublic;
  result.span = span;
  if (!row.fixity.empty()) {
    using Position = NotationDescriptor::Position;
    using Association = NotationDescriptor::Association;
    auto descriptor = std::make_shared<NotationDescriptor>();
    descriptor->position = Position::Infix;
    descriptor->association = row.fixity == "left"    ? Association::Left
                              : row.fixity == "right" ? Association::Right
                                                      : Association::None;
    descriptor->arity = 2;
    descriptor->precedence = row.precedence;
    descriptor->symbol = row.symbol;
    // As for written declarations, ASCII operator syntax is fixed.
    if (static_cast<unsigned char>(row.symbol.front()) < 128) {
      auto fixed = fixedNotationEnvironment(source);
      auto found = fixed.find(descriptor->key());
      if (found == fixed.end() || *found->second.descriptor != *descriptor)
        return refuse("installed notation changes fixed ASCII syntax", span);
    }
    result.notation = std::move(descriptor);
    result.explicitNotation = true;
  }
  return result;
}
} // namespace
std::vector<std::string> installedModules() {
  std::vector<std::string> result;
  for (const auto &row : protocol::frontendDeclarations())
    if (!is_contained(result, row.module))
      result.push_back(row.module);
  return result;
}
Expected<SyntaxDeclaration> readInstalledModule(const SourceBuffer &source,
                                                SourceId id, Work &work) {
  return readInstalledModule(source, id, work, protocol::frontendDeclarations(),
                             protocol::frontendNotations());
}
Expected<SyntaxDeclaration>
readInstalledModule(const SourceBuffer &source, SourceId id, Work &work,
                    ArrayRef<protocol::FrontendDeclaration> declarations,
                    ArrayRef<protocol::FrontendNotation> notations) {
  Span span{id, 0, 0};
  SyntaxDeclaration result;
  result.kind = Declaration::Kind::Module;
  result.name = source.module;
  result.isPublic = true;
  result.span = span;
  if (auto error = work.count(work.declarations, work.limits.declarations,
                              "declaration count", span))
    return std::move(error);
  for (const auto &row : declarations) {
    if (row.module != source.module)
      continue;
    auto member = declaration(row, span, work);
    if (!member)
      return member.takeError();
    result.members.push_back(std::move(*member));
  }
  for (const auto &row : notations) {
    if (row.module != source.module)
      continue;
    if (auto error = work.charge(1, span))
      return std::move(error);
    auto binding = notation(row, id, span);
    if (!binding)
      return binding.takeError();
    result.operators.push_back(std::move(*binding));
  }
  if (result.members.empty())
    return refuse("installed module declares nothing", span);
  return result;
}
} // namespace zkc::language::detail
