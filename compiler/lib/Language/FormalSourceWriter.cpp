#include "FormalSourceWriter.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
class Writer {
  const FormalSource &source;
  const FormalEmit &emit;
  const FormalChild &child;
  json::Value edge(StringRef name, FormalNodeId id, unsigned index = 0) {
    return child(name, index, [&] { return node(id); });
  }
  json::Value edge(StringRef name, std::optional<FormalNodeId> id) {
    return id ? edge(name, *id) : json::Value(nullptr);
  }
  json::Array edges(StringRef name, ArrayRef<FormalNodeId> ids) {
    json::Array result;
    for (unsigned i = 0; i < ids.size(); ++i)
      result.push_back(edge(name, ids[i], i));
    return result;
  }
  json::Value node(FormalNodeId id) {
    const auto &value = source.nodes.at(id.index);
    return std::visit([&](const auto &form) { return write(form, value.span); },
                      value.value);
  }
  json::Value write(const FormalReference &form, source::Span span) {
    return emit("formal.reference", span, json::Object{{"name", form.name}});
  }
  json::Value write(const FormalLiteral &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalLiteral::Kind::Natural:
      kind = "formal.natural";
      break;
    case FormalLiteral::Kind::Boolean:
      kind = "formal.boolean";
      break;
    case FormalLiteral::Kind::String:
      kind = "formal.string";
      break;
    }
    return emit(kind, span, json::Object{{"literal", form.spelling}});
  }
  json::Value write(const FormalHole &, source::Span span) {
    return emit("formal.hole", span, json::Object{});
  }
  json::Value write(const FormalSequence &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalSequence::Kind::Group:
      kind = "formal.group";
      break;
    case FormalSequence::Kind::Tuple:
      kind = "formal.tuple";
      break;
    case FormalSequence::Kind::Array:
      kind = "formal.array";
      break;
    case FormalSequence::Kind::Block:
      kind = "formal.block";
      break;
    case FormalSequence::Kind::Parameters:
      kind = "formal.parameters";
      break;
    case FormalSequence::Kind::StaticParameters:
      kind = "formal.static_parameters";
      break;
    case FormalSequence::Kind::Effects:
      kind = "formal.effects";
      break;
    case FormalSequence::Kind::Constraints:
      kind = "formal.constraints";
      break;
    case FormalSequence::Kind::Result:
      kind = "formal.result";
      break;
    case FormalSequence::Kind::Fields:
      kind = "formal.fields";
      break;
    }
    return emit(kind, span,
                json::Object{{"elements", edges("elements", form.elements)}});
  }
  json::Value write(const FormalArgument &form, source::Span span) {
    StringRef purpose;
    switch (form.purpose) {
    case FormalArgument::Purpose::Ordinary:
      purpose = "ordinary";
      break;
    case FormalArgument::Purpose::Statement:
      purpose = "statement";
      break;
    case FormalArgument::Purpose::Witness:
      purpose = "witness";
      break;
    case FormalArgument::Purpose::Parameter:
      purpose = "parameter";
      break;
    }
    return emit("formal.argument", span,
                json::Object{{"label", edge("label", form.label)},
                             {"type", edge("type", form.type)},
                             {"value", edge("value", form.value)},
                             {"ghost", form.ghost},
                             {"purpose", purpose}});
  }
  json::Value write(const FormalApplication &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalApplication::Kind::Call:
      kind = "formal.call";
      break;
    case FormalApplication::Kind::Static:
      kind = "formal.static";
      break;
    case FormalApplication::Kind::Index:
      kind = "formal.index";
      break;
    case FormalApplication::Kind::Record:
      kind = "formal.record";
      break;
    case FormalApplication::Kind::Delimited:
      kind = "formal.delimited";
      break;
    }
    return emit(kind, span,
                json::Object{{"function", edge("function", form.function)},
                             {"arguments", edges("arguments", form.arguments)},
                             {"notation", form.notation}});
  }
  json::Value write(const FormalMember &form, source::Span span) {
    return emit("formal.member", span,
                json::Object{{"base", edge("base", form.base)},
                             {"member", edge("member", form.member)},
                             {"qualified", form.qualified}});
  }
  json::Value write(const FormalOperator &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalOperator::Kind::Prefix:
      kind = "formal.prefix";
      break;
    case FormalOperator::Kind::Postfix:
      kind = "formal.postfix";
      break;
    case FormalOperator::Kind::Infix:
      kind = "formal.infix";
      break;
    }
    return emit(kind, span,
                json::Object{{"operands", edges("operands", form.operands)},
                             {"symbol", form.symbol}});
  }
  json::Value write(const FormalRoles &form, source::Span span) {
    return emit("formal.roles", span,
                json::Object{{"holder", edge("holder", form.holder)},
                             {"participants",
                              edges("participants", form.participants)}});
  }
  json::Value write(const FormalAvailability &form, source::Span span) {
    return emit("formal.availability", span,
                json::Object{{"value", edge("value", form.value)},
                             {"roles", edge("roles", form.roles)}});
  }
  json::Value write(const FormalDeclaration &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalDeclaration::Kind::Specification:
      kind = "formal.specification";
      break;
    case FormalDeclaration::Kind::Relation:
      kind = "formal.relation";
      break;
    case FormalDeclaration::Kind::GhostFunction:
      kind = "formal.ghost_function";
      break;
    case FormalDeclaration::Kind::OracleFunction:
      kind = "formal.oracle_function";
      break;
    case FormalDeclaration::Kind::Law:
      kind = "formal.law_declaration";
      break;
    }
    return emit(
        kind, span,
        json::Object{{"name", edge("name", form.name)},
                     {"parameters", edge("parameters", form.parameters)},
                     {"inputs", edge("inputs", form.inputs)},
                     {"roles", edge("roles", form.roles)},
                     {"result", edge("result", form.result)},
                     {"constraints", edge("constraints", form.constraints)},
                     {"effects", edge("effects", form.effects)},
                     {"body", edge("body", form.body)},
                     {"subject", edge("subject", form.subject)},
                     {"public", form.isPublic}});
  }
  json::Value write(const FormalClause &form, source::Span span) {
    StringRef kind;
    switch (form.kind) {
    case FormalClause::Kind::Requires:
      kind = "formal.requires";
      break;
    case FormalClause::Kind::Ensures:
      kind = "formal.ensures";
      break;
    case FormalClause::Kind::Target:
      kind = "formal.target";
      break;
    case FormalClause::Kind::Reduces:
      kind = "formal.reduces";
      break;
    case FormalClause::Kind::Request:
      kind = "formal.request";
      break;
    case FormalClause::Kind::Alias:
      kind = "formal.alias";
      break;
    case FormalClause::Kind::Law:
      kind = "formal.law";
      break;
    }
    return emit(kind, span,
                json::Object{{"label", edge("label", form.label)},
                             {"value", edge("value", form.value)},
                             {"residual", edge("residual", form.residual)}});
  }
  json::Value write(const FormalImport &form, source::Span span) {
    return emit("formal.import", span,
                json::Object{{"module", edge("module", form.module)},
                             {"alias", edge("alias", form.alias)},
                             {"members", edges("members", form.members)},
                             {"public", form.isPublic},
                             {"lean", form.lean}});
  }
  json::Value write(const FormalBinding &form, source::Span span) {
    return emit("formal.binding", span,
                json::Object{{"pattern", edge("pattern", form.pattern)},
                             {"value", edge("value", form.value)},
                             {"type", edge("type", form.type)},
                             {"mutable", form.mutableBinding},
                             {"ordered", form.ordered},
                             {"update", form.update}});
  }
  json::Value write(const FormalReturn &form, source::Span span) {
    return emit("formal.return", span,
                json::Object{{"value", edge("value", form.value)}});
  }
  json::Value write(const FormalGuard &form, source::Span span) {
    return emit("formal.guard", span,
                json::Object{{"condition", edge("condition", form.condition)},
                             {"roles", edge("roles", form.roles)}});
  }
  json::Value write(const FormalIf &form, source::Span span) {
    return emit(
        "formal.if", span,
        json::Object{{"condition", edge("condition", form.condition)},
                     {"consequent", edge("consequent", form.consequent)},
                     {"alternative", edge("alternative", form.alternative)}});
  }
  json::Value write(const FormalMatch &form, source::Span span) {
    return emit("formal.match", span,
                json::Object{{"value", edge("value", form.value)},
                             {"cases", edge("cases", form.cases)}});
  }
  json::Value write(const FormalCase &form, source::Span span) {
    return emit("formal.case", span,
                json::Object{{"pattern", edge("pattern", form.pattern)},
                             {"body", edge("body", form.body)}});
  }
  json::Value write(const FormalFor &form, source::Span span) {
    return emit("formal.for", span,
                json::Object{{"index", edge("index", form.index)},
                             {"lower", edge("lower", form.lower)},
                             {"upper", edge("upper", form.upper)},
                             {"body", edge("body", form.body)},
                             {"roles", edge("roles", form.roles)},
                             {"maximum", edge("maximum", form.maximum)}});
  }
  json::Value write(const FormalSend &form, source::Span span) {
    return emit(
        "formal.send", span,
        json::Object{{"value", edge("value", form.value)},
                     {"sender", edge("sender", form.sender)},
                     {"receivers", edges("receivers", form.receivers)}});
  }
  json::Value write(const FormalQuery &form, source::Span span) {
    return emit("formal.query", span,
                json::Object{{"handle", edge("handle", form.handle)},
                             {"position", edge("position", form.position)}});
  }
  json::Value write(const FormalQuantifier &form, source::Span span) {
    return emit("formal.quantifier", span,
                json::Object{{"variable", edge("variable", form.variable)},
                             {"type", edge("type", form.type)},
                             {"body", edge("body", form.body)},
                             {"existential", form.existential}});
  }
  json::Value write(const FormalLambda &form, source::Span span) {
    return emit(
        "formal.lambda", span,
        json::Object{{"parameters", edges("parameters", form.parameters)},
                     {"body", edge("body", form.body)}});
  }
  json::Value write(const FormalReduction &form, source::Span span) {
    json::Array bindings;
    for (unsigned i = 0; i < form.bindings.size(); ++i)
      bindings.push_back(
          json::Object{{"pattern", edge("pattern", form.bindings[i].first, i)},
                       {"domain", edge("domain", form.bindings[i].second, i)}});
    return emit("formal.reduction", span,
                json::Object{{"filter", edge("filter", form.filter)},
                             {"body", edge("body", form.body)},
                             {"symbol", form.symbol},
                             {"bindings", std::move(bindings)}});
  }
  json::Value write(const FormalAttribute &form, source::Span span) {
    return emit(
        "formal.attribute", span,
        json::Object{{"name", edge("name", form.name)},
                     {"arguments", edges("arguments", form.arguments)}});
  }

public:
  Writer(const FormalSource &source, const FormalEmit &emit,
         const FormalChild &child)
      : source(source), emit(emit), child(child) {}
  json::Value run() { return node(source.root); }
};
} // namespace
json::Value writeFormalSource(const FormalSource &source,
                              const FormalEmit &emit,
                              const FormalChild &child) {
  return Writer(source, emit, child).run();
}
} // namespace zkc::language::detail
