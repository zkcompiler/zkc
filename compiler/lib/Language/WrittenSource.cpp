#include "WrittenSource.h"
#include "WrittenSourceIndex.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/Support/ErrorHandling.h"
#include <tuple>

using namespace llvm;
namespace zkc::language::detail {
Expected<std::shared_ptr<WrittenSources>>
retainWrittenHeaders(ArrayRef<SyntaxDeclaration> syntax, Work &work) {
  // Every header node consumes a token. Charge before copying, including the
  // captured and installation source headers, under the checking work ceiling.
  if (auto error = work.charge(work.tokens))
    return std::move(error);
  auto result = std::make_shared<WrittenSources>();
  result->modules.assign(syntax.begin(), syntax.end());
  return result;
}
Error retainWrittenBodies(WrittenSources &written,
                          ArrayRef<SyntaxDeclaration *> sources, Work &work) {
  if (auto error = work.charge(work.tokens + sources.size()))
    return error;
  using Key = std::tuple<uint32_t, uint32_t, uint32_t>;
  auto key = [](Span span) {
    return Key(span.source.index, span.begin, span.end);
  };
  std::map<Key, const SyntaxDeclaration *> parsed;
  for (auto *source : sources)
    if (!source->generated)
      parsed.try_emplace(key(source->span), source);
  std::map<Key, const FormalSyntax *> formalSources;
  for (auto *source : sources)
    for (const auto &formal : source->formalSyntax)
      formalSources.emplace(key(formal.tree.span(formal.node)), &formal);
  std::function<Error(SyntaxDeclaration &)> finish =
      [&](SyntaxDeclaration &source) -> Error {
    for (auto &formal : source.formalSyntax) {
      auto found = formalSources.find(key(formal.tree.span(formal.node)));
      if (found == formalSources.end())
        return failure("source.syntax", "formal source was not retained",
                       formal.tree.span(formal.node));
      formal = *found->second;
    }
    if (source.deferredBody) {
      auto found = parsed.find(key(source.span));
      if (found == parsed.end() || found->second->deferredBody)
        return failure("source.syntax", "written body was not retained",
                       source.span);
      source.expressions = found->second->expressions;
      source.bodies = found->second->bodies;
      source.deferredBody.reset();
    }
    for (auto &member : source.members)
      if (auto error = finish(member))
        return error;
    return Error::success();
  };
  for (auto &module : written.modules)
    if (auto error = finish(module))
      return error;
  return Error::success();
}
} // namespace zkc::language::detail

namespace zkc::language {
namespace {
using namespace detail;
json::Array strings(ArrayRef<std::string> values) {
  json::Array result;
  for (const auto &value : values)
    result.push_back(value);
  return result;
}
json::Value optionalString(const std::optional<std::string> &value) {
  return value ? json::Value(*value) : json::Value(nullptr);
}
json::Object effects(Effects value) {
  return json::Object{{"stop", value.mayStop}, {"opaque", value.opaque}};
}
StringRef syntaxKind(SyntaxType::Kind value) {
  switch (value) {
  case SyntaxType::Kind::Hole:
    return "hole";
  case SyntaxType::Kind::Name:
    return "name";
  case SyntaxType::Kind::Builtin:
    return "builtin";
  case SyntaxType::Kind::Formal:
    return "formal";
  case SyntaxType::Kind::Natural:
    return "natural";
  case SyntaxType::Kind::Add:
    return "add";
  case SyntaxType::Kind::Multiply:
    return "multiply";
  case SyntaxType::Kind::PowerOfTwo:
    return "power_of_two";
  case SyntaxType::Kind::Array:
    return "array";
  case SyntaxType::Kind::Tuple:
    return "tuple";
  }
  llvm_unreachable("unknown syntax kind");
}
StringRef syntaxKind(Pattern::Kind value) {
  switch (value) {
  case Pattern::Kind::Name:
    return "name";
  case Pattern::Kind::Ignore:
    return "ignore";
  case Pattern::Kind::Unit:
    return "unit";
  case Pattern::Kind::Tuple:
    return "tuple";
  case Pattern::Kind::Record:
    return "record";
  }
  llvm_unreachable("unknown syntax kind");
}
StringRef syntaxKind(Expression::Kind value) {
  switch (value) {
  case Expression::Kind::Name:
    return "name";
  case Expression::Kind::Lambda:
    return "lambda";
  case Expression::Kind::Decimal:
    return "decimal";
  case Expression::Kind::Boolean:
    return "boolean";
  case Expression::Kind::Call:
    return "call";
  case Expression::Kind::Kernel:
    return "kernel";
  case Expression::Kind::Intrinsic:
    return "intrinsic";
  case Expression::Kind::Map:
    return "map";
  case Expression::Kind::DomainProduct:
    return "domain_product";
  case Expression::Kind::OracleSequenceEmpty:
    return "oracle_sequence_empty";
  case Expression::Kind::OracleSequenceAppend:
    return "oracle_sequence_append";
  case Expression::Kind::OracleSequenceAt:
    return "oracle_sequence_at";
  case Expression::Kind::OracleSequenceLength:
    return "oracle_sequence_length";
  case Expression::Kind::OracleSend:
    return "oracle_send";
  case Expression::Kind::OracleQuery:
    return "oracle_query";
  case Expression::Kind::OracleContents:
    return "oracle_contents";
  case Expression::Kind::OracleRows:
    return "oracle_rows";
  case Expression::Kind::OracleForgetRows:
    return "oracle_forget_rows";
  case Expression::Kind::MethodCall:
    return "method_call";
  case Expression::Kind::FinishIf:
    return "finish_if";
  case Expression::Kind::NotationCall:
    return "notation_call";
  case Expression::Kind::And:
    return "and";
  case Expression::Kind::Or:
    return "or";
  case Expression::Kind::Not:
    return "not";
  case Expression::Kind::Tuple:
    return "tuple";
  case Expression::Kind::Array:
    return "array";
  case Expression::Kind::Record:
    return "record";
  case Expression::Kind::Projection:
    return "projection";
  case Expression::Kind::Subscript:
    return "subscript";
  case Expression::Kind::If:
    return "if";
  case Expression::Kind::Match:
    return "match";
  case Expression::Kind::For:
    return "for";
  case Expression::Kind::Block:
    return "block";
  }
  llvm_unreachable("unknown syntax kind");
}
StringRef syntaxKind(Statement::Kind value) {
  switch (value) {
  case Statement::Kind::Let:
    return "let";
  case Statement::Kind::Assign:
    return "assign";
  case Statement::Kind::Expression:
    return "expression";
  case Statement::Kind::Drop:
    return "drop";
  case Statement::Kind::Consume:
    return "consume";
  case Statement::Kind::Require:
    return "require";
  }
  llvm_unreachable("unknown syntax kind");
}
StringRef syntaxKind(ClaimExpression::Kind value) {
  switch (value) {
  case ClaimExpression::Kind::Natural:
    return "natural";
  case ClaimExpression::Kind::Reference:
    return "reference";
  case ClaimExpression::Kind::Application:
    return "application";
  case ClaimExpression::Kind::Binary:
    return "binary";
  case ClaimExpression::Kind::Unary:
    return "unary";
  case ClaimExpression::Kind::List:
    return "list";
  }
  llvm_unreachable("unknown syntax kind");
}
StringRef syntaxKind(Declaration::Kind value) {
  switch (value) {
  case Declaration::Kind::Domain:
    return "domain";
  case Declaration::Kind::DomainFunction:
    return "domain_function";
  case Declaration::Kind::Math:
    return "math";
  case Declaration::Kind::Local:
    return "local";
  case Declaration::Kind::Protocol:
    return "protocol";
  case Declaration::Kind::Construction:
    return "construction";
  case Declaration::Kind::Entry:
    return "entry";
  case Declaration::Kind::EntryFunction:
    return "entry_function";
  case Declaration::Kind::Alias:
    return "alias";
  case Declaration::Kind::Record:
    return "record";
  case Declaration::Kind::Variant:
    return "variant";
  case Declaration::Kind::Interface:
    return "interface";
  case Declaration::Kind::Module:
    return "module";
  case Declaration::Kind::Associated:
    return "associated";
  case Declaration::Kind::Relation:
    return "relation";
  }
  llvm_unreachable("unknown syntax kind");
}
/// A flat node table keeps the wire document's nesting bounded independently
/// of source depth. Edges are structural paths relative to one authored owner.
class Writer {
public:
  Writer(const CheckedProject &project, Work &work,
         WrittenIndex *addresses = nullptr)
      : project(project), work(work), addresses(addresses) {}
  Expected<json::Value> run(const WrittenSources &written) {
    for (const auto &module : written.modules)
      declaration(module, module.name);
    if (error)
      return std::move(error);
    json::Array sources;
    for (const auto &source : project.sources())
      sources.push_back(json::Object{
          {"module", source.module},
          {"origin", source.origin == SourceOrigin::Captured ? "captured"
                                                             : "installation"},
          {"bytes", source.text.size()},
          {"sha256", digest(source.text)}});
    return json::Object{{"format", "zkc.source-ast/0"},
                        {"capture", project.capture().identity()},
                        {"installation", project.installationIdentity()},
                        {"sources", std::move(sources)},
                        {"declarations", std::move(declarations)}};
  }

private:
  const CheckedProject &project;
  Work &work;
  Error error = Error::success();
  std::vector<std::pair<std::string, unsigned>> path;
  json::Array nodes, declarations;
  WrittenIndex *addresses;
  Span currentDeclaration{};
  std::string addressOwner;
  void remember(Span declaration, LexicalNode node) {
    if (!addresses || error)
      return;
    if (auto failure = work.charge(1 + 2 * path.size(), declaration)) {
      error = std::move(failure);
      return;
    }
    addresses->lexical[writtenNodeKey(declaration, node)].push_back(
        {addressOwner, path});
  }
  json::Array address() const {
    json::Array result;
    for (const auto &[category, index] : path)
      result.push_back(json::Array{category, index});
    return result;
  }
  json::Value emit(StringRef kind, Span span, json::Object fields = {}) {
    if (error)
      return nullptr;
    if (auto failure = work.charge(1 + 2 * path.size(), span)) {
      error = std::move(failure);
      return nullptr;
    }
    if (addresses) {
      if (auto failure = work.charge(1 + 2 * path.size(), span)) {
        error = std::move(failure);
        return nullptr;
      }
      addresses->spans[writtenSpanKey(span)].push_back({addressOwner, path});
    }
    fields["kind"] = kind.str();
    fields["path"] = address();
    fields["span"] =
        json::Object{{"module", project.sources()[span.source.index].module},
                     {"begin", span.begin},
                     {"end", span.end}};
    nodes.push_back(std::move(fields));
    return address();
  }
  template <class F>
  json::Value child(StringRef category, unsigned index, F f) {
    if (error)
      return nullptr;
    if (path.size() >= work.limits.parseDepth + work.limits.expressionDepth) {
      error = failure("source.limit", "source AST path depth exceeded");
      return nullptr;
    }
    path.emplace_back(category.str(), index);
    auto restore = scope_exit([&] { path.pop_back(); });
    return f();
  }
  template <class T, class F>
  json::Array list(StringRef category, const std::vector<T> &values, F f) {
    json::Array result;
    for (unsigned i = 0; i < values.size() && !error; ++i)
      result.push_back(child(category, i, [&] { return f(values[i]); }));
    return result;
  }
  json::Value type(const SyntaxType &value) {
    return emit(
        ("type." + syntaxKind(value.kind)).str(), value.span,
        json::Object{{"name", value.name},
                     {"arguments", list("argument", value.arguments,
                                        [&](auto &arg) { return type(arg); })},
                     {"labels", labels(value.labels)}});
  }
  json::Array labels(ArrayRef<ArgumentLabel> values) {
    json::Array result;
    for (const auto &value : values)
      result.push_back(
          json::Object{{"index", value.index}, {"name", value.name}});
    return result;
  }
  json::Value optionalType(const std::optional<SyntaxType> &value,
                           StringRef category) {
    return value ? child(category, 0, [&] { return type(*value); })
                 : json::Value(nullptr);
  }
  json::Value selector(const SyntaxSelector &value) {
    return emit("selector", value.span,
                json::Object{{"direction", value.output ? "out" : "in"},
                             {"port", value.port},
                             {"fields", strings(value.path)},
                             {"role", optionalString(value.role)}});
  }
  json::Value inputSelector(const SyntaxInputSelector &value) {
    return emit(
        "input_selector", value.span,
        json::Object{{"port", value.port}, {"fields", strings(value.path)}});
  }
  json::Value named(const SyntaxName &value) {
    return emit("name", value.span, json::Object{{"name", value.name}});
  }
  json::Value port(const SyntaxPort &value, bool field = false) {
    json::Object result{{"name", value.unnamed ? json::Value(nullptr)
                                               : json::Value(value.name)},
                        {"roles", strings(value.roles)},
                        {"domain", optionalType(value.domain, "domain")}};
    if (value.oracleHolder) {
      result["oracle_holder"] = *value.oracleHolder;
      result["oracle_maximum"] =
          optionalType(value.oracleMaximum, "oracle_maximum");
    }
    if (field)
      result["public"] = value.isPublic;
    if (value.purpose)
      result["purpose"] =
          *value.purpose == RelationPurpose::Parameter   ? "parameter"
          : *value.purpose == RelationPurpose::Statement ? "statement"
                                                         : "witness";
    else
      result["purpose"] = nullptr;
    result["binding"] =
        value.binding
            ? child("binding", 0, [&] { return selector(*value.binding); })
            : json::Value(nullptr);
    if (value.scoped) {
      const auto &signature = *value.scoped;
      result["callback"] = json::Object{
          {"mode",
           signature.mode == ScopedSignature::Mode::Math ? "math" : "local"},
          {"inputs", list("callback_input", signature.inputs,
                          [&](auto &t) { return type(t); })},
          {"labels", strings(signature.inputLabels)},
          {"result",
           child("callback_result", 0, [&] { return type(signature.result); })},
          {"effects", signature.explicitAllowance
                          ? json::Value(effects(signature.allowance))
                          : json::Value(nullptr)},
          {"conditions", list("callback_condition", signature.itemOrigins,
                              [&](auto &condition) {
                                return emit(
                                    "item_from", condition.span,
                                    json::Object{{"input", condition.input},
                                                 {"domain", condition.domain}});
                              })}};
    } else
      result["callback"] = nullptr;
    // Inline relation formals bind selectors instead of writing a type.
    result["type"] = value.scoped || value.domain || value.binding ||
                             (value.type.kind == SyntaxType::Kind::Name &&
                              value.type.name.empty())
                         ? json::Value(nullptr)
                         : child("type", 0, [&] { return type(value.type); });
    return emit("port", value.span, std::move(result));
  }
  json::Value pattern(const Pattern &value) {
    if (value.writtenToken)
      remember(currentDeclaration,
               {LexicalNode::Kind::Pattern, *value.writtenToken});
    json::Array shorthand;
    for (bool item : value.shorthand)
      shorthand.push_back(item);
    return emit(
        ("pattern." + syntaxKind(value.kind)).str(), value.span,
        json::Object{{"name", value.name},
                     {"type", optionalType(value.type, "type")},
                     {"labels", strings(value.labels)},
                     {"shorthand", std::move(shorthand)},
                     {"children", list("pattern", value.children,
                                       [&](auto &p) { return pattern(p); })}});
  }
  json::Value notation(const SyntaxOperator &value) {
    json::Object result{
        {"symbol", value.symbol},
        {"public", value.isPublic},
        {"target", child("target", 0, [&] { return type(value.target); })},
        {"holes", strings(value.holes)},
        {"filtered", optionalType(value.filtered, "filtered")}};
    if (value.explicitNotation) {
      const auto &syntax = *value.notation;
      using P = NotationDescriptor::Position;
      using A = NotationDescriptor::Association;
      result["syntax"] = json::Object{
          {"position", syntax.position == P::Prefix      ? "prefix"
                       : syntax.position == P::Postfix   ? "postfix"
                       : syntax.position == P::Infix     ? "infix"
                       : syntax.position == P::Index     ? "index"
                       : syntax.position == P::Reduction ? "reduction"
                                                         : "delimited"},
          {"association", syntax.association == A::Left    ? "left"
                          : syntax.association == A::Right ? "right"
                                                           : "none"},
          {"precedence", syntax.precedence},
          {"closing", syntax.closing}};
    } else
      result["syntax"] = nullptr;
    return emit("notation", value.span, std::move(result));
  }
  json::Value expression(const SyntaxDeclaration &owner, uint32_t id) {
    remember(owner.span, {LexicalNode::Kind::Expression, id});
    const auto &value = owner.expressions.at(id);
    if (!value.reductionBinders.empty()) {
      return emit(
          "expr.reduction", value.span,
          json::Object{
              {"symbol", value.notation->symbol},
              {"grouped", value.grouped},
              {"binders",
               list("binder", value.reductionBinders,
                    [&](auto &binder) {
                      return emit(
                          "binder", binder.first.span,
                          json::Object{
                              {"pattern",
                               child("pattern", 0,
                                     [&] { return pattern(binder.first); })},
                              {"domain", child("domain", 0, [&] {
                                 return expression(owner, binder.second);
                               })}});
                    })},
              {"predicate", value.reductionPredicate
                                ? child("predicate", 0,
                                        [&] {
                                          return expression(
                                              owner, *value.reductionPredicate);
                                        })
                                : json::Value(nullptr)},
              {"term", child("term", 0, [&] {
                 return expression(owner, *value.reductionBody);
               })}});
    }
    json::Array each;
    for (bool item : value.each)
      each.push_back(item);
    json::Array assets;
    for (const auto &item : value.assetParameters) {
      auto index = item.first;
      const auto &term = item.second;
      assets.push_back(json::Object{
          {"index", index},
          {"type", child("asset", index, [&] { return type(term); })}});
    }
    json::Array payloads;
    for (unsigned i = 0; i < value.payloads.size(); ++i)
      payloads.push_back(child("arm", i, [&]() -> json::Value {
        return list("pattern", value.payloads[i],
                    [&](auto &p) { return pattern(p); });
      }));
    return emit(
        ("expr." + syntaxKind(value.kind)).str(), value.span,
        json::Object{
            {"text", value.text},
            {"symbol", value.notation ? json::Value(value.notation->symbol)
                                      : json::Value(nullptr)},
            {"bracket", value.bracket},
            {"grouped", value.grouped},
            {"shorthand", value.shorthand},
            {"filtered", value.filteredReduction},
            {"roles", value.roles ? json::Value(strings(*value.roles))
                                  : json::Value(nullptr)},
            {"labels", strings(value.labels)},
            {"static_labels", labels(value.staticLabels)},
            {"call_labels", labels(value.callLabels)},
            {"each", std::move(each)},
            {"assets", std::move(assets)},
            {"arguments", list("argument", value.arguments,
                               [&](auto &t) { return type(t); })},
            {"operands",
             list("expr", value.children,
                  [&](auto child) { return expression(owner, child); })},
            {"regions", list("body", value.regions,
                             [&](auto region) { return body(owner, region); })},
            {"payloads", std::move(payloads)},
            {"index",
             !value.index.name.empty() || !value.index.children.empty()
                 ? child("index", 0, [&] { return pattern(value.index); })
                 : json::Value(nullptr)}});
  }
  json::Value body(const SyntaxDeclaration &owner, uint32_t id) {
    const auto &value = owner.bodies.at(id);
    auto statements = list("stmt", value.statements, [&](auto &statement) {
      json::Object fields{
          {"mutable", statement.mutableBinding},
          {"evaluation",
           statement.evaluation == Statement::Evaluation::Legacy
               ? json::Value(nullptr)
               : json::Value(statement.evaluation == Statement::Evaluation::Pure
                                 ? "pure"
                                 : "ordered")},
          {"terminated", statement.terminated},
          {"type", optionalType(statement.type, "type")},
          {"roles", statement.roles ? json::Value(strings(*statement.roles))
                                    : json::Value(nullptr)},
          {"owner", optionalString(statement.owner)},
          {"site", optionalString(statement.site)},
          {"expression", child("expr", 0, [&] {
             return expression(owner, statement.expression);
           })}};
      fields["binding"] =
          statement.kind == Statement::Kind::Let ||
                  statement.kind == Statement::Kind::Assign
              ? child("pattern", 0, [&] { return pattern(statement.pattern); })
              : json::Value(nullptr);
      fields["send"] =
          statement.exchange
              ? json::Value(json::Object{
                    {"from", statement.exchange->first.empty()
                                 ? json::Value(nullptr)
                                 : json::Value(statement.exchange->first)},
                    {"to", statement.exchange->second}})
              : json::Value(nullptr);
      return emit(("stmt." + syntaxKind(statement.kind)).str(), statement.span,
                  std::move(fields));
    });
    json::Array results;
    for (unsigned i = 0; i < value.results.size(); ++i) {
      const auto &name = value.results[i].first;
      auto result = value.results[i].second;
      results.push_back(json::Object{
          {"label", owner.kind == Declaration::Kind::Protocol && !name.empty()
                        ? json::Value(name)
                        : json::Value(nullptr)},
          {"value",
           child("result", i, [&] { return expression(owner, result); })}});
    }
    return emit(
        "body", value.span,
        json::Object{
            {"notations", list("notation", value.operators,
                               [&](auto &n) { return notation(n); })},
            {"statements", std::move(statements)},
            {"results", std::move(results)},
            {"terminal", value.stopped                             ? "stop"
                         : value.returned && !value.implicitResult ? "return"
                                                                   : "tail"},
            {"stop_reason", value.stopped ? json::Value(value.stopReason)
                                          : json::Value(nullptr)}});
  }
  json::Value claimExpression(const ClaimExpression &value) {
    return emit(
        ("claim_expr." + syntaxKind(value.kind)).str(), value.span,
        json::Object{{"text", value.text},
                     {"version", value.version ? json::Value(*value.version)
                                               : json::Value(nullptr)},
                     {"labels", strings(value.labels)},
                     {"arguments",
                      list("argument", value.arguments,
                           [&](auto &arg) { return claimExpression(arg); })}});
  }
  json::Value subject(const SyntaxDeclaration &owner,
                      const SyntaxSubject &value) {
    if (value.inlineMember)
      return declarationNode(owner.members[*value.inlineMember], {}, true);
    return emit(
        "relation_application", value.span,
        json::Object{{"relation", child("relation", 0,
                                        [&] { return type(value.relation); })},
                     {"operands", list("selector", value.operands,
                                       [&](auto &s) { return selector(s); })}});
  }
  json::Value requirement(const SyntaxRequirement &value) {
    json::Object result{{"permission", value.permission},
                        {"capability", value.capability},
                        {"arguments", list("argument", value.arguments,
                                           [&](auto &t) { return type(t); })}};
    if (value.data) {
      result["left"] =
          child("left", 0, [&] { return inputSelector(value.left); });
      result["right"] =
          child("right", 0, [&] { return inputSelector(value.right); });
      result["left_axis"] = value.leftAxis;
      result["right_axis"] = value.rightAxis;
      result["data"] = *value.data == DataPrecondition::Kind::IndexBound
                           ? "index_bound"
                           : "equal_extent";
    } else {
      result["left"] = child("left", 0, [&] { return type(value.lhs); });
      result["right"] = value.permission.empty() && value.capability.empty()
                            ? child("right", 0, [&] { return type(value.rhs); })
                            : json::Value(nullptr);
      result["data"] = nullptr;
    }
    return emit("requirement", value.span, std::move(result));
  }
  json::Value formalNode(const syntax::Snapshot &tree, syntax::NodeId id) {
    json::Array children, tokens;
    const auto &node = tree.node(id);
    unsigned cursor = node.firstToken;
    auto appendTokens = [&](unsigned end) {
      for (; cursor < end && !error; ++cursor) {
        auto token = tree.tokens()[cursor];
        if (token.synthetic() || token.trivia())
          continue;
        auto text = tree.text(token);
        if (auto failure = work.charge(text.size() + 1, tree.span(id))) {
          error = std::move(failure);
          return;
        }
        tokens.push_back(json::Object{
            {"text", text}, {"begin", token.begin}, {"end", token.end}});
      }
    };
    for (auto nested : tree.children(id)) {
      appendTokens(tree.node(nested).firstToken);
      children.push_back(child("child", children.size(),
                               [&] { return formalNode(tree, nested); }));
      cursor = tree.node(nested).lastToken;
    }
    appendTokens(node.lastToken);
    return emit("formal_syntax", tree.span(id),
                json::Object{{"syntax_kind", syntax::spelling(node.kind)},
                             {"children", std::move(children)},
                             {"tokens", std::move(tokens)}});
  }
  json::Value declarationNode(const SyntaxDeclaration &value, StringRef owner,
                              bool anonymous = false) {
    auto previousDeclaration = currentDeclaration;
    currentDeclaration = value.span;
    auto restoreDeclaration =
        scope_exit([&] { currentDeclaration = previousDeclaration; });
    if (value.section) {
      json::Array members;
      for (const auto &member : value.members) {
        if (member.section)
          members.push_back(
              json::Object{{"section", child("section", members.size(), [&] {
                              return declarationNode(member, owner);
                            })}});
        else
          members.push_back(
              json::Object{{"owner", (owner + "::" + member.name).str()}});
      }
      return emit(
          "section", value.span,
          json::Object{
              {"parameters",
               list("parameter", value.parameters,
                    [&](auto &p) {
                      return emit(
                          "parameter", p.span,
                          json::Object{
                              {"name", p.name},
                              {"bound",
                               child("bound", 0,
                                     [&] { return type(p.constraint); })},
                              {"permissions", strings(p.writtenPermissions)}});
                    })},
              {"members", std::move(members)},
              {"formal", list("formal", value.formalSyntax, [&](auto &formal) {
                 return formalNode(formal.tree, formal.node);
               })}});
    }
    json::Object result{
        {"formal", list("formal", value.formalSyntax,
                        [&](auto &formal) {
                          return formalNode(formal.tree, formal.node);
                        })},
        {"name", anonymous ? json::Value(nullptr) : json::Value(value.name)},
        {"public", value.explicitPublic},
        {"abstract", value.abstract},
        {"external_module", value.externalModule},
        {"sealed", value.sealed},
        {"resource",
         !value.resource
             ? json::Value(nullptr)
             : json::Value(*value.resource == Resource::Affine ? "affine"
                                                               : "linear")},
        {"permissions", value.permissions
                            ? json::Value(strings(value.writtenPermissions))
                            : json::Value(nullptr)},
        {"associated_sort", value.associatedSort},
        {"completes", value.completes},
        {"roster", strings(value.roles)},
        {"parameters",
         list("parameter", value.parameters,
              [&](auto &parameter) {
                return emit(
                    "parameter", parameter.span,
                    json::Object{
                        {"name", parameter.name},
                        {"bound",
                         child("bound", 0,
                               [&] { return type(parameter.constraint); })},
                        {"permissions",
                         strings(parameter.writtenPermissions)}});
              })},
        {"requirements_written", value.explicitRequirements},
        {"requirements", list("requirement", value.requirements,
                              [&](auto &r) { return requirement(r); })},
        {"effects", value.effects ? json::Value(effects(*value.effects))
                                  : json::Value(nullptr)},
        {"effect_dependencies", strings(value.effectDependencies)},
        {"definition", optionalType(value.definition, "definition")},
        {"primitive", optionalString(value.primitive)},
        {"domain_constructor", optionalString(value.domainConstructor)},
        {"finite_definition", optionalString(value.finiteDefinition)},
        {"domain_result", optionalType(value.domainResult, "domain_result")},
        {"target", value.target},
        {"target_arguments", list("target_argument", value.targetArguments,
                                  [&](auto &t) { return type(t); })},
        {"target_labels", labels(value.targetLabels)}};
    if (value.kind == Declaration::Kind::Domain)
      result["domain"] =
          json::Object{{"sort", value.target},
                       {"source", value.assetDomain ? "asset" : "catalog"},
                       {"name", value.domain}};
    json::Array inputs;
    unsigned inputCount = value.inputOrder.empty() ? value.inputs.size()
                                                   : value.inputOrder.size();
    for (unsigned i = 0; i < inputCount; ++i) {
      using K = Declaration::InputSlot::Kind;
      auto slot = value.inputOrder.empty() ? Declaration::InputSlot{K::Data, i}
                                           : value.inputOrder[i];
      const auto &ports = slot.kind == K::Scoped    ? value.scopedInputs
                          : slot.kind == K::Domain  ? value.domainInputs
                          : slot.kind == K::Service ? value.services
                                                    : value.inputs;
      inputs.push_back(child("input", i, [&] {
        remember(value.span, {LexicalNode::Kind::Input, i});
        return port(ports[slot.index]);
      }));
    }
    result["inputs"] = std::move(inputs);
    // The parser synthesizes a bool result for every relation. It is not a
    // written output port. A function's synthetic result name is likewise not
    // an authored binder; its result type is represented separately.
    if (value.kind == Declaration::Kind::Relation)
      result["outputs"] = json::Array{};
    else if (value.kind == Declaration::Kind::Protocol)
      result["outputs"] =
          list("output", value.outputs, [&](auto &p) { return port(p); });
    else if (!value.outputs.empty())
      result["result_type"] = child(
          "result_type", 0, [&] { return type(value.outputs.front().type); });
    else
      result["result_type"] = nullptr;
    result["fields"] =
        list("field", value.fields, [&](auto &p) { return port(p, true); });
    result["alternatives"] =
        list("alternative", value.alternatives, [&](auto &a) {
          return emit(
              "alternative", a.span,
              json::Object{{"name", a.name},
                           {"fields", list("field", a.fields, [&](auto &p) {
                              return port(p, true);
                            })}});
        });
    result["notations"] =
        list("notation", value.operators, [&](auto &n) { return notation(n); });
    result["imports"] = list("import", value.imports, [&](auto &i) {
      return emit(
          "import", i.span,
          json::Object{{"module", i.module},
                       {"public", i.isPublic},
                       {"alias", i.explicitAlias ? optionalString(i.alias)
                                                 : json::Value(nullptr)},
                       {"names", strings(i.names)},
                       {"operators", strings(i.operators)},
                       {"notations", strings(i.notations)},
                       {"reductions", strings(i.reductions)},
                       {"indexing", i.indexing}});
    });
    result["clauses"] = list("clause", value.specifications, [&](auto &c) {
      using K = SpecificationClause::Kind;
      return emit(
          "clause", c.span,
          json::Object{
              {"category", c.kind == K::Target   ? "target"
                           : c.kind == K::Input  ? "input"
                           : c.kind == K::Output ? "output"
                                                 : "continuation"},
              {"name", c.name},
              {"subject",
               child("subject", 0, [&] { return subject(value, c.subject); })},
              {"residual",
               c.residual ? child("residual", 0,
                                  [&] { return subject(value, *c.residual); })
                          : json::Value(nullptr)},
              {"decision",
               c.decision
                   ? child("decision", 0, [&] { return selector(*c.decision); })
                   : json::Value(nullptr)}});
    });
    result["spec_blocks"] =
        list("spec_block", value.sourceClaims, [&](auto &b) {
          return emit(
              "spec_block", b.value.span,
              json::Object{
                  {"name", b.value.name},
                  {"subject",
                   child("subject", 0, [&] { return type(b.subject); })},
                  {"claims", list("claim", b.value.claims, [&](auto &c) {
                     return emit(
                         "claim", c.span,
                         json::Object{{"label", c.label},
                                      {"property", child("property", 0, [&] {
                                         return claimExpression(c.property);
                                       })}});
                   })}});
        });
    result["verifications"] =
        list("verify", value.sourceVerifications, [&](auto &v) {
          return emit("verify", v.span,
                      json::Object{{"block", v.block},
                                   {"label", v.label},
                                   {"method", child("method", 0, [&] {
                                      return claimExpression(v.method);
                                    })}});
        });
    result["setups"] = list("setup", value.setups, [&](auto &s) {
      return emit("setup", s.span,
                  json::Object{{"name", s.name.name},
                               {"inputs", list("input", s.inputs, [&](auto &p) {
                                  return selector(p);
                                })}});
    });
    if (value.relation) {
      const auto &r = *value.relation;
      using K = RelationDefinition::Kind;
      result["relation"] =
          json::Object{{"kind", r.kind == K::Formula  ? "formula"
                                : r.kind == K::Opaque ? "opaque"
                                : r.kind == K::R1CS   ? "r1cs"
                                : r.kind == K::AIR    ? "air"
                                                      : "bundle"},
                       {"external_kind", r.externalKind},
                       {"key", r.key},
                       {"revision", r.revision},
                       {"asset", r.asset}};
    }
    if (value.proof) {
      const auto &p = *value.proof;
      result["proof"] = child("proof", 0, [&] {
        return emit(
            "proof", p.span,
            json::Object{
                {"prover", p.prover.name},
                {"verifier", p.verifier.name},
                {"public", list("public", p.publicInputs,
                                [&](auto &n) { return named(n); })},
                {"acceptance", child("acceptance", 0,
                                     [&] { return selector(p.acceptance); })},
                {"completion",
                 p.completion ? child("completion", 0,
                                      [&] { return selector(*p.completion); })
                              : json::Value(nullptr)},
                {"target",
                 p.target ? json::Value(p.target->name) : json::Value(nullptr)},
                {"service", p.service ? json::Value(p.service->name)
                                      : json::Value(nullptr)},
                {"construction",
                 optionalType(p.selectedConstruction, "construction")},
                {"base",
                 p.selectedConstruction
                     ? json::Value(nullptr)
                     : json::Value(p.construction ==
                                           ProofEntry::Construction::FiatShamir
                                       ? "fiat_shamir"
                                       : "authored")},
                {"suite", p.suite}});
      });
    }
    if (value.kind == Declaration::Kind::Entry ||
        value.kind == Declaration::Kind::EntryFunction) {
      result["entry_block"] = value.entryBlock;
      result["entry_kind"] = value.entryKind == EntryKind::Proof ? "proof"
                             : value.entryKind == EntryKind::Function
                                 ? "function"
                                 : "run";
    }
    if (value.construction) {
      const auto &c = *value.construction;
      using B = ConstructionDefinition::Base;
      json::Object construction{
          {"base", c.base == B::None
                       ? json::Value(nullptr)
                       : json::Value(c.base == B::Authored ? "authored"
                                     : c.base == B::Native ? "fiat_shamir"
                                                           : "named")},
          {"parent", optionalType(c.parent, "parent")},
          {"provider", optionalType(c.provider, "provider")},
          {"codec", optionalType(c.codec, "codec")},
          {"layout",
           list("layout", c.layout, [&](auto &n) { return named(n); })},
          {"services",
           list("service", c.services, [&](auto &n) { return named(n); })},
          {"suite", c.suite},
          {"applications",
           list("application", c.applications,
                [&](auto &a) {
                  return emit(
                      "application", a.span,
                      json::Object{
                          {"construction",
                           child("construction", 0,
                                 [&] { return type(a.construction); })},
                          {"selector", list("selector", a.path, [&](auto &n) {
                             return named(n);
                           })}});
                })},
          {"rules", json::Array{}}};
      // One written handler can select several occurrences. Header parsing
      // expands it for elaboration; reconstruct its single authored node by
      // the shared source span, preserving all selectors in order.
      json::Array rules;
      for (unsigned first = 0; first < c.rules.size();) {
        unsigned end = first + 1;
        const auto &rule = c.rules[first];
        while (end < c.rules.size() &&
               c.rules[end].span.begin == rule.span.begin &&
               c.rules[end].span.end == rule.span.end)
          ++end;
        rules.push_back(child("rule", rules.size(), [&] {
          json::Array selectors;
          for (unsigned i = first; i < end; ++i)
            selectors.push_back(
                child("selector", i - first, [&]() -> json::Value {
                  return list("name", c.rules[i].path,
                              [&](auto &n) { return named(n); });
                }));
          return emit(
              "rule", rule.span,
              json::Object{
                  {"category", protocol::constructionRuleName(rule.kind)},
                  {"selectors", std::move(selectors)},
                  {"parameters", list("parameter", rule.parameters,
                                      [&](auto &n) { return named(n); })},
                  {"handler", child("handler", 0, [&] {
                     return declarationNode(value.members[rule.member], {},
                                            true);
                   })}});
        }));
        first = end;
      }
      construction["rules"] = std::move(rules);
      construction["format"] =
          !value.proofFormat || c.codec
              ? json::Value(nullptr)
              : json::Value(*value.proofFormat == protocol::ProofFormat::Native
                                ? "Native"
                                : "RawBytes");
      result["construction"] = std::move(construction);
    }
    result["body"] = value.bodies.empty()
                         ? json::Value(nullptr)
                         : child("body", 0, [&] { return body(value, 0); });
    json::Array members;
    for (unsigned i = 0; i < value.members.size(); ++i) {
      const auto &member = value.members[i];
      if (member.anonymous || member.constructionHandler)
        continue;
      if (member.section)
        members.push_back(
            json::Object{{"section", child("section", members.size(), [&] {
                            return declarationNode(member, owner);
                          })}});
      else if (member.externalModule)
        members.push_back(json::Object{
            {"link", child("member", members.size(), [&] {
               return emit("module_link", member.span,
                           json::Object{{"name", member.name},
                                        {"public", member.explicitPublic}});
             })}});
      else
        members.push_back(
            json::Object{{"owner", (owner + "::" + member.name).str()}});
    }
    result["members"] = std::move(members);
    return emit(("declaration." + syntaxKind(value.kind)).str(), value.span,
                std::move(result));
  }
  void declaration(const SyntaxDeclaration &value, StringRef owner) {
    if (error)
      return;
    if (!value.section) {
      path.clear();
      addressOwner = owner.str();
      nodes = {};
      declarationNode(value, owner);
      declarations.push_back(
          json::Object{{"owner", owner.str()}, {"nodes", std::move(nodes)}});
    }
    for (const auto &member : value.members)
      if (!member.anonymous && !member.constructionHandler &&
          !member.externalModule)
        declaration(member, member.section
                                ? owner.str()
                                : (owner + "::" + member.name).str());
  }
};
} // namespace
namespace detail {
Expected<WrittenIndex> indexWrittenSource(const CheckedProject &project,
                                          const WrittenSources &written,
                                          Work &work) {
  WrittenIndex result;
  auto value = Writer(project, work, &result).run(written);
  if (!value)
    return value.takeError();
  return result;
}
Expected<json::Array> encodeWrittenAddresses(ArrayRef<WrittenAddress> values,
                                             Work &work) {
  json::Array result;
  for (const auto &address : values) {
    if (auto error =
            work.charge(1 + address.owner.size() + 2 * address.path.size()))
      return std::move(error);
    json::Array path;
    for (const auto &[category, ordinal] : address.path)
      path.push_back(json::Array{category, ordinal});
    result.push_back(
        json::Object{{"owner", address.owner}, {"path", std::move(path)}});
  }
  return result;
}
} // namespace detail
Expected<std::string> inspectWrittenSource(const CheckedProject &project,
                                           const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return detail::failure("source.limit",
                           "checked project exceeds source AST limits");
  if (!project.storage->writtenSources)
    return detail::failure("source.syntax", "written source was not retained");
  Work work{limits};
  auto value = Writer(project, work).run(*project.storage->writtenSources);
  if (!value)
    return value.takeError();
  std::string bytes;
  BoundedStream out(bytes, limits.apiInspectionBytes);
  out << *value;
  if (out.overflow())
    return detail::failure("source.limit", "source AST byte limit exceeded");
  return bytes;
}

Expected<std::string> inspectSourceBindings(const CheckedProject &project,
                                            const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return detail::failure(
        "source.limit", "checked project exceeds source binding export limits");
  if (!project.storage->writtenSources)
    return detail::failure("source.syntax", "written source was not retained");
  Work work{limits};
  auto index =
      indexWrittenSource(project, *project.storage->writtenSources, work);
  if (!index)
    return index.takeError();
  json::Array references, unassociated;
  for (const auto &resolution : project.storage->lexicalResolutions)
    for (const auto &reference : resolution.references) {
      if (auto error = work.charge(1, resolution.declaration))
        return std::move(error);
      auto uses = index->at(resolution.declaration, reference.use);
      auto binders = reference.binder
                         ? index->at(resolution.declaration, *reference.binder)
                         : ArrayRef<WrittenAddress>{};
      StringRef kind =
          reference.access == LexicalReference::Access::Read   ? "read"
          : reference.access == LexicalReference::Access::Call ? "call"
                                                               : "assign";
      auto from = encodeWrittenAddresses(uses, work);
      if (!from)
        return from.takeError();
      auto to = encodeWrittenAddresses(binders, work);
      if (!to)
        return to.takeError();
      if (!uses.empty() && !binders.empty()) {
        references.push_back(json::Object{{"kind", kind},
                                          {"uses", std::move(*from)},
                                          {"binders", std::move(*to)}});
      } else {
        auto span = resolution.declaration;
        unassociated.push_back(json::Object{
            {"kind", kind},
            {"uses", std::move(*from)},
            {"binders", std::move(*to)},
            {"declaration",
             json::Object{
                 {"module", project.sources()[span.source.index].module},
                 {"begin", span.begin},
                 {"end", span.end}}}});
      }
    }
  auto source = [&](Span span) {
    return json::Object{{"module", project.sources()[span.source.index].module},
                        {"begin", span.begin},
                        {"end", span.end}};
  };
  auto declaration = [&](DeclarationId id) {
    const auto &decl = project.declarations()[id.index];
    return json::Object{{"name", decl.qualifiedName},
                        {"source", source(decl.span)}};
  };
  // Preserve resolver observations, including repeated observations of a node.
  // Exact-span candidates help the checker find a written occurrence; they do
  // not select one or establish its lookup. Unlike local links, these records
  // predate expression/body parsing for some declaration headers.
  json::Array declarations;
  for (const auto &reference : project.storage->api.references) {
    const auto &owner = project.declarations()[reference.owner.index];
    const auto &provider = project.declarations()[reference.provider.index];
    const auto &target = project.declarations()[reference.target.index];
    if (auto error = work.charge(
            1 + reference.written.size() + owner.qualifiedName.size() +
                provider.qualifiedName.size() + target.qualifiedName.size() +
                (reference.abstractModule ? reference.abstractModule->size()
                                          : 0),
            reference.span))
      return std::move(error);
    auto candidates = encodeWrittenAddresses(index->at(reference.span), work);
    if (!candidates)
      return candidates.takeError();
    declarations.push_back(json::Object{
        {"owner", owner.qualifiedName},
        {"written", reference.written},
        {"provider", declaration(reference.provider)},
        {"target", declaration(reference.target)},
        {"abstract_module", optionalString(reference.abstractModule)},
        {"source", source(reference.span)},
        {"candidates", std::move(*candidates)}});
  }
  json::Value value =
      json::Object{{"format", "zkc.source-bindings/0"},
                   {"capture", project.capture().identity()},
                   {"installation", project.installationIdentity()},
                   {"locals", std::move(references)},
                   {"unassociated_locals", std::move(unassociated)},
                   {"declarations", std::move(declarations)}};
  std::string bytes;
  BoundedStream out(bytes, limits.apiInspectionBytes);
  out << value;
  if (out.overflow())
    return detail::failure("source.limit",
                           "source binding export byte limit exceeded");
  return bytes;
}
} // namespace zkc::language
