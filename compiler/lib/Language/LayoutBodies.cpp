#include "LayoutReader.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
using namespace llvm;
namespace zkc::language::detail {
Error LayoutReader::body(Id id, SyntaxDeclaration &decl, bool region) {
  SyntaxBody result;
  result.span = span(id);
  result.notationEnvironment = environment;
  result.parent = scope;
  result.region = region;
  auto previousScope = scope;
  auto restore = scope_exit([&] { scope = previousScope; });
  auto bodyIndex = uint32_t(decl.bodies.size());
  scope = bodyIndex;
  decl.bodies.emplace_back();
  std::optional<std::string> site;
  std::optional<Span> attributeSpan;
  for (auto item : children(id)) {
    if (result.returned)
      return fail(item, "statement follows the return", "source.return");
    if (auto error = charge(item))
      return error;
    auto nodes = children(item);
    if (kind(item) == K::Attribute) {
      if (site || nodes.size() != 2 || children(nodes[1]).size() != 1)
        return fail(item, "expected one site label for the following action",
                    "source.site");
      auto projected2 = name(nodes[0]);
      if (!projected2)
        return projected2.takeError();
      auto attributeName = std::move(*projected2);
      if (attributeName != "site")
        return fail(item, "expected a site attribute", "source.site");
      auto projected3 = argument(children(nodes[1])[0]);
      if (!projected3)
        return projected3.takeError();
      auto label = std::move(*projected3);
      if (kind(label) != K::Name)
        return fail(label, "site label must be a name", "source.site");
      auto projected4 = name(label);
      if (!projected4)
        return projected4.takeError();
      site = std::move(*projected4);
      attributeSpan = span(item);
      continue;
    }
    if (kind(item) == K::Return) {
      if (region)
        return fail(item, "nested suites use a final expression",
                    "source.return");
      if (site)
        return fail(item, "site label cannot select return", "source.site");
      auto projected5 = parts(item, 1, 1);
      if (!projected5)
        return projected5.takeError();
      auto values = std::move(*projected5);
      auto value = values[0];
      result.returned = true;
      if (decl.kind == Declaration::Kind::Protocol &&
          (kind(value) == K::Tuple || kind(value) == K::Group) &&
          any_of(children(value),
                 [&](Id child) { return children(child).size() == 2; })) {
        for (auto child : children(value)) {
          auto projected6 = parts(child, 2, 2);
          if (!projected6)
            return projected6.takeError();
          auto entry = std::move(*projected6);
          auto projected7 = name(entry[0]);
          if (!projected7)
            return projected7.takeError();
          auto label = std::move(*projected7);
          auto projected8 = expression(entry[1], decl);
          if (!projected8)
            return projected8.takeError();
          auto projected = std::move(*projected8);
          result.results.emplace_back(std::move(label), projected);
        }
      } else {
        auto projected9 = expression(value, decl);
        if (!projected9)
          return projected9.takeError();
        auto projected = std::move(*projected9);
        result.results.emplace_back(
            decl.kind == Declaration::Kind::Protocol ? "" : "result",
            projected);
      }
      continue;
    }
    Statement statement;
    statement.span = span(item);
    statement.site = std::move(site);
    site.reset();
    if (attributeSpan)
      statement.span.begin = attributeSpan->begin;
    attributeSpan.reset();
    statement.evaluation = Statement::Evaluation::Pure;
    if (nodes.empty())
      return fail(item, "empty executable statement");
    auto value = nodes.back();
    switch (kind(item)) {
    case K::Binding:
    case K::ActionBinding:
    case K::Update: {
      statement.kind = kind(item) == K::Update ? Statement::Kind::Assign
                                               : Statement::Kind::Let;
      statement.mutableBinding = head(item) == "mut";
      auto projected10 = pattern(nodes[0]);
      if (!projected10)
        return projected10.takeError();
      statement.pattern = std::move(*projected10);
      if (nodes.size() == 3) {
        auto annotation = nodes[1];
        if (kind(annotation) == K::RoleType) {
          auto projected11 = parts(annotation, 2, 2);
          if (!projected11)
            return projected11.takeError();
          auto annotated = std::move(*projected11);
          auto projected12 = roles(annotated[1]);
          if (!projected12)
            return projected12.takeError();
          statement.roles = std::move(*projected12);
          annotation = annotated[0];
        }
        auto projected13 = type(annotation);
        if (!projected13)
          return projected13.takeError();
        statement.type = std::move(*projected13);
      }
      if (kind(item) == K::ActionBinding)
        statement.evaluation = Statement::Evaluation::Ordered;
      if (kind(value) == K::Send) {
        auto projected14 = parts(value, 2, SIZE_MAX);
        if (!projected14)
          return projected14.takeError();
        auto send = std::move(*projected14);
        bool explicitSender = between(send[0], send[1]) == "from";
        if (send.size() != (explicitSender ? 3 : 2))
          return fail(value, "multiple-recipient send is not implemented yet",
                      "source.layout-unavailable");
        std::string sender;
        if (explicitSender) {
          auto projected15 = name(send[1]);
          if (!projected15)
            return projected15.takeError();
          sender = std::move(*projected15);
        }
        auto projected16 = name(send.back());
        if (!projected16)
          return projected16.takeError();
        auto receiver = std::move(*projected16);
        statement.exchange =
            std::make_pair(std::move(sender), std::move(receiver));
        value = send[0];
      }
      break;
    }
    case K::Guard:
      statement.kind = Statement::Kind::Require;
      if (nodes.size() == 2) {
        auto projected17 = roles(nodes[0]);
        if (!projected17)
          return projected17.takeError();
        auto owners = std::move(*projected17);
        if (owners.size() != 1)
          return fail(item, "guard needs one owner", "source.roles");
        statement.owner = owners[0];
      }
      break;
    case K::ExpressionStatement:
      statement.kind = Statement::Kind::Expression;
      if ((region || decl.kind == Declaration::Kind::Math) &&
          item == children(id).back()) {
        if (statement.site)
          return fail(item, "site label cannot select an implicit result",
                      "source.site");
        result.returned = !region;
        result.implicitResult = !region;
        auto projected18 = expression(value, decl);
        if (!projected18)
          return projected18.takeError();
        auto projected = std::move(*projected18);
        result.results.emplace_back("result", projected);
        continue;
      }
      break;
    case K::If:
    case K::Match:
    case K::For:
      statement.kind = Statement::Kind::Expression;
      statement.terminated = false;
      value = item;
      break;
    default:
      return fail(item,
                  "this statement has no native layout execution projection",
                  "source.layout-unavailable");
    }
    auto projected19 = expression(value, decl);
    if (!projected19)
      return projected19.takeError();
    statement.expression = std::move(*projected19);
    result.statements.push_back(std::move(statement));
  }
  if (site)
    return fail(id, "site label needs a following action", "source.site");
  decl.bodies[bodyIndex] = std::move(result);
  if (!region)
    decl.deferredBody.reset();
  return Error::success();
}
} // namespace zkc::language::detail
