#include "Checker.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
// Resolve each authored occurrence once. Region inference uses these
// identities, so shadowing and service aliases never depend on identifier
// spelling.
class Resolver {
public:
  Resolver(Checker &checker, Declaration &decl, SyntaxDeclaration &syntax)
      : checker(checker), decl(decl), syntax(syntax) {}
  bool run() {
    if (syntax.resolved)
      return true;
    if (!elaborateExpressions(checker, syntax))
      return false;
    for (auto &port : decl.inputs) {
      auto id = bind(port.name, port.span, false, false, true);
      if (!id)
        return false;
      syntax.inputBindings.push_back(*id);
    }
    for (auto &port : decl.services) {
      auto id = bind(port.name, port.span, false, true, true);
      if (!id)
        return false;
      syntax.serviceBindings.push_back(*id);
    }
    if (!syntax.primitive && !body(0, 1))
      return false;
    syntax.resolved = true;
    return true;
  }

private:
  Checker &checker;
  Declaration &decl;
  SyntaxDeclaration &syntax;
  std::map<std::string, BindingId> names;
  std::vector<std::pair<std::string, std::optional<BindingId>>> undo;
  unsigned scope = 0;
  std::optional<uint32_t> currentBody;
  bool fail(StringRef code, const Twine &message, Span span) {
    return checker.types.fail(code, message, span);
  }
  bool bounded(unsigned depth, Span span) {
    return depth <= checker.work.limits.expressionDepth
               ? checker.types.charge(1, span)
               : fail("source.limit", "lexical resolution depth exceeded",
                      span);
  }
  std::optional<BindingId> lookup(StringRef name, Span span) {
    auto it = names.find(name.str());
    if (it == names.end()) {
      fail("source.name", "unknown local binding: " + name, span);
      return {};
    }
    return it->second;
  }
  std::optional<BindingId> bind(StringRef name, Span span, bool mut,
                                bool service, bool unique = false) {
    if (!checker.bindingName(decl, name, span) ||
        !checker.types.charge(1, span))
      return {};
    auto prior = names.find(name.str());
    if (prior != names.end()) {
      const auto &binding = syntax.bindings[prior->second.index];
      if (unique || service || binding.service ||
          (binding.mutableBinding && binding.scope < scope)) {
        fail("source.shadow",
             binding.mutableBinding && binding.scope < scope
                 ? "nested binding shadows mutable state; use assignment"
                 : "binding shadows a managed service or duplicate input",
             span);
        return {};
      }
    }
    BindingId id{uint32_t(syntax.bindings.size())};
    syntax.bindings.push_back({name.str(), span, mut, service, scope});
    undo.emplace_back(name.str(),
                      prior == names.end()
                          ? std::nullopt
                          : std::optional<BindingId>(prior->second));
    names.insert_or_assign(name.str(), id);
    return id;
  }
  bool pattern(Pattern &p, bool mut, bool service, std::set<std::string> &seen,
               unsigned depth) {
    if (!bounded(depth, p.span))
      return false;
    if (p.kind == Pattern::Kind::Name) {
      if (!seen.insert(p.name).second)
        return fail("source.binding", "duplicate name in binding pattern",
                    p.span);
      p.binding = bind(p.name, p.span, mut, service);
      return p.binding.has_value();
    }
    if (service)
      return fail("source.service", "service alias requires one immutable name",
                  p.span);
    for (auto &child : p.children)
      if (!pattern(child, false, false, seen, depth + 1))
        return false;
    return true;
  }
  bool expression(uint32_t id, unsigned depth) {
    auto &expr = syntax.expressions[id];
    expr.scope = currentBody;
    if (!bounded(depth, expr.span))
      return false;
    if (expr.kind == Expression::Kind::Name) {
      expr.binding = lookup(expr.text, expr.span);
      return expr.binding.has_value();
    }
    for (auto child : expr.children)
      if (!expression(child, depth + 1))
        return false;
    for (unsigned i = 0; i < expr.regions.size(); ++i) {
      auto mark = undo.size();
      ++scope;
      std::set<std::string> seen;
      if (expr.kind == Expression::Kind::For &&
          !pattern(expr.index, false, false, seen, depth + 1))
        return false;
      if (expr.kind == Expression::Kind::Match)
        for (auto &p : expr.payloads[i])
          if (!pattern(p, false, false, seen, depth + 1))
            return false;
      if (!body(expr.regions[i], depth + 1))
        return false;
      --scope;
      while (undo.size() > mark) {
        auto &[name, prior] = undo.back();
        if (prior)
          names.insert_or_assign(name, *prior);
        else
          names.erase(name);
        undo.pop_back();
      }
    }
    return true;
  }
  bool body(uint32_t id, unsigned depth) {
    auto &b = syntax.bodies[id];
    if (!bounded(depth, b.span))
      return false;
    b.parent = currentBody;
    currentBody = id;
    for (const auto &binding : b.operators) {
      auto value = checker.operatorBinding(decl, binding);
      if (!value)
        return false;
      b.resolvedOperators.push_back(std::move(*value));
    }
    for (auto &s : b.statements) {
      if (!expression(s.expression, depth))
        return false;
      if (s.kind == Statement::Kind::Let) {
        const auto &rhs = syntax.expressions[s.expression];
        bool service = rhs.kind == Expression::Kind::Name && rhs.binding &&
                       syntax.bindings[rhs.binding->index].service;
        if (service && (s.mutableBinding || s.roles || s.type || s.exchange))
          return fail("source.service",
                      "service aliases are immutable unannotated names",
                      s.span);
        std::set<std::string> seen;
        if (!pattern(s.pattern, s.mutableBinding, service, seen, depth))
          return false;
      } else if (s.kind == Statement::Kind::Assign) {
        s.pattern.binding = lookup(s.pattern.name, s.pattern.span);
        if (!s.pattern.binding)
          return false;
        if (!syntax.bindings[s.pattern.binding->index].mutableBinding)
          return fail("source.assignment",
                      "assignment requires a mutable binding", s.span);
      }
    }
    for (auto &[name, value] : b.results)
      if (!expression(value, depth))
        return false;
    currentBody = b.parent;
    return true;
  }
};
} // namespace
bool resolveBindings(Checker &checker, Declaration &decl,
                     SyntaxDeclaration &syntax) {
  return Resolver(checker, decl, syntax).run();
}
} // namespace zkc::language::detail
