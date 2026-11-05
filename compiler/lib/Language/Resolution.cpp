#include "Checker.h"
#include "llvm/Support/SaveAndRestore.h"
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
    if (!elaborateExpressions(checker, syntax) ||
        !checker.types.charge(syntax.inputOrder.size(), syntax.span))
      return false;
    for (auto [i, slot] : llvm::enumerate(syntax.inputOrder))
      inputOrigins.emplace(std::make_pair(slot.kind, slot.index), unsigned(i));
    for (auto &port : decl.inputs) {
      auto id = bind(port.name, port.span, false, false, true);
      if (!id)
        return false;
      inputOrigin(*id, Declaration::InputSlot::Kind::Data,
                  syntax.inputBindings.size());
      syntax.inputBindings.push_back(*id);
    }
    for (auto &port : decl.services) {
      auto id = bind(port.name, port.span, false, true, true);
      if (!id)
        return false;
      inputOrigin(*id, Declaration::InputSlot::Kind::Service,
                  syntax.serviceBindings.size());
      syntax.serviceBindings.push_back(*id);
    }
    for (auto &port : decl.scopedInputs) {
      auto id = bind(port.name, port.span, false, false, true);
      if (!id)
        return false;
      syntax.bindings[id->index].scoped = true;
      inputOrigin(*id, Declaration::InputSlot::Kind::Scoped,
                  syntax.scopedBindings.size());
      syntax.scopedBindings.push_back(*id);
    }
    for (auto &port : decl.domainInputs) {
      auto id = bind(port.name, port.span, false, false, true);
      if (!id)
        return false;
      syntax.bindings[id->index].domain = true;
      inputOrigin(*id, Declaration::InputSlot::Kind::Domain,
                  syntax.domainBindings.size());
      syntax.domainBindings.push_back(*id);
    }
    if (syntax.oracleDefinition) {
      const auto &port = syntax.oracleDefinition->queryParameter;
      auto id = bind(port.name, port.span, false, false, true);
      if (!id)
        return false;
      syntax.oracleDefinition->queryBinding = *id;
      syntax.bindings[id->index].written =
          LexicalNode{LexicalNode::Kind::OracleQueryParameter, 0};
    }
    if (!syntax.primitive && !syntax.domainConstructor &&
        !syntax.finiteDefinition && !body(0, 1))
      return false;
    if (!checker.types.charge(1, syntax.span))
      return false;
    checker.output.lexicalResolutions.push_back(
        {syntax.span, std::move(references), std::move(authoringBindings)});
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
  std::vector<LexicalReference> references;
  std::vector<LexicalBinding> authoringBindings;
  std::optional<Span> bindingScope;
  uint32_t visibleAfter = 0;
  std::map<std::pair<Declaration::InputSlot::Kind, unsigned>, unsigned>
      inputOrigins;
  void inputOrigin(BindingId binding, Declaration::InputSlot::Kind kind,
                   unsigned index) {
    if (syntax.inputOrder.empty() &&
        kind == Declaration::InputSlot::Kind::Data) {
      syntax.bindings[binding.index].written =
          LexicalNode{LexicalNode::Kind::Input, index};
      return;
    }
    if (auto found = inputOrigins.find({kind, index});
        found != inputOrigins.end())
      syntax.bindings[binding.index].written =
          LexicalNode{LexicalNode::Kind::Input, found->second};
  }
  bool use(LexicalReference::Access access, LexicalNode node, BindingId binding,
           Span span) {
    if (!checker.types.charge(1, span))
      return false;
    references.push_back({access, node, syntax.bindings[binding.index].written,
                          span, syntax.bindings[binding.index].span});
    return true;
  }
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
      if (syntax.layoutSyntax && binding.scope == scope) {
        fail("source.shadow",
             "binding already exists in this scope; use ':=' for mutable state",
             span);
        return {};
      }
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
    syntax.bindings.push_back({name.str(), span, mut, service, false, scope});
    auto visible = bindingScope.value_or(
        currentBody ? syntax.bodies[*currentBody].span : syntax.span);
    visible.begin = std::max(visible.begin, visibleAfter);
    authoringBindings.push_back({name.str(), span, visible, scope});
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
      if (p.binding && p.writtenToken)
        syntax.bindings[p.binding->index].written =
            LexicalNode{LexicalNode::Kind::Pattern, *p.writtenToken};
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
  // Independent binder groups do not introduce names into later domains.
  // Refuse an apparent dependency that would otherwise silently resolve to
  // an outer binding with the same spelling. Nested local bindings remain
  // ordinary lexical bindings, and dependent iteration uses a nested binder.
  bool independentDomain(uint32_t id, const Pattern &pattern,
                         std::set<std::string> &prior, unsigned depth) {
    const auto &domain = syntax.expressions[id];
    if (!bounded(depth, domain.span))
      return false;
    if (domain.kind == Expression::Kind::DomainProduct) {
      return independentDomain(domain.children[0], pattern.children[0], prior,
                               depth + 1) &&
             independentDomain(domain.children[1], pattern.children[1], prior,
                               depth + 1);
    }
    std::function<bool(uint32_t, unsigned)> uses = [&](uint32_t expression,
                                                       unsigned depth) {
      const auto &value = syntax.expressions[expression];
      if (!bounded(depth, value.span))
        return false;
      if (value.binding) {
        const auto &binding = syntax.bindings[value.binding->index];
        if (binding.scope <= scope && prior.count(binding.name))
          return fail("source.finite-domain",
                      "independent binder domain refers to an earlier "
                      "binder name; use nested binders for dependent "
                      "iteration, or rename the outer value",
                      value.span);
      }
      for (auto child : value.children)
        if (!uses(child, depth + 1))
          return false;
      for (auto region : value.regions) {
        const auto &body = syntax.bodies[region];
        for (const auto &statement : body.statements)
          if (!uses(statement.expression, depth + 1))
            return false;
        for (const auto &result : body.results)
          if (!uses(result.second, depth + 1))
            return false;
      }
      return true;
    };
    if (!uses(id, depth + 1))
      return false;
    std::function<bool(const Pattern &, unsigned)> names =
        [&](const Pattern &value, unsigned depth) {
          if (!bounded(depth, value.span))
            return false;
          if (value.kind == Pattern::Kind::Name)
            prior.insert(value.name);
          for (const auto &child : value.children)
            if (!names(child, depth + 1))
              return false;
          return true;
        };
    return names(pattern, depth + 1);
  }
  bool expression(uint32_t id, unsigned depth) {
    auto &expr = syntax.expressions[id];
    expr.scope = currentBody;
    if (!bounded(depth, expr.span))
      return false;
    if (expr.kind == Expression::Kind::Name) {
      expr.binding = lookup(expr.text, expr.span);
      return expr.binding &&
             use(LexicalReference::Access::Read,
                 {LexicalNode::Kind::Expression, id}, *expr.binding, expr.span);
    }
    if (expr.kind == Expression::Kind::Call) {
      auto found = names.find(expr.text);
      if (found != names.end()) {
        expr.binding = found->second;
        if (!use(LexicalReference::Access::Call,
                 {LexicalNode::Kind::Expression, id}, *expr.binding, expr.span))
          return false;
      }
    }
    for (unsigned i = 0; i < expr.children.size(); ++i)
      if (!((expr.kind == Expression::Kind::And ||
             expr.kind == Expression::Kind::Or) &&
            i == 1) &&
          !expression(expr.children[i], depth + 1))
        return false;
    if (expr.kind == Expression::Kind::NotationCall && expr.notation &&
        expr.notation->position == NotationDescriptor::Position::Reduction &&
        syntax.expressions[expr.children[0]].kind ==
            Expression::Kind::DomainProduct) {
      std::set<std::string> prior;
      const auto &body = syntax.expressions[expr.children.back()];
      if (!independentDomain(expr.children[0], body.payloads[0][0], prior,
                             depth + 1))
        return false;
    }
    for (unsigned i = 0; i < expr.regions.size(); ++i) {
      SaveAndRestore regionScope(
          bindingScope, std::optional(syntax.bodies[expr.regions[i]].span));
      SaveAndRestore visibility(visibleAfter,
                                syntax.bodies[expr.regions[i]].span.begin);
      auto mark = undo.size();
      ++scope;
      std::set<std::string> seen;
      if (expr.kind == Expression::Kind::For &&
          !pattern(expr.index, false, false, seen, depth + 1))
        return false;
      if (expr.kind == Expression::Kind::Match ||
          expr.kind == Expression::Kind::Lambda)
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
    SaveAndRestore regionScope(bindingScope, std::optional<Span>{});
    SaveAndRestore visibility(visibleAfter, uint32_t(0));
    auto &b = syntax.bodies[id];
    if (!bounded(depth, b.span))
      return false;
    b.parent = currentBody;
    // Boolean control elaboration creates regions after parsing. Those regions
    // inherit the immutable syntax of the enclosing authored body.
    if (!b.notationEnvironment) {
      if (currentBody)
        b.notationEnvironment = syntax.bodies[*currentBody].notationEnvironment;
      else if (decl.module.index < checker.notationEnvironments.size())
        b.notationEnvironment = checker.notationEnvironments[decl.module.index];
    }
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
        bool domain = checker.domainExpression(decl, syntax, s.expression);
        if (checker.types.diagnostic)
          return false;
        if (domain && (s.mutableBinding || s.roles || s.type || s.exchange ||
                       s.pattern.kind != Pattern::Kind::Name))
          return fail("source.finite-domain",
                      "domain aliases require one immutable unannotated name",
                      s.span);
        std::set<std::string> seen;
        SaveAndRestore bindingVisibility(visibleAfter, s.span.end);
        if (!pattern(s.pattern, s.mutableBinding, service, seen, depth))
          return false;
        if (domain)
          syntax.bindings[s.pattern.binding->index].domain = true;
      } else if (s.kind == Statement::Kind::Assign) {
        s.pattern.binding = lookup(s.pattern.name, s.pattern.span);
        if (!s.pattern.binding)
          return false;
        if (s.pattern.writtenToken &&
            !use(LexicalReference::Access::Assign,
                 {LexicalNode::Kind::Pattern, *s.pattern.writtenToken},
                 *s.pattern.binding, s.pattern.span))
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
