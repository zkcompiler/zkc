#include "Internal.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include <algorithm>
#include <numeric>

using namespace llvm;
namespace zkc::language::detail {
namespace {
class Checker {
public:
  Checker(std::vector<SyntaxModule> syntax, CheckedStorage &output, Work &work)
      : syntax(std::move(syntax)), output(output), work(work) {}
  Error run() {
    if (!collect() || !imports() || !signatures())
      return takeError();
    state.resize(output.declarations.size());
    heights.resize(state.size());
    for (auto &decl : output.declarations) {
      if (decl.kind == Declaration::Kind::Math ||
          decl.kind == Declaration::Kind::Protocol) {
        if (!body(decl.id, 1))
          return takeError();
      } else if (decl.kind == Declaration::Kind::Entry) {
        auto target =
            resolve(decl.module, sources[decl.id.index]->target, decl.span);
        if (!target)
          return takeError();
        if (output.declarations[target->index].kind !=
            Declaration::Kind::Protocol) {
          fail("source.entry", "Entry must select a protocol", decl.span);
          return takeError();
        }
        decl.target = *target;
      }
    }
    return Error::success();
  }

private:
  std::vector<SyntaxModule> syntax;
  CheckedStorage &output;
  Work &work;
  std::optional<Diagnostic> diagnostic;
  std::map<std::string, ModuleId> modules;
  std::map<std::string, DeclarationId> qualified;
  std::vector<std::map<std::string, DeclarationId>> visible;
  std::vector<SyntaxDeclaration *> sources;
  std::vector<unsigned> state, heights;
  bool fail(StringRef code, const Twine &message, Span span,
            std::vector<Span> related = {}) {
    if (!diagnostic)
      diagnostic =
          Diagnostic{code.str(), message.str(), span, std::move(related)};
    return false;
  }
  bool accept(Error error) {
    bool success = !error;
    handleAllErrors(std::move(error), [&](const DiagnosticError &value) {
      if (!diagnostic)
        diagnostic = value.diagnostic();
    });
    return success;
  }
  Error takeError() { return make_error<DiagnosticError>(*diagnostic); }
  bool charge(uint64_t count, Span span) {
    return accept(work.charge(count, span));
  }
  bool collect() {
    visible.resize(syntax.size());
    for (auto &module : syntax) {
      const auto &name = output.capture.sources()[module.id.index].module;
      modules.emplace(name, module.id);
      for (auto &source : module.declarations) {
        Declaration decl;
        decl.id = DeclarationId{uint32_t(output.declarations.size())};
        decl.module = module.id;
        decl.kind = source.kind;
        decl.name = source.name;
        decl.qualifiedName = name + "::" + source.name;
        decl.span = source.span;
        decl.isPublic = source.isPublic;
        if (!visible[module.id.index].emplace(decl.name, decl.id).second)
          return fail("source.duplicate", "duplicate declaration: " + decl.name,
                      decl.span);
        auto symbol = encodeSymbol(decl.qualifiedName, work.limits);
        if (!symbol)
          return accept(symbol.takeError());
        decl.symbol = std::move(*symbol);
        qualified.emplace(decl.qualifiedName, decl.id);
        if (source.kind == Declaration::Kind::Domain) {
          if (protocol::installedDomains().identitySort(source.domain) !=
              "Field")
            return fail("source.domain",
                        "expected installed Field identity: " + source.domain,
                        source.span);
          decl.domain = {Type::Kind::Field, source.domain};
        }
        sources.push_back(&source);
        output.declarations.push_back(std::move(decl));
      }
    }
    return true;
  }
  bool imports() {
    std::vector<std::vector<unsigned>> edges(syntax.size());
    for (auto &module : syntax)
      for (const auto &import : module.imports) {
        if (!charge(import.names.size() + 1, import.span))
          return false;
        auto target = modules.find(import.module);
        if (target == modules.end())
          return fail("source.import",
                      "module was not explicitly captured: " + import.module,
                      import.span);
        edges[module.id.index].push_back(target->second.index);
        for (const auto &name : import.names) {
          auto found = qualified.find(import.module + "::" + name);
          if (found == qualified.end())
            return fail("source.import",
                        "unknown imported declaration: " + name, import.span);
          const auto &decl = output.declarations[found->second.index];
          if (!decl.isPublic)
            return fail("source.private",
                        "cannot import private declaration: " + name,
                        import.span, {decl.span});
          if (!visible[module.id.index].emplace(name, decl.id).second)
            return fail("source.duplicate",
                        "import conflicts with visible name: " + name,
                        import.span);
        }
      }
    std::vector<unsigned> active(syntax.size()), height(syntax.size());
    std::function<bool(unsigned, unsigned)> visit = [&](unsigned index,
                                                        unsigned depth) {
      Span span{ModuleId{index}, 0, 0};
      if (depth > work.limits.importDepth)
        return fail("source.limit", "import depth limit exceeded", span);
      if (active[index] == 1)
        return fail("source.cycle", "cyclic module imports", span);
      if (active[index] == 2)
        return depth - 1 + height[index] <= work.limits.importDepth ||
               fail("source.limit", "import depth limit exceeded", span);
      active[index] = 1;
      height[index] = 1;
      for (unsigned edge : edges[index]) {
        if (!charge(1, span) || !visit(edge, depth + 1))
          return false;
        height[index] = std::max(height[index], height[edge] + 1);
      }
      active[index] = 2;
      return true;
    };
    for (unsigned i = 0; i < syntax.size(); ++i)
      if (!visit(i, 1))
        return false;
    return true;
  }
  std::optional<DeclarationId> resolve(ModuleId module, StringRef name,
                                       Span span) {
    if (!charge(1, span))
      return {};
    auto &scope = name.contains("::") ? qualified : visible[module.index];
    auto found = scope.find(name.str());
    if (found == scope.end()) {
      fail("source.name", "unknown declaration: " + name, span);
      return {};
    }
    const auto &decl = output.declarations[found->second.index];
    if (decl.module.index != module.index && !decl.isPublic) {
      fail("source.private", "cannot reference private declaration: " + name,
           span, {decl.span});
      return {};
    }
    return decl.id;
  }
  std::optional<Type> type(ModuleId module, const SyntaxType &syntaxType) {
    if (syntaxType.name == "bool")
      return Type{};
    auto id = resolve(module, syntaxType.name, syntaxType.span);
    if (!id)
      return {};
    const auto &decl = output.declarations[id->index];
    if (decl.kind != Declaration::Kind::Domain) {
      fail("source.type", "expected a domain alias", syntaxType.span);
      return {};
    }
    return decl.domain;
  }
  std::optional<std::vector<unsigned>>
  roles(const Declaration &decl, ArrayRef<std::string> names, Span span) {
    if (!charge(names.size() * (decl.roles.size() + 1), span))
      return {};
    std::vector<unsigned> result;
    for (const auto &name : names) {
      auto found = llvm::find(decl.roles, name);
      if (found == decl.roles.end()) {
        fail("source.roles", "unknown participant: " + name, span);
        return {};
      }
      result.push_back(found - decl.roles.begin());
    }
    std::sort(result.begin(), result.end());
    if (result.empty() ||
        std::adjacent_find(result.begin(), result.end()) != result.end()) {
      fail("source.roles",
           "role set must be nonempty and contain distinct participants", span);
      return {};
    }
    return result;
  }
  bool signatures() {
    for (auto &decl : output.declarations) {
      const auto &source = *sources[decl.id.index];
      if (decl.kind != Declaration::Kind::Math &&
          decl.kind != Declaration::Kind::Protocol)
        continue;
      std::set<std::string> roster;
      decl.roles = source.roles;
      if (decl.roles.size() > 1024)
        return fail("source.limit", "participant roster exceeds target limit",
                    decl.span);
      for (const auto &name : decl.roles)
        if (!roster.insert(name).second)
          return fail("source.roles", "duplicate participant: " + name,
                      decl.span);
      for (bool input : {true, false}) {
        std::set<std::string> names;
        for (const auto &port : input ? source.inputs : source.outputs) {
          if (!names.insert(port.name).second)
            return fail("source.duplicate", "duplicate port: " + port.name,
                        port.span);
          if (input && visible[decl.module.index].count(port.name))
            return fail("source.shadow",
                        "input shadows a visible declaration: " + port.name,
                        port.span);
          auto portType = type(decl.module, port.type);
          if (!portType)
            return false;
          Port result{port.name, *portType, {}, port.span};
          if (decl.kind == Declaration::Kind::Protocol) {
            auto set = roles(decl, port.roles, port.span);
            if (!set)
              return false;
            result.roles = std::move(*set);
          }
          (input ? decl.inputs : decl.outputs).push_back(std::move(result));
        }
      }
    }
    return true;
  }
  bool body(DeclarationId id, unsigned depth) {
    auto &decl = output.declarations[id.index];
    if (depth > work.limits.callDepth)
      return fail("source.limit", "helper call depth limit exceeded",
                  decl.span);
    if (state[id.index] == 1)
      return fail("source.cycle", "recursive mathematical helper", decl.span);
    if (state[id.index] == 2)
      return depth - 1 + heights[id.index] <= work.limits.callDepth ||
             fail("source.limit", "helper call depth limit exceeded",
                  decl.span);
    state[id.index] = 1;
    heights[id.index] = 1;
    const auto &source = *sources[id.index];
    // Check the complete call graph before processing values, including unused
    // work.
    for (const auto &expr : source.expressions)
      if (expr.kind == Expression::Kind::Call) {
        auto callee = resolve(decl.module, expr.text, expr.span);
        if (!callee)
          return false;
        if (output.declarations[callee->index].kind != Declaration::Kind::Math)
          return fail(
              "source.call",
              "only mathematical helpers can be called in this source format",
              expr.span);
        if (!body(*callee, depth + 1))
          return false;
        heights[id.index] =
            std::max(heights[id.index], heights[callee->index] + 1);
      }
    Body checked;
    checked.mode = decl.kind == Declaration::Kind::Math ? Body::Mode::Math
                                                        : Body::Mode::Protocol;
    std::map<std::string, ValueId> bindings;
    for (unsigned i = 0; i < decl.inputs.size(); ++i) {
      const auto &port = decl.inputs[i];
      bindings.emplace(port.name, ValueId{i});
      checked.values.push_back({port.type,
                                checked.mode == Body::Mode::Math
                                    ? std::vector<unsigned>{i}
                                    : port.roles,
                                port.span});
    }
    BodyChecker checker{*this, decl, source, checked, bindings};
    for (unsigned index = 0; index < source.statements.size(); ++index) {
      const auto &statement = source.statements[index];
      checker.statement = index;
      if (bindings.count(statement.name) ||
          visible[decl.module.index].count(statement.name))
        return fail("source.shadow",
                    "binding shadows a visible name: " + statement.name,
                    statement.span);
      std::optional<Type> expected;
      if (statement.type) {
        expected = type(decl.module, *statement.type);
        if (!expected)
          return false;
      }
      auto value = checker.expression(statement.expression, expected);
      if (!value)
        return false;
      if (statement.exchange) {
        auto sender = roles(decl, {statement.exchange->first}, statement.span);
        auto receiver =
            roles(decl, {statement.exchange->second}, statement.span);
        if (!sender || !receiver)
          return false;
        if (*sender == *receiver)
          return fail("source.send", "sender and receiver must be distinct",
                      statement.span);
        const auto payload = checked.values[value->index];
        if (!llvm::is_contained(payload.components, sender->front()))
          return fail("source.roles", "payload is unavailable at sender",
                      statement.span);
        value =
            checker.emit(Exchange{sender->front(), receiver->front(), *value},
                         payload.type, *receiver, statement.span);
        if (!value)
          return false;
      }
      if (statement.roles) {
        auto selected = roles(decl, *statement.roles, statement.span);
        if (!selected)
          return false;
        const auto before = checked.values[value->index];
        if (!std::includes(before.components.begin(), before.components.end(),
                           selected->begin(), selected->end()))
          return fail("source.roles",
                      "binding cannot gain participant availability",
                      statement.span);
        if (*selected != before.components) {
          value = checker.emit(Restriction{*value, *selected}, before.type,
                               *selected, statement.span);
          if (!value)
            return false;
        }
      }
      bindings.emplace(statement.name, *value);
    }
    checker.statement = source.statements.size();
    checked.results.resize(decl.outputs.size());
    std::set<unsigned> returned;
    std::map<std::string, unsigned> outputIndices;
    for (unsigned i = 0; i < decl.outputs.size(); ++i)
      outputIndices.emplace(decl.outputs[i].name, i);
    // Evaluate in written order, then put operands in declared port order.
    for (const auto &result : source.results) {
      const auto &name = result.first;
      auto expr = result.second;
      auto found = outputIndices.find(name);
      if (found == outputIndices.end())
        return fail("source.return", "unknown return port: " + name,
                    source.expressions[expr].span);
      unsigned index = found->second;
      const auto &port = decl.outputs[index];
      if (!returned.insert(index).second)
        return fail("source.return", "duplicate return port: " + name,
                    source.expressions[expr].span);
      auto value = checker.expression(expr, port.type);
      if (!value)
        return false;
      const auto &available = checked.values[value->index].components;
      if (checked.mode == Body::Mode::Protocol &&
          !std::includes(available.begin(), available.end(), port.roles.begin(),
                         port.roles.end()))
        return fail("source.roles",
                    "result is unavailable at declared output roles",
                    source.expressions[expr].span);
      checked.results[index] = *value;
    }
    if (returned.size() != decl.outputs.size())
      return fail("source.return", "missing return port", decl.span);
    decl.body = std::move(checked);
    state[id.index] = 2;
    return true;
  }
  struct BodyChecker {
    Checker &checker;
    Declaration &decl;
    const SyntaxDeclaration &source;
    Body &body;
    std::map<std::string, ValueId> &bindings;
    uint32_t statement = 0;
    bool math() const { return body.mode == Body::Mode::Math; }
    std::vector<unsigned> allRoles() const {
      std::vector<unsigned> value(decl.roles.size());
      std::iota(value.begin(), value.end(), 0);
      return value;
    }
    std::optional<std::vector<unsigned>> combine(ArrayRef<ValueId> operands,
                                                 Span span) {
      std::vector<unsigned> result =
          math() ? std::vector<unsigned>{} : allRoles();
      for (ValueId value : operands) {
        const auto &components = body.values[value.index].components;
        if (!checker.charge(result.size() + components.size() + 1, span))
          return {};
        std::vector<unsigned> next;
        if (math())
          std::set_union(result.begin(), result.end(), components.begin(),
                         components.end(), std::back_inserter(next));
        else
          std::set_intersection(result.begin(), result.end(),
                                components.begin(), components.end(),
                                std::back_inserter(next));
        result = std::move(next);
      }
      if (!math() && result.empty()) {
        checker.fail("source.roles", "operation has no common participant",
                     span);
        return {};
      }
      return result;
    }
    template <typename Action>
    std::optional<ValueId> emit(Action action, const Type &type,
                                std::vector<unsigned> components, Span span) {
      if (!checker.accept(checker.work.count(checker.work.operations,
                                             checker.work.limits.operations,
                                             "operation count", span)) ||
          !checker.charge(components.size() + 1, span))
        return {};
      ValueId id{uint32_t(body.values.size())};
      body.values.push_back({type, std::move(components), span});
      body.operations.push_back({std::move(action), id, span, statement});
      return id;
    }
    std::optional<Type> hint(uint32_t id, unsigned depth = 1) {
      const auto &expr = source.expressions[id];
      if (depth > checker.work.limits.expressionDepth) {
        checker.fail("source.limit", "expression depth limit exceeded",
                     expr.span);
        return {};
      }
      if (!checker.charge(1, expr.span))
        return {};
      using K = Expression::Kind;
      if (expr.kind == K::Boolean || expr.kind == K::Equal)
        return Type{};
      if (expr.kind == K::Decimal)
        return {};
      if (expr.kind == K::Name) {
        auto found = bindings.find(expr.text);
        if (found == bindings.end()) {
          checker.fail("source.name", "unknown local value: " + expr.text,
                       expr.span);
          return {};
        }
        return body.values[found->second.index].type;
      }
      if (expr.kind == K::Call) {
        auto callee = checker.resolve(decl.module, expr.text, expr.span);
        if (!callee)
          return {};
        return checker.output.declarations[callee->index].outputs.front().type;
      }
      for (uint32_t child : expr.children) {
        auto value = hint(child, depth + 1);
        if (value || checker.diagnostic)
          return value;
      }
      return {};
    }
    std::optional<ValueId> expression(uint32_t id,
                                      std::optional<Type> expected = {},
                                      unsigned depth = 1) {
      const auto &expr = source.expressions[id];
      if (depth > checker.work.limits.expressionDepth) {
        checker.fail("source.limit", "expression depth limit exceeded",
                     expr.span);
        return {};
      }
      if (!checker.charge(1, expr.span))
        return {};
      using K = Expression::Kind;
      std::optional<ValueId> result;
      if (expr.kind == K::Name) {
        auto found = bindings.find(expr.text);
        if (found == bindings.end()) {
          checker.fail("source.name", "unknown local value: " + expr.text,
                       expr.span);
          return {};
        }
        result = found->second;
      } else if (expr.kind == K::Decimal || expr.kind == K::Boolean) {
        Type type;
        if (expr.kind == K::Decimal) {
          if (!expected || expected->kind != Type::Kind::Field) {
            checker.fail("source.inference",
                         "field literal needs a unique field context",
                         expr.span);
            return {};
          }
          type = *expected;
          if (auto error = protocol::checkParameters(
                  "field.constant", {expr.text}, type.domain)) {
            checker.fail("source.literal", toString(std::move(error)),
                         expr.span);
            return {};
          }
        }
        result = emit(MathValue{expr.kind == K::Decimal
                                    ? MathematicalIdentity::FieldConstant
                                    : MathematicalIdentity::BooleanConstant,
                                {},
                                expr.text},
                      type, math() ? std::vector<unsigned>{} : allRoles(),
                      expr.span);
      } else if (expr.kind == K::Call) {
        auto target = checker.resolve(decl.module, expr.text, expr.span);
        if (!target)
          return {};
        const auto &callee = checker.output.declarations[target->index];
        if (expr.children.size() != callee.inputs.size()) {
          checker.fail("source.call", "helper argument count mismatch",
                       expr.span);
          return {};
        }
        std::vector<ValueId> args;
        for (unsigned i = 0; i < expr.children.size(); ++i) {
          auto value =
              expression(expr.children[i], callee.inputs[i].type, depth + 1);
          if (!value)
            return {};
          args.push_back(*value);
        }
        auto substitute = [&](ArrayRef<unsigned> dependencies)
            -> std::optional<std::vector<unsigned>> {
          if (!checker.charge(dependencies.size() + 1, expr.span))
            return {};
          std::vector<ValueId> selected;
          for (unsigned input : dependencies)
            selected.push_back(args[input]);
          return combine(selected, expr.span);
        };
        for (const auto &requirement : callee.body->formationRequirements) {
          auto required = substitute(requirement);
          if (!required)
            return {};
          if (math() && !required->empty())
            body.formationRequirements.push_back(std::move(*required));
        }
        auto components = substitute(
            callee.body->values[callee.body->results.front().index].components);
        if (!components)
          return {};
        result = emit(HelperCall{*target, std::move(args)},
                      callee.outputs.front().type, std::move(*components),
                      expr.span);
      } else {
        bool equal = expr.kind == K::Equal;
        std::optional<Type> operandType =
            equal ? std::optional<Type>{} : expected;
        if (!operandType)
          for (auto child : expr.children) {
            operandType = hint(child, depth + 1);
            if (checker.diagnostic)
              return {};
            if (operandType)
              break;
          }
        if (!operandType) {
          checker.fail("source.inference",
                       "expression needs a unique operand type", expr.span);
          return {};
        }
        if (!equal && operandType->kind != Type::Kind::Field) {
          checker.fail("source.type", "arithmetic requires a field", expr.span);
          return {};
        }
        std::vector<ValueId> args;
        for (auto child : expr.children) {
          auto value = expression(child, operandType, depth + 1);
          if (!value)
            return {};
          args.push_back(*value);
        }
        auto components = combine(args, expr.span);
        if (!components)
          return {};
        if (math() && !components->empty())
          body.formationRequirements.push_back(*components);
        MathematicalIdentity identity =
            expr.kind == K::Add        ? MathematicalIdentity::FieldAdd
            : expr.kind == K::Subtract ? MathematicalIdentity::FieldSubtract
            : expr.kind == K::Multiply ? MathematicalIdentity::FieldMultiply
            : operandType->kind == Type::Kind::Field
                ? MathematicalIdentity::FieldEqual
                : MathematicalIdentity::BooleanEqual;
        result = emit(MathValue{identity, std::move(args), {}},
                      equal ? Type{} : *operandType, std::move(*components),
                      expr.span);
      }
      if (result && expected && body.values[result->index].type != *expected) {
        checker.fail("source.type", "expression type does not match context",
                     expr.span);
        return {};
      }
      return result;
    }
  };
};
} // namespace
Error check(std::vector<SyntaxModule> syntax, CheckedStorage &output,
            Work &work) {
  return Checker(std::move(syntax), output, work).run();
}
} // namespace zkc::language::detail
