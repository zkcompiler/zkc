#include "Checker.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
Checker::Checker(std::vector<SyntaxModule> syntax, CheckedStorage &output,
                 Work &work)
    : output(output), work(work),
      naturals(work.limits.work, work.limits.naturalTerms,
               work.limits.naturalFactors),
      syntax(std::move(syntax)) {}
Checker::Checker(CheckedStorage &output, Work &work)
    : Checker({}, output, work) {
  signatureState.assign(output.declarations.size(), 2);
  for (const auto &decl : output.declarations) {
    if (!decl.anonymous)
      qualified.emplace(decl.qualifiedName, decl.id);
    for (unsigned i = 0; i < decl.parameters.size(); ++i)
      parameters.emplace(decl.parameters[i].atom, std::make_pair(decl.id, i));
  }
}
bool Checker::fail(StringRef code, const Twine &message, Span span,
                   std::vector<Span> related) {
  if (!diagnostic)
    diagnostic =
        Diagnostic{code.str(), message.str(), span, std::move(related)};
  return false;
}
bool Checker::accept(Error error) {
  bool success = !error;
  handleAllErrors(
      std::move(error),
      [&](const DiagnosticError &e) {
        if (!diagnostic)
          diagnostic = e.diagnostic();
      },
      [&](const ErrorInfoBase &e) {
        if (!diagnostic) {
          std::string message = e.message();
          auto parts = StringRef(message).split(':');
          diagnostic =
              Diagnostic{parts.first.str(), parts.second.trim().str(), {}, {}};
        }
      });
  return success;
}
bool Checker::charge(uint64_t count, Span span) {
  return accept(work.charge(count, span));
}
Error Checker::takeError() { return make_error<DiagnosticError>(*diagnostic); }
Error Checker::run() {
  if (auto error = checkCapabilityInstallation())
    return error;
  if (!collect() || !imports())
    return takeError();
  signatureState.resize(output.declarations.size());
  for (unsigned i = 0; i < output.declarations.size(); ++i)
    if (!signature(DeclarationId{i}))
      return takeError();
  if (!relationIdentities())
    return takeError();
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Component && !conformance(decl.id))
      return takeError();
  if (!representations())
    return takeError();
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Record ||
        decl.kind == Declaration::Kind::Variant) {
      SyntaxType syntax;
      syntax.name = decl.qualifiedName;
      syntax.span = decl.span;
      for (auto &p : decl.parameters) {
        SyntaxType argument;
        argument.name = p.name;
        argument.span = p.span;
        syntax.arguments.push_back(std::move(argument));
      }
      auto nominal = type(decl, syntax);
      if (!nominal || !permissions(*nominal, decl.span, &decl))
        return takeError();
    }
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Math)
      for (auto *ports : {&decl.inputs, &decl.outputs})
        for (const auto &port : *ports) {
          auto caps = permissions(port.type, port.span, &decl);
          if (!caps)
            return takeError();
          if (!caps->copy || !caps->drop) {
            fail("source.mode", "mathematical signatures require Copy and Drop",
                 port.span);
            return takeError();
          }
        }
  bodyState.resize(output.declarations.size());
  bodyHeights.resize(bodyState.size());
  for (unsigned i = 0; i < sources.size(); ++i) {
    auto &decl = output.declarations[i];
    if ((decl.kind == Declaration::Kind::Math ||
         decl.kind == Declaration::Kind::Local ||
         decl.kind == Declaration::Kind::Protocol ||
         (decl.kind == Declaration::Kind::Relation &&
          decl.relation->kind == RelationDefinition::Kind::Formula)) &&
        !decl.abstract && !body(decl.id, 1))
      return takeError();
  }
  for (auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Protocol && !specifications(decl))
      return takeError();
  if (!entries())
    return takeError();
  return Error::success();
}
bool Checker::bindingName(const Declaration &decl, StringRef name, Span span) {
  if (visible[decl.module.index].count(name.str()) ||
      llvm::any_of(decl.parameters, [&](auto &p) { return p.name == name; }))
    return fail("source.shadow",
                "binding shadows a visible declaration or static parameter",
                span);
  return true;
}
bool Checker::collect() {
  visible.resize(syntax.size());
  std::function<bool(SyntaxDeclaration &, ModuleId,
                     std::optional<DeclarationId>)>
      add;
  add = [&](SyntaxDeclaration &source, ModuleId module,
            std::optional<DeclarationId> parent) {
    Declaration decl;
    decl.id = {uint32_t(output.declarations.size())};
    decl.module = module;
    decl.kind = source.kind;
    decl.name = source.name;
    decl.parent = parent;
    decl.span = source.span;
    decl.qualifiedName =
        (parent ? output.declarations[parent->index].qualifiedName
                : output.capture.sources()[module.index].module) +
        "::" + source.name;
    decl.isPublic = source.isPublic;
    decl.abstract = source.abstract;
    decl.completes = source.completes;
    decl.permissions = source.permissions;
    decl.effectAllowance = source.effects;
    decl.associatedSort = source.associatedSort;
    decl.anonymous = source.anonymous;
    decl.specificationBlock = source.specificationBlock;
    if (source.relation) {
      const auto &definition = *source.relation;
      decl.relation = RelationDefinition{
          definition.kind,     {}, definition.externalKind, definition.key,
          definition.revision, {}};
      for (const auto &port : source.inputs)
        decl.relation->purposes.push_back(*port.purpose);
    }
    if (decl.anonymous)
      decl.qualifiedName = output.declarations[parent->index].qualifiedName +
                           "::<" + source.name + ">";
    if (!decl.anonymous &&
        !qualified.emplace(decl.qualifiedName, decl.id).second)
      return fail("source.duplicate", "duplicate declaration: " + decl.name,
                  decl.span);
    if (!parent && !visible[module.index].emplace(decl.name, decl.id).second)
      return fail("source.duplicate", "duplicate declaration: " + decl.name,
                  decl.span);
    auto symbol =
        decl.anonymous
            ? Expected<std::string>("zki_" + digest(decl.qualifiedName))
            : encodeSymbol(decl.qualifiedName, work.limits);
    if (!symbol)
      return accept(symbol.takeError());
    decl.symbol = std::move(*symbol);
    if (source.kind == Declaration::Kind::Domain) {
      auto sorts = protocol::domainSorts();
      auto sort = llvm::find_if(sorts, [&](const std::string &sort) {
        return StringRef(sort).lower() == source.target;
      });
      if (sort == sorts.end())
        return fail("source.domain", "unknown domain sort: " + source.target,
                    source.span);
      if (protocol::installedDomains().identitySort(source.domain) != *sort)
        return fail("source.domain",
                    "expected installed " + source.target +
                        " identity: " + source.domain,
                    source.span);
      decl.domain = domainType(*sort, source.domain);
    }
    auto id = decl.id;
    sources.push_back(&source);
    output.declarations.push_back(std::move(decl));
    if (parent)
      output.declarations[parent->index].members.push_back(id);
    for (auto &member : source.members)
      if (!add(member, module, id))
        return false;
    return true;
  };
  for (auto &module : syntax) {
    modules.emplace(output.capture.sources()[module.id.index].module,
                    module.id);
    for (auto &decl : module.declarations)
      if (!add(decl, module.id, {}))
        return false;
  }
  return true;
}
bool Checker::imports() {
  std::vector<std::vector<unsigned>> edges(syntax.size());
  for (auto &module : syntax)
    for (auto &import : module.imports) {
      if (!charge(import.names.size() + 1, import.span))
        return false;
      auto target = modules.find(import.module);
      if (target == modules.end())
        return fail("source.import",
                    "module was not explicitly captured: " + import.module,
                    import.span);
      edges[module.id.index].push_back(target->second.index);
      for (auto &name : import.names) {
        auto found = qualified.find(import.module + "::" + name);
        if (found == qualified.end())
          return fail("source.import", "unknown imported declaration: " + name,
                      import.span);
        auto &decl = output.declarations[found->second.index];
        if (!decl.isPublic)
          return fail("source.private",
                      "cannot import private declaration: " + name, import.span,
                      {decl.span});
        if (!visible[module.id.index].emplace(name, decl.id).second)
          return fail("source.duplicate",
                      "import conflicts with visible name: " + name,
                      import.span);
      }
    }
  std::vector<unsigned> active(syntax.size()), height(syntax.size());
  std::function<bool(unsigned, unsigned)> visit = [&](unsigned i,
                                                      unsigned depth) {
    Span span{ModuleId{i}, 0, 0};
    if (depth > work.limits.importDepth)
      return fail("source.limit", "import depth limit exceeded", span);
    if (active[i] == 1)
      return fail("source.cycle", "cyclic module imports", span);
    if (active[i] == 2)
      return depth - 1 + height[i] <= work.limits.importDepth ||
             fail("source.limit", "import depth limit exceeded", span);
    active[i] = 1;
    height[i] = 1;
    for (auto edge : edges[i]) {
      if (!charge(1, span) || !visit(edge, depth + 1))
        return false;
      height[i] = std::max(height[i], height[edge] + 1);
    }
    active[i] = 2;
    return true;
  };
  for (unsigned i = 0; i < syntax.size(); ++i)
    if (!visit(i, 1))
      return false;
  return true;
}
std::optional<DeclarationId> Checker::resolve(const Declaration &context,
                                              StringRef name, Span span) {
  if (!charge(1, span))
    return {};
  std::optional<DeclarationId> id;
  for (auto parent = context.parent; parent;
       parent = output.declarations[parent->index].parent) {
    auto found = qualified.find(
        output.declarations[parent->index].qualifiedName + "::" + name.str());
    if (found != qualified.end()) {
      id = found->second;
      break;
    }
  }
  if (!id) {
    auto found = qualified.find(name.str());
    if (found != qualified.end())
      id = found->second;
  }
  if (!id) {
    auto parts = name.split("::");
    auto found = visible[context.module.index].find(parts.first.str());
    if (found != visible[context.module.index].end()) {
      if (parts.second.empty())
        id = found->second;
      else {
        auto member = qualified.find(
            output.declarations[found->second.index].qualifiedName +
            "::" + parts.second.str());
        if (member != qualified.end())
          id = member->second;
      }
    }
  }
  if (!id) {
    fail("source.name", "unknown declaration: " + name, span);
    return {};
  }
  auto &decl = output.declarations[id->index];
  for (auto current = std::optional<DeclarationId>{*id}; current;
       current = output.declarations[current->index].parent) {
    auto &ancestor = output.declarations[current->index];
    if (ancestor.module.index != context.module.index && !ancestor.isPublic) {
      fail("source.private", "cannot reference private declaration: " + name,
           span, {ancestor.span});
      return {};
    }
  }
  return decl.id;
}
std::optional<std::vector<unsigned>> Checker::roles(const Declaration &decl,
                                                    ArrayRef<std::string> names,
                                                    Span span) {
  if (!charge(names.size() * (decl.roles.size() + 1), span))
    return {};
  std::vector<unsigned> result;
  for (auto &name : names) {
    auto found = llvm::find(decl.roles, name);
    if (found == decl.roles.end()) {
      fail("source.roles", "unknown participant: " + name, span);
      return {};
    }
    result.push_back(found - decl.roles.begin());
  }
  llvm::sort(result);
  if (result.empty() ||
      std::adjacent_find(result.begin(), result.end()) != result.end()) {
    fail("source.roles", "role set must be nonempty and distinct", span);
    return {};
  }
  return result;
}
Error check(std::vector<SyntaxModule> syntax, CheckedStorage &output,
            Work &work) {
  return Checker(std::move(syntax), output, work).run();
}
} // namespace zkc::language::detail
