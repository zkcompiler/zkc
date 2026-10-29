#include "Checker.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include <functional>
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
using E = ClaimExpression;
const E *argument(const E &expression, StringRef label) {
  for (unsigned i = 0; i < expression.labels.size(); ++i)
    if (expression.labels[i] == label)
      return &expression.arguments[i];
  return nullptr;
}
bool versionedApplication(const E &expression) {
  return expression.kind == E::Kind::Application && expression.version;
}
bool importedLanguageTarget(const E &expression) {
  return expression.kind == E::Kind::Application &&
         expression.text == "imported_language";
}
Error normalizeDomains(E &value, detail::Semantics &types,
                       const detail::Substitution &bindings) {
  if (!types.charge(value.text.size() + value.arguments.size() + 1, value.span))
    return types.takeError();
  if (value.cardinalityDomain) {
    auto domain =
        types.substitute(*value.cardinalityDomain, bindings, value.span);
    if (!domain) {
      if (types.diagnostic && types.diagnostic->code != "source.limit")
        types.diagnostic->code = "source.claim.domain";
      return types.takeError();
    }
    if (domainSort(*domain).empty() || types.symbolic(*domain))
      return detail::failure("source.claim.domain",
                             "cardinality requires a closed nominal domain",
                             value.arguments[0].span);
    value.arguments[0].text = domain->domain;
  }
  for (auto &child : value.arguments)
    if (auto e = normalizeDomains(child, types, bindings))
      return e;
  return Error::success();
}
bool sameSelector(const SpecificationSelector &a,
                  const SpecificationSelector &b) {
  return a.anchor == b.anchor && a.output == b.output && a.port == b.port &&
         a.role == b.role && a.path == b.path;
}
bool matchesSubject(const SourceClaimBlock &block, const ClosedEntry &entry) {
  if (!block.subject)
    return false;
  const auto &authored = entry.project().declarations()[block.subject->index];
  if (authored.kind == Declaration::Kind::Entry)
    return authored.id.index == entry.entry().id.index;
  const auto *protocol = entry.protocolOrNull();
  return authored.kind == Declaration::Kind::Protocol && protocol &&
         entry.invocationKind() == HostInvocation::Kind::Run &&
         protocol->origin && protocol->origin->index == block.subject->index &&
         protocol->staticArguments == block.arguments;
}
// A path traverses only explicitly labelled calls. Repeated occurrences are
// static sites, not dynamic loop iterations. No synthetic ordinal is exported.
using Sites = std::map<std::string, const Operation *>;
Error exportedSites(ArrayRef<Declaration> declarations, const Body *body,
                    StringRef prefix, Sites &sites, detail::Work &work,
                    unsigned depth = 1) {
  if (!body)
    return Error::success();
  if (depth > work.limits.callDepth)
    return detail::failure("source.limit", "source claim site depth exceeded");
  for (const auto &op : body->operations) {
    if (auto e = work.charge(1, op.span))
      return e;
    auto path = op.site ? (prefix + *op.site).str() : std::string();
    if (path.size() > work.limits.symbolBytes)
      return detail::failure("source.limit", "source claim site path exceeded");
    if (op.site && !sites.emplace(path, &op).second)
      return detail::failure("source.claim.site", "ambiguous exported site",
                             op.span);
    if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
      if (auto e = exportedSites(declarations, repeat->region.get(), prefix,
                                 sites, work, depth + 1))
        return e;
    } else if (auto *call = std::get_if<ProtocolApplication>(&op.action)) {
      if (op.site)
        if (auto e = exportedSites(declarations,
                                   declarations[call->callee.index].body.get(),
                                   path + ".", sites, work, depth + 1))
          return e;
    }
  }
  return Error::success();
}
Error checkSites(const E &expression, const Sites &sites, detail::Work &work) {
  if (auto e = work.charge(1, expression.span))
    return e;
  if (expression.kind == E::Kind::Reference &&
      StringRef(expression.text).starts_with("sites.") &&
      !sites.count(expression.text.substr(6)))
    return detail::failure("source.claim.site", "unexported source site",
                           expression.span);
  for (const auto &child : expression.arguments)
    if (auto e = checkSites(child, sites, work))
      return e;
  return Error::success();
}
json::Value expression(const E &value) {
  switch (value.kind) {
  case E::Kind::Natural:
    return json::Object{{"kind", "natural"}, {"value", value.text}};
  case E::Kind::Reference:
    return json::Object{{"kind", "reference"}, {"name", value.text}};
  case E::Kind::Application: {
    json::Array arguments;
    for (unsigned i = 0; i < value.arguments.size(); ++i)
      arguments.push_back(json::Object{
          {"label", value.labels[i].empty() ? json::Value(nullptr)
                                            : json::Value(value.labels[i])},
          {"value", expression(value.arguments[i])}});
    return json::Object{{"kind", "application"},
                        {"name", value.text},
                        {"version", value.version ? json::Value(*value.version)
                                                  : json::Value(nullptr)},
                        {"arguments", std::move(arguments)}};
  }
  case E::Kind::Binary:
    return json::Object{{"kind", "binary"},
                        {"operator", value.text},
                        {"left", expression(value.arguments[0])},
                        {"right", expression(value.arguments[1])}};
  case E::Kind::Unary:
    return json::Object{{"kind", "unary"},
                        {"operator", value.text},
                        {"operand", expression(value.arguments[0])}};
  case E::Kind::List: {
    json::Array items;
    for (const auto &item : value.arguments)
      items.push_back(expression(item));
    return json::Object{{"kind", "list"}, {"items", std::move(items)}};
  }
  }
  llvm_unreachable("claim expression kind");
}
json::Object selector(const SpecificationSelector &value) {
  json::Array path;
  for (auto index : value.path)
    path.push_back(index);
  return json::Object{
      {"output", value.output},
      {"port", value.port},
      {"role", value.anchor ? json::Value(nullptr) : json::Value(value.role)},
      {"path", std::move(path)}};
}
json::Object sourceNode(const CheckedProject &project, Span span) {
  return json::Object{{"module", project.sources()[span.source.index].module},
                      {"begin", span.begin},
                      {"end", span.end}};
}
} // namespace

Expected<std::string> inspectComponentDeclarations(const ClosedEntry &entry,
                                                   const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  detail::Work work{limits};
  Layouts layouts(entry, limits);
  json::Array records, protocols;
  bool linear = false;
  std::set<std::string> seen;
  std::function<Error(const Layout &, unsigned)> retain =
      [&](const Layout &layout, unsigned depth) -> Error {
    if (depth > limits.typeDepth)
      return detail::failure("source.limit", "component declaration depth");
    if (auto e = work.charge(layout.fields.size() + 1))
      return e;
    auto key = typeIdentity(layout.type);
    if (!seen.insert(key).second)
      return Error::success();
    for (const auto &field : layout.fields)
      if (auto e = retain(*field.layout, depth + 1))
        return e;
    if (layout.type.kind != Type::Kind::Record)
      return Error::success();
    const Declaration *declaration = nullptr;
    for (const auto &candidate : entry.declarations())
      if (candidate.qualifiedName == layout.type.domain &&
          candidate.kind == Declaration::Kind::Record) {
        declaration = &candidate;
        break;
      }
    if (!declaration)
      return detail::failure("component-declaration", "missing source record");
    linear |= declaration->resource == Resource::Linear;
    auto term = encodeStaticTerm(layout.type);
    if (!term)
      return term.takeError();
    json::Array fields;
    for (const auto &field : layout.fields) {
      auto type = encodeStaticTerm(field.layout->type);
      if (!type)
        return type.takeError();
      fields.push_back(json::Array{field.name, std::move(*type)});
    }
    records.push_back(json::Array{std::move(*term),
                                  !declaration->resource ? "ordinary"
                                  : *declaration->resource == Resource::Linear
                                      ? "linear"
                                      : "affine",
                                  declaration->sealed, std::move(fields)});
    return Error::success();
  };
  for (const auto &declaration : entry.declarations()) {
    if (declaration.kind != Declaration::Kind::Protocol || !declaration.body ||
        !declaration.parameters.empty())
      continue;
    json::Array sides;
    for (bool output : {false, true}) {
      json::Array ports;
      unsigned offset = 0;
      for (const auto &port :
           output ? declaration.outputs : declaration.inputs) {
        auto layout = layouts.get(port.type);
        if (!layout)
          return layout.takeError();
        if (auto e = retain(**layout, 0))
          return std::move(e);
        auto term = encodeStaticTerm(port.type);
        if (!term)
          return term.takeError();
        json::Array roles;
        for (auto role : port.roles)
          roles.push_back(nativeRoleName(role));
        ports.push_back(json::Array{port.name, std::move(*term),
                                    std::move(roles), offset,
                                    (*layout)->leaves.size()});
        offset += (*layout)->leaves.size();
      }
      sides.push_back(std::move(ports));
    }
    protocols.push_back(json::Array{declaration.symbol, std::move(sides[0]),
                                    std::move(sides[1])});
  }
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  if (!linear) {
    records.clear();
    protocols.clear();
  }
  out << json::Value(json::Array{std::move(records), std::move(protocols)});
  if (out.overflow())
    return detail::failure("source.limit", "component declaration bytes");
  return bytes;
}

bool detail::Checker::sourceClaimDomains(const Declaration &scope, E &value) {
  if (!types.charge(1, value.span))
    return false;
  // Registry applications, including cardinality@VERSION, keep their own
  // argument contracts. Only this exact unversioned mathematical builtin
  // resolves a source type; an explicitly nested builtin is still checked.
  if (value.kind == E::Kind::Application && value.text == "cardinality" &&
      !value.version) {
    if (value.arguments.size() != 1 ||
        value.labels != std::vector<std::string>{""} ||
        value.arguments[0].kind != E::Kind::Reference)
      return types.fail(
          "source.claim.domain",
          "cardinality requires one positional domain type reference",
          value.span);
    const auto &reference = value.arguments[0];
    detail::SyntaxType syntax;
    syntax.span = reference.span;
    for (char ch : reference.text)
      syntax.name += ch == '.' ? "::" : std::string(1, ch);
    auto domain = type(scope, syntax);
    if (!domain) {
      if (types.diagnostic && types.diagnostic->code != "source.limit")
        types.diagnostic->code = "source.claim.domain";
      return false;
    }
    if (domainSort(*domain).empty())
      return types.fail("source.claim.domain",
                        "cardinality argument is not a nominal domain",
                        reference.span);
    value.cardinalityDomain = std::move(*domain);
  }
  for (auto &child : value.arguments)
    if (!sourceClaimDomains(scope, child))
      return false;
  return true;
}

bool detail::Checker::sourceClaims() {
  for (auto &owner : output.declarations) {
    // External blocks and Entry-inline blocks share the enclosing module's
    // claim namespace. They are not executable declarations or imports.
    std::map<std::string, SourceClaimBlock *> blocks;
    auto add = [&](Declaration &declaration) {
      for (unsigned index = 0; index < declaration.sourceClaims.size();
           ++index) {
        auto &block = declaration.sourceClaims[index];
        const auto &syntax =
            sources[declaration.id.index]->sourceClaims[index].subject;
        if (!blocks.emplace(block.name, &block).second)
          return types.fail("source.claim.duplicate-label",
                            "duplicate claim block", block.span);
        auto subject = declaration.kind == Declaration::Kind::Entry
                           ? std::optional(declaration.id)
                           : resolve(owner, block.entry, block.span, false);
        if (types.diagnostic)
          return false;
        if (!subject)
          return types.fail("source.claim.subject", "unknown claim subject",
                            block.span);
        const auto &entry = output.declarations[subject->index];
        if (entry.kind == Declaration::Kind::Protocol) {
          auto arguments = this->arguments(owner, entry, syntax.arguments,
                                           syntax.span, syntax.labels);
          if (!arguments)
            return false;
          for (const auto &argument : *arguments)
            if (types.symbolic(argument))
              return types.fail(
                  "source.claim.subject",
                  "claim subject requires closed static arguments",
                  syntax.span);
          block.arguments = std::move(*arguments);
        } else if (entry.kind != Declaration::Kind::Entry || !entry.proof() ||
                   !syntax.arguments.empty()) {
          return types.fail(
              "source.claim.subject",
              "claim subject must name a closed protocol or proof", block.span);
        }
        block.subject = subject;
        const auto &protocol = entry.kind == Declaration::Kind::Protocol
                                   ? entry
                                   : output.declarations[entry.target->index];
        Sites sites;
        if (auto e = exportedSites(output.declarations, protocol.body.get(), "",
                                   sites, work)) {
          types.diagnostic = detail::diagnose(std::move(e));
          return false;
        }
        for (auto &claim : block.claims) {
          const auto &property = claim.property;
          if (!versionedApplication(property))
            return types.fail("source.claim.identifier",
                              "property requires an explicit registry version",
                              claim.span);
          unsigned positional = 0, quantities = 0;
          for (const auto &label : property.labels) {
            if (label.empty())
              ++positional;
            else if (label == "error" || label == "charge" ||
                     label == "guarantee")
              ++quantities;
            else if (label != "model" && label != "accept" &&
                     label != "stage" && label != "capabilities" &&
                     label != "parameters")
              return types.fail("source.claim.field",
                                "unknown claim envelope field", claim.span);
          }
          if (positional != 1 || quantities != 1 ||
              !argument(property, "model") || !argument(property, "accept") ||
              !argument(property, "stage"))
            return types.fail(
                "source.claim.field",
                "claim requires one target, model, accept, stage and quantity",
                claim.span);
          const auto &target = property.arguments[0];
          auto found = protocol.specifications.end();
          if (importedLanguageTarget(target)) {
            if (target.version || target.arguments.size() != 1 ||
                target.labels != std::vector<std::string>{""})
              return types.fail(
                  "source.claim.target",
                  "imported_language requires exactly one positional registry "
                  "application and no wrapper version",
                  target.span);
            if (!versionedApplication(target.arguments[0]))
              return types.fail(
                  "source.claim.identifier",
                  "imported language requires an explicit registry version",
                  target.arguments[0].span);
            if (!entry.proof() || !protocol.specifications.empty())
              return types.fail(
                  "source.claim.target",
                  "imported language requires a proof Entry with no retained "
                  "clauses in its closed unit",
                  target.span);
          } else {
            if (target.kind != E::Kind::Reference ||
                !StringRef(target.text).starts_with("target."))
              return types.fail("source.claim.target",
                                "claim requires target.NAME or "
                                "imported_language(application)",
                                target.span);
            auto name = StringRef(target.text).drop_front(7);
            found =
                llvm::find_if(protocol.specifications, [&](const auto &clause) {
                  return clause.kind == SpecificationClause::Kind::Target &&
                         clause.name == name;
                });
            if (found == protocol.specifications.end() ||
                (entry.proof() && entry.proof()->target &&
                 *entry.proof()->target !=
                     unsigned(found - protocol.specifications.begin())))
              return types.fail(
                  "source.claim.target",
                  "target is absent or differs from Entry's retained target",
                  target.span);
          }
          const auto &model = *argument(property, "model");
          if (!versionedApplication(model))
            return types.fail("source.claim.identifier",
                              "model requires an explicit registry version",
                              model.span);
          const auto &stage = *argument(property, "stage");
          if (stage.kind != E::Kind::Reference ||
              (stage.text != "interactive" && stage.text != "compiled_ideal" &&
               stage.text != "executable_bytes") ||
              (!entry.proof() && stage.text != "interactive"))
            return types.fail("source.claim.stage", "invalid stage for Entry",
                              stage.span);
          const auto &accept = *argument(property, "accept");
          if (accept.kind != E::Kind::Reference ||
              !StringRef(accept.text).starts_with("out."))
            return types.fail("source.claim.accept",
                              "accept must select an Entry result",
                              accept.span);
          SmallVector<StringRef> parts;
          StringRef(accept.text).drop_front(4).split(parts, '.');
          SyntaxSelector authored;
          authored.output = true;
          authored.port = parts.front().str();
          authored.span = accept.span;
          if (entry.proof())
            authored.role = protocol.roles[entry.proof()->verifier];
          for (auto part : ArrayRef(parts).drop_front())
            authored.path.push_back(part.str());
          auto selected = this->selector(protocol, authored);
          if (!selected) {
            if (types.diagnostic)
              types.diagnostic->code = "source.claim.accept";
            return false;
          }
          auto type = types.selectedType(protocol, *selected);
          if (!type || type->kind != Type::Kind::Boolean ||
              (!importedLanguageTarget(target) &&
               (!found->decision ||
                !sameSelector(*found->decision, *selected))) ||
              (entry.proof() &&
               !sameSelector(entry.proof()->acceptance, *selected)))
            return types.fail(
                "source.claim.accept",
                "accept must be the Boolean retained target or Entry decision",
                accept.span);
          if (auto *guarantee = argument(property, "guarantee"))
            if (!versionedApplication(*guarantee))
              return types.fail(
                  "source.claim.identifier",
                  "guarantee requires an explicit registry version",
                  guarantee->span);
          if (auto *capabilities = argument(property, "capabilities")) {
            if (capabilities->kind != E::Kind::List)
              return types.fail("source.claim.field",
                                "capabilities requires a list",
                                capabilities->span);
            std::set<std::pair<std::string, uint32_t>> unique;
            for (const auto &capability : capabilities->arguments)
              if (!versionedApplication(capability) ||
                  !unique
                       .emplace(capability.text, capability.version.value_or(0))
                       .second)
                return types.fail(
                    "source.claim.identifier",
                    "capabilities require distinct versioned applications",
                    capability.span);
          }
          if (auto *charge = argument(property, "charge")) {
            auto valid = [](const E &site) {
              return site.kind == E::Kind::Application &&
                     site.text == "per_site" && !site.version &&
                     site.arguments.size() == 2 &&
                     site.labels == std::vector<std::string>{"", ""} &&
                     site.arguments[0].kind == E::Kind::Reference &&
                     StringRef(site.arguments[0].text).starts_with("sites.");
            };
            std::set<std::string> unique;
            ArrayRef<E> charges = charge->kind == E::Kind::List
                                      ? ArrayRef(charge->arguments)
                                      : ArrayRef(*charge);
            for (const auto &site : charges)
              if (!valid(site) || !unique.insert(site.arguments[0].text).second)
                return types.fail("source.claim.field",
                                  "charge requires distinct per_site(site, "
                                  "expression) bindings",
                                  site.span);
          }
          if (auto e = checkSites(property, sites, work)) {
            types.diagnostic = detail::diagnose(std::move(e));
            return false;
          }
          if (!sourceClaimDomains(declaration, claim.property))
            return false;
        }
      }
      return true;
    };
    if (owner.kind != Declaration::Kind::Module)
      continue;
    if (!add(owner))
      return false;
    for (auto id : owner.members)
      if (output.declarations[id.index].kind == Declaration::Kind::Entry &&
          !add(output.declarations[id.index]))
        return false;
    std::set<std::pair<std::string, std::string>> plans;
    for (auto &plan : owner.sourceVerifications) {
      auto block = blocks.find(plan.block);
      if (block == blocks.end() ||
          !llvm::any_of(block->second->claims, [&](const auto &claim) {
            return claim.label == plan.label;
          }))
        return types.fail("source.claim.verify",
                          "verify names an absent local claim", plan.span);
      if (!plans.emplace(plan.block, plan.label).second)
        return types.fail("source.claim.verify", "duplicate verify plan",
                          plan.span);
      if (!versionedApplication(plan.method))
        return types.fail(
            "source.claim.identifier",
            "verify requires a versioned registry method application",
            plan.span);
      const auto &entry = output.declarations[block->second->subject->index];
      Sites sites;
      if (auto e =
              exportedSites(output.declarations,
                            (entry.kind == Declaration::Kind::Protocol
                                 ? entry
                                 : output.declarations[entry.target->index])
                                .body.get(),
                            "", sites, work)) {
        types.diagnostic = detail::diagnose(std::move(e));
        return false;
      }
      if (auto e = checkSites(plan.method, sites, work)) {
        types.diagnostic = detail::diagnose(std::move(e));
        return false;
      }
      if (!sourceClaimDomains(owner, plan.method))
        return false;
    }
  }
  return true;
}

Error detail::checkClosedSourceClaims(const ClosedEntry &entry, Work &work) {
  std::optional<Span> imported;
  for (const auto &owner : entry.project().declarations()) {
    if (auto e = work.charge(1, owner.span))
      return e;
    for (const auto &block : owner.sourceClaims) {
      if (!matchesSubject(block, entry))
        continue;
      for (const auto &claim : block.claims) {
        if (auto e = work.charge(1, claim.span))
          return e;
        if (importedLanguageTarget(claim.property.arguments[0]))
          imported = claim.property.arguments[0].span;
      }
    }
  }
  if (!imported)
    return Error::success();
  // Specialization retains templates as well as closed instances. Only the
  // latter are emitted into the original. Inspect every emitted protocol,
  // including unlabelled calls and loop bodies, exactly as Endpoint's
  // original.contracts.all (fun contract => contract.clauses.isEmpty).
  for (const auto &decl : entry.declarations()) {
    if (auto e = work.charge(1, decl.span))
      return e;
    if (decl.body && decl.parameters.empty() &&
        decl.kind == Declaration::Kind::Protocol &&
        !decl.specifications.empty())
      return detail::failure(
          "source.claim.target",
          "imported language requires every closed protocol clause list empty",
          *imported, {decl.specifications.front().span});
  }
  return Error::success();
}

Expected<std::string> inspectSourceClaimInventory(const CheckedProject &project,
                                                  const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return detail::failure("source.limit",
                           "checked claims exceed inspection limits");
  detail::Work work{limits};
  json::Array inventory;
  for (const auto &owner : project.declarations()) {
    if (auto e = work.charge(1, owner.span))
      return std::move(e);
    for (unsigned b = 0; b < owner.sourceClaims.size(); ++b) {
      const auto &block = owner.sourceClaims[b];
      const auto &subject = project.declarations()[block.subject->index];
      const auto &module = project.declarations()[owner.module.index];
      for (unsigned c = 0; c < block.claims.size(); ++c) {
        const auto &claim = block.claims[c];
        if (auto e = work.charge(1, claim.span))
          return std::move(e);
        json::Array arguments;
        for (const auto &argument : block.arguments) {
          auto term = encodeStaticTerm(argument);
          if (!term)
            return term.takeError();
          arguments.push_back(std::move(*term));
        }
        inventory.push_back(json::Object{
            {"node", json::Object{{"kind", "source-claim"},
                                  {"owner", owner.qualifiedName},
                                  {"block", b},
                                  {"claim", c}}},
            {"declaration", module.qualifiedName + "::" + block.name},
            {"label", claim.label},
            {"subject",
             json::Object{{"kind", subject.kind == Declaration::Kind::Protocol
                                       ? "protocol"
                                       : "proof"},
                          {"declaration", subject.qualifiedName},
                          {"arguments", std::move(arguments)}}},
            {"source", sourceNode(project, claim.span)}});
      }
    }
  }
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  out << json::Value(std::move(inventory));
  if (out.overflow())
    return detail::failure("source.limit",
                           "source claim inventory byte limit exceeded");
  return bytes;
}

Expected<std::string> inspectSourceClaims(const ClosedEntry &entry,
                                          const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  if (!entry.protocolOrNull())
    return detail::failure(
        "source.claim.subject",
        "Host Entry claims require a separate correspondence; "
        "select a closed protocol or proof subject");
  const auto &project = entry.project();
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return detail::failure("source.limit",
                           "checked claims exceed inspection limits");
  detail::Work work{limits};
  if (auto e = detail::checkClosedSourceClaims(entry, work))
    return std::move(e);
  detail::Semantics types(entry.declarations(), entry.assets(), work);
  const auto &protocol = entry.protocol();
  const auto bindings = types.substitution(
      project.declarations()[protocol.origin->index], protocol.staticArguments);
  json::Array claims;
  Sites sites;
  if (auto e = exportedSites(entry.declarations(), entry.protocol().body.get(),
                             "", sites, work))
    return std::move(e);
  for (const auto &owner : project.declarations()) {
    for (unsigned b = 0; b < owner.sourceClaims.size(); ++b) {
      const auto &block = owner.sourceClaims[b];
      if (!matchesSubject(block, entry))
        continue;
      const auto &module = project.declarations()[owner.module.index];
      for (unsigned c = 0; c < block.claims.size(); ++c) {
        const auto &claim = block.claims[c];
        auto property = claim.property;
        if (auto e = normalizeDomains(property, types, bindings))
          return std::move(e);
        if (auto e = work.charge(1, claim.span))
          return std::move(e);
        const auto &protocol = entry.protocol();
        const auto &target = property.arguments[0];
        json::Object targetReference;
        const SpecificationSelector *acceptance;
        if (importedLanguageTarget(target)) {
          targetReference =
              json::Object{{"protocol", protocol.symbol},
                           {"language", expression(target.arguments[0])}};
          acceptance = &entry.entry().proof()->acceptance;
        } else {
          auto name = StringRef(target.text).drop_front(7);
          auto found =
              llvm::find_if(protocol.specifications, [&](const auto &clause) {
                return clause.kind == SpecificationClause::Kind::Target &&
                       clause.name == name;
              });
          if (found == protocol.specifications.end())
            return detail::failure("source.claim.target",
                                   "closed target is absent", claim.span);
          targetReference = json::Object{
              {"protocol", protocol.symbol},
              {"clause", unsigned(found - protocol.specifications.begin())},
              {"name", found->name}};
          acceptance = &*found->decision;
        }
        if (auto e = checkSites(property, sites, work))
          return std::move(e);
        json::Object quantity;
        if (auto *error = argument(property, "error"))
          quantity = json::Object{{"kind", "scalar"},
                                  {"expression", expression(*error)}};
        else if (auto *guarantee = argument(property, "guarantee"))
          quantity = json::Object{{"kind", "guarantee"},
                                  {"form", expression(*guarantee)}};
        else {
          const auto &charge = *argument(property, "charge");
          ArrayRef<E> charges = charge.kind == E::Kind::List
                                    ? ArrayRef(charge.arguments)
                                    : ArrayRef(charge);
          json::Array bindings;
          for (const auto &site : charges) {
            const auto &path = site.arguments[0].text;
            bindings.push_back(
                json::Object{{"site", path.substr(6)},
                             {"expression", expression(site.arguments[1])}});
          }
          quantity = json::Object{{"kind", "charged"},
                                  {"charges", std::move(bindings)}};
        }
        json::Value capabilities = json::Array{};
        if (auto *value = argument(property, "capabilities"))
          for (const auto &capability : value->arguments)
            capabilities.getAsArray()->push_back(expression(capability));
        // Occurrence proposals are attachments. Native paths follow labelled
        // calls and the final source site; aggregate messages may have several
        // native leaves, which the admitted construction context must resolve.
        json::Array siteBindings;
        std::set<std::string> referencedSites;
        std::function<void(const E &)> collectSites = [&](const E &value) {
          if (value.kind == E::Kind::Reference &&
              StringRef(value.text).starts_with("sites."))
            referencedSites.insert(value.text.substr(6));
          for (const auto &child : value.arguments)
            collectSites(child);
        };
        collectSites(property);
        for (const auto &path : referencedSites) {
          SmallVector<StringRef> parts;
          StringRef(path).split(parts, '.');
          json::Array nativePath;
          for (auto part : parts)
            nativePath.push_back(nativeSiteName(part, 0));
          siteBindings.push_back(json::Object{
              {"site", path},
              {"source", sourceNode(project, sites.at(path)->span)},
              {"native_path", std::move(nativePath)}});
        }
        json::Value method = nullptr;
        for (const auto &plan : module.sourceVerifications)
          if (plan.block == block.name && plan.label == claim.label) {
            auto normalized = plan.method;
            if (auto e = normalizeDomains(normalized, types, bindings))
              return std::move(e);
            method = expression(normalized);
          }
        json::Object request{
            {"subject",
             json::Object{
                 {"entry", entry.entry().qualifiedName},
                 {"stage",
                  argument(property, "stage")->text == "compiled_ideal"
                      ? "compiled-ideal"
                  : argument(property, "stage")->text == "executable_bytes"
                      ? "executable-bytes"
                      : "interactive"}}},
            {"property",
             json::Object{{"name", property.text},
                          {"version", *property.version},
                          {"parameters",
                           argument(property, "parameters")
                               ? expression(*argument(property, "parameters"))
                               : json::Value(nullptr)}}},
            {"model", expression(*argument(property, "model"))},
            {"target", std::move(targetReference)},
            {"accept", selector(*acceptance)},
            {"quantity", std::move(quantity)},
            {"capabilities", std::move(capabilities)}};
        claims.push_back(json::Object{
            {"attachment",
             json::Object{
                 {"module", project.sources()[claim.span.source.index].module},
                 {"declaration", module.qualifiedName + "::" + block.name},
                 {"label", claim.label},
                 {"node", json::Object{{"kind", "source-claim"},
                                       {"owner", owner.qualifiedName},
                                       {"block", b},
                                       {"claim", c}}},
                 {"source", sourceNode(project, claim.span)}}},
            {"request", std::move(request)},
            {"method", std::move(method)},
            {"site_bindings", std::move(siteBindings)}});
      }
    }
  }
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  out << json::Value(json::Object{{"format", "zkc.source-claims/0"},
                                  {"registry_resolution", "deferred-to-lean"},
                                  {"entry", entry.entry().qualifiedName},
                                  {"claims", std::move(claims)},
                                  {"proposals", json::Array{}},
                                  {"seams", json::Array{}}});
  if (out.overflow())
    return detail::failure("source.limit",
                           "source claim export byte limit exceeded");
  return bytes;
}

Error checkSourceClaims(const ClosedEntry &entry, StringRef bytes,
                        const Limits &limits) {
  auto expected = inspectSourceClaims(entry, limits);
  if (!expected)
    return expected.takeError();
  auto actual = zkc::parseNaturalJson(bytes, limits.interfaceBytes,
                                      limits.expressionDepth * 4 + 16,
                                      "source.claim.export", "source.limit");
  if (!actual)
    return actual.takeError();
  auto canonical = json::parse(*expected);
  if (!canonical)
    return canonical.takeError();
  if (!zkc::equalNaturalJson(*actual, *canonical))
    return detail::failure("source.claim.export",
                           "claim export differs from the checked source");
  return Error::success();
}
} // namespace zkc::language
