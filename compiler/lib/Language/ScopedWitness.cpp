#include "ScopedWitness.h"
#include "Arguments.h"
#include "BindingWitness.h"
#include "CallResolution.h"
#include "ConstructionWitness.h"
#include "Effects.h"
#include "FiniteContracts.h"
#include "FiniteDomains.h"
#include "FreePlaces.h"
#include "HelperResults.h"
#include "ManagedServices.h"
#include "RecordIntrinsics.h"
#include "Semantics.h"
#include "SignatureWitness.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool same(Span a, Span b) {
  return a.source.index == b.source.index && a.begin == b.begin &&
         a.end == b.end;
}
uint64_t indexedWork(uint64_t count) {
  uint64_t levels = 1;
  for (auto size = count; size > 1; size >>= 1)
    levels += 2;
  return count * levels;
}
Body::Mode sourceMode(Declaration::Kind kind) {
  return kind == Declaration::Kind::Oracle ? Body::Mode::Oracle
         : kind == Declaration::Kind::Math ||
                 kind == Declaration::Kind::Relation
             ? Body::Mode::Math
         : kind == Declaration::Kind::Local ||
                 kind == Declaration::Kind::EntryFunction
             ? Body::Mode::Local
             : Body::Mode::Protocol;
}
/// Resolved lexical scopes are immutable source identities. Transparent blocks
/// share a checked Body with their parent; selected arms and lambdas do not.
/// Build this product for every authored body mode, not just managed services.
class LexicalRegions {
  Semantics &types;
  const SyntaxDeclaration &syntax;
  struct Scope {
    unsigned region = 0, eagerRegion = 0, begin = 0, end = 0;
  };
  std::vector<Scope> scopes;

public:
  LexicalRegions(Semantics &types, const SyntaxDeclaration &syntax)
      : types(types), syntax(syntax) {}
  bool prepare() {
    if (!types.charge(syntax.bodies.size() + syntax.expressions.size() + 1,
                      syntax.span))
      return false;
    scopes.resize(syntax.bodies.size());
    std::vector<unsigned> boundary(scopes.size());
    std::vector<std::vector<unsigned>> children(scopes.size());
    if (scopes.empty())
      return true;
    // Generated oracle predicates retain unused query syntax as well. Only
    // bodies reachable from this declaration's actual root have authority.
    std::vector<bool> bodies(scopes.size()),
        expressions(syntax.expressions.size());
    std::vector<std::pair<bool, uint32_t>> pending{{true, 0}};
    unsigned expectedBodies = 0;
    while (!pending.empty()) {
      auto [isBody, id] = pending.back();
      pending.pop_back();
      if (!types.charge(1, syntax.span))
        return false;
      if (isBody) {
        if (id >= bodies.size())
          return refuse(syntax.span);
        if (bodies[id])
          continue;
        bodies[id] = true;
        ++expectedBodies;
        const auto &body = syntax.bodies[id];
        for (const auto &statement : body.statements)
          pending.emplace_back(false, statement.expression);
        for (const auto &result : body.results)
          pending.emplace_back(false, result.second);
      } else {
        if (id >= expressions.size())
          return refuse(syntax.span);
        if (expressions[id])
          continue;
        expressions[id] = true;
        const auto &expr = syntax.expressions[id];
        for (auto child : expr.children)
          pending.emplace_back(false, child);
        for (auto region : expr.regions) {
          if (region >= scopes.size())
            return refuse(expr.span);
          if (expr.kind != Expression::Kind::Block)
            boundary[region] = expr.kind == Expression::Kind::And ||
                                       expr.kind == Expression::Kind::Or
                                   ? 2
                                   : 1;
          pending.emplace_back(true, region);
        }
      }
    }
    for (unsigned i = 0; i < scopes.size(); ++i) {
      if (!bodies[i])
        continue;
      auto parent = syntax.bodies[i].parent;
      if (i == 0 ? bool(parent)
                 : (!parent || *parent >= scopes.size() || !bodies[*parent]))
        return refuse(syntax.bodies[i].span);
      if (parent)
        children[*parent].push_back(i);
    }
    unsigned clock = 0, visited = 0;
    std::function<bool(unsigned, unsigned, unsigned, unsigned)> visit =
        [&](unsigned id, unsigned region, unsigned eagerRegion,
            unsigned depth) {
          if (depth > types.work.limits.expressionDepth)
            return types.fail("source.limit", "lexical region depth exceeded",
                              syntax.bodies[id].span);
          if (!types.charge(1, syntax.bodies[id].span))
            return false;
          ++visited;
          scopes[id] = {boundary[id] ? id : region,
                        boundary[id] == 1 ? id : eagerRegion, clock++, 0};
          for (auto child : children[id])
            if (!visit(child, scopes[id].region, scopes[id].eagerRegion,
                       depth + 1))
              return false;
          scopes[id].end = clock;
          return true;
        };
    if (!visit(0, 0, 0, 1))
      return false;
    return visited == expectedBodies || refuse(syntax.span);
  }
  bool refuse(Span span) {
    return types.fail("source.binding-witness",
                      "candidate region differs from authored lexical region",
                      span);
  }
  bool contains(uint32_t expression, unsigned region, Body::Mode mode,
                Span span) {
    if (!types.charge(1, span))
      return false;
    if (expression >= syntax.expressions.size())
      return refuse(span);
    auto scope = syntax.expressions[expression].scope;
    return (scope && *scope < scopes.size() &&
            scopes[*scope].begin < scopes[*scope].end &&
            (mode == Body::Mode::Local
                 ? scopes[*scope].region
                 : scopes[*scope].eagerRegion) == region) ||
           refuse(span);
  }
  bool visible(unsigned declarationScope, unsigned useScope) const {
    return declarationScope < scopes.size() && useScope < scopes.size() &&
           scopes[declarationScope].begin < scopes[declarationScope].end &&
           scopes[declarationScope].begin <= scopes[useScope].begin &&
           scopes[useScope].begin < scopes[declarationScope].end;
  }
  std::optional<std::vector<uint32_t>> regions(const Body &body,
                                               const Operation &op) {
    if (!op.expression || *op.expression >= syntax.expressions.size()) {
      refuse(op.span);
      return {};
    }
    const auto &expr = syntax.expressions[*op.expression];
    const auto *control = std::get_if<Control>(&op.action);
    bool repeat = std::holds_alternative<ProtocolRepeat>(op.action);
    using K = Expression::Kind;
    bool match = expr.kind == K::Match;
    bool loop = expr.kind == K::For;
    if (!same(expr.span, op.span) ||
        (repeat ? !loop
                : !control || control->kind != (loop    ? Control::Kind::For
                                                : match ? Control::Kind::Match
                                                        : Control::Kind::If)) ||
        (!loop && !match && expr.kind != K::If && expr.kind != K::And &&
         expr.kind != K::Or) ||
        !types.charge(expr.regions.size() + 1, op.span)) {
      if (!types.diagnostic)
        refuse(op.span);
      return {};
    }
    if (!match)
      return expr.regions;
    // Checked native control orders nominal alternatives by their declaration,
    // while source arms may be written in any order. Derive the permutation
    // from the subject's checked type and the immutable authored labels.
    auto subject = expr.children.size() == 1
                       ? body.expressionValues.find(expr.children.front())
                       : body.expressionValues.end();
    if (control->operands.empty() ||
        control->operands.front().index >= body.values.size() ||
        subject == body.expressionValues.end() ||
        subject->second.index != control->operands.front().index) {
      refuse(op.span);
      return {};
    }
    auto alternatives = types.alternatives(
        body.values[control->operands.front().index].type, op.span);
    if (!alternatives)
      return {};
    if (alternatives->size() != expr.regions.size() ||
        expr.labels.size() != expr.regions.size() ||
        control->alternatives.size() != alternatives->size()) {
      refuse(op.span);
      return {};
    }
    std::map<StringRef, uint32_t> written;
    std::vector<uint32_t> result;
    if (!types.charge(2 * indexedWork(expr.labels.size()), op.span))
      return {};
    for (unsigned i = 0; i < expr.labels.size(); ++i) {
      StringRef label = expr.labels[i];
      if (label.contains("::"))
        label = label.rsplit("::").second;
      if (!written.emplace(label, expr.regions[i]).second) {
        refuse(op.span);
        return {};
      }
    }
    for (unsigned i = 0; i < alternatives->size(); ++i) {
      auto at = written.find((*alternatives)[i].name);
      if (at == written.end() ||
          control->alternatives[i] != (*alternatives)[i].name) {
        refuse(op.span);
        return {};
      }
      result.push_back(at->second);
    }
    return result;
  }
};
/// A retained managed binding resolves once to an authored declaration input.
/// Ordinary aliases never enter this graph, nor does candidate capture data.
class ServiceRoots {
  Semantics &types;
  const SyntaxDeclaration &syntax;
  const LexicalRegions &lexical;
  struct Entry {
    std::optional<BindingId> source;
    std::optional<unsigned> root;
    unsigned depth = 0, scope = 0;
    uint32_t visibleAfter = 0;
    bool active = false;
  };
  std::vector<Entry> entries;
  bool resolve(BindingId binding, unsigned depth) {
    if (!types.charge(1, syntax.span))
      return false;
    if (binding.index >= entries.size())
      return types.fail("source.binding-witness", "unknown managed alias",
                        syntax.span);
    auto &entry = entries[binding.index];
    if (entry.root)
      return true;
    if (entry.active || !entry.source)
      return types.fail("source.binding-witness", "invalid managed alias graph",
                        syntax.bindings[binding.index].span);
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "managed alias depth exceeded",
                        syntax.bindings[binding.index].span);
    entry.active = true;
    if (!resolve(*entry.source, depth + 1))
      return false;
    const auto &parent = entries[entry.source->index];
    entry.depth = parent.depth + 1;
    if (entry.depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "managed alias depth exceeded",
                        syntax.bindings[binding.index].span);
    entry.root = parent.root;
    entry.active = false;
    return true;
  }

public:
  ServiceRoots(Semantics &types, const SyntaxDeclaration &syntax,
               const LexicalRegions &lexical)
      : types(types), syntax(syntax), lexical(lexical) {}
  bool prepare() {
    if (!types.charge(syntax.bindings.size() + syntax.serviceBindings.size() +
                          1,
                      syntax.span))
      return false;
    entries.resize(syntax.bindings.size());
    for (unsigned i = 0; i < syntax.serviceBindings.size(); ++i) {
      auto binding = syntax.serviceBindings[i];
      if (binding.index >= entries.size() ||
          !syntax.bindings[binding.index].service ||
          entries[binding.index].root)
        return types.fail("source.binding-witness", "invalid managed input",
                          syntax.span);
      entries[binding.index].root = i;
    }
    for (unsigned scope = 0; scope < syntax.bodies.size(); ++scope)
      for (const auto &statement : syntax.bodies[scope].statements) {
        if (!types.charge(1, statement.span))
          return false;
        if (statement.kind != Statement::Kind::Let ||
            !statement.pattern.binding)
          continue;
        auto binding = *statement.pattern.binding;
        if (binding.index >= entries.size())
          return types.fail("source.binding-witness", "unknown lexical binding",
                            statement.span);
        if (!syntax.bindings[binding.index].service)
          continue;
        const auto &rhs = syntax.expressions.at(statement.expression);
        if (rhs.kind != Expression::Kind::Name || !rhs.binding ||
            rhs.binding->index >= entries.size() ||
            !syntax.bindings[rhs.binding->index].service)
          return types.fail("source.binding-witness", "invalid managed alias",
                            statement.span);
        entries[binding.index].source = rhs.binding;
        entries[binding.index].scope = scope;
        entries[binding.index].visibleAfter = statement.span.end;
      }
    for (unsigned i = 0; i < entries.size(); ++i)
      if (syntax.bindings[i].service && !resolve(BindingId{i}, 1))
        return false;
    return true;
  }
  std::optional<unsigned> input(BindingId binding, Span span) {
    if (!types.charge(1, span) || binding.index >= entries.size())
      return {};
    return entries[binding.index].root;
  }
  std::optional<std::vector<unsigned>> captures(const Operation &op) {
    auto refuse = [&]() -> std::optional<std::vector<unsigned>> {
      types.fail("source.binding-witness",
                 "managed region captures differ from source", op.span);
      return {};
    };
    if (!op.expression || *op.expression >= syntax.expressions.size())
      return refuse();
    const auto &expr = syntax.expressions[*op.expression];
    if (!expr.scope)
      return refuse();
    FreePlaceEnvironment environment;
    // Free-place traversal asks only about names it actually visits. Scope
    // ancestry and definition order are constant-time retained-source queries.
    environment.service = [&](BindingId binding) {
      if (binding.index >= entries.size())
        return false;
      const auto &entry = entries[binding.index];
      return entry.root && entry.visibleAfter <= expr.span.begin &&
             lexical.visible(entry.scope, *expr.scope);
    };
    auto free = queryFreePlaces(types, syntax, expr, environment);
    if (!free || types.diagnostic)
      return {};
    std::vector<unsigned> roots;
    std::set<unsigned> seen;
    if (!types.charge(indexedWork(free->services.size()), op.span))
      return {};
    for (auto binding : free->services) {
      auto root = input(binding, op.span);
      if (!root)
        return refuse();
      if (seen.insert(*root).second)
        roots.push_back(*root);
    }
    return roots;
  }
};
class CaptureCheck {
  Semantics &types;
  const ScopedSource &source;
  const Declaration &owner;
  const SyntaxDeclaration &syntax;
  struct Place {
    BindingId binding;
    std::vector<unsigned> path;
    Span span;
  };
  std::vector<Place> reads;
  const std::vector<const Operation *> &producers;
  std::set<BindingId> scoped, domains;
  bool refuse(Span span) {
    return types.fail("source.scoped-witness",
                      "scoped extraction differs from authored lexical places",
                      span);
  }
  std::optional<Place> place(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (depth > types.work.limits.expressionDepth ||
        !types.charge(1, expr.span))
      return {};
    if (expr.kind == Expression::Kind::Name) {
      if (expr.binding && source.environment.count(*expr.binding))
        return Place{*expr.binding, {}, expr.span};
      return {};
    }
    if (expr.kind != Expression::Kind::Projection &&
        expr.kind != Expression::Kind::Subscript)
      return {};
    auto result = place(expr.children.front(), depth + 1);
    if (!result)
      return {};
    auto type =
        types.projectedType(owner, source.environment.at(result->binding).type,
                            result->path, expr.span);
    if (!type)
      return {};
    if (expr.kind == Expression::Kind::Subscript &&
        type->kind != Type::Kind::Array)
      return {};
    auto label = expr.kind == Expression::Kind::Subscript
                     ? staticSubscriptIndex(syntax, expr)
                     : std::optional<StringRef>(expr.text);
    if (!label) {
      refuse(expr.span);
      return {};
    }
    auto index = types.fieldIndex(owner, *type, *label, expr.span);
    if (!index)
      return {};
    result->path.push_back(*index);
    result->span = expr.span;
    return result;
  }
  bool expression(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions.at(id);
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "scoped source witness depth",
                        expr.span);
    if (!types.charge(1, expr.span))
      return false;
    if (expr.binding && source.scoped.count(*expr.binding))
      scoped.insert(*expr.binding);
    if (expr.binding && source.domains.count(*expr.binding))
      domains.insert(*expr.binding);
    auto selected = place(id, depth);
    if (types.diagnostic)
      return false;
    if (selected) {
      reads.push_back(std::move(*selected));
      return true;
    }
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      if ((expr.kind == Expression::Kind::And ||
           expr.kind == Expression::Kind::Or) &&
          i == 1)
        continue;
      if (!expression(expr.children[i], depth + 1))
        return false;
    }
    for (auto id : expr.regions) {
      const auto &region = syntax.bodies.at(id);
      for (const auto &statement : region.statements) {
        if (statement.kind == Statement::Kind::Assign &&
            statement.pattern.binding &&
            source.environment.count(*statement.pattern.binding))
          return refuse(statement.span);
        if (!expression(statement.expression, depth + 1))
          return false;
      }
      for (const auto &result : region.results)
        if (!expression(result.second, depth + 1))
          return false;
    }
    return true;
  }

public:
  CaptureCheck(Semantics &types, const ScopedSource &source,
               const Declaration &owner,
               const std::vector<const Operation *> &producers)
      : types(types), source(source), owner(owner), syntax(*source.syntax),
        producers(producers) {}
  bool run(const Body &outer, const ScopedBinding &binding) {
    const auto &computation = *binding.computation;
    const auto &authored = syntax.expressions.at(source.expression);
    if (authored.kind != Expression::Kind::Lambda ||
        !same(binding.span, authored.span) ||
        computation.lexicalOwner.index != source.owner.index ||
        computation.expression != source.expression ||
        !(binding.signature == source.signature) ||
        !(computation.signature == source.signature) || binding.parameter ||
        !computation.body)
      return refuse(binding.span);
    if (!expression(source.expression, 1))
      return false;
    // A prefix trie keeps one capture for each minimal lexical place. Each
    // subtree remembers its earliest occurrence even if a later whole-place
    // read replaces that subtree.
    struct Node {
      std::optional<Place> selected;
      std::optional<Span> first;
      std::map<unsigned, Node> children;
    };
    std::map<BindingId, Node> roots;
    for (const auto &read : reads) {
      if (!types.charge(read.path.size() + 1, read.span))
        return false;
      auto *node = &roots[read.binding];
      bool covered = false;
      for (unsigned position = 0;; ++position) {
        if (!node->first || read.span.begin < node->first->begin)
          node->first = read.span;
        if (node->selected) {
          node->selected->span = *node->first;
          covered = true;
          break;
        }
        if (position == read.path.size())
          break;
        node = &node->children[read.path[position]];
      }
      if (!covered) {
        node->selected = read;
        node->selected->span = *node->first;
        node->children.clear();
      }
    }
    std::vector<Place> minimal;
    std::function<void(const Node &)> collect = [&](const Node &node) {
      if (node.selected)
        minimal.push_back(*node.selected);
      for (const auto &[index, child] : node.children)
        collect(child);
    };
    for (const auto &[binding, root] : roots)
      collect(root);
    uint64_t levels = 1;
    for (auto count = minimal.size(); count > 1; count >>= 1)
      ++levels;
    if (!types.charge(minimal.size() * levels, binding.span))
      return false;
    llvm::stable_sort(minimal, [](const Place &a, const Place &b) {
      return a.span.begin < b.span.begin;
    });
    auto prefix = [](ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
      return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
    };
    const auto &body = *computation.body;
    unsigned explicitInputs = source.signature.inputs.size();
    if (minimal.size() != computation.captures.size() ||
        minimal.size() != binding.captures.size() ||
        body.inputs != explicitInputs + minimal.size() ||
        body.values.size() < body.inputs ||
        body.mode != (source.signature.mode == ScopedSignature::Mode::Math
                          ? Body::Mode::Math
                          : Body::Mode::Local) ||
        !effectsWithin(types, body.effects,
                       EffectSummary{source.signature.allowance}, binding.span))
      return refuse(binding.span);
    for (unsigned i = 0; i < explicitInputs; ++i)
      if (body.values[i].type != source.signature.inputs[i])
        return refuse(binding.span);
    for (unsigned i = 0; i < minimal.size(); ++i) {
      const auto &expected = minimal[i];
      const auto &actual = computation.captures[i];
      const auto &environment = source.environment.at(expected.binding);
      auto type = types.projectedType(owner, environment.type, expected.path,
                                      expected.span);
      if (!type || actual.binding != expected.binding.index ||
          actual.path != expected.path || actual.type != *type ||
          !same(actual.firstUse, expected.span) ||
          body.values[explicitInputs + i].type != *type ||
          body.values[explicitInputs + i].components !=
              (body.mode == Body::Mode::Math
                   ? std::vector<unsigned>{explicitInputs + i}
                   : std::vector<unsigned>{}))
        return refuse(binding.span);
      ValueId root{};
      auto path = expected.path;
      if (environment.value)
        root = *environment.value;
      else {
        bool found = false;
        for (const auto &[piece, value] : environment.pieces)
          if (prefix(piece, path)) {
            root = value;
            path.erase(path.begin(), path.begin() + piece.size());
            found = true;
            break;
          }
        if (!found)
          return refuse(binding.span);
      }
      auto value = binding.captures[i];
      const auto *op =
          value.index < producers.size() ? producers[value.index] : nullptr;
      const auto *projection =
          op ? std::get_if<Projection>(&op->action) : nullptr;
      if (!types.charge(path.size() + 1, binding.span))
        return false;
      if (!projection || op->results.size() != 1 ||
          projection->input.index != root.index || projection->path != path ||
          !same(op->span, expected.span) ||
          value.index >= outer.values.size() ||
          root.index >= outer.values.size() ||
          outer.values[value.index].type != *type ||
          outer.values[value.index].components !=
              outer.values[root.index].components)
        return refuse(binding.span);
    }
    if (scoped.size() != computation.scopedCaptures.size() ||
        scoped.size() != binding.scopedCaptures.size())
      return refuse(binding.span);
    if (domains.size() != computation.domainCaptures.size() ||
        domains.size() != binding.domainCaptures.size())
      return refuse(binding.span);
    unsigned domainIndex = 0;
    for (auto name : domains) {
      auto outerIndex = source.domains.at(name);
      if (computation.domainCaptures[domainIndex] != name.index ||
          binding.domainCaptures[domainIndex] != outerIndex ||
          outerIndex >= outer.domainBindings.size() ||
          domainIndex >= body.domainBindings.size())
        return refuse(binding.span);
      const auto &parameter = body.domainBindings[domainIndex];
      if (parameter.kind != DomainBinding::Kind::Parameter ||
          parameter.parameter != domainIndex ||
          parameter.item != outer.domainBindings[outerIndex].item)
        return refuse(binding.span);
      ++domainIndex;
    }
    unsigned i = 0;
    for (auto name : scoped) {
      if (computation.scopedCaptures[i] != name.index ||
          binding.scopedCaptures[i] != source.scoped.at(name))
        return refuse(binding.span);
      ++i;
    }
    return true;
  }
};
} // namespace
Error checkScopedSources(const CheckedStorage &storage, Work &work) {
  Semantics types(storage.declarations, storage.assets, work);
  if (!storage.declarationIndex || !storage.sources ||
      !checkDeclarationAssociations(types, storage.declarations,
                                    *storage.declarationIndex,
                                    *storage.sources))
    return types.diagnostic
               ? types.takeError()
               : failure("source.installation", "missing declaration index");
  if (!storage.authoredReferences ||
      storage.authoredReferences->size() != storage.api.references.size())
    return failure("source.binding-witness",
                   "source reference inventory differs");
  for (unsigned i = 0; i < storage.api.references.size(); ++i) {
    const auto &authored = (*storage.authoredReferences)[i];
    const auto &candidate = storage.api.references[i];
    if (!types.charge(authored.reference.path.size() + 1, authored.span))
      return types.takeError();
    if (authored.owner.index != candidate.owner.index ||
        authored.provider.index != candidate.provider.index ||
        authored.target.index != candidate.target.index ||
        !same(authored.span, candidate.span) ||
        authored.written != candidate.written ||
        authored.route != candidate.route ||
        authored.abstractModule != candidate.abstractModule ||
        authored.position.node.index != candidate.position.node.index ||
        authored.position.kind != candidate.position.kind ||
        authored.position.slot != candidate.position.slot ||
        authored.position.ordinal != candidate.position.ordinal ||
        authored.reference != candidate.reference)
      return failure("source.binding-witness",
                     "source reference occurrence differs", authored.span);
    for (const auto &step : authored.reference.path) {
      auto selected = storage.declarationIndex->member(
          SourceAccess{authored.owner}, step.owner, step.name,
          {[&] { return types.charge(1, authored.span); }, {}});
      if (!std::holds_alternative<ResolvedReference>(selected))
        return types.diagnostic
                   ? types.takeError()
                   : failure("source.binding-witness",
                             "source reference route is inaccessible",
                             authored.span);
    }
  }
  // Constructor authority belongs to the port's authored occurrence. It is
  // independent of the field type and of later managed-query evidence.
  for (const auto &decl : storage.declarations) {
    if (!types.charge(decl.services.size() + 1, decl.span))
      return types.takeError();
    auto source = storage.bodySources.find(decl.id.index);
    if (source == storage.bodySources.end()) {
      if (!decl.services.empty())
        return failure("source.binding-witness",
                       "missing managed constructor source", decl.span);
      continue;
    }
    if (!source->second || !source->second->syntax)
      return failure("source.binding-witness",
                     "missing managed constructor syntax", decl.span);
    const auto &written = source->second->syntax->services;
    if (written.size() != decl.services.size())
      return failure("source.binding-witness",
                     "managed constructor coverage differs", decl.span);
    for (unsigned i = 0; i < written.size(); ++i)
      if (!written[i].serviceReference ||
          *written[i].serviceReference != decl.services[i].constructor)
        return failure("source.binding-witness",
                       "managed constructor provider differs",
                       decl.services[i].span);
  }
  // This closure is immutable for the whole check; share operand-relative
  // summaries, while each declaration reconstructs its own premise scope.
  HelperResults helperResults(types, storage.declarations);
  if (auto error = checkModuleContracts(storage, work))
    return error;
  if (auto error = checkSignatureSources(storage, work))
    return error;
  if (auto error = checkConstructionSources(storage, work))
    return error;
  auto servicePorts = replayServicePorts(storage, work);
  if (!servicePorts)
    return servicePorts.takeError();
  std::map<uint32_t, std::unique_ptr<LexicalRegions>> lexicalSources;
  for (const auto &[owner, source] : storage.bodySources) {
    if (!source || !source->syntax)
      return failure("source.binding-witness", "missing lexical source syntax");
    auto lexical = std::make_unique<LexicalRegions>(types, *source->syntax);
    if (!lexical->prepare())
      return types.takeError();
    lexicalSources.emplace(owner, std::move(lexical));
  }
  std::map<uint32_t, std::unique_ptr<ServiceRoots>> serviceSources;
  for (const auto &[owner, ports] : *servicePorts) {
    auto source = storage.bodySources.find(owner);
    if (source == storage.bodySources.end() || !source->second ||
        !source->second->syntax)
      return failure("source.binding-witness", "missing managed root syntax");
    auto roots = std::make_unique<ServiceRoots>(types, *source->second->syntax,
                                                *lexicalSources.at(owner));
    if (!roots->prepare())
      return types.takeError();
    const auto &candidate = storage.declarations[owner].services;
    auto samePort = [&](const ServicePort &a, const ServicePort &b) {
      return a.name == b.name && a.field == b.field && a.owner == b.owner &&
             a.constructor == b.constructor && same(a.span, b.span);
    };
    if (candidate.size() != ports.size() ||
        !std::equal(candidate.begin(), candidate.end(), ports.begin(),
                    samePort))
      return failure("source.binding-witness",
                     "managed input differs from authored header");
    serviceSources.emplace(owner, std::move(roots));
  }
  std::map<const Body *, std::vector<unsigned>> serviceMaps;
  auto sourceRoot = [&](const SourceCall &source, const Body &body,
                        const Expression &argument, ServiceId actual) {
    auto owner = serviceSources.find(source.owner.index);
    auto mapping = serviceMaps.find(&body);
    if (argument.kind != Expression::Kind::Name || !argument.binding ||
        owner == serviceSources.end() || mapping == serviceMaps.end() ||
        actual.index >= mapping->second.size())
      return false;
    auto expected = owner->second->input(*argument.binding, argument.span);
    return expected && *expected == mapping->second[actual.index];
  };
  std::vector<unsigned> uses(storage.scopedSources.size());
  std::vector<unsigned> callUses(storage.scopedCalls.size());
  std::vector<unsigned> intrinsicUses(storage.intrinsicCalls.size());
  std::vector<unsigned> invocationUses(storage.scopedInvocations.size());
  auto authoredCall = [&](const Body &body, const Operation &op,
                          const SourceCall &source) {
    const char *diagnostic =
        op.binding && (!op.binding->scopedArguments.empty() ||
                       !op.binding->domainArguments.empty())
            ? "source.scoped-witness"
            : "source.binding-witness";
    auto refuse = [&](StringRef message =
                          "invocation differs from its authored source") {
      return types.fail(diagnostic, message, op.span);
    };
    if (!op.binding || !source.syntax ||
        source.owner.index >= storage.declarations.size() ||
        source.target.index >= storage.declarations.size() ||
        source.expression >= source.syntax->expressions.size())
      return refuse();
    const auto &binding = *op.binding;
    const auto &expr = source.syntax->expressions[source.expression];
    const auto &callee = storage.declarations[source.target.index];
    const auto &owner = storage.declarations[source.owner.index];
    if (!same(expr.span, op.span) || expr.binding ||
        binding.target.declaration.index != source.target.index ||
        binding.target.module != source.module ||
        binding.target.reference != source.reference ||
        source.reference.target.index != source.target.index ||
        binding.arguments != source.arguments)
      return refuse("resolved source target or static arguments differ");
    if (expr.kind == Expression::Kind::Call && !source.module) {
      // A protocol's generated Host companions are members of its public
      // namespace, not lexical declarations visible inside its own body.
      auto selected = storage.declarationIndex->lookup(
          SourceAccess{source.owner}, expr.text,
          {[&] { return types.charge(1, op.span); }, {}});
      auto *reference = std::get_if<ResolvedReference>(&selected);
      if (!reference || *reference != source.reference)
        return types.diagnostic ? false
                                : refuse("source declaration lookup differs");
    }
    // Abstract member evidence is typed and immutable. Re-authorize its path
    // using the same source access policy, independently of candidate metadata.
    if (source.module) {
      if (!source.reference.abstract ||
          source.reference.abstract->module != *source.module)
        return refuse("abstract source context differs");
      for (const auto &step : source.reference.path) {
        auto selected = storage.declarationIndex->member(
            SourceAccess{source.owner}, step.owner, step.name,
            {[&] { return types.charge(1, op.span); }, {}});
        if (!std::holds_alternative<ResolvedReference>(selected))
          return types.diagnostic
                     ? false
                     : refuse("abstract source route is inaccessible");
      }
    }
    if (source.reference.category == ResolutionCategory::ServiceMethod) {
      if (expr.kind != Expression::Kind::MethodCall ||
          expr.children.size() != 1 || op.expression != source.expression ||
          !expr.callLabels.empty() || !expr.staticLabels.empty() ||
          expr.roles || binding.services.size() != 1 ||
          !sourceRoot(source, body,
                      source.syntax->expressions.at(expr.children.front()),
                      binding.services.front()))
        return types.diagnostic ? false
                                : refuse("authored managed root differs");
      const auto &port = body.services[binding.services.front().index];
      auto selected =
          resolveServiceMethod(types, *storage.declarationIndex, source.owner,
                               port.constructor, expr.text, expr.span);
      const auto *row =
          storage.declarationIndex->serviceAssociation(source.target);
      if (!selected || !row || selected->reference != source.reference ||
          expr.arguments.size() != serviceStaticCount(row->signature) ||
          source.arguments.size() != 1 + expr.arguments.size() ||
          source.arguments.front() != port.field)
        return refuse("authored managed member differs");
      if (!row->capability.empty() &&
          !types.entails(
              &owner, CapabilityBound{row->capability, {port.field}, expr.span},
              "source.binding-witness"))
        return false;
      return checkCallAction(types, storage.declarations, body, op,
                             storage.declarationIndex.get());
    }
    auto order = bindArguments(types, inputNames(callee), expr.children.size(),
                               expr.callLabels, true, expr.span, diagnostic);
    if (!order || *order != binding.argumentOrder)
      return types.diagnostic ? false : refuse();
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      const auto slot =
          callee.inputOrder.empty()
              ? Declaration::InputSlot{Declaration::InputSlot::Kind::Data,
                                       (*order)[i]}
              : callee.inputOrder[(*order)[i]];
      auto child = expr.children[i];
      if (child >= source.syntax->expressions.size())
        return refuse();
      if (slot.kind == Declaration::InputSlot::Kind::Data) {
        auto value = body.expressionValues.find(child);
        if (value == body.expressionValues.end() ||
            slot.index >= binding.operands.size() ||
            value->second.index >= body.values.size() ||
            value->second.index != binding.operands[slot.index].index)
          return refuse("source argument value differs");
      } else if (slot.kind == Declaration::InputSlot::Kind::Service) {
        const auto &argument = source.syntax->expressions[child];
        if (argument.kind != Expression::Kind::Name || !argument.binding ||
            slot.index >= binding.services.size())
          return refuse();
        if (!sourceRoot(source, body, argument, binding.services[slot.index]))
          return types.diagnostic
                     ? false
                     : refuse("authored managed argument root differs");
      }
    }
    if (expr.kind == Expression::Kind::MethodCall) {
      if (expr.children.empty())
        return refuse();
      auto receiver = body.expressionValues.find(expr.children.front());
      if (receiver == body.expressionValues.end() ||
          receiver->second.index >= body.values.size())
        return refuse();
      auto selected = resolveHomeMethod(
          types, storage.declarations, *storage.declarationIndex, owner,
          body.values[receiver->second.index].type, expr.text, expr.span);
      if (!selected || selected->declaration.index != source.target.index ||
          selected->module != source.module ||
          selected->reference != source.reference)
        return types.diagnostic ? false : refuse();
    }
    if (callee.kind == Declaration::Kind::Protocol) {
      std::vector<unsigned> expected;
      if (expr.kind == Expression::Kind::MethodCall) {
        if (expr.roles || callee.inputs.empty() || binding.operands.empty())
          return refuse();
        const auto &port = callee.inputs.front();
        const auto &receiver = body.values[binding.operands.front().index];
        std::vector<std::optional<unsigned>> roles(callee.roles.size());
        if (port.placement &&
            std::holds_alternative<ProductPlacement>(port.placement->value)) {
          if (!receiver.placement || !std::holds_alternative<ProductPlacement>(
                                         receiver.placement->value))
            return refuse();
          const auto &formal =
              std::get<ProductPlacement>(port.placement->value).arguments;
          const auto &actual =
              std::get<ProductPlacement>(receiver.placement->value).arguments;
          if (formal.size() != actual.size())
            return refuse();
          for (unsigned i = 0; i < formal.size(); ++i) {
            if (formal[i] >= roles.size())
              return refuse();
            roles[formal[i]] = actual[i];
          }
        } else {
          auto formal = port.roles;
          auto actual = receiver.components;
          if (port.oracle) {
            if (!receiver.oracleHolder || port.oracle->holder >= roles.size())
              return refuse();
            roles[port.oracle->holder] = *receiver.oracleHolder;
            llvm::erase(formal, port.oracle->holder);
            llvm::erase(actual, *receiver.oracleHolder);
          }
          if (formal.size() != actual.size() || formal.size() > 1)
            return refuse();
          if (!formal.empty()) {
            if (formal.front() >= roles.size())
              return refuse();
            roles[formal.front()] = actual.front();
          }
        }
        for (auto role : roles) {
          if (!role || *role >= source.syntax->roles.size() ||
              llvm::is_contained(expected, *role))
            return refuse();
          expected.push_back(*role);
        }
      } else {
        auto header = storage.bodySources.find(callee.id.index);
        if (header == storage.bodySources.end() || !header->second ||
            !header->second->syntax)
          return refuse();
        for (const auto &name :
             expr.roles ? *expr.roles : header->second->syntax->roles) {
          auto at = llvm::find(source.syntax->roles, name);
          if (at == source.syntax->roles.end())
            return refuse();
          expected.push_back(at - source.syntax->roles.begin());
        }
      }
      if (binding.roles != expected)
        return refuse();
    }
    if (!binding.scopedArguments.empty() || !binding.domainArguments.empty())
      return true;
    return checkCallAction(types, storage.declarations, body, op,
                           storage.declarationIndex.get());
  };
  auto checkCall = [&](const Body &body, const Operation &op) {
    if (op.binding &&
        (op.binding->installedSignature || op.binding->intrinsicSource)) {
      const auto &binding = *op.binding;
      if (!binding.intrinsicSource ||
          *binding.intrinsicSource >= storage.intrinsicCalls.size() ||
          !storage.intrinsicCalls[*binding.intrinsicSource] ||
          ++intrinsicUses[*binding.intrinsicSource] != 1)
        return types.fail("source.binding-witness",
                          "intrinsic source occurrence differs", op.span);
      const auto &source = *storage.intrinsicCalls[*binding.intrinsicSource];
      if (!source.syntax ||
          source.expression >= source.syntax->expressions.size() ||
          !binding.lexicalOwner ||
          binding.lexicalOwner->index != source.owner.index ||
          binding.target.declaration.index != source.target.index)
        return types.fail("source.binding-witness",
                          "intrinsic authored authority differs", op.span);
      const auto &expr = source.syntax->expressions[source.expression];
      auto selected = storage.declarationIndex->lookup(
          SourceAccess{source.owner}, expr.text,
          {[&] { return types.charge(1, op.span); }, {}});
      auto *reference = std::get_if<ResolvedReference>(&selected);
      if (expr.kind != Expression::Kind::Call || expr.binding ||
          !same(expr.span, op.span) || !reference ||
          *reference != source.reference ||
          binding.target.reference != source.reference ||
          expr.children.size() != binding.operands.size() ||
          !expr.callLabels.empty() || !expr.arguments.empty() || expr.roles)
        return types.diagnostic
                   ? false
                   : types.fail("source.binding-witness",
                                "intrinsic resolved declaration differs",
                                op.span);
      return authoredCall(body, op, source);
    }
    auto refuse = [&] {
      return types.fail("source.scoped-witness",
                        "scoped call differs from authored argument mapping",
                        op.span);
    };
    bool managed = std::holds_alternative<ServiceQuery>(op.action) ||
                   (op.binding && op.binding->target.reference.category ==
                                      ResolutionCategory::ServiceMethod);
    auto missing = [&] {
      return managed ? types.fail("source.binding-witness",
                                  "managed source occurrence differs", op.span)
                     : refuse();
    };
    const auto *call = std::get_if<HelperCall>(&op.action);
    if (!op.binding || !op.binding->scopedSource) {
      if (call &&
          (!call->scopedArguments.empty() || !call->domainArguments.empty()))
        return refuse();
      if (managed)
        return missing();
      if (!op.binding)
        return true;
      return types.fail("source.binding-witness",
                        "invocation has no authored occurrence", op.span);
    }
    const auto &binding = *op.binding;
    if (*binding.scopedSource >= storage.scopedCalls.size() ||
        !storage.scopedCalls[*binding.scopedSource] ||
        ++callUses[*binding.scopedSource] != 1)
      return missing();
    const auto &source = *storage.scopedCalls[*binding.scopedSource];
    if (!source.syntax || source.target.index >= storage.declarations.size() ||
        !authoredCall(body, op, source))
      return types.diagnostic ? false : refuse();
    const auto &expr = source.syntax->expressions.at(source.expression);
    const auto &callee = storage.declarations[source.target.index];
    if (binding.scopedArguments.empty() && binding.domainArguments.empty()) {
      if (!binding.notation)
        return source.notationFamily.empty() || refuse();
      if (!expr.notation || !expr.scope ||
          *expr.scope >= source.syntax->bodies.size() ||
          !source.syntax->bodies[*expr.scope].notationEnvironment ||
          op.results.size() != 1 ||
          op.results.front().index >= body.values.size())
        return refuse();
      std::vector<Type> inputs;
      std::vector<ValueId> authored;
      for (auto operand : binding.operands) {
        if (operand.index >= body.values.size())
          return refuse();
        inputs.push_back(body.values[operand.index].type);
      }
      for (auto child : expr.children) {
        auto value = body.expressionValues.find(child);
        if (value == body.expressionValues.end())
          return refuse();
        authored.push_back(value->second);
      }
      return checkNotationOccurrence(
                 types, expr,
                 *source.syntax->bodies[*expr.scope].notationEnvironment) &&
             checkOperatorOperands(types, *expr.notation, binding,
                                   binding.argumentOrder, authored, op.span) &&
             checkOperatorWitness(
                 types, storage.declarations, source.notationFamily,
                 *expr.notation, binding, inputs,
                 body.values[op.results.front().index].type, op.span);
    }
    if (!call || call->callee.index != source.target.index ||
        call->scopedArguments != binding.scopedArguments ||
        call->domainArguments != binding.domainArguments)
      return refuse();
    if (expr.kind == Expression::Kind::MethodCall) {
      if (expr.children.empty())
        return refuse();
      auto receiver = body.expressionValues.find(expr.children.front());
      if (receiver == body.expressionValues.end() ||
          receiver->second.index >= body.values.size() ||
          call->operands.empty() ||
          receiver->second.index != call->operands.front().index)
        return refuse();
      auto selected = resolveHomeMethod(
          types, storage.declarations, *storage.declarationIndex,
          storage.declarations[source.owner.index],
          body.values[receiver->second.index].type, expr.text, expr.span);
      if (!selected || selected->declaration.index != source.target.index ||
          selected->module != binding.target.module ||
          selected->reference != source.reference)
        return refuse();
    }
    if (!same(expr.span, op.span) ||
        expr.children.size() != callee.inputOrder.size() ||
        binding.argumentOrder.size() != expr.children.size() ||
        call->scopedArguments.size() != callee.scopedInputs.size() ||
        call->domainArguments.size() != callee.domainInputs.size())
      return refuse();
    if (expr.kind == Expression::Kind::NotationCall ||
        expr.kind == Expression::Kind::Subscript) {
      if (!expr.notation ||
          expr.notation->position != NotationDescriptor::Position::Reduction ||
          expr.filteredReduction != binding.filteredReduction ||
          op.results.size() != 1 || op.results[0].index >= body.values.size() ||
          !expr.scope || *expr.scope >= source.syntax->bodies.size() ||
          !source.syntax->bodies[*expr.scope].notationEnvironment)
        return refuse();
      if (!checkNotationOccurrence(
              types, expr,
              *source.syntax->bodies[*expr.scope].notationEnvironment) ||
          !checkOperatorOperands(types, *expr.notation, binding,
                                 binding.argumentOrder, {}, op.span) ||
          !checkOperatorWitness(types, storage.declarations,
                                source.notationFamily, *expr.notation, binding,
                                {}, body.values[op.results[0].index].type,
                                op.span) ||
          !checkCallAction(types, storage.declarations, body, op,
                           storage.declarationIndex.get()))
        return false;
    } else if (binding.notation || binding.filteredReduction ||
               !source.notationFamily.empty())
      return refuse();
    std::function<bool(uint32_t, unsigned, unsigned)> domain =
        [&](uint32_t expression, unsigned index, unsigned depth) {
          if (depth > work.limits.expressionDepth)
            return types.fail("source.limit", "domain witness depth exceeded",
                              op.span);
          if (!types.charge(1, op.span))
            return false;
          if (expression >= source.syntax->expressions.size() ||
              index >= body.domainBindings.size())
            return refuse();
          const auto &argument = source.syntax->expressions[expression];
          const auto &application = body.domainBindings[index];
          if (argument.kind == Expression::Kind::Name && argument.binding) {
            auto lexical = source.domains.find(*argument.binding);
            if (lexical != source.domains.end())
              return lexical->second == index || refuse();
          }
          if (argument.kind == Expression::Kind::DomainProduct) {
            if (argument.children.size() != 2 ||
                application.children.size() != 2 ||
                application.kind != DomainBinding::Kind::Product ||
                application.expression != expression ||
                !same(application.span, argument.span) ||
                !application.operands.empty() || application.axis ||
                application.parameter || application.factory ||
                !application.arguments.empty() ||
                !application.argumentOrder.empty())
              return refuse();
            Type item(Type::Kind::Tuple);
            for (unsigned i = 0; i < 2; ++i) {
              if (!domain(argument.children[i], application.children[i],
                          depth + 1))
                return false;
              item.arguments.push_back(
                  body.domainBindings[application.children[i]].item);
            }
            return application.item == item || refuse();
          }
          auto expected = source.domainCalls.find(expression);
          if (expected == source.domainCalls.end()) {
            auto value = body.expressionValues.find(expression);
            if (value == body.expressionValues.end() ||
                value->second.index >= body.values.size() ||
                application.expression != expression ||
                !same(application.span, argument.span) ||
                application.operands.size() != 1 ||
                application.operands.front().index != value->second.index ||
                !application.children.empty() || application.axis ||
                application.parameter || application.factory ||
                !application.arguments.empty() ||
                !application.argumentOrder.empty())
              return refuse();
            const auto &type = body.values[value->second.index].type;
            auto kind = type.kind == Type::Kind::Array
                            ? DomainBinding::Kind::SourceArray
                            : DomainBinding::Kind::Elements;
            return (application.kind == kind &&
                    finiteDomainElement(type) == application.item) ||
                   refuse();
          }
          const auto &authored = expected->second;
          if (argument.kind != Expression::Kind::Call ||
              authored.target.declaration.index >=
                  storage.declarations.size() ||
              application.kind != DomainBinding::Kind::Application ||
              application.expression != expression ||
              !same(application.span, argument.span) || application.axis ||
              application.parameter || !application.factory ||
              application.factory->declaration.index !=
                  authored.target.declaration.index ||
              application.factory->module != authored.target.module ||
              application.factory->reference != authored.target.reference ||
              application.arguments != authored.arguments)
            return refuse();
          const auto &factory =
              storage.declarations[authored.target.declaration.index];
          if (factory.kind != Declaration::Kind::DomainFunction ||
              !factory.domainResult ||
              application.arguments.size() != factory.parameters.size() ||
              application.operands.size() != factory.inputs.size() ||
              application.children.size() != factory.domainInputs.size())
            return refuse();
          auto order =
              bindArguments(types, inputNames(factory),
                            argument.children.size(), argument.callLabels, true,
                            argument.span, "source.scoped-witness");
          if (!order || *order != application.argumentOrder)
            return refuse();
          auto substitution = types.substitution(factory, authored.arguments);
          if (authored.target.module && factory.parent)
            substitution.emplace(
                "self:" +
                    storage.declarations[factory.parent->index].qualifiedName,
                *authored.target.module);
          auto item = types.substitute(*factory.domainResult, substitution,
                                       argument.span);
          if (!item || *item != application.item)
            return refuse();
          for (unsigned i = 0; i < argument.children.size(); ++i) {
            const auto &slot = factory.inputOrder[(*order)[i]];
            auto child = argument.children[i];
            if (slot.kind == Declaration::InputSlot::Kind::Domain) {
              auto nested = application.children[slot.index];
              if (!domain(child, nested, depth + 1))
                return false;
              auto item =
                  types.substitute(factory.domainInputs[slot.index].item,
                                   substitution, argument.span);
              if (!item || *item != body.domainBindings[nested].item)
                return refuse();
            } else if (slot.kind == Declaration::InputSlot::Kind::Data) {
              auto value = body.expressionValues.find(child);
              auto type = types.substitute(factory.inputs[slot.index].type,
                                           substitution, argument.span);
              if (!type || value == body.expressionValues.end() ||
                  value->second.index >= body.values.size() ||
                  value->second.index !=
                      application.operands[slot.index].index ||
                  *type != body.values[value->second.index].type)
                return refuse();
            } else
              return refuse();
          }
          return true;
        };
    std::vector<bool> assigned(callee.inputOrder.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      unsigned parameter = i;
      for (const auto &label : expr.callLabels)
        if (label.index == i) {
          parameter = callee.inputOrder.size();
          for (unsigned j = 0; j < callee.inputOrder.size(); ++j) {
            const auto &slot = callee.inputOrder[j];
            const auto &name =
                slot.kind == Declaration::InputSlot::Kind::Scoped
                    ? callee.scopedInputs[slot.index].name
                : slot.kind == Declaration::InputSlot::Kind::Domain
                    ? callee.domainInputs[slot.index].name
                    : callee.inputs[slot.index].name;
            if (name == label.name)
              parameter = j;
          }
        }
      if (parameter >= assigned.size() || assigned[parameter] ||
          binding.argumentOrder[i] != parameter)
        return refuse();
      assigned[parameter] = true;
      const auto &slot = callee.inputOrder[parameter];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        if (!domain(expr.children[i], call->domainArguments[slot.index], 1))
          return false;
        continue;
      }
      if (slot.kind != Declaration::InputSlot::Kind::Scoped)
        continue;
      auto index = call->scopedArguments[slot.index];
      if (index >= body.scopedBindings.size())
        return refuse();
      const auto &actual = body.scopedBindings[index];
      auto effect = bindingEffects(types, body, index);
      if (!effect ||
          !effectsWithin(
              types, *effect,
              EffectSummary{
                  callee.scopedInputs[slot.index].signature.allowance},
              op.span))
        return types.diagnostic ? false : refuse();
      const auto &argument = source.syntax->expressions[expr.children[i]];
      if (argument.kind == Expression::Kind::Lambda) {
        if (!actual.computation ||
            actual.computation->lexicalOwner.index != source.owner.index ||
            actual.computation->expression != expr.children[i])
          return refuse();
      } else if (argument.kind == Expression::Kind::Name && argument.binding) {
        auto lexical = source.scoped.find(*argument.binding);
        if (lexical == source.scoped.end() || lexical->second != index ||
            !actual.parameter)
          return refuse();
      } else
        return refuse();
    }
    return checkCallAction(types, storage.declarations, body, op,
                           storage.declarationIndex.get());
  };
  using Formal = std::pair<const ScopedSignature *, Span>;
  std::function<bool(const Body &, ArrayRef<Formal>, unsigned, DeclarationId,
                     ArrayRef<unsigned>, std::optional<uint32_t>, Body::Mode)>
      visit = [&](const Body &body, ArrayRef<Formal> formals, unsigned depth,
                  DeclarationId lexicalOwner, ArrayRef<unsigned> roots,
                  std::optional<uint32_t> region, Body::Mode mode) {
        if (depth > work.limits.expressionDepth)
          return types.fail("source.limit", "scoped witness body depth", {});
        if (!types.charge(body.values.size() + body.operations.size() +
                              indexedWork(roots.size()) + 1,
                          {}))
          return false;
        if (body.mode != mode)
          return types.fail("source.binding-witness",
                            "body source mode differs", {});
        auto lexicalSource = lexicalSources.find(lexicalOwner.index);
        auto *lexical = lexicalSource == lexicalSources.end()
                            ? nullptr
                            : lexicalSource->second.get();
        auto belongs = [&](uint32_t expression, Span span) {
          if (!region)
            return true;
          return lexical ? lexical->contains(expression, *region, mode, span)
                         : types.fail("source.binding-witness",
                                      "missing lexical region source", span);
        };
        for (const auto &[expression, value] : body.expressionValues)
          if (!belongs(expression, {}))
            return false;
        serviceMaps.emplace(&body, roots.vec());
        std::map<unsigned, unsigned> serviceSlots;
        auto ports = servicePorts->find(lexicalOwner.index);
        if (body.services.size() != roots.size())
          return types.fail("source.binding-witness",
                            "managed region input coverage differs", {});
        for (unsigned i = 0; i < roots.size(); ++i) {
          if (!serviceSlots.emplace(roots[i], i).second)
            return types.fail("source.binding-witness",
                              "duplicated managed root", {});
          if (ports == servicePorts->end() || roots[i] >= ports->second.size())
            return types.fail("source.binding-witness",
                              "unknown managed source root", {});
          const auto &expected = ports->second[roots[i]];
          const auto &actual = body.services[i];
          if (actual.name != expected.name || actual.field != expected.field ||
              actual.owner != expected.owner ||
              actual.constructor != expected.constructor ||
              !same(actual.span, expected.span))
            return types.fail("source.binding-witness",
                              "managed region input differs from source root",
                              actual.span);
        }
        std::vector<const Operation *> producers(body.values.size());
        for (const auto &op : body.operations)
          for (auto value : op.results) {
            if (value.index >= producers.size() || producers[value.index])
              return types.fail("source.scoped-witness",
                                "invalid operation result", op.span);
            producers[value.index] = &op;
          }
        if (body.scopedBindings.size() < formals.size())
          return types.fail("source.scoped-witness", "missing scoped formal",
                            {});
        unsigned formalIndex = 0;
        for (const auto &binding : body.scopedBindings) {
          if (!types.charge(1, binding.span))
            return false;
          if (binding.parameter) {
            if (formalIndex >= formals.size() ||
                *binding.parameter != formalIndex ||
                !(binding.signature == *formals[formalIndex].first) ||
                !same(binding.span, formals[formalIndex].second))
              return types.fail("source.scoped-witness",
                                "scoped formal identity differs", binding.span);
            ++formalIndex;
            if (binding.source || binding.computation ||
                !binding.captures.empty() || !binding.scopedCaptures.empty() ||
                !binding.domainCaptures.empty())
              return types.fail("source.scoped-witness",
                                "formal scoped binding has an environment",
                                binding.span);
            continue;
          }
          if (formalIndex != formals.size())
            return types.fail("source.scoped-witness",
                              "scoped formal order differs", binding.span);
          if (!binding.source ||
              *binding.source >= storage.scopedSources.size() ||
              !storage.scopedSources[*binding.source] ||
              !storage.scopedSources[*binding.source]->syntax ||
              !binding.computation || ++uses[*binding.source] != 1)
            return types.fail("source.scoped-witness",
                              "missing or duplicated scoped source witness",
                              binding.span);
          const auto &source = *storage.scopedSources[*binding.source];
          if (source.owner.index != lexicalOwner.index ||
              !belongs(source.expression, binding.span) ||
              source.expression >= source.syntax->expressions.size() ||
              source.syntax->expressions[source.expression].regions.size() != 1)
            return types.fail("source.binding-witness",
                              "callback lexical region differs", binding.span);
          if (!types.charge(binding.scopedCaptures.size(), binding.span))
            return false;
          std::vector<Formal> captured;
          for (auto index : binding.scopedCaptures) {
            if (index >= body.scopedBindings.size() ||
                !body.scopedBindings[index].parameter)
              return types.fail("source.scoped-witness",
                                "invalid captured scoped formal", binding.span);
            const auto &formal = body.scopedBindings[index];
            captured.emplace_back(&formal.signature, formal.span);
          }
          if (!source.syntax ||
              source.owner.index >= storage.declarations.size() ||
              !CaptureCheck(types, source,
                            storage.declarations[source.owner.index], producers)
                   .run(body, binding) ||
              !checkScopedValues(types, storage, source, binding) ||
              !visit(
                  *binding.computation->body, captured, depth + 1, source.owner,
                  {},
                  source.syntax->expressions[source.expression].regions.front(),
                  source.signature.mode == ScopedSignature::Mode::Math
                      ? Body::Mode::Math
                      : Body::Mode::Local))
            return false;
          if (!effectsWithin(types, binding.computation->body->effects,
                             EffectSummary{binding.signature.allowance},
                             binding.span))
            return types.fail("source.scoped-witness",
                              "callback exceeds its effect ceiling",
                              binding.span);
        }
        for (const auto &op : body.operations) {
          if (op.expression && !belongs(*op.expression, op.span))
            return false;
          // The immutable occurrence is also checked when a candidate removes
          // its optional originating-expression hint.
          auto occurrence = [&](const auto &sources, unsigned index) {
            if (index >= sources.size() || !sources[index])
              return true; // The owning invocation check diagnoses this shape.
            const auto &source = *sources[index];
            return (source.owner.index == lexicalOwner.index &&
                    belongs(source.expression, op.span)) ||
                   types.fail("source.binding-witness",
                              "invocation lexical region differs", op.span);
          };
          if (op.binding &&
              ((op.binding->scopedSource &&
                !occurrence(storage.scopedCalls, *op.binding->scopedSource)) ||
               (op.binding->intrinsicSource &&
                !occurrence(storage.intrinsicCalls,
                            *op.binding->intrinsicSource))))
            return false;
          if (op.binding &&
              ((op.binding->installedSignature &&
                (!op.binding->lexicalOwner ||
                 op.binding->lexicalOwner->index != lexicalOwner.index)) ||
               (op.binding->scopedSource &&
                (*op.binding->scopedSource >= storage.scopedCalls.size() ||
                 !storage.scopedCalls[*op.binding->scopedSource] ||
                 !storage.scopedCalls[*op.binding->scopedSource]->syntax ||
                 storage.scopedCalls[*op.binding->scopedSource]->owner.index !=
                     lexicalOwner.index))))
            return types.fail("source.binding-witness",
                              "record invocation lexical owner differs",
                              op.span);
          if (!types.charge(1, op.span) || !checkCall(body, op))
            return false;
          if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
            auto refuse = [&] {
              return types.fail("source.scoped-witness",
                                "scoped invocation target differs", op.span);
            };
            if (invoke->source >= storage.scopedInvocations.size() ||
                !storage.scopedInvocations[invoke->source] ||
                ++invocationUses[invoke->source] != 1 ||
                invoke->binding >= body.scopedBindings.size())
              return refuse();
            const auto &source = *storage.scopedInvocations[invoke->source];
            if (!occurrence(storage.scopedInvocations, invoke->source))
              return false;
            if (!source.syntax ||
                source.owner.index >= storage.declarations.size() ||
                source.expression >= source.syntax->expressions.size())
              return refuse();
            const auto &expr = source.syntax->expressions[source.expression];
            if (expr.kind != Expression::Kind::Call || !expr.binding ||
                !same(expr.span, op.span))
              return refuse();
            if (expr.binding->index >= source.syntax->bindings.size())
              return refuse();
            const auto &lexical = source.syntax->bindings[expr.binding->index];
            const auto &selected = body.scopedBindings[invoke->binding];
            // Scoped names refer to declaration formals. Extraction and
            // region forwarding preserve their original declaration span;
            // the expected identity comes from resolved source syntax, not
            // another producer-recorded body-slot map.
            if (!lexical.scoped || !selected.parameter ||
                !same(lexical.span, selected.span))
              return refuse();
            if (invoke->operands.size() != expr.children.size() ||
                !types.charge(expr.children.size(), op.span))
              return types.diagnostic ? false : refuse();
            for (unsigned i = 0; i < expr.children.size(); ++i) {
              auto value = body.expressionValues.find(expr.children[i]);
              if (value == body.expressionValues.end() ||
                  value->second.index != invoke->operands[i].index)
                return refuse();
            }
          }
          auto nested = [&](ArrayRef<ServiceId> advertised,
                            ArrayRef<unsigned> roles,
                            ArrayRef<std::shared_ptr<const Body>> regions) {
            std::vector<uint32_t> authored;
            if (region) {
              auto expected = lexical->regions(body, op);
              if (!expected)
                return false;
              authored = std::move(*expected);
              if (authored.size() != regions.size())
                return lexical->refuse(op.span);
            }
            auto visitRegions = [&](ArrayRef<unsigned> expectedRoots) {
              for (unsigned i = 0; i < regions.size(); ++i) {
                if (!regions[i])
                  return types.fail("source.binding-witness",
                                    "missing candidate region", op.span);
                if (!visit(*regions[i], formals, depth + 1, lexicalOwner,
                           expectedRoots,
                           region ? std::optional(authored[i]) : std::nullopt,
                           mode))
                  return false;
              }
              return true;
            };
            auto source = serviceSources.find(lexicalOwner.index);
            if (source == serviceSources.end()) {
              if (!advertised.empty())
                return types.fail("source.binding-witness",
                                  "region has unauthored services", op.span);
              return visitRegions({});
            }
            auto expected = source->second->captures(op);
            if (!expected || advertised.size() != expected->size())
              return types.diagnostic
                         ? false
                         : types.fail("source.binding-witness",
                                      "managed capture coverage differs",
                                      op.span);
            for (unsigned i = 0; i < expected->size(); ++i) {
              auto at = serviceSlots.find((*expected)[i]);
              if (at == serviceSlots.end() ||
                  advertised[i].index != at->second ||
                  !llvm::is_contained(
                      roles,
                      servicePorts->at(lexicalOwner.index)[(*expected)[i]]
                          .owner))
                return types.fail("source.binding-witness",
                                  "managed capture order differs from source",
                                  op.span);
            }
            return visitRegions(*expected);
          };
          if (const auto *control = std::get_if<Control>(&op.action))
            if (!nested(control->services, control->roles, control->regions))
              return false;
          if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
            if (!nested(repeat->services, repeat->roles, {repeat->region}))
              return false;
        }
        auto effects = inferEffects(types, storage.declarations, body);
        if (!effects || *effects != body.effects)
          return types.fail("source.scoped-witness",
                            "effect summary differs from operations", {});
        return true;
      };
  for (const auto &decl : storage.declarations) {
    if (!decl.body)
      continue;
    if (!types.charge(decl.scopedInputs.size(), decl.span))
      return types.takeError();
    std::vector<Formal> formals;
    for (const auto &parameter : decl.scopedInputs)
      formals.emplace_back(&parameter.signature, parameter.span);
    std::vector<unsigned> roots;
    if (auto at = servicePorts->find(decl.id.index); at != servicePorts->end())
      for (unsigned i = 0; i < at->second.size(); ++i)
        roots.push_back(i);
    auto source = storage.bodySources.find(decl.id.index);
    auto region = source != storage.bodySources.end() && source->second &&
                          source->second->syntax &&
                          !source->second->syntax->bodies.empty()
                      ? std::optional<uint32_t>(0)
                      : std::nullopt;
    auto mode =
        region ? sourceMode(source->second->syntax->kind) : decl.body->mode;
    if (!visit(*decl.body, formals, 1, decl.id, roots, region, mode) ||
        !checkFiniteContracts(types, storage.declarations, decl, *decl.body,
                              helperResults))
      return types.takeError();
    if (auto source = storage.bodySources.find(decl.id.index);
        source != storage.bodySources.end() &&
        (!source->second ||
         !checkInvocationValues(types, storage, *source->second, *decl.body)))
      return types.diagnostic
                 ? types.takeError()
                 : failure("source.binding-witness", "missing body source");
    if (decl.effectAllowance &&
        !effectsWithin(types, decl.body->effects, *decl.effectAllowance,
                       decl.span)) {
      types.fail("source.scoped-witness",
                 "body exceeds its authored effect contract", decl.span);
      return types.takeError();
    }
  }
  for (const auto &[owner, source] : storage.bodySources)
    if (!source || !source->syntax ||
        (!source->syntax->bodies.empty() &&
         (owner >= storage.declarations.size() ||
          !storage.declarations[owner].body)))
      return failure("source.binding-witness", "missing authored body");
  for (auto count : intrinsicUses)
    if (count != 1)
      return failure("source.binding-witness",
                     "missing intrinsic invocation occurrence");
  for (auto count : invocationUses)
    if (count != 1)
      return failure("source.scoped-witness",
                     "missing scoped invocation occurrence");
  for (auto count : uses)
    if (count != 1)
      return failure("source.scoped-witness", "missing scoped occurrence");
  for (unsigned i = 0; i < callUses.size(); ++i)
    if (callUses[i] != 1)
      return failure(!storage.scopedCalls[i] ||
                             storage.scopedCalls[i]->reference.category ==
                                 ResolutionCategory::ServiceMethod
                         ? "source.binding-witness"
                         : "source.scoped-witness",
                     "missing source call occurrence");
  return Error::success();
}
} // namespace zkc::language::detail
namespace zkc::language {
llvm::Error
checkScopedElaboration(const CheckedProject &project, const Limits &limits,
                       std::vector<SourceWorkBudget> *observations) {
  if (auto error = checkLimits(limits))
    return error;
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations)
    return detail::failure("source.limit",
                           "checked project exceeds scoped witness limits");
  detail::Work work{limits};
  detail::Work::Scope phase(work, SourceWorkPhase::ScopedElaboration);
  detail::Work::Record record(work, SourceWorkPhase::ScopedElaboration,
                              observations);
  return detail::checkScopedSources(*project.storage, work);
}
} // namespace zkc::language
