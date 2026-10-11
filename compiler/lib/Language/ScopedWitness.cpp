#include "ScopedWitness.h"
#include "Arguments.h"
#include "BindingWitness.h"
#include "Effects.h"
#include "FiniteContracts.h"
#include "FiniteDomains.h"
#include "Semantics.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool same(Span a, Span b) {
  return a.module.index == b.module.index && a.begin == b.begin &&
         a.end == b.end;
}
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
  for (const auto &[index, syntax] : storage.effectSources) {
    auto refuse = [&] {
      return failure("source.scoped-witness",
                     "effect contract differs from authored signature");
    };
    if (!syntax || index >= storage.declarations.size())
      return refuse();
    const auto &decl = storage.declarations[index];
    if (!types.charge(syntax->scopedInputs.size() +
                          syntax->effectDependencies.size() + 1,
                      decl.span))
      return types.takeError();
    if (decl.scopedInputs.size() != syntax->scopedInputs.size())
      return refuse();
    for (unsigned slot = 0; slot < decl.scopedInputs.size(); ++slot) {
      const auto &written = syntax->scopedInputs[slot].scoped;
      const auto &actual = decl.scopedInputs[slot].signature;
      if (!written || written->mode != actual.mode ||
          written->allowance != actual.allowance)
        return refuse();
    }
    std::optional<EffectSummary> expected;
    if (syntax->effects) {
      expected = EffectSummary{*syntax->effects};
      for (const auto &name : syntax->effectDependencies) {
        if (!types.charge(syntax->scopedInputs.size() + 1, decl.span))
          return types.takeError();
        auto found =
            llvm::find_if(syntax->scopedInputs, [&](const auto &input) {
              return input.name == name;
            });
        if (found == syntax->scopedInputs.end() || !found->scoped)
          return refuse();
        expected->dependencies.emplace(
            unsigned(found - syntax->scopedInputs.begin()),
            found->scoped->allowance);
      }
      if (!joinEffects(types, *expected, EffectSummary{}, decl.span))
        return types.takeError();
    }
    if (expected != decl.effectAllowance)
      return refuse();
  }
  std::vector<unsigned> uses(storage.scopedSources.size());
  std::vector<unsigned> callUses(storage.scopedCalls.size());
  std::vector<unsigned> invocationUses(storage.scopedInvocations.size());
  auto checkCall = [&](const Body &body, const Operation &op) {
    auto refuse = [&] {
      return types.fail("source.scoped-witness",
                        "scoped call differs from authored argument mapping",
                        op.span);
    };
    const auto *call = std::get_if<HelperCall>(&op.action);
    if (!op.binding || !op.binding->scopedSource)
      return (!call || (call->scopedArguments.empty() &&
                        call->domainArguments.empty())) &&
                     (!op.binding || (op.binding->scopedArguments.empty() &&
                                      op.binding->domainArguments.empty() &&
                                      op.binding->argumentOrder.empty()))
                 ? true
                 : refuse();
    const auto &binding = *op.binding;
    if (!call || *binding.scopedSource >= storage.scopedCalls.size() ||
        ++callUses[*binding.scopedSource] != 1)
      return refuse();
    const auto &source = *storage.scopedCalls[*binding.scopedSource];
    if (!source.syntax || source.target.index >= storage.declarations.size() ||
        source.target.index != binding.target.declaration.index ||
        call->callee.index != source.target.index ||
        call->scopedArguments != binding.scopedArguments ||
        call->domainArguments != binding.domainArguments)
      return refuse();
    const auto &expr = source.syntax->expressions.at(source.expression);
    const auto &callee = storage.declarations[source.target.index];
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
          !checkCallAction(types, storage.declarations, body, op))
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
              application.factory->component != authored.target.component ||
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
          if (authored.target.component && factory.parent)
            substitution.emplace(
                "self:" +
                    storage.declarations[factory.parent->index].qualifiedName,
                *authored.target.component);
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
    return true;
  };
  using Formal = std::pair<const ScopedSignature *, Span>;
  std::function<bool(const Body &, ArrayRef<Formal>, unsigned)> visit =
      [&](const Body &body, ArrayRef<Formal> formals, unsigned depth) {
        if (depth > work.limits.expressionDepth)
          return types.fail("source.limit", "scoped witness body depth", {});
        if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
          return false;
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
              !binding.computation || ++uses[*binding.source] != 1)
            return types.fail("source.scoped-witness",
                              "missing or duplicated scoped source witness",
                              binding.span);
          const auto &source = *storage.scopedSources[*binding.source];
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
              !visit(*binding.computation->body, captured, depth + 1))
            return false;
        }
        for (const auto &op : body.operations) {
          if (!types.charge(1, op.span) || !checkCall(body, op))
            return false;
          if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
            auto refuse = [&] {
              return types.fail("source.scoped-witness",
                                "scoped invocation target differs", op.span);
            };
            if (invoke->source >= storage.scopedInvocations.size() ||
                ++invocationUses[invoke->source] != 1 ||
                invoke->binding >= body.scopedBindings.size())
              return refuse();
            const auto &source = *storage.scopedInvocations[invoke->source];
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
          if (const auto *control = std::get_if<LocalControl>(&op.action))
            for (const auto &region : control->regions)
              if (!visit(*region, formals, depth + 1))
                return false;
          if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
            if (!visit(*repeat->region, {}, depth + 1))
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
    if (!visit(*decl.body, formals, 1) ||
        !checkFiniteContracts(types, storage.declarations, decl, *decl.body))
      return types.takeError();
  }
  for (auto count : invocationUses)
    if (count != 1)
      return failure("source.scoped-witness",
                     "missing scoped invocation occurrence");
  for (auto count : uses)
    if (count != 1)
      return failure("source.scoped-witness", "missing scoped occurrence");
  for (auto count : callUses)
    if (count != 1)
      return failure("source.scoped-witness", "missing scoped call occurrence");
  return Error::success();
}
} // namespace zkc::language::detail
namespace zkc::language {
llvm::Error checkScopedElaboration(const CheckedProject &project,
                                   const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations)
    return detail::failure("source.limit",
                           "checked project exceeds scoped witness limits");
  detail::Work work{limits};
  return detail::checkScopedSources(*project.storage, work);
}
} // namespace zkc::language
