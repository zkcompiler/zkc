#include "ScopedWitness.h"
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
  std::set<BindingId> scoped;
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
    if (expr.kind != Expression::Kind::Projection)
      return {};
    auto result = place(expr.children.front(), depth + 1);
    if (!result)
      return {};
    auto type =
        types.projectedType(owner, source.environment.at(result->binding).type,
                            result->path, expr.span);
    if (!type)
      return {};
    auto index = types.fieldIndex(owner, *type, expr.text, expr.span);
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
               const Declaration &owner)
      : types(types), source(source), owner(owner), syntax(*source.syntax) {}
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
    // Independent antichain: replace a covered subtree at its earliest lexical
    // occurrence, without using the producer's region/capture query.
    std::vector<Place> minimal;
    auto prefix = [](ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
      return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
    };
    for (const auto &read : reads) {
      bool covered = false;
      for (auto &prior : minimal)
        if (prior.binding == read.binding && prefix(prior.path, read.path)) {
          if (read.span.begin < prior.span.begin)
            prior.span = read.span;
          covered = true;
          break;
        }
      if (covered)
        continue;
      Place selected = read;
      for (auto it = minimal.begin(); it != minimal.end();)
        if (it->binding == read.binding && prefix(read.path, it->path)) {
          if (it->span.begin < selected.span.begin)
            selected.span = it->span;
          it = minimal.erase(it);
        } else
          ++it;
      minimal.push_back(std::move(selected));
    }
    llvm::stable_sort(minimal, [](const Place &a, const Place &b) {
      return a.span.begin < b.span.begin;
    });
    const auto &body = *computation.body;
    unsigned explicitInputs = source.signature.inputs.size();
    if (minimal.size() != computation.captures.size() ||
        minimal.size() != binding.captures.size() ||
        body.inputs != explicitInputs + minimal.size() ||
        body.values.size() < body.inputs ||
        body.mode != (source.signature.mode == ScopedSignature::Mode::Math
                          ? Body::Mode::Math
                          : Body::Mode::Local) ||
        (body.mayStop && !source.signature.allowance.mayStop) ||
        (body.opaque && !source.signature.allowance.opaque))
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
      unsigned matches = 0;
      for (const auto &op : outer.operations)
        if (op.results.size() == 1 && op.results.front().index == value.index) {
          auto *projection = std::get_if<Projection>(&op.action);
          if (!projection || projection->input.index != root.index ||
              projection->path != path || !same(op.span, expected.span))
            return refuse(binding.span);
          ++matches;
        }
      if (matches != 1 || value.index >= outer.values.size() ||
          root.index >= outer.values.size() ||
          outer.values[value.index].type != *type ||
          outer.values[value.index].components !=
              outer.values[root.index].components)
        return refuse(binding.span);
    }
    if (scoped.size() != computation.scopedCaptures.size() ||
        scoped.size() != binding.scopedCaptures.size())
      return refuse(binding.span);
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
  std::vector<unsigned> uses(storage.scopedSources.size());
  std::vector<unsigned> callUses(storage.scopedCalls.size());
  auto checkCall = [&](const Body &body, const Operation &op) {
    auto refuse = [&] {
      return types.fail("source.scoped-witness",
                        "scoped call differs from authored argument mapping",
                        op.span);
    };
    const auto *call = std::get_if<HelperCall>(&op.action);
    if (!op.binding || !op.binding->scopedSource)
      return (!call || call->scopedArguments.empty()) &&
                     (!op.binding || (op.binding->scopedArguments.empty() &&
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
        call->scopedArguments != binding.scopedArguments)
      return refuse();
    const auto &expr = source.syntax->expressions.at(source.expression);
    const auto &callee = storage.declarations[source.target.index];
    if (!same(expr.span, op.span) ||
        expr.children.size() != callee.inputOrder.size() ||
        binding.argumentOrder.size() != expr.children.size() ||
        call->scopedArguments.size() != callee.scopedInputs.size())
      return refuse();
    std::vector<bool> assigned(callee.inputOrder.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      unsigned parameter = i;
      for (const auto &label : expr.callLabels)
        if (label.index == i) {
          parameter = callee.inputOrder.size();
          for (unsigned j = 0; j < callee.inputOrder.size(); ++j) {
            const auto &slot = callee.inputOrder[j];
            const auto &name = slot.kind == Declaration::InputSlot::Kind::Scoped
                                   ? callee.scopedInputs[slot.index].name
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
  std::function<bool(const Body &, unsigned)> visit = [&](const Body &body,
                                                          unsigned depth) {
    if (depth > work.limits.expressionDepth)
      return types.fail("source.limit", "scoped witness body depth", {});
    for (const auto &binding : body.scopedBindings) {
      if (!types.charge(1, binding.span))
        return false;
      if (binding.parameter) {
        if (binding.source || binding.computation ||
            !binding.captures.empty() || !binding.scopedCaptures.empty())
          return types.fail("source.scoped-witness",
                            "formal scoped binding has an environment",
                            binding.span);
        continue;
      }
      if (!binding.source || *binding.source >= storage.scopedSources.size() ||
          !binding.computation || ++uses[*binding.source] != 1)
        return types.fail("source.scoped-witness",
                          "missing or duplicated scoped source witness",
                          binding.span);
      const auto &source = *storage.scopedSources[*binding.source];
      if (!source.syntax || source.owner.index >= storage.declarations.size() ||
          !CaptureCheck(types, source, storage.declarations[source.owner.index])
               .run(body, binding) ||
          !visit(*binding.computation->body, depth + 1))
        return false;
    }
    for (const auto &op : body.operations) {
      if (!types.charge(1, op.span) || !checkCall(body, op))
        return false;
      if (const auto *control = std::get_if<LocalControl>(&op.action))
        for (const auto &region : control->regions)
          if (!visit(*region, depth + 1))
            return false;
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        if (!visit(*repeat->region, depth + 1))
          return false;
    }
    return true;
  };
  for (const auto &decl : storage.declarations)
    if (decl.body && !visit(*decl.body, 1))
      return types.takeError();
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
