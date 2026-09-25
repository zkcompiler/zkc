#include "LinkInternal.h"
#include <algorithm>

namespace zkc::frontend::library::detail {
llvm::Error World::merge(const Environment &incoming) {
  if (auto err = validateEnvironment(incoming))
    return err;
  for (const auto &l : incoming.libraries) {
    auto same = [&](const CapturedLibrary &c) {
      return identity(QualifiedDecl{c.id, {}, ""}) ==
             identity(QualifiedDecl{l.id, {}, ""});
    };
    auto old = std::find_if(environment.libraries.begin(),
                            environment.libraries.end(), same);
    if (old == environment.libraries.end())
      environment.libraries.push_back(l);
    else
      for (const auto &d : l.declarations) {
        bool found = false;
        for (const auto &o : old->declarations)
          found |= identity(o) == identity(d);
        if (!found)
          old->declarations.push_back(d);
      }
  }
  auto mergeEntries = [&](auto Environment::*field, auto key) -> llvm::Error {
    for (const auto &entry : incoming.*field) {
      auto &entries = environment.*field;
      auto old =
          std::find_if(entries.begin(), entries.end(),
                       [&](const auto &v) { return key(v) == key(entry); });
      if (old == entries.end())
        entries.push_back(entry);
      else {
        Environment a, b;
        (a.*field).push_back(*old);
        (b.*field).push_back(entry);
        if (encode(a) != encode(b))
          return fail("library-capture-conflict",
                      "conflicting captured declaration " + key(entry));
      }
    }
    return llvm::Error::success();
  };
  if (auto err = mergeEntries(&Environment::statics,
                              [](const auto &d) { return identity(d.id); }))
    return err;
  if (auto err = mergeEntries(&Environment::logicalTypes,
                              [](const auto &d) { return d.contract.name; }))
    return err;
  if (auto err = mergeEntries(&Environment::operations,
                              [](const auto &d) { return d.contract.name; }))
    return err;
  if (auto err = mergeEntries(&Environment::implications, [](const auto &d) {
        Writer w;
        w.add(d.premise);
        w.add(d.conclusion);
        return w.bytes;
      }))
    return err;
  environment.expansionLimit =
      std::min(environment.expansionLimit, incoming.expansionLimit);
  return llvm::Error::success();
}
llvm::Error World::validateArguments(const Substitution &s) {
  std::set<std::string> seen;
  for (const auto &p : s.statics) {
    if (p.first.kind != StaticTerm::Kind::Root ||
        !seen.insert(identity(p.first)).second)
      return fail("library-substitution",
                  "static formal must be a unique root");
    const auto *d = findStatic(p.first.declaration, environment);
    if (!d || !d->parameter)
      return fail("library-substitution",
                  "substitution formal is not a parameter");
    auto a = sortOf(p.first, environment);
    if (!a)
      return a.takeError();
    // Component identity and member dispatch have one authority: the binding
    // graph. A parallel static substitution would let equality proofs see a
    // different selection from the one whose implementation is called.
    if (sameSort(*a, Sort::component()))
      return fail("library-substitution-component",
                  "component parameters require bindings, not static actuals");
    auto b = sortOf(p.second, environment);
    if (!b)
      return b.takeError();
    if (!sameSort(*a, *b))
      return fail("library-static-sort", "substitution changes static sort");
  }
  for (const auto &p : s.types) {
    if (!seen.insert(identity(StaticTerm::root(p.first))).second)
      return fail("library-substitution", "duplicate type/static actual");
    const auto *d = findStatic(p.first, environment);
    if (!d || !d->parameter || !sameSort(d->result, Sort::type()))
      return fail("library-substitution",
                  "type actual formal is not a type parameter");
  }
  return llvm::Error::success();
}
llvm::Expected<LinkScope> World::scope(const CheckedBody &body,
                                       const std::vector<Binding> &bindings,
                                       const Substitution &arguments,
                                       const std::string &path) {
  if (auto err = merge(body.environment()))
    return err;
  if (auto err = validateArguments(arguments))
    return err;
  LinkScope result;
  result.arguments = arguments;
  for (const auto &binding : bindings) {
    auto node = select(binding, path + "/" + binding.importPath);
    if (!node)
      return node.takeError();
    if (!result.components.emplace(identity(binding.parameter), *node).second)
      return fail("library-binding", "duplicate parameter binding");
  }
  for (const auto &import : body.imports()) {
    auto i = result.components.find(identity(import.parameter));
    if (i == result.components.end())
      return fail("library-binding", "missing component selection");
    if (i->second->implementation.interface.identity() !=
        import.interface.identity())
      return fail("library-interface-drift",
                  "selection does not conform to exact recorded interface");
  }
  return result;
}
llvm::Expected<Selection *> World::select(const Binding &binding,
                                          const std::string &path) {
  if (!binding.implementation)
    return fail("library-binding", "null implementation at " + path);
  if (selections.size() >= environment.expansionLimit || active.size() >= 128)
    return fail("library-limit", "selection count exceeds limit");
  const auto *pointer = binding.implementation.get();
  if (auto old = resolved.find(pointer); old != resolved.end()) {
    old->second->paths.push_back(path);
    return old->second;
  }
  if (!active.insert(pointer).second)
    return fail("library-link-cycle", "recursive selection at " + path);
  // Mutable builders are copied; successful output never retains their
  // pointers.
  auto node = std::make_unique<Selection>(
      Selection{*pointer, {}, {}, {}, {}, {}, {}, {path}});
  auto &impl = node->implementation;
  if (auto err = merge(impl.interface.environment()))
    return err;
  if (impl.environment)
    if (auto err = merge(*impl.environment))
      return err;
  for (const auto &f : impl.functions)
    if (auto err = merge(f.second.environment()))
      return err;
  for (const auto &i : impl.imports)
    if (auto err = merge(i.interface.environment()))
      return err;
  auto checked = checkComponent({impl.interface, impl.representations,
                                 impl.statics, impl.functions, impl.imports,
                                 impl.typeBounds, impl.requirements},
                                environment);
  if (!checked)
    return checked.takeError();
  node->scope.arguments = impl.arguments;
  if (auto err = validateArguments(impl.arguments))
    return err;
  for (const auto &dep : impl.dependencies) {
    auto selected = select(dep, path + "/" + dep.importPath);
    if (!selected)
      return selected.takeError();
    if (!node->scope.components.emplace(identity(dep.parameter), *selected)
             .second)
      return fail("library-binding",
                  "duplicate dependency parameter at " + path);
  }
  if (node->scope.components.size() != impl.imports.size())
    return fail("library-binding",
                "dependency set differs from persistent component imports");
  for (const auto &import : impl.imports) {
    auto dep = node->scope.components.find(identity(import.parameter));
    if (dep == node->scope.components.end())
      return fail("library-binding", "missing component dependency bound");
    if (dep->second->implementation.interface.identity() !=
        import.interface.identity())
      return fail("library-interface-drift",
                  "dependency violates exact component interface bound");
  }
  auto selected = term(impl.selection, node->scope);
  if (!selected)
    return selected.takeError();
  auto sort = sortOf(*selected, environment);
  if (!sort)
    return sort.takeError();
  if (!sameSort(*sort, Sort::component()))
    return fail("library-selection", "selection is not a component at " + path);
  node->selected = *selected;
  auto base = selectionIdentity(*selected, environment);
  if (!base)
    return base.takeError();
  Writer key;
  node->normalizedSelection = *base;
  key.add("static-actuals");
  key.add(impl.arguments.statics.size());
  // Extra explicitly supplied actuals are key-bearing too, including private
  // type/static captures. Order is declared and is not an alias display order.
  for (const auto &a : impl.arguments.statics) {
    auto actual = term(a.second, node->scope);
    if (!actual)
      return actual.takeError();
    auto k = selectionIdentity(*actual, environment);
    if (!k)
      return k.takeError();
    key.add(identity(a.first));
    key.add(*k);
  }
  key.add("type-actuals");
  key.add(impl.arguments.types.size());
  for (const auto &a : impl.arguments.types) {
    auto permission = publicPermissions(a.second, node->scope);
    if (!permission)
      return permission.takeError();
    auto actual = publicType(a.second, node->scope);
    if (!actual)
      return actual.takeError();
    auto normalized = normalizedTypeIdentity(*actual, environment);
    if (!normalized)
      return normalized.takeError();
    key.add(identity(a.first));
    key.add(*normalized);
  }
  key.add("dependencies");
  key.add(node->scope.components.size());
  for (const auto &dep : node->scope.components) {
    key.add(dep.first);
    key.add(dep.second->key);
  }
  node->captureIdentity = key.bytes;
  Writer completeKey;
  completeKey.add(node->normalizedSelection);
  completeKey.add(node->captureIdentity);
  node->key = completeKey.bytes;
  Writer artifact;
  artifact.add(impl.interface.identity());
  std::map<std::string, std::string> obligations;
  for (const auto &i : impl.imports)
    obligations.emplace(identity(i.parameter), i.interface.identity());
  artifact.list(obligations, [&](const auto &p) {
    artifact.add(p.first);
    artifact.add(p.second);
  });
  Body boundsSubject;
  boundsSubject.typeBounds = impl.typeBounds;
  boundsSubject.signature.preconditions = impl.requirements;
  artifact.add(encode(boundsSubject));
  if (impl.environment)
    artifact.add(encode(*impl.environment));
  artifact.add("representations");
  artifact.add(impl.representations.size());
  for (const auto &r : impl.representations) {
    artifact.add(r.first);
    artifact.add(identity(r.second));
  }
  artifact.add("statics");
  artifact.add(impl.statics.size());
  for (const auto &s : impl.statics) {
    artifact.add(s.first);
    artifact.add(identity(s.second));
  }
  artifact.add("functions");
  artifact.add(impl.functions.size());
  for (const auto &f : impl.functions) {
    artifact.add(f.first);
    artifact.add(f.second.identity());
  }
  artifact.add("dependencies");
  artifact.add(node->scope.components.size());
  for (const auto &dep : node->scope.components) {
    artifact.add(dep.first);
    artifact.add(dep.second->key);
    artifact.add(dep.second->artifact);
  }
  node->artifact = artifact.bytes;
  auto previous = byKey.find(node->key);
  if (previous != byKey.end()) {
    if (previous->second->artifact != node->artifact)
      return fail("library-diamond-conflict",
                  "one selection has conflicting bodies/layouts via " +
                      previous->second->paths.front() + " and " + path);
    previous->second->paths.push_back(path);
    active.erase(pointer);
    resolved.emplace(pointer, previous->second);
    return previous->second;
  }
  // Same apparent component term cannot hide different extra actual bindings.
  // Callers must supply explicit applications/seals to distinguish them.
  for (const auto &old : selections) {
    auto oldKey = selectionIdentity(old->selected, environment);
    if (!oldKey)
      return oldKey.takeError();
    if (*oldKey == *base && old->key != node->key)
      return fail("library-selection-capture",
                  "same selection spelling hides different actual/dependency "
                  "captures via " +
                      old->paths.front() + " and " + path);
  }
  Selection *out = node.get();
  out->scope.self = out;
  selections.push_back(std::move(node));
  byKey.emplace(out->key, out);
  active.erase(pointer);
  resolved.emplace(pointer, out);
  return out;
}
llvm::Expected<Selection *> World::component(const StaticTerm &t,
                                             const LinkScope &scope) {
  if (scope.self &&
      (identity(t) ==
           identity(scope.self->implementation.interface.declaration().self) ||
       identity(t) == identity(scope.self->selected)))
    return scope.self;
  auto exact = scope.components.find(identity(t));
  if (exact != scope.components.end())
    return exact->second;
  auto closed = term(t, scope);
  if (!closed)
    return closed.takeError();
  auto key = selectionIdentity(*closed, environment);
  if (!key)
    return key.takeError();
  for (const auto &binding : scope.components) {
    const auto *s = binding.second;
    auto candidate = selectionIdentity(s->selected, environment);
    if (!candidate)
      return candidate.takeError();
    if (*candidate == *key)
      return binding.second;
  }
  return fail("library-selection",
              "no selected implementation for component term");
}
llvm::Expected<StaticTerm> World::term(const StaticTerm &t,
                                       const LinkScope &scope, unsigned depth) {
  if (depth > 128)
    return fail("library-substitution-cycle",
                "static substitution exceeds depth");
  for (const auto &p : scope.arguments.statics)
    if (identity(p.first) == identity(t))
      return term(p.second, scope, depth + 1);
  if (scope.self &&
      identity(t) ==
          identity(scope.self->implementation.interface.declaration().self))
    return scope.self->selected;
  auto imported = scope.components.find(identity(t));
  if (imported != scope.components.end())
    return imported->second->selected;
  if (t.kind == StaticTerm::Kind::Project && t.arguments.size() == 1) {
    // Resolve projections against the selected associated-member definition.
    Selection *owner = nullptr;
    if (scope.self &&
        (identity(t.arguments[0]) ==
             identity(
                 scope.self->implementation.interface.declaration().self) ||
         identity(t.arguments[0]) == identity(scope.self->selected)))
      owner = scope.self;
    auto dep = scope.components.find(identity(t.arguments[0]));
    if (dep != scope.components.end())
      owner = dep->second;
    if (!owner)
      for (const auto &binding : scope.components)
        if (identity(binding.second->selected) == identity(t.arguments[0]))
          owner = binding.second;
    if (owner) {
      auto m = owner->implementation.statics.find(t.member);
      if (m == owner->implementation.statics.end())
        return fail("library-static-member",
                    "missing selected static member " + t.member);
      return term(m->second, owner->scope, depth + 1);
    }
  }
  StaticTerm out = t;
  for (auto &a : out.arguments) {
    auto actual = term(a, scope, depth + 1);
    if (!actual)
      return actual.takeError();
    a = *actual;
  }
  if (out.kind == StaticTerm::Kind::Project && out.arguments.size() == 1) {
    auto parent = selectionIdentity(out.arguments[0], environment);
    if (!parent)
      return parent.takeError();
    for (const auto &binding : scope.components) {
      const auto *selected = binding.second;
      auto candidate = selectionIdentity(selected->selected, environment);
      if (!candidate)
        return candidate.takeError();
      if (*parent != *candidate)
        continue;
      auto member = selected->implementation.statics.find(out.member);
      if (member == selected->implementation.statics.end())
        return fail("library-static-member",
                    "missing selected member " + out.member);
      return term(member->second, selected->scope, depth + 1);
    }
  }
  if (out.kind == StaticTerm::Kind::Project && out.arguments.size() == 1) {
    auto parentSort = sortOf(out.arguments[0], environment);
    if (!parentSort)
      return parentSort.takeError();
    if (parentSort->kind == Sort::Kind::Component)
      return fail("library-selection",
                  "associated member has no lexical component binding");
  }
  auto s = sortOf(out, environment);
  if (!s)
    return s.takeError();
  if (out.kind == StaticTerm::Kind::Root) {
    const auto *d = findStatic(out.declaration, environment);
    if (d && d->parameter)
      return fail("library-open-term", "unselected parameter " + d->id.name);
  }
  return out;
}
std::string functionSymbol(const Selection &s, llvm::StringRef member) {
  // A digest is a readable locator only. link() separately checks symbol
  // collisions against exact content before constructing LinkedProgram.
  Writer w;
  w.add(s.key);
  w.add(member);
  return "lib_" + hash(w.bytes);
}
} // namespace zkc::frontend::library::detail
