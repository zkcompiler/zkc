#include "LinkInternal.h"
#include <algorithm>

namespace zkc::frontend::library {
namespace detail {
namespace {
// Expand only after the generic region has checked. Aliases substitute semantic
// paths; every iteration gets fresh definitions, including nested arm
// parameters.
llvm::Error expandTraversals(Body &body, World &world, const LinkScope &scope) {
  uint64_t next = 0;
  std::map<uint32_t, Type> types;
  std::function<void(const Region &)> collect = [&](const Region &r) {
    auto value = [&](const Value &v) {
      next = std::max(next, uint64_t(v.id.index) + 1);
      types.emplace(v.id.index, v.port.type);
    };
    for (const auto &v : r.inputs)
      value(v);
    for (const auto &i : r.instructions) {
      std::visit(
          [&](const auto &n) {
            using T = std::decay_t<decltype(n)>;
            if constexpr (std::is_same_v<T, Conditional>) {
              for (const auto &v : n.branches.outputs)
                value(v);
              for (const auto &a : n.branches.arms)
                collect(*a.body);
            } else if constexpr (std::is_same_v<T, Call> ||
                                 std::is_same_v<T, Match> ||
                                 std::is_same_v<T, ArrayTraversal>) {
              for (const auto &v : n.outputs)
                value(v);
              if constexpr (std::is_same_v<T, Match>)
                for (const auto &a : n.arms)
                  collect(*a.body);
              if constexpr (std::is_same_v<T, ArrayTraversal>) {
                if (n.collected)
                  value(*n.collected);
                collect(*n.body);
              }
            } else if constexpr (!std::is_same_v<T, Drop> &&
                                 !std::is_same_v<T, Stop>)
              value(n.output);
          },
          i);
    }
  };
  Region root{body.inputs, body.instructions, body.returns};
  collect(root);
  using Aliases = std::map<uint32_t, Place>;
  uint64_t steps = 0;
  bool exhaustedIds = false;
  auto replacePlace = [](Place p, const Aliases &aliases) {
    auto f = aliases.find(p.value.index);
    if (f != aliases.end()) {
      auto path = f->second.path;
      path.insert(path.end(), p.path.begin(), p.path.end());
      p = {f->second.value, std::move(path)};
    }
    return p;
  };
  std::function<llvm::Expected<Region>(const Region &, Aliases, bool, bool)>
      expand;
  expand = [&](const Region &r, Aliases aliases, bool fresh,
               bool bindInputs) -> llvm::Expected<Region> {
    Region result;
    // Set once the expanded prefix provably stops: the remaining instructions
    // and the returns of this region are then unreachable and not emitted.
    bool stops = false;
    auto value = [&](Value v) {
      if (fresh) {
        if (next >= uint64_t(UINT32_MAX)) {
          exhaustedIds = true;
          return v;
        }
        auto old = v.id;
        v.id.index = next++;
        aliases[old.index] = {v.id, {}};
      }
      types.emplace(v.id.index, v.port.type);
      return v;
    };
    if (bindInputs)
      for (const auto &v : r.inputs)
        result.inputs.push_back(value(v));
    auto places = [&](std::vector<Place> &ps) {
      for (auto &p : ps)
        p = replacePlace(p, aliases);
    };
    for (auto instruction : r.instructions) {
      if (exhaustedIds)
        return fail("library-limit", "expanded ValueId space exhausted");
      if (++steps > world.environment.expansionLimit)
        return fail("library-limit",
                    "expanded region exceeds instruction limit");
      if (auto *a = std::get_if<ArrayTraversal>(&instruction)) {
        Place input = replacePlace(a->input, aliases);
        auto actual = world.publicType(types.at(input.value.index), scope);
        if (!actual)
          return actual.takeError();
        const std::vector<Import> imports;
        const std::vector<TypeBound> bounds;
        auto selected =
            placeType(*actual, input.path,
                      TypeContext{world.environment, imports, bounds});
        if (!selected)
          return selected.takeError();
        const auto &count = selected->arguments.front();
        if (count.kind != StaticTerm::Kind::Natural)
          return fail("library-array-unresolved",
                      "traversal count remains symbolic");
        if (count.number > world.environment.expansionLimit)
          return fail("library-limit",
                      "traversal count exceeds expansion limit");
        places(a->initial);
        places(a->captures);
        auto carried = a->initial;
        std::vector<Place> collected;
        for (uint64_t index = 0; index < count.number && !stops; ++index) {
          Aliases args;
          Place element = input;
          element.path.push_back(index);
          args.emplace(a->body->inputs[0].id.index, element);
          size_t formal = 1;
          for (const auto &p : carried)
            args.emplace(a->body->inputs[formal++].id.index, p);
          for (const auto &p : a->captures)
            args.emplace(a->body->inputs[formal++].id.index, p);
          auto iteration = expand(*a->body, std::move(args), true, false);
          if (!iteration)
            return iteration.takeError();
          result.instructions.insert(result.instructions.end(),
                                     iteration->instructions.begin(),
                                     iteration->instructions.end());
          // A trip that stops ends the whole computation. Later trips and the
          // carried state after it are unreachable; a zero-trip traversal never
          // enters the body and still transfers the initial state below.
          stops = terminal(iteration->instructions);
          carried = std::move(iteration->returns);
          if (!stops && a->collected) {
            collected.push_back(carried.back());
            carried.pop_back();
          }
        }
        if (stops)
          break;
        for (size_t i = 0; i < a->outputs.size(); ++i) {
          auto output = value(a->outputs[i]);
          result.instructions.push_back(Project{carried[i], output});
          if (++steps > world.environment.expansionLimit)
            return fail("library-limit",
                        "expanded state transfer exceeds limit");
        }
        if (a->collected) {
          result.instructions.push_back(
              Construct{value(*a->collected), std::move(collected)});
          if (++steps > world.environment.expansionLimit)
            return fail("library-limit", "expanded collection exceeds limit");
        }
        continue;
      }
      if (auto *c = std::get_if<Call>(&instruction)) {
        places(c->inputs);
        for (auto &v : c->outputs)
          v = value(v);
      } else if (auto *c = std::get_if<Construct>(&instruction)) {
        places(c->elements);
        c->output = value(c->output);
      } else if (auto *p = std::get_if<Project>(&instruction)) {
        p->input = replacePlace(p->input, aliases);
        p->output = value(p->output);
      } else if (auto *d = std::get_if<Drop>(&instruction)) {
        d->input = replacePlace(d->input, aliases);
      } else if (auto *c = std::get_if<VariantConstruct>(&instruction)) {
        c->payload = replacePlace(c->payload, aliases);
        c->output = value(c->output);
      } else if (auto *m = branches(instruction)) {
        m->input = replacePlace(m->input, aliases);
        places(m->captures);
        for (auto &v : m->outputs)
          v = value(v);
        bool continues = false;
        for (auto &arm : m->arms) {
          auto region = expand(*arm.body, {}, fresh, true);
          if (!region)
            return region.takeError();
          continues |= !terminal(region->instructions);
          arm.body = std::make_shared<const Region>(std::move(*region));
        }
        // A selected terminal expansion has no reachable result consumers.
        if (!continues)
          m->outputs.clear();
        stops = !continues;
      } else if (std::holds_alternative<Stop>(instruction))
        stops = true;
      result.instructions.push_back(std::move(instruction));
      if (stops)
        break;
    }
    if (exhaustedIds)
      return fail("library-limit", "expanded ValueId space exhausted");
    if (stops)
      return result;
    result.returns = r.returns;
    places(result.returns);
    return result;
  };
  auto expanded = expand(root, {}, false, true);
  if (!expanded)
    return expanded.takeError();
  body.instructions = std::move(expanded->instructions);
  body.returns = std::move(expanded->returns);
  return llvm::Error::success();
}
bool under(llvm::ArrayRef<unsigned> path, llvm::ArrayRef<unsigned> leaf) {
  return path.size() <= leaf.size() &&
         std::equal(path.begin(), path.end(), leaf.begin());
}
std::vector<LayoutLeaf> selectedLeaves(const LinkedFunction &f,
                                       const Place &p) {
  std::vector<LayoutLeaf> out;
  for (auto leaf : f.values.at(p.value.index).leaves)
    if (under(p.path, leaf.path)) {
      leaf.path.erase(leaf.path.begin(), leaf.path.begin() + p.path.size());
      out.push_back(std::move(leaf));
    }
  return out;
}
bool compatibleLeaves(const std::vector<LayoutLeaf> &a,
                      const std::vector<LayoutLeaf> &b,
                      const Environment &environment) {
  if (a.size() != b.size())
    return false;
  for (size_t i = 0; i < a.size(); ++i) {
    if (a[i].kind != b[i].kind ||
        a[i].resourceIdentity != b[i].resourceIdentity)
      return false;
    if (a[i].kind == LayoutLeaf::Kind::Variant) {
      if (a[i].variantIdentity != b[i].variantIdentity ||
          a[i].type.fields != b[i].type.fields ||
          identity(a[i].type.declaration) != identity(b[i].type.declaration) ||
          a[i].alternatives.size() != b[i].alternatives.size() ||
          a[i].permissions.copy != b[i].permissions.copy ||
          a[i].permissions.drop != b[i].permissions.drop)
        return false;
      for (size_t j = 0; j < a[i].alternatives.size(); ++j)
        if (!compatibleLeaves(a[i].alternatives[j], b[i].alternatives[j],
                              environment))
          return false;
    }
    if (a[i].kind == LayoutLeaf::Kind::Logical) {
      if (auto err = equalTypes(a[i].type, b[i].type, {}, environment)) {
        llvm::consumeError(std::move(err));
        return false;
      }
    }
  }
  return true;
}
bool onlyResources(const std::vector<LayoutLeaf> &leaves) {
  return !leaves.empty() &&
         std::all_of(leaves.begin(), leaves.end(), [](const auto &l) {
           return l.kind == LayoutLeaf::Kind::ResourceUnit;
         });
}
bool refineVariantPermissions(std::vector<LayoutLeaf> &leaves) {
  bool changed = false;
  for (auto &leaf : leaves) {
    if (leaf.kind != LayoutLeaf::Kind::Variant)
      continue;
    // Payload refinement can expose hidden ownership. Meet all alternatives,
    // recursively, with the existing schema permission: an inserted droppable
    // unit never grants drop to a schema or another payload that denies it.
    auto permission = leaf.permissions;
    for (auto &alternative : leaf.alternatives) {
      changed |= refineVariantPermissions(alternative);
      for (const auto &payload : alternative) {
        permission.copy &= payload.permissions.copy;
        permission.drop &= payload.permissions.drop;
      }
    }
    changed |= permission.copy != leaf.permissions.copy ||
               permission.drop != leaf.permissions.drop;
    leaf.permissions = permission;
  }
  return changed;
}
// Checked representation equality leaves linking only zero-storage units to
// reconcile, and adaptation inserts their creation, transfer and disposal at
// every edge. A layout that still disagrees afterwards is a linker defect, not
// a property of the source, so it stops the compiler instead of refusing.
[[noreturn]] void linkerDefect(const llvm::Twine &what) {
  llvm::report_fatal_error("library linking: " + what);
}
bool abstractType(const Type &t) {
  return t.kind == Type::Kind::Abstract ||
         std::any_of(t.elements.begin(), t.elements.end(), abstractType);
}
// Resource propagation only ever adds a resource unit, gives a concrete variant
// schema the opaque public identity it corresponds to, or clears a permission.
// This counts those facts; there are finitely many for a function's types.
size_t propagatedFacts(const std::vector<LayoutLeaf> &leaves) {
  size_t facts = 0;
  for (const auto &leaf : leaves) {
    facts += 1 + !leaf.permissions.copy + !leaf.permissions.drop;
    if (leaf.kind != LayoutLeaf::Kind::Variant)
      continue;
    facts += abstractType(leaf.type);
    for (const auto &alternative : leaf.alternatives)
      facts += propagatedFacts(alternative);
  }
  return facts;
}
llvm::Error refineResourcePaths(LinkedFunction &f,
                                const Environment &environment,
                                bool propagate = true) {
  // Propagate ownership forward through concrete projections and aggregates.
  // A join's result may need a token absent from one arm; reconcile that arm
  // with an explicit creation, never by widening its plain public inputs.
  // Variant schemas retain their existing bidirectional correspondence.
  std::vector<const Instruction *> instructions;
  std::vector<Place> returns = f.body.returns;
  std::function<void(const std::vector<Instruction> &)> collect =
      [&](const auto &is) {
        for (const auto &i : is) {
          instructions.push_back(&i);
          if (const auto *m = branches(i))
            for (const auto &arm : m->arms) {
              collect(arm.body->instructions);
              // A stopping arm has no yields; its remaining values are the
              // runtime's to release, never a public result of this function.
              returns.insert(returns.end(), arm.body->returns.begin(),
                             arm.body->returns.end());
            }
        }
      };
  collect(f.body.instructions);
  auto facts = [&] {
    size_t count = 0;
    for (const auto &value : f.values)
      count += propagatedFacts(value.second.leaves);
    return count;
  };
  size_t established = facts();
  bool changed = propagate;
  while (changed) {
    changed = false;
    // Representation correspondence crosses region boundaries without exposing
    // inactive payloads. Public zero-storage tokens flow to exactly the active
    // constructor operand / arm parameter and through continuing yields.
    std::function<void(std::vector<LayoutLeaf> &, std::vector<LayoutLeaf> &,
                       bool)>
        merge;
    merge = [&](auto &a, auto &b, bool variantPayload) {
      // Empty subobjects can occur beside stored leaves. Reconcile them by
      // semantic path, not by flattened position (which omits empty fields).
      auto retain = [&](const auto &from, auto &to) {
        for (const auto &leaf : from)
          if (leaf.kind == LayoutLeaf::Kind::ResourceUnit &&
              std::none_of(to.begin(), to.end(), [&](const auto &other) {
                return other.path == leaf.path;
              })) {
            to.push_back(leaf);
            changed = true;
          }
        std::stable_sort(
            to.begin(), to.end(),
            [](const auto &x, const auto &y) { return x.path < y.path; });
      };
      retain(a, b);
      if (variantPayload)
        retain(b, a);
      if (a.size() != b.size())
        return;
      for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].kind != LayoutLeaf::Kind::Variant ||
            b[i].kind != LayoutLeaf::Kind::Variant ||
            a[i].alternatives.size() != b[i].alternatives.size())
          continue;
        // A public schema can retain an opaque slot where its checked private
        // body uses a concrete payload. Propagate that boundary identity; two
        // different public schemas never acquire equality from shared storage.
        if (a[i].variantIdentity != b[i].variantIdentity) {
          bool ac = abstractType(a[i].type), bc = abstractType(b[i].type);
          if (ac != bc) {
            auto &from = ac ? a[i] : b[i];
            auto &to = ac ? b[i] : a[i];
            to.type = from.type;
            to.variantIdentity = from.variantIdentity;
            changed = true;
          }
        }
        for (size_t j = 0; j < a[i].alternatives.size(); ++j)
          merge(a[i].alternatives[j], b[i].alternatives[j], true);
        const Permissions p{a[i].permissions.copy && b[i].permissions.copy,
                            a[i].permissions.drop && b[i].permissions.drop};
        if (a[i].permissions.copy != p.copy ||
            a[i].permissions.drop != p.drop ||
            b[i].permissions.copy != p.copy || b[i].permissions.drop != p.drop)
          changed = true;
        a[i].permissions = b[i].permissions = p;
      }
    };
    auto edge = [&](const Place &p, std::vector<LayoutLeaf> &output) {
      auto input = selectedLeaves(f, p);
      auto old = input;
      merge(input, output, false);
      if (!compatibleLeaves(old, input, environment)) {
        auto &source = f.values.at(p.value.index).leaves;
        source.erase(std::remove_if(source.begin(), source.end(),
                                    [&](const auto &leaf) {
                                      return under(p.path, leaf.path);
                                    }),
                     source.end());
        for (auto leaf : input) {
          leaf.path.insert(leaf.path.begin(), p.path.begin(), p.path.end());
          source.push_back(std::move(leaf));
        }
        std::stable_sort(
            source.begin(), source.end(),
            [](const auto &a, const auto &b) { return a.path < b.path; });
      }
    };
    for (const auto *instruction : instructions) {
      if (const auto *p = std::get_if<Project>(instruction)) {
        edge(p->input, f.values.at(p->output.id.index).leaves);
      } else if (const auto *c = std::get_if<Construct>(instruction)) {
        auto &result = f.values.at(c->output.id.index).leaves;
        // A unit constructor creates its own token; an aggregate transports
        // the tokens of its actual elements, including empty nested fields.
        for (size_t j = 0; j < c->elements.size(); ++j) {
          Place field{c->output.id, {unsigned(j)}};
          auto leaves = selectedLeaves(f, field);
          edge(c->elements[j], leaves);
          result.erase(std::remove_if(result.begin(), result.end(),
                                      [&](const auto &leaf) {
                                        return under(field.path, leaf.path);
                                      }),
                       result.end());
          for (auto leaf : leaves) {
            leaf.path.insert(leaf.path.begin(), unsigned(j));
            result.push_back(std::move(leaf));
          }
        }
        std::stable_sort(
            result.begin(), result.end(),
            [](const auto &a, const auto &b) { return a.path < b.path; });
      } else if (const auto *c = std::get_if<VariantConstruct>(instruction)) {
        auto &ls = f.values.at(c->output.id.index).leaves;
        if (ls.size() == 1 && ls[0].kind == LayoutLeaf::Kind::Variant) {
          auto alt = std::find(ls[0].type.fields.begin(),
                               ls[0].type.fields.end(), c->alternative);
          if (alt != ls[0].type.fields.end())
            edge(c->payload,
                 ls[0].alternatives[alt - ls[0].type.fields.begin()]);
        }
      } else if (const auto *m = branches(*instruction)) {
        bool conditional = std::holds_alternative<Conditional>(*instruction);
        auto ls = selectedLeaves(f, m->input);
        if (!conditional &&
            (ls.size() != 1 || ls[0].kind != LayoutLeaf::Kind::Variant))
          continue;
        for (const auto &arm : m->arms) {
          if (!conditional) {
            auto alt = std::find(ls[0].type.fields.begin(),
                                 ls[0].type.fields.end(), arm.alternative);
            if (alt != ls[0].type.fields.end())
              merge(ls[0].alternatives[alt - ls[0].type.fields.begin()],
                    f.values.at(arm.body->inputs[0].id.index).leaves, false);
          }
          for (size_t j = 0; j < m->captures.size(); ++j)
            edge(m->captures[j],
                 f.values
                     .at(arm.body->inputs[j + (conditional ? 0 : 1)].id.index)
                     .leaves);
          // Only a continuing arm has yields to correspond with the join.
          for (size_t j = 0;
               j < m->outputs.size() && j < arm.body->returns.size(); ++j)
            edge(arm.body->returns[j],
                 f.values.at(m->outputs[j].id.index).leaves);
        }
        edge(m->input, ls);
      }
    }
    for (auto &value : f.values)
      changed |= refineVariantPermissions(value.second.leaves);
    // Every step moves a fact one way, so a round that reports a change without
    // establishing one would repeat forever. That is a linker defect.
    if (changed) {
      size_t now = facts();
      if (now <= established)
        llvm::report_fatal_error(
            "library resource propagation reported a change without progress");
      established = now;
    }
  }
  if (propagate)
    return llvm::Error::success();
  std::map<uint32_t, std::set<size_t>> consumed;
  auto use = [&](const Place &p) -> llvm::Error {
    const auto &ls = f.values.at(p.value.index).leaves;
    for (size_t j = 0; j < ls.size(); ++j)
      if ((ls[j].kind == LayoutLeaf::Kind::ResourceUnit ||
           (ls[j].kind == LayoutLeaf::Kind::Variant &&
            !ls[j].permissions.copy)) &&
          under(p.path, ls[j].path) &&
          !consumed[p.value.index].insert(j).second)
        return fail(
            "library-resource-use",
            "private representation duplicates a logical resource unit");
    return llvm::Error::success();
  };
  for (const auto *instruction : instructions) {
    const auto &i = *instruction;
    if (const auto *p = std::get_if<Project>(&i)) {
      if (!compatibleLeaves(selectedLeaves(f, p->input),
                            f.values.at(p->output.id.index).leaves,
                            environment))
        linkerDefect("projection changes logical resource layout");
      if (auto e = use(p->input))
        return e;
    } else if (const auto *c = std::get_if<Construct>(&i)) {
      std::vector<LayoutLeaf> operands;
      for (const auto &p : c->elements) {
        if (auto e = use(p))
          return e;
        auto ls = selectedLeaves(f, p);
        operands.insert(operands.end(), ls.begin(), ls.end());
      }
      const auto &result = f.values.at(c->output.id.index).leaves;
      if (!(operands.empty() && onlyResources(result)) &&
          !compatibleLeaves(operands, result, environment))
        linkerDefect("aggregate changes logical resource layout");
    } else if (const auto *c = std::get_if<Call>(&i)) {
      for (const auto &p : c->inputs)
        if (auto e = use(p))
          return e;
    } else if (const auto *d = std::get_if<Drop>(&i)) {
      if (auto e = use(d->input))
        return e;
    } else if (const auto *c = std::get_if<VariantConstruct>(&i)) {
      const auto &ls = f.values.at(c->output.id.index).leaves;
      if (ls.size() != 1 || ls[0].kind != LayoutLeaf::Kind::Variant)
        linkerDefect("variant constructor has no variant layout");
      auto alt = std::find(ls[0].type.fields.begin(), ls[0].type.fields.end(),
                           c->alternative);
      if (alt == ls[0].type.fields.end() ||
          !compatibleLeaves(selectedLeaves(f, c->payload),
                            ls[0].alternatives[alt - ls[0].type.fields.begin()],
                            environment))
        linkerDefect("active payload layout differs");
      if (auto e = use(c->payload))
        return e;
    } else if (const auto *m = branches(i)) {
      bool conditional = std::holds_alternative<Conditional>(i);
      auto ls = selectedLeaves(f, m->input);
      if (!conditional &&
          (ls.size() != 1 || ls[0].kind != LayoutLeaf::Kind::Variant))
        linkerDefect("match has no variant layout");
      if (auto e = use(m->input))
        return e;
      for (const auto &p : m->captures)
        if (auto e = use(p))
          return e;
      for (const auto &arm : m->arms) {
        if (!conditional) {
          auto alt = std::find(ls[0].type.fields.begin(),
                               ls[0].type.fields.end(), arm.alternative);
          if (alt == ls[0].type.fields.end() ||
              !compatibleLeaves(
                  f.values.at(arm.body->inputs[0].id.index).leaves,
                  ls[0].alternatives[alt - ls[0].type.fields.begin()],
                  environment))
            linkerDefect("arm active payload layout differs");
        }
        for (size_t j = 0; j < m->captures.size(); ++j)
          if (!compatibleLeaves(
                  selectedLeaves(f, m->captures[j]),
                  f.values
                      .at(arm.body->inputs[j + (conditional ? 0 : 1)].id.index)
                      .leaves,
                  environment))
            linkerDefect("arm capture layout differs");
        if (terminal(arm.body->instructions))
          continue;
        for (size_t j = 0; j < m->outputs.size(); ++j)
          if (!compatibleLeaves(selectedLeaves(f, arm.body->returns[j]),
                                f.values.at(m->outputs[j].id.index).leaves,
                                environment))
            linkerDefect("arm result layout differs");
      }
    }
  }
  for (const auto &p : returns)
    if (auto e = use(p))
      return e;
  return llvm::Error::success();
}
// A checked representation equality is not a resource identity equality.
// Adapt zero-storage leaves with ordinary ownership operations, descending
// through identical nominal variants by matching and rebuilding active
// payloads. The common carrier independently checks these operations; stored
// leaves agree. Keeping this at edges avoids assigning two nominal slots to one
// ValueId, or propagating a newly created result token back into a plain public
// input.
struct ResourceAdapters {
  LinkedFunction &function;
  const Environment &environment;
  uint64_t next = 0, work = 0;

  ResourceAdapters(LinkedFunction &f, const Environment &e)
      : function(f), environment(e) {
    for (const auto &v : f.values)
      next = std::max(next, uint64_t(v.first) + 1);
  }
  llvm::Expected<Value> fresh(const Layout &layout, const std::string &role) {
    if (next >= uint64_t(UINT32_MAX) || ++work > environment.expansionLimit)
      return fail("library-limit", "resource adapters exceed expansion limit");
    Value value{{uint32_t(next++)}, {layout.concreteType, role}};
    function.values.emplace(value.id.index, layout);
    return value;
  }
  llvm::Expected<Place> adapt(const Place &input, const Layout &expected,
                              const std::string &role,
                              std::vector<Instruction> &instructions,
                              unsigned depth = 0) {
    if (depth > 128)
      return fail("library-limit", "resource adapter recursion exceeds limit");
    auto actual = selectedLeaves(function, input);
    if (compatibleLeaves(actual, expected.leaves, environment) &&
        std::equal(
            actual.begin(), actual.end(), expected.leaves.begin(),
            [](const auto &a, const auto &b) { return a.path == b.path; }))
      return input;
    std::vector<bool> used(actual.size(), false);
    std::vector<Place> elements;
    auto select = [&](const LayoutLeaf &leaf) {
      Place place = input;
      place.path.insert(place.path.end(), leaf.path.begin(), leaf.path.end());
      return place;
    };
    for (auto leaf : expected.leaves) {
      if (++work > environment.expansionLimit)
        return fail("library-limit",
                    "resource adapters exceed expansion limit");
      auto found =
          std::find_if(actual.begin(), actual.end(), [&](const auto &a) {
            return a.path == leaf.path &&
                   compatibleLeaves({a}, {leaf}, environment);
          });
      if (found != actual.end()) {
        used[found - actual.begin()] = true;
        elements.push_back(select(*found));
      } else {
        auto variant =
            std::find_if(actual.begin(), actual.end(), [&](const auto &a) {
              return a.path == leaf.path &&
                     a.kind == LayoutLeaf::Kind::Variant &&
                     leaf.kind == LayoutLeaf::Kind::Variant;
            });
        if (variant != actual.end()) {
          const std::vector<Import> imports;
          const std::vector<TypeBound> bounds;
          auto concrete = placeType(expected.concreteType, leaf.path,
                                    TypeContext{environment, imports, bounds});
          if (!concrete)
            return concrete.takeError();
          auto value = adaptVariant(select(*variant), *variant, leaf, *concrete,
                                    role, instructions, depth + 1);
          if (!value)
            return value.takeError();
          used[variant - actual.begin()] = true;
          elements.push_back(*value);
          continue;
        }
        if (leaf.kind != LayoutLeaf::Kind::ResourceUnit)
          linkerDefect(
              "representation adapter changes stored or variant layout");
        leaf.path.clear();
        Layout unit{leaf.type, Type::product({}), {leaf}};
        auto value = fresh(unit, role);
        if (!value)
          return value.takeError();
        instructions.push_back(Construct{*value, {}});
        elements.push_back({value->id, {}});
      }
    }
    for (size_t i = 0; i < actual.size(); ++i)
      if (!used[i]) {
        if (actual[i].kind != LayoutLeaf::Kind::ResourceUnit ||
            !actual[i].permissions.drop)
          linkerDefect(
              "representation adapter discards a stored or linear leaf");
        instructions.push_back(Drop{select(actual[i])});
      }
    auto result = fresh(expected, role);
    if (!result)
      return result.takeError();
    instructions.push_back(Construct{*result, std::move(elements)});
    return Place{result->id, {}};
  }
  llvm::Expected<Place> adaptVariant(const Place &input, const LayoutLeaf &from,
                                     LayoutLeaf to, const Type &concrete,
                                     const std::string &role,
                                     std::vector<Instruction> &instructions,
                                     unsigned depth) {
    // Only an already-known, identical nominal schema may be reconstructed.
    // Inactive alternatives are never inspected at runtime. Each isolated arm
    // moves its active payload through the same zero-storage adapter, which
    // cannot discard stored leaves or manufacture another nominal variant.
    if (from.variantIdentity != to.variantIdentity ||
        identity(from.type.declaration) != identity(to.type.declaration) ||
        from.type.fields != to.type.fields ||
        from.alternatives.size() != to.alternatives.size())
      linkerDefect("variant adapter changes nominal schema");
    const std::vector<Import> imports;
    const std::vector<TypeBound> bounds;
    auto source =
        placeType(function.values.at(input.value.index).concreteType,
                  input.path, TypeContext{environment, imports, bounds});
    if (!source)
      return source.takeError();
    if (source->kind != Type::Kind::Variant ||
        concrete.kind != Type::Kind::Variant ||
        source->elements.size() != from.alternatives.size() ||
        concrete.elements.size() != to.alternatives.size())
      linkerDefect("variant adapter has no concrete schema");
    to.path.clear();
    Layout resultLayout{to.type, concrete, {to}};
    auto result = fresh(resultLayout, role);
    if (!result)
      return result.takeError();
    Match match{input, role, {}, {*result}, {}};
    for (size_t i = 0; i < from.alternatives.size(); ++i) {
      auto arm = std::make_shared<Region>();
      Layout payload{from.type.elements[i], source->elements[i],
                     from.alternatives[i]};
      auto parameter = fresh(payload, role);
      if (!parameter)
        return parameter.takeError();
      arm->inputs.push_back(*parameter);
      Layout expected{to.type.elements[i], concrete.elements[i],
                      to.alternatives[i]};
      auto adapted =
          adapt({parameter->id, {}}, expected, role, arm->instructions, depth);
      if (!adapted)
        return adapted.takeError();
      auto output = fresh(resultLayout, role);
      if (!output)
        return output.takeError();
      arm->instructions.push_back(
          VariantConstruct{*output, to.type.fields[i], *adapted});
      arm->returns.push_back({output->id, {}});
      match.arms.push_back({to.type.fields[i], std::move(arm)});
    }
    instructions.push_back(std::move(match));
    return Place{result->id, {}};
  }
};
} // namespace
llvm::Expected<std::string> World::helper(const SourceCall &call,
                                          const LinkScope &caller) {
  const auto &contract = call.callable.declaration();
  const auto declaration = identity(contract.id);
  auto body = helpers.find(declaration);
  if (body == helpers.end())
    return fail("library-open-call",
                "missing checked source helper body " + contract.id.name);
  if (auto err = matchesCallable(call.callable, body->second))
    return err;
  if (activeHelpers.size() >= 128 || !activeHelpers.insert(declaration).second)
    return fail("library-call-cycle", "recursive source helper graph");
  if (auto err = merge(body->second.environment()))
    return err;
  LinkScope scope;
  Writer selection;
  selection.add("source-helper");
  selection.add(declaration);
  for (const auto &a : call.arguments.statics) {
    auto sort = sortOf(a.first, environment);
    if (!sort)
      return sort.takeError();
    selection.add(identity(a.first));
    if (sameSort(*sort, Sort::component())) {
      auto selected = component(a.second, caller);
      if (!selected)
        return selected.takeError();
      scope.components.emplace(identity(a.first), *selected);
      selection.add((*selected)->key);
    } else {
      auto selected = term(a.second, caller);
      if (!selected)
        return selected.takeError();
      scope.arguments.statics.push_back({a.first, *selected});
      auto key = selectionIdentity(*selected, environment);
      if (!key)
        return key.takeError();
      selection.add(*key);
    }
  }
  for (const auto &a : call.arguments.types) {
    auto selected = publicType(a.second, caller);
    if (!selected)
      return selected.takeError();
    scope.arguments.types.push_back({a.first, *selected});
    selection.add(identity(a.first));
    auto key = normalizedTypeIdentity(*selected, environment);
    if (!key)
      return key.takeError();
    selection.add(*key);
  }
  for (const auto &i : contract.imports) {
    auto selected = scope.components.find(identity(i.parameter));
    if (selected == scope.components.end() ||
        selected->second->implementation.interface.identity() !=
            i.interface.identity())
      return fail("library-interface-drift",
                  "linked helper violates component bound");
  }
  if (auto err = bounds(contract.typeBounds, scope))
    return err;
  Writer subject;
  subject.add(selection.bytes);
  subject.add(call.callable.identity());
  subject.add(body->second.identity());
  const auto symbol = "lib_" + hash(subject.bytes);
  auto [old, fresh] = helperSymbols.emplace(symbol, subject.bytes);
  // Distinct subjects with one symbol would be a SHA-256 collision.
  if (!fresh && old->second != subject.bytes)
    llvm::report_fatal_error("two helper subjects share one generated symbol");
  if (!helperFunctions.count(symbol)) {
    if (helperSymbols.size() > environment.expansionLimit)
      return fail("library-limit", "helper specialization count exceeds limit");
    auto linked = function(body->second, scope, symbol);
    if (!linked)
      return linked.takeError();
    linked->exactSubject = subject.bytes;
    helperFunctions.emplace(symbol, std::move(*linked));
  }
  DependencyRecord record;
  record.selection = record.normalizedSelection = selection.bytes;
  record.interfaceIdentity = call.callable.identity();
  record.implementationIdentity = subject.bytes;
  record.captureIdentity = body->second.identity();
  record.interfaceFingerprint = hash(record.interfaceIdentity);
  record.implementationFingerprint = hash(record.implementationIdentity);
  record.captureFingerprint = hash(record.captureIdentity);
  record.paths.push_back(contract.id.name);
  for (const auto &p : scope.components)
    record.dependencies.push_back(p.second->key);
  for (const auto &c : helperFunctions.at(symbol).calls)
    if (!c.second.logical)
      record.dependencies.push_back(c.second.target);
  auto [dependency, added] =
      helperDependencies.emplace(selection.bytes, record);
  if (!added && dependency->second.implementationIdentity !=
                    record.implementationIdentity)
    return fail("library-source-signature-drift",
                "incoherent helper contract or implementation");
  activeHelpers.erase(declaration);
  return symbol;
}
llvm::Expected<LinkedFunction> World::function(const CheckedBody &checked,
                                               const LinkScope &scope,
                                               std::string symbol,
                                               const Signature *publicSignature,
                                               const LinkScope *publicScope) {
  LinkedFunction out;
  out.symbol = std::move(symbol);
  out.body = checked.body();
  out.logicalSignature =
      publicSignature ? *publicSignature : checked.body().signature;
  const auto &logicalScope = publicScope ? *publicScope : scope;
  for (auto *ports :
       {&out.logicalSignature.inputs, &out.logicalSignature.outputs})
    for (auto &port : *ports) {
      auto selected = publicType(port.type, logicalScope);
      if (!selected)
        return selected.takeError();
      port.type = std::move(*selected);
    }
  for (auto *facts : {&out.logicalSignature.preconditions,
                      &out.logicalSignature.postconditions}) {
    auto selected = requirements(*facts, logicalScope);
    if (!selected)
      return selected.takeError();
    *facts = std::move(*selected);
  }
  if (auto err = expandTraversals(out.body, *this, scope))
    return err;
  auto sig = signature(out.body.signature, scope);
  if (!sig)
    return sig.takeError();
  out.body.signature = *sig;
  if (publicSignature)
    out.body.signature.inputLabels = publicSignature->inputLabels;
  out.body.typeBounds.clear();
  auto value = [&](Value &v) -> llvm::Error {
    auto l = layout(v.port.type, scope);
    if (!l)
      return l.takeError();
    v.port.type = l->concreteType;
    out.values.emplace(v.id.index, std::move(*l));
    return llvm::Error::success();
  };
  for (auto &v : out.body.inputs)
    if (auto err = value(v))
      return err;
  std::function<llvm::Error(std::vector<Instruction> &, std::vector<size_t>)>
      resolve;
  resolve = [&](std::vector<Instruction> &instructions,
                std::vector<size_t> prefix) -> llvm::Error {
    for (size_t i = 0; i < instructions.size(); ++i) {
      auto path = prefix;
      path.push_back(i);
      auto &instruction = instructions[i];
      if (auto *call = std::get_if<Call>(&instruction)) {
        LinkedCall target;
        if (auto *member = std::get_if<MemberCall>(&call->target)) {
          auto selected = component(member->component, scope);
          if (!selected)
            return selected.takeError();
          target.target = functionSymbol(**selected, member->member);
          member->component = (*selected)->selected;
        } else if (auto *source = std::get_if<SourceCall>(&call->target)) {
          auto selected = helper(*source, scope);
          if (!selected)
            return selected.takeError();
          target.target = std::move(*selected);
          for (auto &a : source->arguments.statics) {
            auto closed = term(a.second, scope);
            if (!closed)
              return closed.takeError();
            a.second = std::move(*closed);
          }
          for (auto &a : source->arguments.types) {
            auto closed = publicType(a.second, scope);
            if (!closed)
              return closed.takeError();
            a.second = std::move(*closed);
          }
        } else {
          auto &logical = std::get<LogicalCall>(call->target);
          target.logical = true;
          target.target = logical.operation;
          for (auto &a : logical.arguments) {
            auto closed = term(a, scope);
            if (!closed)
              return closed.takeError();
            a = *closed;
          }
          if (auto err =
                  checkAttributes(logical, call->attributes, environment))
            return err;
        }
        out.calls.emplace(path, std::move(target));
        for (auto &v : call->outputs)
          if (auto err = value(v))
            return err;
      } else if (auto *construct = std::get_if<Construct>(&instruction)) {
        if (auto err = value(construct->output))
          return err;
      } else if (auto *project = std::get_if<Project>(&instruction)) {
        if (auto err = value(project->output))
          return err;
      } else if (auto *c = std::get_if<VariantConstruct>(&instruction)) {
        if (auto err = value(c->output))
          return err;
      } else if (auto *m = branches(instruction)) {
        for (auto &v : m->outputs)
          if (auto err = value(v))
            return err;
        for (size_t j = 0; j < m->arms.size(); ++j) {
          auto r = std::make_shared<Region>(*m->arms[j].body);
          for (auto &v : r->inputs)
            if (auto err = value(v))
              return err;
          auto nested = path;
          nested.push_back(j);
          if (auto err = resolve(r->instructions, nested))
            return err;
          m->arms[j].body = std::move(r);
        }
      }
    }
    return llvm::Error::success();
  };
  if (auto err = resolve(out.body.instructions, {}))
    return err;
  // Inputs retain their public ownership. Results are adapted independently
  // at linked edges: a projected return or A -> B conversion must not overwrite
  // an existing value's nominal identity.
  if (publicSignature && publicScope) {
    for (size_t i = 0; i < out.body.inputs.size(); ++i) {
      auto expected = layout(publicSignature->inputs[i].type, *publicScope);
      if (!expected)
        return expected.takeError();
      out.values.insert_or_assign(out.body.inputs[i].id.index,
                                  std::move(*expected));
    }
    // Variants remain one nominal carrier with an active payload. Retain the
    // existing schema correspondence through constructors and matches; a flat
    // zero-storage adapter must never reinterpret an opaque variant carrier.
    for (size_t i = 0; i < out.body.returns.size(); ++i) {
      auto expected = layout(publicSignature->outputs[i].type, *publicScope);
      if (!expected)
        return expected.takeError();
      const auto &place = out.body.returns[i];
      auto &leaves = out.values.at(place.value.index).leaves;
      for (auto leaf : expected->leaves) {
        if (leaf.kind != LayoutLeaf::Kind::Variant)
          continue;
        leaf.path.insert(leaf.path.begin(), place.path.begin(),
                         place.path.end());
        auto found =
            std::find_if(leaves.begin(), leaves.end(), [&](const auto &a) {
              return a.path == leaf.path && a.kind == LayoutLeaf::Kind::Variant;
            });
        if (found != leaves.end())
          *found = std::move(leaf);
      }
    }
  }
  if (auto err = refineResourcePaths(out, environment))
    return err;
  // Representation propagation cannot add hidden ports to a public boundary.
  const auto &expectedSignature =
      publicSignature ? *publicSignature : checked.body().signature;
  const auto &expectedScope = publicScope ? *publicScope : scope;
  for (size_t i = 0; i < out.body.inputs.size(); ++i) {
    auto expected = layout(expectedSignature.inputs[i].type, expectedScope);
    if (!expected)
      return expected.takeError();
    if (!compatibleLeaves(out.values.at(out.body.inputs[i].id.index).leaves,
                          expected->leaves, environment))
      return fail("library-resource-boundary",
                  "private body changes public input resource layout");
  }
  // The promised results survive a body that always stops: it produces none of
  // them, and its callers still agree with the declared boundary.
  for (size_t i = 0; i < expectedSignature.outputs.size(); ++i) {
    auto expected = layout(expectedSignature.outputs[i].type, expectedScope);
    if (!expected)
      return expected.takeError();
    out.results.push_back(std::move(*expected));
  }
  if (!out.body.returns.empty() &&
      out.body.returns.size() != out.results.size())
    return fail("library-return", "linked body result count differs");
  return out;
}
} // namespace detail
struct LinkedProgram::Data {
  Environment environment;
  std::vector<LinkedFunction> functions;
  std::vector<DependencyRecord> dependencies;
  std::vector<Evidence> evidence;
  std::string entry, identity, fingerprint;
};
LinkedProgram::LinkedProgram(std::shared_ptr<const Data> d)
    : data(std::move(d)) {}
const Environment &LinkedProgram::environment() const {
  return data->environment;
}
const std::vector<LinkedFunction> &LinkedProgram::functions() const {
  return data->functions;
}
const std::vector<DependencyRecord> &LinkedProgram::dependencies() const {
  return data->dependencies;
}
const std::vector<Evidence> &LinkedProgram::evidence() const {
  return data->evidence;
}
const std::string &LinkedProgram::identity() const { return data->identity; }
const std::string &LinkedProgram::entry() const { return data->entry; }
const std::string &LinkedProgram::fingerprint() const {
  return data->fingerprint;
}
llvm::Expected<LinkedProgram> link(LinkRequest request) {
  using namespace detail;
  World world;
  if (request.selectionEnvironment)
    if (auto err = world.merge(*request.selectionEnvironment))
      return err;
  for (const auto &body : request.helpers) {
    auto [found, added] = world.helpers.emplace(identity(body.body().id), body);
    if (!added && found->second.identity() != body.identity())
      return fail("library-source-body-drift",
                  "conflicting checked helper bodies");
  }
  auto scope = world.scope(request.client, request.bindings, request.arguments,
                           "client");
  if (!scope)
    return scope.takeError();
  if (auto err = world.bounds(request.client.body().typeBounds, *scope))
    return err;
  for (auto &s : world.selections)
    if (auto err = world.conform(*s))
      return err;
  auto required =
      world.requirements(request.client.body().signature.preconditions, *scope);
  if (!required)
    return required.takeError();
  if (auto err = prove({}, *required, world.environment))
    return err;
  auto data = std::make_shared<LinkedProgram::Data>();
  Writer content;
  content.add(request.client.identity());
  content.add("client-bindings");
  content.add(scope->components.size());
  for (const auto &binding : scope->components) {
    content.add(binding.first);
    content.add(binding.second->key);
  }
  content.add(request.arguments.statics.size());
  for (const auto &a : request.arguments.statics) {
    auto actual = world.term(a.second, *scope);
    if (!actual)
      return actual.takeError();
    auto key = selectionIdentity(*actual, world.environment);
    if (!key)
      return key.takeError();
    content.add(identity(a.first));
    content.add(*key);
  }
  content.add(request.arguments.types.size());
  for (const auto &a : request.arguments.types) {
    auto permission = world.publicPermissions(a.second, *scope);
    if (!permission)
      return permission.takeError();
    auto actual = world.publicType(a.second, *scope);
    if (!actual)
      return actual.takeError();
    auto normalized = normalizedTypeIdentity(*actual, world.environment);
    if (!normalized)
      return normalized.takeError();
    content.add(identity(a.first));
    content.add(*normalized);
  }
  std::map<std::string, std::string> selectedContent;
  for (const auto &s : world.selections)
    selectedContent.emplace(s->key, s->artifact);
  content.list(selectedContent, [&](const auto &s) {
    content.add(s.first);
    content.add(s.second);
  });
  std::map<std::string, std::string> symbols;
  auto registerSymbol = [&](const std::string &symbol,
                            const std::string &exact) -> llvm::Error {
    auto p = symbols.emplace(symbol, exact);
    if (!p.second && p.first->second != exact)
      llvm::report_fatal_error("two exact subjects share one generated symbol");
    return llvm::Error::success();
  };
  for (const auto &s : world.selections) {
    DependencyRecord record;
    record.selection = s->key;
    record.normalizedSelection = s->normalizedSelection;
    record.captureIdentity = s->captureIdentity;
    record.captureFingerprint = hash(record.captureIdentity);
    record.interfaceIdentity = s->implementation.interface.identity();
    record.implementationIdentity = s->artifact;
    record.paths = s->paths;
    record.interfaceFingerprint = hash(record.interfaceIdentity);
    record.implementationFingerprint = hash(record.implementationIdentity);
    for (const auto &dep : s->scope.components)
      record.dependencies.push_back(dep.second->key);
    data->dependencies.push_back(std::move(record));
    for (const auto &f : s->implementation.functions) {
      std::string symbol = functionSymbol(*s, f.first);
      Writer subject;
      subject.add(s->key);
      subject.add(f.first);
      subject.add(s->artifact);
      if (auto err = registerSymbol(symbol, subject.bytes))
        return err;
      const auto &promised =
          s->implementation.interface.declaration().functions.at(f.first);
      auto linked =
          world.function(f.second, s->scope, symbol, &promised, &s->scope);
      if (!linked)
        return linked.takeError();
      linked->exactSubject = subject.bytes;
      data->functions.push_back(std::move(*linked));
    }
  }
  data->entry = "client_" + hash(content.bytes);
  if (auto err = registerSymbol(data->entry, content.bytes))
    return err;
  auto client = world.function(request.client, *scope, data->entry);
  if (!client)
    return client.takeError();
  // Exact reached helper bodies participate in the executable identity.
  for (const auto &[key, dependency] : world.helperDependencies) {
    content.add(key);
    content.add(dependency.interfaceIdentity);
    content.add(dependency.implementationIdentity);
    data->dependencies.push_back(dependency);
  }
  data->entry = "client_" + hash(content.bytes);
  if (auto err = registerSymbol(data->entry, content.bytes))
    return err;
  client->symbol = data->entry;
  client->exactSubject = content.bytes;
  for (auto &[symbol, helper] : world.helperFunctions) {
    if (auto err = registerSymbol(symbol, world.helperSymbols.at(symbol)))
      return err;
    data->functions.push_back(std::move(helper));
  }
  data->functions.push_back(std::move(*client));
  // All references are closed and local call recursion is refused. No external
  // member declarations can acquire a successfully linked capability.
  std::map<std::string, LinkedFunction *> functions;
  for (auto &f : data->functions)
    functions.emplace(f.symbol, &f);
  for (auto &f : data->functions) {
    ResourceAdapters adapters(f, world.environment);
    std::map<std::vector<size_t>, LinkedCall> calls;
    std::function<llvm::Error(Region &, const std::vector<Layout> &,
                              std::vector<size_t>, std::vector<size_t>)>
        reconcile;
    reconcile = [&](Region &region, const std::vector<Layout> &results,
                    std::vector<size_t> oldPrefix,
                    std::vector<size_t> newPrefix) -> llvm::Error {
      auto &instructions = region.instructions;
      std::vector<Instruction> rewritten;
      for (size_t index = 0; index < instructions.size(); ++index) {
        auto oldPath = oldPrefix;
        oldPath.push_back(index);
        auto instruction = instructions[index];
        std::vector<Instruction> after;
        if (auto *call = std::get_if<Call>(&instruction)) {
          const auto &site = f.calls.at(oldPath);
          if (!site.logical) {
            auto callee = functions.find(site.target);
            if (callee == functions.end())
              return fail("library-open-call", "missing concrete member body");
            const auto &target = *callee->second;
            // Stopping callees still expose their declared result boundary.
            if (call->inputs.size() != target.body.inputs.size() ||
                call->outputs.size() != target.results.size())
              linkerDefect("linked call port arity differs");
            for (size_t i = 0; i < call->inputs.size(); ++i) {
              const auto &port = target.body.inputs[i];
              auto input = adapters.adapt(call->inputs[i],
                                          target.values.at(port.id.index),
                                          port.port.role, rewritten);
              if (!input)
                return input.takeError();
              call->inputs[i] = *input;
            }
            for (size_t i = 0; i < call->outputs.size(); ++i) {
              auto original = call->outputs[i];
              const auto expected = f.values.at(original.id.index);
              if (compatibleLeaves(expected.leaves, target.results[i].leaves,
                                   world.environment))
                continue;
              auto result =
                  adapters.fresh(target.results[i], original.port.role);
              if (!result)
                return result.takeError();
              call->outputs[i] = *result;
              auto output = adapters.adapt({result->id, {}}, expected,
                                           original.port.role, after);
              if (!output)
                return output.takeError();
              after.push_back(Project{*output, original});
            }
          }
          auto newPath = newPrefix;
          newPath.push_back(rewritten.size());
          calls.emplace(std::move(newPath), site);
        } else if (auto *project = std::get_if<Project>(&instruction)) {
          auto input = adapters.adapt(project->input,
                                      f.values.at(project->output.id.index),
                                      project->output.port.role, rewritten);
          if (!input)
            return input.takeError();
          project->input = *input;
        } else if (auto *aggregate = std::get_if<Construct>(&instruction)) {
          auto fields =
              children(aggregate->output.port.type, world.environment);
          if (!fields)
            return fields.takeError();
          for (size_t j = 0; j < aggregate->elements.size(); ++j) {
            if (j >= fields->size())
              linkerDefect("aggregate field count differs");
            Layout expected{
                (*fields)[j], (*fields)[j],
                selectedLeaves(f, {aggregate->output.id, {unsigned(j)}})};
            auto input = adapters.adapt(aggregate->elements[j], expected,
                                        aggregate->output.port.role, rewritten);
            if (!input)
              return input.takeError();
            aggregate->elements[j] = *input;
          }
        } else if (auto *variant =
                       std::get_if<VariantConstruct>(&instruction)) {
          const auto &layout = f.values.at(variant->output.id.index);
          if (layout.leaves.size() != 1 ||
              layout.leaves[0].kind != LayoutLeaf::Kind::Variant)
            linkerDefect("constructor has no variant layout");
          const auto &schema = layout.leaves[0];
          auto alt = std::find(schema.type.fields.begin(),
                               schema.type.fields.end(), variant->alternative);
          if (alt == schema.type.fields.end())
            linkerDefect("unknown active alternative");
          auto index = alt - schema.type.fields.begin();
          Layout expected{schema.type.elements[index],
                          layout.concreteType.elements[index],
                          schema.alternatives[index]};
          auto input = adapters.adapt(variant->payload, expected,
                                      variant->output.port.role, rewritten);
          if (!input)
            return input.takeError();
          variant->payload = *input;
        } else if (auto *join = branches(instruction)) {
          std::vector<Layout> outputs;
          for (const auto &v : join->outputs)
            outputs.push_back(f.values.at(v.id.index));
          for (size_t j = 0; j < join->arms.size(); ++j) {
            auto arm = std::make_shared<Region>(*join->arms[j].body);
            auto oldNested = oldPath;
            oldNested.push_back(j);
            auto newNested = newPrefix;
            newNested.push_back(rewritten.size());
            newNested.push_back(j);
            if (auto err = reconcile(*arm, outputs, oldNested, newNested))
              return err;
            join->arms[j].body = std::move(arm);
          }
        }
        rewritten.push_back(std::move(instruction));
        rewritten.insert(rewritten.end(), after.begin(), after.end());
      }
      for (size_t i = 0; i < region.returns.size(); ++i) {
        if (i >= results.size())
          return fail("library-return", "region result count differs");
        auto result =
            adapters.adapt(region.returns[i], results[i], "", rewritten);
        if (!result)
          return result.takeError();
        region.returns[i] = *result;
      }
      instructions = std::move(rewritten);
      return llvm::Error::success();
    };
    Region root{f.body.inputs, f.body.instructions, f.body.returns};
    if (auto err = reconcile(root, f.results, {}, {}))
      return err;
    f.body.instructions = std::move(root.instructions);
    f.body.returns = std::move(root.returns);
    f.calls = std::move(calls);
    // Check the rewritten ownership graph without propagating through adapter
    // constructors: their fields intentionally describe the destination ABI.
    if (auto err = refineResourcePaths(f, world.environment, false))
      return err;
  }
  std::set<std::string> visiting, done;
  std::function<llvm::Error(const std::string &)> visit =
      [&](const std::string &name) -> llvm::Error {
    if (done.count(name))
      return llvm::Error::success();
    if (!visiting.insert(name).second)
      return fail("library-call-cycle", "recursive linked member body");
    auto f = functions.find(name);
    if (f == functions.end())
      return fail("library-open-call", "missing linked callee " + name);
    for (const auto &call : f->second->calls)
      if (!call.second.logical)
        if (auto err = visit(call.second.target))
          return err;
    // Callees have now been normalized. Preserve each reached call (and hence
    // its effects, origins and stop reason), but remove its dead continuation.
    // The halt after a terminal call is unreachable carrier scaffolding, as
    // for an all-terminal branch; it never substitutes for executing the call.
    auto &linked = *f->second;
    std::map<std::vector<size_t>, LinkedCall> reached;
    std::function<llvm::Error(Region &, std::vector<size_t>)> normalize;
    normalize = [&](Region &region, std::vector<size_t> prefix) -> llvm::Error {
      for (size_t i = 0; i < region.instructions.size(); ++i) {
        auto path = prefix;
        path.push_back(i);
        auto &instruction = region.instructions[i];
        bool stops = std::holds_alternative<Stop>(instruction);
        if (std::holds_alternative<Call>(instruction)) {
          const auto &target = linked.calls.at(path);
          reached.emplace(path, target);
          if (!target.logical &&
              terminal(functions.at(target.target)->body.instructions)) {
            region.instructions.resize(i + 1);
            region.instructions.push_back(Stop{"abort"});
            region.returns.clear();
            return llvm::Error::success();
          }
        } else if (auto *join = branches(instruction)) {
          bool continues = false;
          for (size_t j = 0; j < join->arms.size(); ++j) {
            auto arm = std::make_shared<Region>(*join->arms[j].body);
            auto nested = path;
            nested.push_back(j);
            if (auto err = normalize(*arm, nested))
              return err;
            continues |= !terminal(arm->instructions);
            join->arms[j].body = std::move(arm);
          }
          if (!continues)
            join->outputs.clear();
          stops = !continues;
        }
        if (stops) {
          region.instructions.resize(i + 1);
          region.returns.clear();
          return llvm::Error::success();
        }
      }
      return llvm::Error::success();
    };
    Region root{linked.body.inputs, linked.body.instructions,
                linked.body.returns};
    if (auto err = normalize(root, {}))
      return err;
    linked.body.instructions = std::move(root.instructions);
    linked.body.returns = std::move(root.returns);
    linked.calls = std::move(reached);
    visiting.erase(name);
    done.insert(name);
    return llvm::Error::success();
  };
  for (const auto &f : data->functions)
    if (auto err = visit(f.symbol))
      return err;
  data->environment = std::move(world.environment);
  data->evidence = std::move(world.evidence);
  data->identity = content.bytes;
  data->fingerprint = hash(data->identity);
  return LinkedProgram(std::move(data));
}
} // namespace zkc::frontend::library
