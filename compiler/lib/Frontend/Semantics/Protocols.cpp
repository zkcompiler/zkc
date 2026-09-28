#include "Protocols.h"
#include "../Static/Domains.h"
#include "Places.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>
#include <set>

using namespace llvm;
namespace zkc::frontend::semantics {
namespace {
class ProtocolChecker {
  model::Module &model;
  const syntax::Protocol &protocol;
  DeclId owner;
  ScopeId scope;
  const std::function<TypeId(const syntax::Type &)> &resolveType;
  source::Protocol *emitted;
  const CheckPlacement &checkPlacement;
  bool valid = true;
  unsigned instructions = 0;
  using Substitution = std::map<DeclId, StaticArgument>;
  // A captured place a loop region reads under its checked flat key.
  struct Alias {
    syntax::Place place;
    std::string key;
  };
  // Protocol values by flat key: each aggregate port also binds its
  // components under `name.field` or `name.N`.
  struct Environment {
    std::map<std::string, Port> ports;
    std::vector<Alias> captured;
  };
  // A place checked against its ports' nominal types. `complete` is false
  // when an inferred capture stopped at an index into one collection value.
  struct Selected {
    syntax::Place place;
    std::string key;
    bool complete = true;
  };
  std::set<std::string> roles;
  std::map<DeclId, Substitution> dependencyBindings;

  bool fail(const source::Node &node, StringRef code, const Twine &message) {
    if (valid)
      model.diagnostics.push_back({code.str(), message.str(), node.location});
    valid = false;
    return false;
  }
  bool closed(DomainId id) const {
    const auto &d = model.domains.at(id.index);
    return d.kind == Domain::Kind::Identity ||
           (d.kind == Domain::Kind::Projection && closed(d.parent));
  }
  bool entails(ArrayRef<Requirement> goals, const source::Node &node,
               bool diagnose = true) {
    std::vector<requirements::Term> terms;
    std::map<DomainId, unsigned> indices;
    std::function<unsigned(DomainId)> intern = [&](DomainId id) {
      if (auto it = indices.find(id); it != indices.end())
        return it->second;
      const auto d = model.domains.at(id.index);
      std::optional<unsigned> parent;
      if (d.kind == Domain::Kind::Projection)
        parent = intern(d.parent);
      unsigned index = terms.size();
      // Distinct binder IDs remain distinct even when the display name agrees.
      std::string name = d.kind == Domain::Kind::Parameter
                             ? "parameter_" + std::to_string(d.parameter.index)
                             : d.name;
      terms.push_back({name, parent});
      indices.emplace(id, index);
      return index;
    };
    auto predicate = [&](const Requirement &r) {
      std::vector<unsigned> args;
      for (DomainId argument : r.arguments)
        args.push_back(intern(argument));
      return r.predicate == "="
                 ? requirements::Predicate::equal(args.at(0), args.at(1))
                 : requirements::Predicate::holds(r.predicate, args);
    };
    std::vector<requirements::Predicate> premises, required;
    for (const auto &r : model.declarations[owner.index].requirements)
      premises.push_back(predicate(r));
    for (const auto &r : goals) {
      auto p = predicate(r);
      required.push_back(p);
      if (llvm::all_of(r.arguments, [&](DomainId d) { return closed(d); })) {
        source::Names identities;
        std::vector<unsigned> positions;
        for (DomainId d : r.arguments) {
          positions.push_back(identities.size());
          identities.push_back(model.spelling(d));
        }
        auto closedGoal =
            r.predicate == "="
                ? requirements::Predicate::equal(0, 1)
                : requirements::Predicate::holds(r.predicate, positions);
        if (auto e =
                protocol::checkClosedRequirements({closedGoal}, identities))
          consumeError(std::move(e));
        else
          premises.push_back(p);
      }
    }
    if (terms.size() > 128 || premises.size() + required.size() > 1024)
      return fail(
          node, "requirements-limit",
          "protocol source requirements exceed the finite checker budget");
    auto proof = requirements::derive(
        terms, premises, protocol::boundCapabilityRules(), required);
    if (!proof)
      return fail(node, "requirements-limit", toString(proof.takeError()));
    if (llvm::all_of(proof->goals,
                     [](const auto &goal) { return goal.has_value(); }))
      return true;
    return diagnose ? fail(node, "source-protocol-requirement",
                           "protocol requirements do not entail this call's "
                           "requirements")
                    : false;
  }
  bool equal(DomainId a, DomainId b, const source::Node &node) {
    if (a == b)
      return true;
    Requirement goal;
    goal.predicate = "=";
    goal.arguments = {a, b};
    return entails({goal}, node, false);
  }
  bool same(TypeId a, TypeId b, const source::Node &node) {
    if (a == b)
      return true;
    const auto x = model.types.at(a.index), y = model.types.at(b.index);
    if (x.kind != y.kind || x.constructor != y.constructor ||
        x.declaration != y.declaration || x.count != y.count ||
        x.arguments.size() != y.arguments.size() ||
        x.elements.size() != y.elements.size())
      return false;
    for (auto [left, right] : zip(x.elements, y.elements))
      if (!same(left, right, node))
        return false;
    for (auto [left, right] : zip(x.arguments, y.arguments))
      if (left.kind != right.kind ||
          (left.kind == StaticArgument::Kind::Domain &&
           !equal(left.domain, right.domain, node)) ||
          (left.kind == StaticArgument::Kind::Type &&
           !same(left.type, right.type, node)) ||
          (left.kind == StaticArgument::Kind::Natural &&
           (left.parameter != right.parameter || left.number != right.number)))
        return false;
    return true;
  }
  bool requireType(TypeId actual, TypeId expected, const source::Node &node,
                   StringRef code, StringRef message) {
    if (same(actual, expected, node))
      return true;
    const bool left = model.types[actual.index].kind == Type::Kind::Record;
    const bool right = model.types[expected.index].kind == Type::Kind::Record;
    return fail(node,
                left != right ? "source-struct-value"
                : left        ? "source-struct-mismatch"
                              : code,
                message);
  }
  bool role(StringRef name, const source::Node &node) {
    return roles.count(name.str()) ||
           fail(node, "source-protocol-role",
                "unknown protocol role '" + name + "'");
  }
  bool bind(Environment &environment, StringRef name, Port port,
            const source::Node &node) {
    port.name = name.str();
    if (!environment.ports.emplace(port.name, port).second)
      return fail(node, "source-value-duplicate",
                  "duplicate protocol value '" + name + "'");
    const auto t = model.types.at(port.type.index);
    if (t.kind == Type::Kind::Product || t.kind == Type::Kind::Array) {
      auto count = t.kind == Type::Kind::Array ? t.count : t.elements.size();
      for (size_t i = 0; i < count; ++i) {
        auto element = t.elements[t.kind == Type::Kind::Array ? 0 : i];
        Port child{std::to_string(i), port.role, element, port.location};
        if (!bind(environment, (name + "." + child.name).str(), child, node))
          return false;
      }
    } else if (t.kind == Type::Kind::Record) {
      const auto d = model.declarations.at(t.declaration.index);
      Substitution sub;
      for (auto [parameter, argument] : zip(d.parameters, t.arguments))
        sub.emplace(parameter, argument);
      for (auto field : d.fields) {
        field.type = model.substitute(field.type, sub);
        field.role = port.role;
        if (!bind(environment, (name + "." + field.name).str(), field, node))
          return false;
      }
    }
    return true;
  }
  const Port *port(const Environment &environment, StringRef key,
                   const source::Node &node) {
    auto it = environment.ports.find(key.str());
    if (it != environment.ports.end())
      return &it->second;
    fail(node, "source-value-reference",
         "unknown protocol value '" + key + "'");
    return nullptr;
  }
  /// Check a reference-only place against the nominal types of its ports. A
  /// region reads a captured place through its longest captured ancestor.
  std::optional<Selected> select(const Environment &environment,
                                 const syntax::Place &place,
                                 const source::Node &node,
                                 bool captureCollection = false) {
    Selected result;
    const auto &at =
        place.location ? static_cast<const source::Node &>(place) : node;
    const auto *root = syntax::localRoot(place);
    const auto *alias =
        places::capturedAncestor(ArrayRef(environment.captured), place);
    size_t begin = 0;
    if (alias) {
      result.place = alias->place;
      result.key = alias->key;
      begin = alias->place.steps.size();
    } else if (root && environment.ports.count(*root)) {
      result.place.root = place.root;
      result.place.location = place.location;
      result.key = *root;
    } else {
      fail(at, "source-value-reference",
           "unknown protocol value '" + syntax::spelling(place) + "'");
      return std::nullopt;
    }
    for (size_t i = begin; i < place.steps.size(); ++i) {
      const auto &step = place.steps[i];
      const auto t =
          model.types.at(environment.ports.at(result.key).type.index);
      auto kind = places::AggregateKind::Scalar;
      size_t arity = 0;
      source::Names fields;
      if (t.kind == Type::Kind::Product) {
        kind = places::AggregateKind::Product;
        arity = t.elements.size();
      } else if (t.kind == Type::Kind::Array) {
        kind = places::AggregateKind::Array;
        arity = t.count;
      } else if (t.kind == Type::Kind::Record) {
        kind = places::AggregateKind::Record;
        for (const auto &field : model.declarations[t.declaration.index].fields)
          fields.push_back(field.name);
        arity = fields.size();
      } else if (captureCollection &&
                 step.kind == syntax::Projection::Kind::Index) {
        // An element of one collection value: capture the whole value.
        result.complete = false;
        return result;
      }
      auto selection = places::select(step, kind, arity, fields);
      if (!selection) {
        fail(step.location ? static_cast<const source::Node &>(step) : at,
             "source-projection",
             kind == places::AggregateKind::Scalar
                 ? "projection requires the corresponding aggregate kind"
                 : "invalid projection kind, field, or static index");
        return std::nullopt;
      }
      auto checked = step;
      checked.key = selection->key;
      result.place.steps.push_back(std::move(checked));
      result.key += "." + selection->key;
      if (!environment.ports.count(result.key)) {
        fail(at, "source-value-reference",
             "unknown protocol value '" + syntax::spelling(place) + "'");
        return std::nullopt;
      }
    }
    return result;
  }
  /// Check captured places before flattening. An inferred index into one
  /// collection value captures that value; inferred captures keep first use
  /// and a whole value subsumes its selections. Explicit lists stay as written.
  std::optional<std::vector<Selected>> captures(const Environment &environment,
                                                const syntax::Places &places,
                                                bool explicitCaptures,
                                                const source::Node &node) {
    std::vector<Selected> result;
    for (const auto &place : places) {
      auto selected = select(environment, place, node, !explicitCaptures);
      if (!selected)
        return std::nullopt;
      if (explicitCaptures)
        result.push_back(std::move(*selected));
      else
        syntax::unite(
            result, std::move(*selected),
            [](const Selected &a, const Selected &b) {
              return syntax::ancestor(a.place, b.place);
            },
            [](Selected &, Selected &&) {});
    }
    return result;
  }
  std::optional<source::Names> keys(const Environment &environment,
                                    const syntax::Places &places,
                                    const source::Node &node) {
    source::Names result;
    for (const auto &place : places) {
      auto selected = select(environment, place, node);
      if (!selected)
        return std::nullopt;
      result.push_back(std::move(selected->key));
    }
    return result;
  }
  source::Names flatten(const source::Names &names,
                        const Environment &environment) const {
    source::Names result;
    for (const auto &name : names)
      for (const auto &leaf : model.leaves(environment.ports.at(name)))
        result.push_back(leaf.name);
    return result;
  }
  std::vector<Requirement> requirements(DeclId target,
                                        const Substitution &sub) {
    auto result = model.declarations[target.index].requirements;
    for (auto &r : result)
      for (auto &term : r.arguments)
        term = model.substitute(term, sub);
    return result;
  }
  DomainId domain(StringRef spelling, const syntax::StaticTerm *writtenTerm,
                  const source::Node &node) {
    if (!writtenTerm)
      return model.internDomain(spelling, scope);
    // A quoted identity is never captured by a same-spelled domain binder.
    ScopeId rootScope = writtenTerm->root.kind == syntax::Atom::Kind::String
                            ? ScopeId{0}
                            : scope;
    if (!isDomainRoot(writtenTerm->root.value,
                      writtenTerm->root.kind == syntax::Atom::Kind::String)) {
      fail(node, "source-static-sort",
           "unknown domain root; use :: for associated members");
      return {};
    }
    DomainId result = model.internDomain(writtenTerm->root.value, rootScope);
    for (const auto &member : writtenTerm->members) {
      const auto sort = model.domains[result.index].sort;
      if (protocol::associatedMemberSort(sort, member).empty()) {
        fail(node, "source-static-sort", "unknown associated domain member");
        return {};
      }
      result =
          model.internDomain(model.spelling(result) + "." + member, rootScope);
    }
    return result;
  }
  std::optional<StaticArgument> argument(StringRef sort, StringRef term,
                                         const syntax::StaticTerm *written,
                                         const source::Node &node) {
    if (sort == "Nat") {
      if (written &&
          (written->root.kind == syntax::Atom::Kind::String ||
           !written->members.empty() || !written->arguments.empty())) {
        fail(node, "source-static-sort", "expected a natural static argument");
        return {};
      }
      auto parameter = model.lookup(scope, term);
      if (parameter.valid() &&
          model.declarations[parameter.index].kind ==
              Declaration::Kind::Parameter &&
          model.declarations[parameter.index].sort == "Nat")
        return StaticArgument::natural(0, parameter);
      uint64_t number;
      if (term.getAsInteger(10, number) || number > 1048576) {
        fail(node, "source-static-sort",
             "expected a bounded natural or a scoped Nat parameter");
        return {};
      }
      return StaticArgument::natural(number);
    }
    if (sort == "Type") {
      if (written) {
        auto selected = resolveType(syntax::typeExpression(*written));
        if (!selected.valid())
          return {};
        return StaticArgument::typeOf(selected);
      }
      auto parameter = model.lookup(scope, term);
      if (parameter.valid() &&
          model.declarations[parameter.index].sort == "Type")
        return StaticArgument::typeOf(model.logical(term, scope));
      auto checked = protocol::parseBoundType(term, false);
      if (!checked) {
        consumeError(checked.takeError());
        fail(node, "source-static-sort", "expected a logical type argument");
        return {};
      }
      return StaticArgument::typeOf(model.logical(checked->spelling(), scope));
    }
    auto selected = domain(term, written, node);
    if (!selected.valid())
      return {};
    if (model.domains[selected.index].sort != sort) {
      fail(node, "source-static-sort",
           "static argument has the wrong domain sort");
      return {};
    }
    return StaticArgument(selected);
  }
  bool arguments(DeclId target,
                 const std::optional<syntax::StaticTerms> &written,
                 const source::Node &node, Substitution &sub) {
    const auto d = model.declarations.at(target.index);
    if (!d.parameters.empty() && !written)
      return fail(node, "source-local-generic",
                  "protocol calls require explicit static arguments or a "
                  "closed configuration");
    if (written && written->size() != d.parameters.size())
      return fail(node, "generic-static-arity", "supply every static argument");
    if (written)
      for (auto [parameter, term] : zip(d.parameters, *written)) {
        auto selected = argument(model.declarations[parameter.index].sort,
                                 syntax::staticSpelling(term), &term, node);
        if (!selected)
          return false;
        sub.emplace(parameter, *selected);
      }
    return true;
  }
  // `inputs` are checked flat keys; `outputs` are the names bound.
  bool apply(DeclId target, const Substitution &sub,
             const source::Names &inputs, const source::Names &outputs,
             StringRef localRole, const source::Node &node, StringRef site,
             Environment &environment, ResolvedUse::Kind kind, bool written,
             bool destructure = false) {
    auto d = model.declarations.at(target.index);
    if (!localRole.empty() && d.outputs.size() == 1) {
      auto t = model.types.at(d.outputs.front().type.index);
      if (t.kind == Type::Kind::Product &&
          (destructure || (outputs.empty() && t.elements.empty()))) {
        d.outputs.clear();
        for (auto e : t.elements)
          d.outputs.push_back({{}, {}, e, node.location});
      }
    }
    if (inputs.size() != d.inputs.size() || outputs.size() != d.outputs.size())
      return fail(node, "source-call-arity",
                  "protocol call has incorrect authored operand/result arity");
    for (auto [name, input] : zip(inputs, d.inputs)) {
      const auto *actual = port(environment, name, node);
      if (!actual)
        return false;
      if (!requireType(
              actual->type, model.substitute(input.type, sub), node,
              "source-call-type",
              "protocol call operand differs from its declared nominal type"))
        return false;
      StringRef expectedRole =
          localRole.empty() ? StringRef(input.role) : localRole;
      if (actual->role != expectedRole)
        return fail(node, "source-protocol-role",
                    "call operand belongs to a different role");
    }
    auto obligations = requirements(target, sub);
    if (!entails(obligations, node))
      return false;
    ResolvedUse use;
    use.kind = kind;
    use.owner = owner;
    use.target = target;
    use.scope = scope;
    use.site = site.str();
    use.location = node.location;
    use.role = localRole.str();
    use.writtenArguments = written;
    use.requirements = std::move(obligations);
    for (DeclId parameter : d.parameters)
      if (auto it = sub.find(parameter); it != sub.end())
        use.bindings.push_back({parameter, it->second});
    for (auto [name, declared] : zip(outputs, d.outputs)) {
      auto port = declared;
      port.type = model.substitute(port.type, sub);
      if (!localRole.empty())
        port.role = localRole.str();
      port.name = name;
      port.location = node.location;
      if (!bind(environment, name, port, node))
        return false;
      use.results.push_back(std::move(port));
    }
    model.uses.push_back(std::move(use));
    return true;
  }
  bool dependency(const syntax::Dependency &dependency, DeclId alias,
                  DeclId target) {
    const auto d = model.declarations[target.index];
    Substitution sub;
    if (dependency.arguments)
      for (const auto &[name, term] : *dependency.arguments) {
        auto parameter = model.lookup(d.members, name);
        if (!is_contained(d.parameters, parameter) || sub.count(parameter))
          return fail(dependency, "source-static-parameter",
                      "unknown or duplicate dependency parameter");
        auto selected =
            argument(model.declarations[parameter.index].sort,
                     syntax::staticSpelling(term), &term, dependency);
        if (!selected)
          return false;
        sub.emplace(parameter, *selected);
      }
    if (sub.size() != d.parameters.size())
      return fail(dependency, "source-static-required",
                  "dependency must bind every protocol static parameter");
    if (!entails(requirements(target, sub), dependency))
      return false;
    dependencyBindings.emplace(alias, std::move(sub));
    return true;
  }
  std::optional<source::Names> orderPorts(const source::Names &keys,
                                          const source::Names &values,
                                          ArrayRef<Port> ports,
                                          const source::Node &node) {
    std::map<std::string, std::string> bindings;
    if (keys.size() != ports.size() || keys.size() != values.size()) {
      fail(node, "source-output-port",
           "bind every declared output port exactly once");
      return {};
    }
    for (auto [key, value] : zip(keys, values))
      if (key.empty() || !bindings.emplace(key, value).second) {
        fail(node, "source-output-port", "duplicate or unnamed output port");
        return {};
      }
    source::Names ordered;
    for (const auto &port : ports) {
      auto found = bindings.find(port.name);
      if (port.name.empty() || found == bindings.end()) {
        fail(node, "source-output-port",
             "unknown or missing named output port");
        return {};
      }
      ordered.push_back(found->second);
    }
    return ordered;
  }
  bool body(const syntax::Body &body, Environment environment,
            ArrayRef<Port> results, bool loop, unsigned depth,
            source::Body *out = nullptr) {
    if (body.empty() || depth > 64)
      return fail(protocol, "source-protocol-body",
                  "protocol body is empty or exceeds the nesting budget");
    for (const auto &instruction : body) {
      source::Instruction lowered;
      lowered.location = instruction.location;
      lowered.site = instruction.site;
      if (++instructions > 32768)
        return fail(instruction, "source-limit",
                    "protocol body exceeds the instruction budget");
      const auto *finish = std::get_if<syntax::Finish>(&instruction.value);
      const auto *ret = std::get_if<syntax::Return>(&instruction.value);
      const auto *yield = std::get_if<syntax::Yield>(&instruction.value);
      const auto *stop = std::get_if<source::Stop>(&instruction.value);
      if (finish && loop)
        return fail(instruction, "source-output-port",
                    "finish terminates a protocol, not a loop region");
      if (bool(finish || ret || yield || stop) !=
          (&instruction == &body.back()))
        return fail(instruction, "source-protocol-terminator",
                    "protocol regions end in a return, yield or stop");
      if (finish || ret || yield) {
        // Checked keys of the returned places, in declared result order.
        source::Names names;
        if (finish) {
          source::Names ports, values;
          for (const auto &[key, value] : finish->values) {
            auto selected = select(environment, value, instruction);
            if (!selected)
              return false;
            ports.push_back(key);
            values.push_back(std::move(selected->key));
          }
          auto ordered = orderPorts(ports, values, results, instruction);
          if (!ordered)
            return false;
          names = std::move(*ordered);
        } else {
          auto selected =
              keys(environment, ret ? ret->values : yield->values, instruction);
          if (!selected)
            return false;
          names = std::move(*selected);
        }
        if (bool(yield) != loop || names.size() != results.size())
          return fail(instruction, "source-protocol-return",
                      "return/yield has the wrong region or result arity");
        for (auto [name, expected] : zip(names, results)) {
          const auto *actual = port(environment, name, instruction);
          if (!actual)
            return false;
          if (actual->role != expected.role)
            return fail(instruction, "source-protocol-return",
                        "return/yield differs from its declared type or role");
          if (!requireType(
                  actual->type, expected.type, instruction,
                  "source-protocol-return",
                  "return/yield differs from its declared nominal type"))
            return false;
        }
        if (out) {
          auto values = flatten(names, environment);
          if (yield)
            lowered.value = source::Yield{std::move(values)};
          else
            lowered.value = source::Return{std::move(values)};
        }
      } else if (stop) {
        if (!role(stop->role, instruction))
          return false;
        lowered.value = *stop;
      } else if (const auto *placement =
                     std::get_if<syntax::Placement>(&instruction.value)) {
        if (!role(placement->role, instruction))
          return false;
        std::vector<Port> available;
        for (const auto &[name, port] : environment.ports) {
          if (port.role != placement->role)
            continue;
          bool child = false;
          auto prefix = StringRef(name);
          while (prefix.contains('.')) {
            prefix = prefix.rsplit('.').first;
            auto parent = environment.ports.find(prefix.str());
            if (parent != environment.ports.end() &&
                model.types[parent->second.type.index].kind !=
                    Type::Kind::Logical) {
              child = true;
              break;
            }
          }
          if (!child)
            available.push_back(port);
        }
        auto checked =
            checkPlacement(*placement, lowered, available, out != nullptr);
        if (!checked)
          return false;
        Substitution sub;
        const auto helper = model.declarations[checked->function.index];
        for (auto parameter : helper.parameters) {
          const auto &p = model.declarations[parameter.index];
          sub.emplace(parameter, model.argument(p.name, p.sort, scope));
        }
        if (!apply(checked->function, sub, checked->captures,
                   placement->outputs, placement->role, instruction,
                   instruction.site, environment, ResolvedUse::Kind::Call,
                   false, placement->destructure))
          return false;
        if (placement->annotation) {
          auto expected = resolveType(*placement->annotation);
          auto actual = model.substitute(helper.outputs.front().type, sub);
          if (!expected.valid() ||
              !requireType(actual, expected, instruction, "source-call-type",
                           "placement result differs from its annotation"))
            return false;
        }
        if (out)
          lowered.value =
              source::LocalCall{placement->role, helper.name, checked->captures,
                                flatten(placement->outputs, environment)};
      } else if (const auto *call =
                     std::get_if<syntax::Call>(&instruction.value)) {
        auto target = call->operatorSymbol
                          ? DeclId{}
                          : model.lookup({0}, syntax::encode(call->callee));
        if (!target.valid() || (model.declarations[target.index].kind !=
                                    Declaration::Kind::Function &&
                                model.declarations[target.index].kind !=
                                    Declaration::Kind::Configuration))
          return fail(
              *call, "source-call-target",
              "local call requires a resolved function or configuration");
        if (!call->role)
          return fail(*call, "source-protocol-role",
                      "protocol local call requires a role");
        if (!role(*call->role, *call))
          return false;
        if (!call->attributes.empty())
          return fail(*call, "algorithm-call-syntax",
                      "algorithm calls do not accept operation attributes");
        const auto &callee = model.declarations[target.index];
        if (!out &&
            ((callee.kind == Declaration::Kind::Configuration &&
              (!callee.parameters.empty() || call->staticArguments)) ||
             (callee.kind == Declaration::Kind::Function && callee.generic &&
              callee.parameters.empty() && !call->staticArguments)))
          return fail(*call, "source-local-configuration",
                      "family locals require a closed configuration or an "
                      "explicit generic function instantiation");
        if (out &&
            (!callee.parameters.empty() || call->staticArguments ||
             (callee.generic && callee.kind == Declaration::Kind::Function)))
          return fail(*call, "source-local-configuration",
                      "emitted protocol locals require a closed configuration");
        Substitution sub;
        auto inputs = keys(environment, call->inputs, *call);
        if (!inputs || !arguments(target, call->staticArguments, *call, sub) ||
            !apply(target, sub, *inputs, call->outputs, *call->role, *call,
                   instruction.site, environment, ResolvedUse::Kind::Call,
                   bool(call->staticArguments), call->destructure))
          return false;
        auto annotations = call->annotation;
        if (annotations && call->destructure && annotations->size() == 1 &&
            annotations->front().product)
          annotations =
              std::vector<syntax::Type>(annotations->front().arguments);
        if (annotations) {
          if (annotations->size() != call->outputs.size())
            return fail(*call, "source-annotation-arity",
                        "annotation must cover every result");
          for (auto [name, type] : zip(call->outputs, *annotations)) {
            auto expected = resolveType(type);
            if (!expected.valid())
              return false;
            if (!same(environment.ports.at(name).type, expected, *call))
              return fail(
                  *call, "source-call-type",
                  "result annotation differs from the resolved nominal type");
          }
        }
        if (out)
          lowered.value = source::LocalCall{
              *call->role, model.declarations[target.index].name,
              flatten(*inputs, environment),
              flatten(call->outputs, environment)};
      } else if (const auto *call =
                     std::get_if<syntax::Invocation>(&instruction.value)) {
        auto alias = model.lookup(scope, call->callee);
        if (!alias.valid() || model.declarations[alias.index].kind !=
                                  Declaration::Kind::Dependency)
          return fail(instruction, "source-call-target",
                      "invoke requires a resolved dependency alias");
        auto target = model.declarations[alias.index].target;
        if (!target.valid() || model.declarations[target.index].kind !=
                                   Declaration::Kind::Protocol)
          return fail(instruction, "source-call-target",
                      "dependency target is not a protocol");
        const auto &sub = dependencyBindings.at(alias);
        const bool written =
            llvm::any_of(protocol.dependencies, [&](const auto &dependency) {
              return dependency.name == call->callee &&
                     bool(dependency.arguments);
            });
        auto inputs = keys(environment, call->inputs, instruction);
        if (!inputs)
          return false;
        auto outputs = call->outputs;
        if (!call->resultNames.empty()) {
          auto ordered =
              orderPorts(call->resultNames, outputs,
                         model.declarations[target.index].outputs, instruction);
          if (!ordered)
            return false;
          outputs = std::move(*ordered);
        }
        if (!apply(target, sub, *inputs, outputs, {}, instruction,
                   instruction.site, environment, ResolvedUse::Kind::Invoke,
                   written))
          return false;
        if (out)
          lowered.value = source::ProtocolCall{
              model.declarations[alias.index].name,
              flatten(*inputs, environment), flatten(outputs, environment)};
      } else if (const auto *message =
                     std::get_if<syntax::Message>(&instruction.value)) {
        auto selected = select(environment, message->input, instruction);
        if (!selected)
          return false;
        const auto *input = &environment.ports.at(selected->key);
        if (!role(message->sender, instruction) ||
            !role(message->receiver, instruction))
          return false;
        if (input->role != message->sender)
          return fail(instruction, "source-protocol-role",
                      "message input does not belong to its sender");
        if (model.types[input->type.index].kind != Type::Kind::Logical)
          return fail(instruction, "source-struct-message",
                      "message payload requires one explicit logical value");
        Port output = *input;
        output.role = message->receiver;
        if (!bind(environment, message->output, output, instruction))
          return false;
        lowered.value =
            source::Message{message->schema, message->sender, message->receiver,
                            selected->key, message->output};
      } else if (const auto *region =
                     std::get_if<syntax::Loop>(&instruction.value)) {
        if (region->count.kind == syntax::Atom::Kind::String)
          return fail(instruction, "source-protocol-count",
                      "quoted data is not a natural parameter reference");
        source::LoopCount count;
        count.kind = region->count.kind == syntax::Atom::Kind::Number
                         ? source::LoopCount::Kind::Constant
                         : source::LoopCount::Kind::Parameter;
        count.value = region->count.value;
        if (count.kind == source::LoopCount::Kind::Parameter &&
            !is_contained(protocol.parameters, count.value)) {
          auto declaration = model.lookup({0}, count.value);
          bool constant = declaration.valid() &&
                          model.declarations[declaration.index].kind ==
                              Declaration::Kind::Constant &&
                          !environment.ports.count(count.value) &&
                          !model.lookup(scope, count.value).valid();
          if (!constant)
            return fail(instruction, "source-protocol-count",
                        "loop count requires a natural parameter or unshadowed "
                        "static constant");
        }
        Environment inner;
        std::vector<Port> carried;
        source::Loop loweredLoop;
        loweredLoop.count = count;
        for (const auto &[name, initial] : region->carried) {
          auto selected = select(environment, initial, instruction);
          if (!selected)
            return false;
          const auto &port = environment.ports.at(selected->key);
          carried.push_back(port);
          if (!bind(inner, name, port, instruction))
            return false;
          if (out) {
            auto arguments = flatten({name}, inner);
            auto inputs = flatten({selected->key}, environment);
            for (auto [argument, input] : zip(arguments, inputs))
              loweredLoop.carried.emplace_back(argument, input);
          }
        }
        auto captured = captures(environment, region->captures,
                                 region->explicitCaptures, instruction);
        if (!captured)
          return false;
        source::Names capturedKeys;
        for (const auto &capture : *captured) {
          if (!bind(inner, capture.key, environment.ports.at(capture.key),
                    instruction))
            return false;
          inner.captured.push_back({capture.place, capture.key});
          capturedKeys.push_back(capture.key);
        }
        if (out)
          loweredLoop.captures = flatten(capturedKeys, environment);
        if (region->outputs.size() != carried.size())
          return fail(instruction, "source-call-arity",
                      "loop outputs must match carried values");
        if (!this->body(region->body, std::move(inner), carried, true,
                        depth + 1, out ? &loweredLoop.body : nullptr))
          return false;
        for (auto [name, port] : zip(region->outputs, carried))
          if (!bind(environment, name, port, instruction))
            return false;
        if (out) {
          loweredLoop.outputs = flatten(region->outputs, environment);
          lowered.value = std::move(loweredLoop);
        }
      } else
        return fail(instruction, "source-local-control",
                    "unsupported protocol instruction");
      if (out)
        out->push_back(std::move(lowered));
    }
    return valid;
  }

public:
  ProtocolChecker(
      model::Module &model, const syntax::Protocol &protocol,
      const std::function<TypeId(const syntax::Type &)> &resolveType,
      const CheckPlacement &checkPlacement, source::Protocol *emitted)
      : model(model), protocol(protocol),
        owner(model.lookup({0}, protocol.name)),
        scope(model.declarations[owner.index].members),
        resolveType(resolveType), emitted(emitted),
        checkPlacement(checkPlacement) {}
  bool run() {
    if (protocol.roles.empty())
      return fail(protocol, "source-protocol-role",
                  "protocol requires at least one role");
    for (const auto &name : protocol.roles)
      if (!roles.insert(name).second)
        return fail(protocol, "source-protocol-role",
                    "duplicate protocol role");
    // Common dependencies preserve protocol role names. Instance role mapping
    // is a distinct later boundary, so source calls cannot remap these labels.
    for (const auto &dependency : protocol.dependencies) {
      auto alias = model.lookup(scope, dependency.name);
      const auto &target =
          model.declarations[model.declarations[alias.index].target.index];
      for (const auto &childRole : target.roles)
        if (!role(childRole, dependency))
          return false;
      if (!this->dependency(dependency, alias, target.id))
        return false;
      std::set<std::string> agreed;
      for (const auto &[child, parent] : dependency.agreements)
        if (!agreed.insert(child).second ||
            !is_contained(target.naturalParameters, child) ||
            !is_contained(protocol.parameters, parent))
          return fail(
              dependency, "source-protocol-parameter",
              "dependency agreement must connect declared natural parameters");
    }
    Environment environment;
    const auto d = model.declarations[owner.index];
    for (const auto &port : d.inputs)
      if (!role(port.role, protocol) ||
          !bind(environment, port.name, port, protocol))
        return false;
    std::set<std::string> outputNames;
    bool named =
        llvm::any_of(d.outputs, [](const auto &p) { return !p.name.empty(); });
    for (const auto &port : d.outputs) {
      if (!role(port.role, protocol))
        return false;
      if (named && (port.name.empty() || !outputNames.insert(port.name).second))
        return fail(protocol, "source-output-port",
                    "output ports must have distinct names");
    }
    if (!protocol.body)
      return true;
    source::Body lowered;
    if (!body(*protocol.body, std::move(environment), d.outputs, false, 0,
              emitted ? &lowered : nullptr))
      return false;
    if (emitted)
      emitted->body = std::move(lowered);
    model.declarations[owner.index].bodyState = Declaration::BodyState::Checked;
    return true;
  }
};
} // namespace
bool checkProtocolBody(
    model::Module &model, const syntax::Protocol &protocol,
    const std::function<TypeId(const syntax::Type &)> &resolveType,
    const CheckPlacement &checkPlacement, source::Protocol *emitted) {
  return ProtocolChecker(model, protocol, resolveType, checkPlacement, emitted)
      .run();
}
} // namespace zkc::frontend::semantics
