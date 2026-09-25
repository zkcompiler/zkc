#include "Callable.h"
#include <algorithm>

namespace zkc::frontend::library {
namespace detail {
llvm::Error extends(const Environment &old, const Environment &now) {
  for (const auto &l : old.libraries)
    for (const auto &d : l.declarations)
      if (auto err = captured(d, now))
        return err;
  auto sameEntry = [&](auto Environment::*field) -> bool {
    std::set<std::string> current;
    for (const auto &entry : now.*field) {
      Environment e;
      (e.*field).push_back(entry);
      current.insert(encode(e));
    }
    for (const auto &entry : old.*field) {
      Environment e;
      (e.*field).push_back(entry);
      if (!current.count(encode(e)))
        return false;
    }
    return true;
  };
  if (!sameEntry(&Environment::statics) ||
      !sameEntry(&Environment::logicalTypes) ||
      !sameEntry(&Environment::operations) ||
      !sameEntry(&Environment::implications))
    return fail("library-assumption-drift",
                "captured static or installed contract changed");
  return llvm::Error::success();
}
llvm::Expected<std::vector<Requirement>>
assumptions(const std::vector<TypeBound> &bounds,
            const std::vector<Import> &imports, std::vector<Requirement> facts,
            const Environment &e) {
  std::set<std::string> parameters, boundNames;
  for (const auto &bound : bounds) {
    if (!boundNames.insert(library::identity(bound.parameter)).second)
      return fail("library-type-bound", "duplicate type bound");
    auto s = sortOf(StaticTerm::root(bound.parameter), e);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, Sort::type()))
      return fail("library-type-bound", "bound is not on type");
  }
  for (const auto &i : imports) {
    if (auto err = importsInterface(i.interface, e))
      return err;
    auto s = sortOf(i.parameter, e);
    if (!s)
      return s.takeError();
    if (!sameSort(*s, Sort::component()) ||
        !parameters.insert(library::identity(i.parameter)).second)
      return fail("library-import", "duplicate or noncomponent import");
    const auto &d = i.interface.declaration();
    for (const auto &t : d.types) {
      auto sort = sortOf(StaticTerm::project(i.parameter, t.name), e);
      if (!sort)
        return sort.takeError();
      if (!sameSort(*sort, Sort::type()))
        return fail("library-import", "type member sort drift");
    }
    for (const auto &m : d.statics) {
      auto sort = sortOf(StaticTerm::project(i.parameter, m.name), e);
      if (!sort)
        return sort.takeError();
      if (!sameSort(*sort, m.sort))
        return fail("library-import", "static member sort drift");
      if (m.equation)
        facts.push_back({"",
                         {StaticTerm::project(i.parameter, m.name),
                          replace(*m.equation, d.self, i.parameter)}});
    }
    for (const auto &r : d.requirements)
      facts.push_back(replace(r, d.self, i.parameter));
  }
  if (auto err = validateRequirements(facts, e))
    return err;
  return facts;
}
} // namespace detail
struct Callable::Data {
  CallableDecl declaration;
  Environment environment;
  std::string identity;
};
Callable::Callable(std::shared_ptr<const Data> d) : data(std::move(d)) {}
const CallableDecl &Callable::declaration() const { return data->declaration; }
const Environment &Callable::environment() const { return data->environment; }
const std::string &Callable::identity() const { return data->identity; }
llvm::Expected<Callable> formCallable(CallableDecl d, Environment e) {
  using namespace detail;
  if (auto err = validateEnvironment(e))
    return err;
  if (auto err = captured(d.id, e))
    return err;
  std::set<std::string> parameters;
  for (const auto &p : d.parameters) {
    const auto *decl = findStatic(p, e);
    if (!decl || !decl->parameter ||
        !parameters.insert(library::identity(p)).second)
      return fail("library-callable-parameter",
                  "duplicate or nonparameter formal");
  }
  for (const auto &i : d.imports)
    if (i.parameter.kind != StaticTerm::Kind::Root ||
        !parameters.count(library::identity(i.parameter.declaration)))
      return fail("library-callable-parameter",
                  "import must bind a declared formal");
  for (const auto &b : d.typeBounds)
    if (!parameters.count(library::identity(b.parameter)))
      return fail("library-callable-parameter",
                  "type bound must bind a declared formal");
  auto facts =
      assumptions(d.typeBounds, d.imports, d.signature.preconditions, e);
  if (!facts)
    return facts.takeError();
  if (auto err =
          signature(d.signature, TypeContext{e, d.imports, d.typeBounds}))
    return err;
  auto data = std::make_shared<Callable::Data>();
  Writer w;
  w.add("zkc.checked-library.callable/1");
  w.add(callableShape(d));
  w.add(encode(e));
  data->identity = std::move(w.bytes);
  data->declaration = std::move(d);
  data->environment = std::move(e);
  return Callable(std::move(data));
}
namespace detail {
llvm::Error matchesCallable(const Callable &contract, const CheckedBody &body) {
  const auto &d = contract.declaration();
  CallableDecl actual{body.body().id, body.body().signature, d.parameters,
                      body.body().typeBounds, body.imports()};
  if (callableShape(d) != callableShape(actual))
    return fail("library-source-signature-drift",
                "helper body differs from exact callable contract");
  return extends(contract.environment(), body.environment());
}
llvm::Expected<Signature> sourceSignature(const SourceCall &call,
                                          const TypeContext &ctx) {
  const auto &d = call.callable.declaration();
  if (auto error = captured(d.id, ctx.environment))
    return error;
  std::set<std::string> formals, seen;
  for (const auto &p : d.parameters)
    formals.insert(identity(p));
  // The signature was formed in its owner's environment. A caller needs the
  // public static closure, not the owner's unrelated/private declarations.
  // Compare every reached descriptor exactly before substituting formals.
  std::set<std::string> checkedRoots;
  uint64_t work = 0;
  std::function<llvm::Error(const StaticTerm &)> checkTerm;
  checkTerm = [&](const StaticTerm &term) -> llvm::Error {
    if (++work > ctx.environment.expansionLimit)
      return fail("library-limit",
                  "callable public static closure exceeds limit");
    if (term.kind == StaticTerm::Kind::Root ||
        term.kind == StaticTerm::Kind::Apply ||
        term.kind == StaticTerm::Kind::Seal) {
      auto key = identity(term.declaration);
      if (!formals.count(key) && checkedRoots.insert(key).second) {
        const auto *owned =
            findStatic(term.declaration, call.callable.environment());
        const auto *visible = findStatic(term.declaration, ctx.environment);
        if (!owned || !visible)
          return fail("library-assumption-drift",
                      "callable public static subject is not captured");
        Environment a, b;
        a.statics.push_back(*owned);
        b.statics.push_back(*visible);
        if (encode(a) != encode(b))
          return fail("library-assumption-drift",
                      "callable public static descriptor changed");
        for (const auto &dependency : owned->capturedDependencies)
          if (auto err = checkTerm(dependency))
            return err;
      }
    }
    for (const auto &argument : term.arguments)
      if (auto err = checkTerm(argument))
        return err;
    return llvm::Error::success();
  };
  std::function<llvm::Error(const Type &)> checkType;
  checkType = [&](const Type &type) -> llvm::Error {
    for (const auto &a : type.arguments)
      if (auto err = checkTerm(a))
        return err;
    for (const auto &e : type.elements)
      if (auto err = checkType(e))
        return err;
    return llvm::Error::success();
  };
  for (const auto *ports : {&d.signature.inputs, &d.signature.outputs})
    for (const auto &p : *ports)
      if (auto err = checkType(p.type))
        return err;
  for (const auto *requirements :
       {&d.signature.preconditions, &d.signature.postconditions})
    for (const auto &r : *requirements)
      for (const auto &a : r.arguments)
        if (auto err = checkTerm(a))
          return err;
  for (const auto &a : call.arguments.statics) {
    if (a.first.kind != StaticTerm::Kind::Root ||
        !formals.count(identity(a.first.declaration)) ||
        !seen.insert(identity(a.first.declaration)).second)
      return fail("library-source-actual",
                  "unknown or duplicate static formal");
    auto formal = sortOf(a.first, call.callable.environment());
    if (!formal)
      return formal.takeError();
    auto value = sortOf(a.second, ctx.environment);
    if (!value)
      return value.takeError();
    if (!sameSort(*formal, *value) || sameSort(*formal, Sort::type()))
      return fail("library-static-sort", "helper actual changes static sort");
  }
  for (const auto &a : call.arguments.types) {
    if (!formals.count(identity(a.first)) ||
        !seen.insert(identity(a.first)).second)
      return fail("library-source-actual", "unknown or duplicate type formal");
    auto formal =
        sortOf(StaticTerm::root(a.first), call.callable.environment());
    if (!formal)
      return formal.takeError();
    if (!sameSort(*formal, Sort::type()))
      return fail("library-static-sort",
                  "type actual supplied to non-type formal");
    auto p = permissions(a.second, ctx);
    if (!p)
      return p.takeError();
  }
  if (seen != formals)
    return fail("library-source-actual",
                "helper actuals do not cover all parameters");
  for (const auto &i : d.imports) {
    auto selected = actual(i.parameter, call.arguments);
    auto found = std::find_if(
        ctx.imports.begin(), ctx.imports.end(), [&](const auto &j) {
          return identity(j.parameter) == identity(selected);
        });
    // A helper is checked against the caller's imported interfaces; a
    // concrete component is selected by a link, not by a helper call
    // (docs/spec/profiles/source/checked-libraries.md).
    if (found == ctx.imports.end())
      return fail("library-component-actual",
                  "a helper's component actual must be a component parameter "
                  "the caller imports");
    if (found->interface.identity() != i.interface.identity())
      return fail("library-interface-drift",
                  "helper component actual violates exact public bound");
  }
  for (const auto &b : d.typeBounds) {
    auto p =
        permissions(actual(Type::parameter(b.parameter), call.arguments), ctx);
    if (!p)
      return p.takeError();
    if ((b.permissions.copy && !p->copy) || (b.permissions.drop && !p->drop))
      return fail("library-permission-bound",
                  "helper type actual lacks public permission");
  }
  return actual(d.signature, call.arguments);
}
} // namespace detail
struct CheckedBody::Data {
  Body body;
  Environment environment;
  std::vector<Import> imports;
  std::vector<Requirement> obligations;
  std::string identity, fingerprint;
};
CheckedBody::CheckedBody(std::shared_ptr<const Data> d) : data(std::move(d)) {}
const Body &CheckedBody::body() const { return data->body; }
const Environment &CheckedBody::environment() const {
  return data->environment;
}
const std::vector<Import> &CheckedBody::imports() const {
  return data->imports;
}
const std::vector<Requirement> &CheckedBody::obligations() const {
  return data->obligations;
}
const std::string &CheckedBody::identity() const { return data->identity; }
const std::string &CheckedBody::fingerprint() const {
  return data->fingerprint;
}
namespace {
bool prefix(const std::vector<unsigned> &a, const std::vector<unsigned> &b) {
  return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
}
struct Resources {
  const detail::TypeContext &ctx;
  std::set<uint32_t> &defined;
  std::map<uint32_t, Port> values;
  std::map<uint32_t, std::vector<std::vector<unsigned>>> moves, uses;
  llvm::Error define(const Value &v) {
    if (!v.id.valid() || !defined.insert(v.id.index).second ||
        !values.emplace(v.id.index, v.port).second)
      return detail::fail("library-value", "duplicate/invalid ValueId");
    auto p = detail::permissions(v.port.type, ctx);
    if (!p)
      return p.takeError();
    return llvm::Error::success();
  }
  llvm::Expected<Port> use(const Place &p, bool dropping = false) {
    using namespace detail;
    auto value = values.find(p.value.index);
    if (value == values.end())
      return fail("library-value", "use before definition");
    auto t = placeType(value->second.type, p.path, ctx);
    if (!t)
      return t.takeError();
    auto permission = permissions(*t, ctx);
    if (!permission)
      return permission.takeError();
    for (const auto &m : moves[p.value.index])
      if (prefix(m, p.path) || prefix(p.path, m))
        return fail("library-resource-use",
                    "use overlaps a consumed semantic path");
    if (dropping && !permission->drop)
      return fail("library-drop", "drop permission is absent");
    uses[p.value.index].push_back(p.path);
    if (!permission->copy)
      moves[p.value.index].push_back(p.path);
    return Port{*t, value->second.role};
  }
  llvm::Error remaining(const Type &t, uint32_t id, std::vector<unsigned> path,
                        unsigned depth) {
    using namespace detail;
    if (depth > 128)
      return fail("library-limit", "resource path depth");
    for (const auto &m : uses[id])
      if (prefix(m, path))
        return llvm::Error::success();
    auto p = permissions(t, ctx);
    if (!p)
      return p.takeError();
    if (p->drop)
      return llvm::Error::success();
    if (t.kind != Type::Kind::Product && t.kind != Type::Kind::Record &&
        t.kind != Type::Kind::Array)
      return fail("library-resource-leak",
                  "non-droppable value remains on return");
    auto cs = children(t, ctx.environment);
    if (!cs)
      return cs.takeError();
    for (size_t i = 0; i < cs->size(); ++i) {
      auto child = path;
      child.push_back(i);
      if (auto err = remaining((*cs)[i], id, std::move(child), depth + 1))
        return err;
    }
    return llvm::Error::success();
  }
};
} // namespace
llvm::Expected<CheckedBody> checkBody(Body b, Environment e,
                                      std::vector<Import> imports) {
  using namespace detail;
  if (auto err = validateEnvironment(e))
    return err;
  if (auto err = captured(b.id, e))
    return err;
  auto formed =
      assumptions(b.typeBounds, imports, b.signature.preconditions, e);
  if (!formed)
    return formed.takeError();
  auto facts = std::move(*formed);
  std::vector<Requirement> obligations;
  TypeContext ctx{e, imports, b.typeBounds};
  if (auto err = signature(b.signature, ctx))
    return err;
  if (auto err = validateRequirements(facts, e))
    return err;
  if (b.inputs.size() != b.signature.inputs.size())
    return fail("library-body-arity",
                "body input count differs from signature");
  std::set<uint32_t> defined;
  uint64_t steps = 0;
  std::function<llvm::Error(Region &, const std::vector<Port> &,
                            const std::vector<Port> &, std::vector<Requirement>,
                            unsigned, const std::string &,
                            std::vector<Requirement> *)>
      checkRegion;
  checkRegion = [&](Region &region, const std::vector<Port> &inputs,
                    const std::vector<Port> &outputs,
                    std::vector<Requirement> facts, unsigned depth,
                    const std::string &role,
                    std::vector<Requirement> *established) -> llvm::Error {
    if (depth > 128 || (steps += region.instructions.size()) > e.expansionLimit)
      return fail("library-limit", "region depth or instruction limit");
    Resources resources{ctx, defined, {}, {}, {}};
    auto portEqual = [&](const Port &a, const Port &expected) -> llvm::Error {
      if (a.role != expected.role)
        return fail("library-role", "role/custody mismatch");
      return equalTypes(a.type, expected.type, facts, e);
    };
    if (region.inputs.size() != inputs.size())
      return fail("library-body-arity", "region input count differs");
    for (size_t i = 0; i < inputs.size(); ++i) {
      if (auto err = portEqual(region.inputs[i].port, inputs[i]))
        return err;
      if (auto err = resources.define(region.inputs[i]))
        return err;
    }
    auto &instructions = region.instructions;
    bool stops = false;
    for (auto &instruction : instructions) {
      // A stop, or an exhaustive join of terminal arms, ends its region.
      // Nothing after it can execute, so an instruction there is an authoring
      // error.
      if (stops)
        return fail("library-stop", "an instruction follows a terminal stop");
      if (depth) {
        // A stop ends the whole algorithm and schedules nobody, so it is local
        // to every role rather than to the region's own participant.
        bool local = std::visit(
            [&](const auto &node) {
              using T = std::decay_t<decltype(node)>;
              if constexpr (std::is_same_v<T, Conditional>) {
                const auto &b = node.branches;
                return b.role == role &&
                       std::all_of(
                           b.outputs.begin(), b.outputs.end(),
                           [&](const auto &v) { return v.port.role == role; });
              } else if constexpr (std::is_same_v<T, Call> ||
                                   std::is_same_v<T, Match> ||
                                   std::is_same_v<T, ArrayTraversal>) {
                if (node.role != role)
                  return false;
                for (const auto &v : node.outputs)
                  if (v.port.role != role)
                    return false;
                if constexpr (std::is_same_v<T, ArrayTraversal>)
                  if (node.collected && node.collected->port.role != role)
                    return false;
              } else if constexpr (!std::is_same_v<T, Drop> &&
                                   !std::is_same_v<T, Stop>) {
                if (node.output.port.role != role)
                  return false;
              }
              return true;
            },
            instruction);
        if (!local)
          return fail("library-role",
                      "region cannot schedule another participant");
      }
      if (const auto *call = std::get_if<Call>(&instruction)) {
        Signature sig;
        if (const auto *m = std::get_if<MemberCall>(&call->target)) {
          if (!call->attributes.empty())
            return fail("library-call-attributes",
                        "member calls have no attribute parameters");
          const Import *import = nullptr;
          for (const auto &i : imports)
            if (library::identity(i.parameter) ==
                library::identity(m->component))
              import = &i;
          if (!import)
            return fail("library-call",
                        "call is outside exact imported interface assumptions");
          const auto &d = import->interface.declaration();
          auto member = d.functions.find(m->member);
          if (member == d.functions.end())
            return fail("library-call",
                        "unknown interface function " + m->member);
          sig = replace(member->second, d.self, m->component);
        } else if (const auto *source =
                       std::get_if<SourceCall>(&call->target)) {
          if (!call->attributes.empty())
            return fail("library-call-attributes",
                        "source helpers have no attributes");
          auto instantiated = sourceSignature(*source, ctx);
          if (!instantiated)
            return instantiated.takeError();
          sig = std::move(*instantiated);
        } else {
          if (auto err = checkAttributes(std::get<LogicalCall>(call->target),
                                         call->attributes, e))
            return err;
          auto logical =
              logicalSignature(std::get<LogicalCall>(call->target), e);
          if (!logical)
            return logical.takeError();
          sig = *logical;
        }
        for (auto &p : sig.inputs) {
          if (p.role.empty())
            p.role = call->role;
          if (p.role != call->role)
            return fail("library-role",
                        "local call cannot span participant roles");
        }
        for (auto &p : sig.outputs) {
          if (p.role.empty())
            p.role = call->role;
          if (p.role != call->role)
            return fail("library-role", "local call cannot transfer custody");
        }
        if (auto err = signature(sig, ctx))
          return err;
        if (call->inputs.size() != sig.inputs.size() ||
            call->outputs.size() != sig.outputs.size())
          return fail("library-call-arity", "call port count differs");
        if (!std::includes(b.signature.effects.begin(),
                           b.signature.effects.end(), sig.effects.begin(),
                           sig.effects.end()))
          return fail("library-effect", "body exceeds declared effects");
        obligations.insert(obligations.end(), sig.preconditions.begin(),
                           sig.preconditions.end());
        if (auto err = prove(facts, sig.preconditions, e))
          return err;
        for (size_t i = 0; i < call->inputs.size(); ++i) {
          auto p = resources.use(call->inputs[i]);
          if (!p)
            return p.takeError();
          if (auto err = portEqual(*p, sig.inputs[i]))
            return err;
        }
        for (size_t i = 0; i < call->outputs.size(); ++i) {
          if (auto err = portEqual(call->outputs[i].port, sig.outputs[i]))
            return err;
          if (auto err = resources.define(call->outputs[i]))
            return err;
        }
        facts.insert(facts.end(), sig.postconditions.begin(),
                     sig.postconditions.end());
      } else if (const auto *c = std::get_if<Construct>(&instruction)) {
        auto ps = permissions(c->output.port.type, ctx);
        if (!ps)
          return ps.takeError();
        auto fields = children(c->output.port.type, e);
        if (!fields)
          return fields.takeError();
        if (fields->size() != c->elements.size())
          return fail("library-construct", "aggregate element count differs");
        for (size_t i = 0; i < fields->size(); ++i) {
          auto p = resources.use(c->elements[i]);
          if (!p)
            return p.takeError();
          if (auto err = portEqual(*p, Port{(*fields)[i], c->output.port.role}))
            return err;
        }
        if (auto err = resources.define(c->output))
          return err;
      } else if (const auto *p = std::get_if<Project>(&instruction)) {
        auto input = resources.use(p->input);
        if (!input)
          return input.takeError();
        if (auto err = portEqual(*input, p->output.port))
          return err;
        if (auto err = resources.define(p->output))
          return err;
      } else if (const auto *d = std::get_if<Drop>(&instruction)) {
        auto dropped = resources.use(d->input, true);
        if (!dropped)
          return dropped.takeError();
      } else if (const auto *c = std::get_if<VariantConstruct>(&instruction)) {
        auto permission = permissions(c->output.port.type, ctx);
        if (!permission)
          return permission.takeError();
        const auto &t = c->output.port.type;
        auto alternative =
            std::find(t.fields.begin(), t.fields.end(), c->alternative);
        if (t.kind != Type::Kind::Variant || alternative == t.fields.end())
          return fail("library-variant", "construction names no alternative");
        auto payload = resources.use(c->payload);
        if (!payload)
          return payload.takeError();
        if (auto err =
                portEqual(*payload, {t.elements[alternative - t.fields.begin()],
                                     c->output.port.role}))
          return err;
        if (auto err = resources.define(c->output))
          return err;
      } else if (auto *m = branches(instruction)) {
        auto input = resources.use(m->input);
        if (!input)
          return input.takeError();
        const auto &t = input->type;
        bool conditional = std::holds_alternative<Conditional>(instruction);
        const auto labels =
            conditional ? std::vector<std::string>{"then", "else"} : t.fields;
        if (conditional && !sameType(t, Type::logical("bool")))
          return fail("library-condition",
                      "conditional requires a Bool condition");
        if (!conditional && (t.kind != Type::Kind::Variant ||
                             m->arms.size() != t.fields.size()))
          return fail("library-match",
                      "match must cover every alternative exactly once");
        if (input->role != m->role)
          return fail("library-role", "match tag is not local to participant");
        std::vector<Port> captures, outputs;
        for (const auto &p : m->captures) {
          auto v = resources.use(p);
          if (!v)
            return v.takeError();
          if (v->role != m->role)
            return fail("library-role", "nonlocal match capture");
          captures.push_back(*v);
        }
        for (const auto &v : m->outputs) {
          if (v.port.role != m->role)
            return fail("library-role", "nonlocal match result");
          outputs.push_back(v.port);
        }
        if (m->arms.size() != labels.size())
          return fail("library-branch-arm",
                      "branch must cover each arm exactly once");
        std::set<std::string> seen;
        std::vector<Requirement> common;
        bool firstArm = true, continues = false;
        auto factKey = [](const Requirement &r) {
          Writer w;
          w.add(r.relation);
          w.list(r.arguments,
                 [&](const auto &a) { w.add(library::identity(a)); });
          return w.bytes;
        };
        // Every arm is checked, whatever constructor a producer is known to
        // select: selection is a runtime fact, not a checking premise.
        for (auto &arm : m->arms) {
          auto found = std::find(labels.begin(), labels.end(), arm.alternative);
          if (!arm.body || found == labels.end() ||
              !seen.insert(arm.alternative).second)
            return fail(conditional ? "library-branch-arm" : "library-match",
                        "missing, duplicate or unknown branch arm");
          auto region = std::make_shared<Region>(*arm.body);
          std::vector<Port> inputs;
          if (!conditional)
            inputs.push_back({t.elements[found - labels.begin()], m->role});
          inputs.insert(inputs.end(), captures.begin(), captures.end());
          std::vector<Requirement> branchFacts;
          if (auto err = checkRegion(*region, inputs, outputs, facts, depth + 1,
                                     m->role, &branchFacts))
            return err;
          // A terminal arm yields nothing, so it can neither establish nor
          // weaken a continuation fact. The join keeps exactly what every
          // continuing arm established.
          if (!terminal(region->instructions)) {
            continues = true;
            if (firstArm) {
              common = std::move(branchFacts);
              firstArm = false;
            } else {
              std::set<std::string> keys;
              for (const auto &r : branchFacts)
                keys.insert(factKey(r));
              common.erase(std::remove_if(common.begin(), common.end(),
                                          [&](const auto &r) {
                                            return !keys.count(factKey(r));
                                          }),
                           common.end());
            }
          }
          arm.body = std::move(region);
        }
        // An exhaustive join whose every arm is terminal cannot continue
        // either: it carries no result and ends its own region.
        if (!continues && !m->outputs.empty())
          return fail("library-stop",
                      "every arm stops while the join declares results");
        if (continues)
          facts = std::move(common);
        else
          stops = true;
        for (const auto &v : m->outputs)
          if (auto err = resources.define(v))
            return err;
      } else if (const auto *s = std::get_if<Stop>(&instruction)) {
        // The reason reaches the lowered stop unchanged, so only the terminal
        // vocabulary that the common source model already admits is accepted.
        if (s->reason != "reject" && s->reason != "abort" &&
            s->reason != "exhausted" && s->reason != "incomplete" &&
            s->reason != "refused")
          return fail("library-stop", "unknown terminal stop reason");
        stops = true;
      } else {
        auto &a = std::get<ArrayTraversal>(instruction);
        auto input = resources.use(a.input);
        if (!input)
          return input.takeError();
        if (input->type.kind != Type::Kind::Array || !a.body)
          return fail("library-traversal",
                      "traversal requires an array and body");
        if (input->role != a.role)
          return fail("library-role", "nonlocal traversal");
        std::vector<Port> inputs{{input->type.elements.front(), a.role}},
            outputs;
        for (const auto &p : a.initial) {
          auto v = resources.use(p);
          if (!v)
            return v.takeError();
          if (v->role != a.role)
            return fail("library-role", "nonlocal carried state");
          outputs.push_back(*v);
          inputs.push_back(*v);
        }
        for (const auto &p : a.captures) {
          auto v = resources.use(p);
          if (!v)
            return v.takeError();
          auto permission = permissions(v->type, ctx);
          if (!permission)
            return permission.takeError();
          if (!permission->copy)
            return fail("library-traversal-capture",
                        "invariant capture must be copyable");
          if (v->role != a.role)
            return fail("library-role", "nonlocal traversal capture");
          inputs.push_back(*v);
        }
        if (a.outputs.size() != outputs.size())
          return fail("library-traversal", "carried state arity differs");
        if (a.collected) {
          const auto &t = a.collected->port.type;
          if (t.kind != Type::Kind::Array || t.arguments.size() != 1 ||
              t.elements.size() != 1 || a.collected->port.role != a.role ||
              !sameType(Type::array(input->type.elements.front(),
                                    t.arguments.front()),
                        input->type))
            return fail("library-traversal",
                        "collected array count or role differs");
          outputs.push_back({t.elements.front(), a.role});
        }
        auto region = std::make_shared<Region>(*a.body);
        if (auto err = checkRegion(*region, inputs, outputs, facts, depth + 1,
                                   a.role, nullptr))
          return err;
        a.body = std::move(region);
        for (size_t i = 0; i < a.outputs.size(); ++i) {
          if (auto err = portEqual(a.outputs[i].port, outputs[i]))
            return err;
          if (auto err = resources.define(a.outputs[i]))
            return err;
        }
        if (a.collected)
          if (auto err = resources.define(*a.collected))
            return err;
      }
    }

    // A terminal region owes no result, no postcondition and no remaining
    // resource: nothing continues, and cleanup after a stop belongs to the
    // runtime rather than to a fabricated drop here.
    if (stops) {
      if (!region.returns.empty())
        return fail("library-stop", "a terminal region cannot return values");
      return llvm::Error::success();
    }
    if (region.returns.size() != outputs.size())
      return fail("library-return", "region return count differs");
    for (size_t i = 0; i < outputs.size(); ++i) {
      auto p = resources.use(region.returns[i]);
      if (!p)
        return p.takeError();
      if (auto err = portEqual(*p, outputs[i]))
        return err;
    }
    for (const auto &v : resources.values)
      if (auto err = resources.remaining(v.second.type, v.first, {}, 0))
        return err;
    if (established)
      *established = facts;
    if (!depth)
      return prove(facts, b.signature.postconditions, e);
    return llvm::Error::success();
  };
  Region root{b.inputs, b.instructions, b.returns};
  if (auto err = checkRegion(root, b.signature.inputs, b.signature.outputs,
                             facts, 0, "", nullptr))
    return err;
  b.instructions = std::move(root.instructions);
  obligations.insert(obligations.end(), b.signature.postconditions.begin(),
                     b.signature.postconditions.end());
  auto data = std::make_shared<CheckedBody::Data>();
  Writer key;
  key.add(encode(b));
  key.add(encode(e));
  for (const auto &i : imports) {
    key.add(library::identity(i.parameter));
    key.add(i.interface.identity());
  }
  data->identity = std::move(key.bytes);
  data->fingerprint = hash(data->identity);
  data->body = std::move(b);
  data->environment = std::move(e);
  data->imports = std::move(imports);
  data->obligations = std::move(obligations);
  return CheckedBody(std::move(data));
}
} // namespace zkc::frontend::library
