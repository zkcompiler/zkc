#include "Names.h"
#include "../Static/Attributes.h"
#include "../Static/Types.h"
#include "Declarations.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::frontend::resolution {
namespace {
struct Names {
  std::set<std::string> values, statics, types, components;
};
/// Records each syntax reference's resolved target in its lexical scope. A
/// lexical binder is a one-segment reference in its own category; everything
/// else is resolved from its authored segments by the project resolver.
class Qualifier {
  const Context &context;
  const ModuleResolver &resolver;
  bool signature = false;

  // A reference is recorded at its owning node: a call expression, place,
  // declaration clause or term root. Provenance relates diagnostics inside
  // that node to the referenced declaration.
  std::optional<Resolved> resolve(const syntax::Path &path,
                                  const source::Node &n, ReferenceKind kind) {
    return resolver.path(path, n, kind, signature);
  }
  const Declaration *reference(syntax::Reference &r, const source::Node &n,
                               const Names &locals, ReferenceKind kind) {
    const auto &segments = r.path.segments;
    // Later stages construct already resolved references without a path.
    if (segments.empty())
      return nullptr;
    const auto &head = segments.front();
    if (segments.size() == 1 &&
        ((kind == ReferenceKind::Value && locals.values.count(head)) ||
         (kind == ReferenceKind::Predicate && locals.statics.count(head)))) {
      r.target = syntax::Target::local(head);
      return nullptr;
    }
    // Only a member of an interface-bound component parameter is a local
    // call; every other path names a declaration or installed operation.
    if (segments.size() == 2 && kind == ReferenceKind::Call &&
        locals.components.count(head)) {
      r.target = {syntax::Target::Kind::Parameter, head, {segments[1]}};
      return nullptr;
    }
    auto resolved = resolve(r.path, n, kind);
    if (!resolved)
      return nullptr;
    r.target = std::move(resolved->target);
    return resolved->declaration;
  }
  // A static root and its members form one path. The root becomes the
  // resolved symbol; the remaining members stay associated projections.
  void rooted(std::string &root, source::Names &members, const source::Node &n,
              const Names &locals, ReferenceKind kind) {
    bool local = kind == ReferenceKind::Type
                     ? locals.types.count(root) ||
                           (!members.empty() && locals.statics.count(root))
                     : locals.statics.count(root);
    if (local)
      return;
    syntax::Path path;
    path.location = n.location;
    path.segments.push_back(root);
    llvm::append_range(path.segments, members);
    auto resolved = resolve(path, n, kind);
    if (!resolved)
      return;
    root = resolved->target.symbol;
    members = resolved->target.members;
  }
  void atom(syntax::Atom &a, const Names &locals,
            ReferenceKind kind = ReferenceKind::Static) {
    if (a.kind == syntax::Atom::Kind::Name) {
      source::Names members;
      rooted(a.value, members, a, locals, kind);
    }
  }
  void term(syntax::StaticTerm &t, const Names &locals,
            ReferenceKind kind = ReferenceKind::Static) {
    if (t.root.kind == syntax::Atom::Kind::Number)
      return;
    if (kind == ReferenceKind::Static && typeArgumentSyntax(t)) {
      auto expression = syntax::typeExpression(t);
      type(expression, locals);
      t = syntax::staticExpression(expression);
      return;
    }
    // A quoted root is exact installed data, never a lexical reference.
    if (t.root.kind == syntax::Atom::Kind::String) {
      resolver.exact(t.root.value, t.root, kind);
      return;
    }
    rooted(t.root.value, t.members, t.root, locals, kind);
  }
  void terms(syntax::StaticAssignments &assignments, const Names &locals) {
    for (auto &[name, value] : assignments)
      term(value, locals);
  }
  void type(syntax::Type &t, const Names &locals, bool staticArgument = false) {
    if (!t.natural() && !t.product) {
      if (t.quoted())
        resolver.exact(t.name, t,
                       staticArgument || !t.members.empty()
                           ? ReferenceKind::Static
                           : ReferenceKind::Type);
      else
        rooted(t.name, t.members, t, locals,
               staticArgument ? ReferenceKind::Static : ReferenceKind::Type);
    }
    // A ResourceUnit slot is an opaque literal checked by its type owner.
    if (!t.quoted() && t.name == "ResourceUnit")
      return;
    for (size_t i = 0; i < t.arguments.size(); ++i) {
      // Array/Vector/Matrix contain element types. Other installed constructors
      // and source nominal applications take static domains/counts/components.
      bool argument =
          !t.product && ((t.name == "Array" && i == 1) ||
                         (t.name != "Array" && !elementTypeFamily(t.name)));
      if (const auto *declaration =
              protocol::typeDeclaration(logicalConstructor(t.name));
          declaration && i < declaration->parameters.size())
        argument =
            declaration->parameters[i].kind != protocol::StaticKind::Type;
      type(t.arguments[i], locals, argument);
    }
  }
  void place(syntax::Place &p, const source::Node &n, const Names &locals) {
    reference(p.root, p.location ? p : n, locals, ReferenceKind::Value);
  }
  void places(syntax::Places &places, const source::Node &n,
              const Names &locals) {
    for (auto &p : places)
      place(p, n, locals);
  }
  void libraryTerm(syntax::LibraryTerm &t, const Names &locals) {
    syntax::StaticTerm s{t.root, t.members};
    term(s, locals);
    t.root = std::move(s.root);
    t.members = std::move(s.members);
    for (auto &arg : t.arguments)
      libraryTerm(arg, locals);
  }
  void parameters(std::vector<syntax::StaticParameter> &ps, Names &locals) {
    for (const auto &p : ps) {
      locals.statics.insert(p.name);
      if (llvm::any_of(p.bounds, [](const auto &bound) {
            return bound.path.segments == source::Names{"Type"};
          }))
        locals.types.insert(p.name);
    }
    for (auto &p : ps)
      for (auto &bound : p.bounds)
        if (const auto *d =
                reference(bound, p, locals, ReferenceKind::Predicate))
          if (d->kind == Declaration::Kind::Interface)
            locals.components.insert(p.name);
  }
  void requirements(std::vector<syntax::Requirement> &rs, const Names &locals) {
    for (auto &r : rs)
      if (r.predicate)
        reference(*r.predicate, r, locals, ReferenceKind::Predicate);
    for (auto &r : rs)
      for (auto &t : r.arguments)
        term(t, locals);
  }
  // Only operation-owned natural slots name constants. Other attributes are
  // opaque operation data (labels, schema names, codecs), even when bare.
  void attributes(std::vector<syntax::Atom> &atoms,
                  const syntax::Target &callee, const Names &locals) {
    std::string operation;
    if (callee.kind == syntax::Target::Kind::Operation)
      operation = callee.symbol;
    else if (callee.kind == syntax::Target::Kind::Declaration &&
             callee.members.empty()) {
      auto binding = context.bindingContracts.find(callee.symbol);
      if (binding == context.bindingContracts.end())
        return;
      operation = binding->second;
    } else
      return;
    for (size_t i = 0; i < atoms.size(); ++i)
      if (naturalAttribute(operation, i))
        atom(atoms[i], locals);
  }
  void expression(syntax::Expression &e, const Names &locals) {
    using K = syntax::Expression::Kind;
    if (e.kind == K::Call)
      reference(e.reference, e, locals, ReferenceKind::Call);
    else if (e.kind == K::Struct)
      reference(e.reference, e, locals, ReferenceKind::Constructor);
    else if (e.kind == K::Name)
      reference(e.reference, e, locals, ReferenceKind::Value);
    if (e.staticArguments)
      for (auto &s : *e.staticArguments)
        term(s, locals);
    if (e.kind == K::Call)
      attributes(e.attributes, e.reference.target, locals);
    for (auto &o : e.operands)
      expression(o, locals);
    if (e.traversal) {
      auto nested = locals;
      nested.values.insert(e.traversal->element);
      if (!e.traversal->state.empty())
        nested.values.insert(e.traversal->state);
      body(e.traversal->body, std::move(nested));
    }
  }
  void body(syntax::Body &b, Names locals) {
    for (auto &i : b) {
      std::visit(
          [&](auto &v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, syntax::Call>) {
              if (!v.operatorSymbol)
                reference(v.callee, v, locals, ReferenceKind::Call);
              if (v.staticArguments)
                for (auto &s : *v.staticArguments)
                  term(s, locals);
              attributes(v.attributes, v.callee.target, locals);
              places(v.inputs, v, locals);
              if (v.annotation)
                for (auto &t : *v.annotation)
                  type(t, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Binding>) {
              expression(v.expression, locals);
              if (v.assignment)
                place(*v.assignment, v, locals);
              if (v.annotation)
                for (auto &t : *v.annotation)
                  type(t, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Placement>) {
              if (v.annotation)
                type(*v.annotation, locals);
              body(v.body, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Exit>) {
              expression(v.expression, locals);
            } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
              places(v.captures, i, locals);
              expression(v.condition, locals);
              body(v.thenBody, locals);
              body(v.elseBody, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Match>) {
              place(v.input, i, locals);
              places(v.captures, i, locals);
              for (auto &a : v.arms) {
                auto inner = locals;
                inner.values.insert(a.payload.begin(), a.payload.end());
                body(a.body, std::move(inner));
              }
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Loop> ||
                                 std::is_same_v<T, syntax::For> ||
                                 std::is_same_v<T, syntax::ArrayTraversal>) {
              places(v.captures, i, locals);
              auto inner = locals;
              if constexpr (std::is_same_v<T, syntax::Loop>) {
                atom(v.count, locals);
              } else if constexpr (std::is_same_v<T, syntax::For>) {
                expression(v.lower, locals);
                expression(v.upper, locals);
                inner.values.insert(v.induction);
              } else {
                place(v.input, i, locals);
                inner.values.insert(v.element);
              }
              for (auto &p : v.carried) {
                place(p.second, i, locals);
                inner.values.insert(p.first);
              }
              body(v.body, std::move(inner));
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Message>) {
              place(v.input, i, locals);
              locals.values.insert(v.output);
            } else if constexpr (std::is_same_v<T, syntax::Return> ||
                                 std::is_same_v<T, syntax::Yield>) {
              places(v.values, i, locals);
            } else if constexpr (std::is_same_v<T, syntax::Finish>) {
              for (auto &value : v.values)
                place(value.second, i, locals);
            } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
              // Protocol dependency aliases, like roles, live in a separate
              // scope. Inputs still use the enclosing lexical value scope.
              places(v.inputs, i, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            }
          },
          i.value);
    }
  }
  void function(syntax::Function &f, Names locals) {
    signature = true; // Private signatures also participate in public closure.
    parameters(f.parameters, locals);
    requirements(f.requirements, locals);
    for (auto &a : f.arguments) {
      type(a.type, locals);
      locals.values.insert(a.name);
    }
    for (auto &r : f.results)
      type(r, locals);
    signature = false;
    if (f.body)
      body(*f.body, std::move(locals));
  }
  void interface(syntax::LibraryInterface &i, Names locals,
                 bool concrete = false) {
    signature = true;
    locals.statics.insert("Self");
    locals.components.insert("Self");
    if (!concrete) {
      // Interface equations and signatures refer to their abstract members.
      for (const auto &t : i.types)
        locals.types.insert(t.name);
      for (const auto &s : i.statics)
        locals.statics.insert(s.name);
    }
    // Concrete equations/representations bind sequentially, exactly as
    // Author::checkComponent does. A self/forward spelling cannot authorize an
    // unrelated declaration from the eventual merged namespace.
    for (auto &s : i.statics) {
      if (s.equation)
        libraryTerm(*s.equation, locals);
      locals.statics.insert(s.name);
    }
    for (auto &t : i.types) {
      if (t.representation)
        type(*t.representation, locals);
      locals.types.insert(t.name);
    }
    signature = false;
    for (auto &f : i.functions)
      function(f, locals);
  }

public:
  Qualifier(const Context &context, const ModuleResolver &resolver)
      : context(context), resolver(resolver) {}
  void run(syntax::Module &m) {
    for (auto &f : m.functions)
      function(f, {});
    for (auto &p : m.protocols) {
      Names locals;
      signature = true;
      parameters(p.staticParameters, locals);
      requirements(p.requirements, locals);
      locals.statics.insert(p.parameters.begin(), p.parameters.end());
      for (auto &a : p.arguments) {
        type(a.type, locals);
        locals.values.insert(a.name);
      }
      for (auto &r : p.results)
        type(r.type, locals);
      signature = false;
      for (auto &d : p.dependencies) {
        reference(d.protocol, d, {}, ReferenceKind::Declaration);
        if (d.arguments)
          terms(*d.arguments, locals);
      }
      if (p.body)
        body(*p.body, locals);
    }
    for (auto &i : m.libraryInterfaces)
      interface(i, {});
    for (auto &c : m.libraryComponents) {
      Names locals;
      signature = true;
      parameters(c.parameters, locals);
      reference(c.interface, c, locals, ReferenceKind::Declaration);
      interface(c, locals, true);
    }
    signature = true;
    for (auto &s : m.librarySelections)
      libraryTerm(s.target, {});
    for (auto &l : m.libraryLinks) {
      reference(l.client, l, {}, ReferenceKind::Call);
      for (auto &a : l.arguments)
        libraryTerm(a, {});
    }
    for (auto &s : m.structs) {
      Names locals;
      signature = true;
      parameters(s.parameters, locals);
      for (auto &f : s.fields)
        type(f.type, locals);
      signature = false;
      for (auto &c : s.constructors)
        reference(c, s, {}, ReferenceKind::Call);
    }
    for (auto &e : m.enums) {
      Names locals;
      signature = true;
      parameters(e.parameters, locals);
      for (auto &a : e.alternatives)
        type(a.type, locals);
      signature = false;
    }
    for (auto &b : m.bundles) {
      Names locals;
      locals.statics.insert(b.parameters.begin(), b.parameters.end());
      requirements(b.requirements, locals);
    }
    for (auto &c : m.constants)
      expression(c.expression, {});
    signature = true;
    for (auto &c : m.configurations) {
      reference(c.base, c, {}, ReferenceKind::Declaration);
      terms(c.arguments, {});
    }
    signature = false;
    for (auto &v : m.relationViews) {
      reference(v.relation, v, {}, ReferenceKind::Declaration);
      if (v.height)
        atom(*v.height, {});
    }
    for (auto &i : m.instances) {
      reference(i.protocol, i, {}, ReferenceKind::Declaration);
      for (auto &d : i.dependencies)
        reference(d.second, i, {}, ReferenceKind::Declaration);
      for (auto &[key, parameter] : i.parameters) {
        atom(parameter.value, {});
        if (parameter.ingress)
          for (auto &s : *parameter.ingress)
            reference(s.function, i, {}, ReferenceKind::Call);
      }
    }
    for (auto &e : m.entries) {
      reference(e.instance, e, {}, ReferenceKind::Declaration);
      if (e.arguments)
        terms(*e.arguments, {});
    }
    // Definitions are renamed only after all references have resolved in their
    // original lexical scope. The symbol is an injective projection of DeclId.
    declarations(m, [&](auto &d, auto) {
      if (auto symbol = resolver.definition(d.name))
        d.name = std::move(*symbol);
    });
    for (auto &f : m.functions)
      if (!f.generic && !f.explicitOrigin)
        if (const auto *d = context.lookup(f.name))
          f.origin = source::LogicalOrigin{d->origin, {}};
  }
};
} // namespace
void qualify(syntax::Module &m, const Context &c, const ModuleResolver &r) {
  Qualifier(c, r).run(m);
}
} // namespace zkc::frontend::resolution
