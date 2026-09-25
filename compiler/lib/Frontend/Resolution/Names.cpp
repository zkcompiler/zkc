#include "Names.h"
#include "Declarations.h"
#include "Vocabulary.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::frontend::resolution {
namespace {
struct Names {
  std::set<std::string> values, statics, types, components;
};
class Qualifier {
  const Context &context;
  const ReferenceResolver &resolve;
  bool signature = false;
  source::Node ownerNode;

  const Declaration *name(std::string &s, const source::Node &n,
                          const Names &locals = {},
                          ReferenceKind kind = ReferenceKind::Value,
                          bool quoted = false, StringRef lexicalRoot = {}) {
    // Static/type roots come from parser structure. A dot inside an opaque
    // identifier does not turn its prefix into a local namespace.
    const auto head =
        !lexicalRoot.empty() ? lexicalRoot.str()
        : kind == ReferenceKind::Value || kind == ReferenceKind::QualifiedCall
            ? StringRef(s).split('.').first.str()
            : s;
    bool local = false;
    switch (kind) {
    case ReferenceKind::Value:
      local = locals.values.count(s) || locals.values.count(head);
      break;
    case ReferenceKind::Type:
      local = locals.types.count(head) ||
              (!lexicalRoot.empty() && lexicalRoot != s &&
               locals.statics.count(head));
      break;
    case ReferenceKind::Static:
    case ReferenceKind::Predicate:
      local = locals.statics.count(head);
      break;
    case ReferenceKind::QualifiedCall:
      local = StringRef(s).contains('.') && locals.components.count(head);
      break;
    case ReferenceKind::Call:
    case ReferenceKind::Constructor:
    case ReferenceKind::Declaration:
      break;
    }
    if (!quoted && local)
      return nullptr;
    return resolve(s, n.location ? n : ownerNode, kind, signature, quoted);
  }
  void atom(syntax::Atom &a, const Names &locals,
            ReferenceKind kind = ReferenceKind::Static) {
    if (a.kind == syntax::Atom::Kind::Name)
      name(a.value, a, locals, kind);
  }
  void term(syntax::StaticTerm &t, const Names &locals,
            ReferenceKind kind = ReferenceKind::Static) {
    if (t.root.kind == syntax::Atom::Kind::Number)
      return;
    // An installed opaque root (bn254.fr) remains one root. Only the parser's
    // explicit members are projections; namespace names cannot split it.
    if (t.root.kind == syntax::Atom::Kind::String ||
        !protocol::installedIdentitySort(t.root.value).empty()) {
      if (name(t.root.value, t.root, {}, kind,
               t.root.kind == syntax::Atom::Kind::String))
        t.root.kind = syntax::Atom::Kind::Name;
      return;
    }
    std::string s = t.root.value;
    for (const auto &m : t.members)
      s += "::" + m;
    const auto *d = name(s, t.root, locals, kind, false, t.root.value);
    if (!d)
      return;
    t.root.value = d->symbol;
    projectedMembers(StringRef(s).drop_front(d->symbol.size()), t.members);
  }
  // Resolution retains explicit separators until the structured path is
  // rebuilt. A dot inside one parser member must never become two members.
  void projectedMembers(StringRef tail, source::Names &members) {
    members.clear();
    while (!tail.empty()) {
      const bool explicitMember = tail.consume_front("::");
      if (!explicitMember)
        tail.consume_front(".");
      auto end = explicitMember ? tail.find("::") : tail.find_first_of(".:");
      members.push_back(tail.take_front(end).str());
      tail = end == StringRef::npos ? StringRef{} : tail.drop_front(end);
    }
  }

  void type(syntax::Type &t, const Names &locals, bool staticArgument = false) {
    if (!t.natural && !t.product) {
      if (t.quoted || !protocol::installedIdentitySort(t.name).empty()) {
        if (name(t.name, t, {},
                 (staticArgument || !t.members.empty()) ? ReferenceKind::Static
                                                        : ReferenceKind::Type,
                 t.quoted))
          t.quoted = false;
      } else {
        std::string s = t.name;
        for (const auto &m : t.members)
          s += "::" + m;
        const auto *d =
            name(s, t, locals,
                 staticArgument ? ReferenceKind::Static : ReferenceKind::Type,
                 false, t.name);
        if (d) {
          t.name = d->symbol;
          projectedMembers(StringRef(s).drop_front(d->symbol.size()), t.members);
        }
      }
    }
    // A ResourceUnit slot is an opaque literal checked by its type owner.
    if (!t.quoted && t.name == "ResourceUnit")
      return;
    for (size_t i = 0; i < t.arguments.size(); ++i) {
      // Array/Vector/Matrix contain element types. Other installed constructors
      // and source nominal applications take static domains/counts/components.
      bool argument =
          !t.product &&
          ((t.name == "Array" && i == 1) ||
           (t.name != "Array" && t.name != "Vector" && t.name != "Matrix"));
      type(t.arguments[i], locals, argument);
    }
  }
  void callable(std::string &s, const source::Node &n, const Names &locals,
                bool &quoted, bool &qualified) {
    // Only explicit member syntax denotes a local component's member. An
    // opaque dotted callee must resolve as an exact declaration/installed name.
    const auto *d = name(
        s, n, qualified ? locals : Names{},
        qualified ? ReferenceKind::QualifiedCall : ReferenceKind::Call, quoted);
    if (d)
      quoted = false;
    if (d && ((s == d->symbol && (d->kind == Declaration::Kind::Function ||
                                  d->kind == Declaration::Kind::Configuration ||
                                  d->kind == Declaration::Kind::Link)) ||
              (d->kind == Declaration::Kind::View &&
               StringRef(s).starts_with(d->symbol + "_"))))
      qualified = false;
  }
  void values(source::Names &names, const source::Node &n,
              const Names &locals) {
    for (auto &s : names)
      name(s, n, locals);
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
    for (const auto &p : ps)
      locals.statics.insert(p.name);
    for (auto &p : ps)
      for (auto &bound : p.bounds)
        if (const auto *d = name(bound, p, locals, ReferenceKind::Predicate))
          if (d->kind == Declaration::Kind::Interface)
            locals.components.insert(p.name);
  }
  void requirements(std::vector<source::Requirement> &rs,
                    std::vector<std::vector<syntax::StaticTerm>> &ts,
                    const Names &locals) {
    for (auto &r : rs) {
      name(r.predicate, r, locals, ReferenceKind::Predicate);
    }
    for (size_t i = 0; i < ts.size(); ++i) {
      for (auto &t : ts[i])
        term(t, locals);
      if (i < rs.size())
        for (size_t j = 0; j < ts[i].size() && j < rs[i].arguments.size();
             ++j) {
          auto &out = rs[i].arguments[j];
          out = ts[i][j].root.value;
          for (const auto &member : ts[i][j].members)
            out += "." + member;
        }
    }
  }
  void sync(source::Names &names, const std::vector<syntax::StaticTerm> &ts) {
    for (size_t i = 0; i < names.size() && i < ts.size(); ++i) {
      names[i] = ts[i].root.value;
      for (const auto &member : ts[i].members)
        names[i] += "." + member;
    }
  }
  void attributes(source::Names &values, std::vector<syntax::Atom> &atoms,
                  StringRef callee, bool qualified, const Names &locals) {
    auto op = callee.str();
    if (!qualified) {
      auto binding = context.bindingContracts.find(op);
      if (binding == context.bindingContracts.end())
        return;
      op = binding->second;
    }
    // Match the staging owner's numeric slots. Other attributes are opaque
    // operation data (labels, schema names, codecs), even when written bare.
    for (size_t i = 0; i < atoms.size() && i < values.size(); ++i) {
      bool numeric =
          ((op == "index.constant" || op == "vector.splat" ||
            op == "vector.powers" || op == "vector.at" ||
            op == "vector.length_check" || op == "poly.degree_check" ||
            op == "random.vector" || op == "curve.at") &&
           i == 0) ||
          (op == "matrix.shape_check" && i < 2) ||
          (op == "vector.matvec" && i < 3);
      if (numeric) {
        atom(atoms[i], locals);
        values[i] = atoms[i].value;
      }
    }
  }
  void expression(syntax::Expression &e, const Names &locals) {
    using K = syntax::Expression::Kind;
    if (e.kind == K::Call)
      callable(e.name, e, locals, e.quoted, e.qualified);
    else if (e.kind == K::Struct)
      name(e.name, e, locals, ReferenceKind::Constructor, e.quoted);
    else if (e.kind == K::Name && !e.quoted)
      name(e.name, e, locals);
    for (auto &s : e.staticTerms)
      term(s, locals);
    if (e.staticArguments)
      sync(*e.staticArguments, e.staticTerms);
    attributes(e.attributes, e.attributeAtoms, e.name, e.qualified, locals);
    for (auto &o : e.operands)
      expression(o, locals);
    if (e.traversal) {
      values(e.traversal->captures, e, locals);
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
              if (!v.isOperator)
                callable(v.callee, v, locals, v.quoted, v.qualified);
              for (auto &s : v.staticTerms)
                term(s, locals);
              if (v.staticArguments)
                sync(*v.staticArguments, v.staticTerms);
              attributes(v.attributes, v.attributeAtoms, v.callee, v.qualified,
                         locals);
              for (auto &a : v.inputAtoms)
                atom(a, locals, ReferenceKind::Value);
              for (size_t n = 0; n < v.inputs.size(); ++n)
                if (n < v.inputAtoms.size())
                  v.inputs[n] = v.inputAtoms[n].value;
                else
                  name(v.inputs[n], v, locals);
              if (v.annotation)
                for (auto &t : *v.annotation)
                  type(t, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Binding>) {
              expression(v.expression, locals);
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
              values(v.captures, i, locals);
              expression(v.condition, locals);
              body(v.thenBody, locals);
              body(v.elseBody, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Match>) {
              name(v.input, i, locals);
              values(v.captures, i, locals);
              for (auto &a : v.arms) {
                auto inner = locals;
                inner.values.insert(a.payload.begin(), a.payload.end());
                body(a.body, std::move(inner));
              }
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Loop> ||
                                 std::is_same_v<T, syntax::For> ||
                                 std::is_same_v<T, syntax::ArrayTraversal>) {
              values(v.captures, i, locals);
              auto inner = locals;
              if constexpr (std::is_same_v<T, syntax::Loop>) {
                if (v.countAtom) {
                  atom(*v.countAtom, locals);
                  v.count.value = v.countAtom->value;
                }
              } else if constexpr (std::is_same_v<T, syntax::For>) {
                expression(v.lower, locals);
                expression(v.upper, locals);
                inner.values.insert(v.induction);
              } else {
                name(v.input, i, locals);
                inner.values.insert(v.element);
              }
              for (auto &p : v.carried) {
                name(p.second, i, locals);
                inner.values.insert(p.first);
              }
              body(v.body, std::move(inner));
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, source::Message>) {
              name(v.input, i, locals);
              locals.values.insert(v.output);
            } else if constexpr (std::is_same_v<T, source::Return> ||
                                 std::is_same_v<T, source::Yield>) {
              values(v.values, i, locals);
            } else if constexpr (std::is_same_v<T, syntax::Finish>) {
              for (auto &value : v.values)
                name(value.second, i, locals);
            } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
              // Protocol dependency aliases, like roles, live in a separate
              // scope. Inputs still use the enclosing lexical value scope.
              values(v.inputs, i, locals);
              locals.values.insert(v.outputs.begin(), v.outputs.end());
            }
          },
          i.value);
    }
  }
  void function(syntax::Function &f, Names locals, bool /*isPublic*/) {
    signature = true; // Private signatures also participate in public closure.
    parameters(f.parameters, locals);
    requirements(f.requirements, f.requirementTerms, locals);
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
  void interface(syntax::LibraryInterface &i, Names locals, bool isPublic,
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
      function(f, locals, isPublic);
  }
  template <typename Map, typename Fn> void keys(Map &map, Fn fn) {
    Map renamed;
    for (auto &[key, value] : map) {
      auto k = key;
      // A key is its own definition's name: exact, as a quoted name is.
      const auto *d = name(k, {}, {}, ReferenceKind::Declaration, true);
      ownerNode.location = d ? d->location : std::nullopt;
      fn(value);
      ownerNode = {};
      renamed.emplace(std::move(k), std::move(value));
    }
    map = std::move(renamed);
  }

public:
  Qualifier(const Context &context, const ReferenceResolver &resolve)
      : context(context), resolve(resolve) {}
  void run(syntax::Module &m) {
    auto exported = [&](StringRef s) {
      return llvm::is_contained(m.exports, s);
    };
    for (auto &f : m.functions)
      function(f, {}, exported(f.name));
    for (auto &p : m.protocols) {
      Names locals;
      signature = true;
      parameters(p.staticParameters, locals);
      requirements(p.requirements, p.requirementTerms, locals);
      locals.statics.insert(p.parameters.begin(), p.parameters.end());
      for (auto &a : p.arguments) {
        type(a.type, locals);
        locals.values.insert(a.name);
      }
      for (auto &r : p.results)
        type(r.type, locals);
      signature = false;
      for (auto &d : p.dependencies)
        name(d.protocol, d, {}, ReferenceKind::Declaration,
             p.quotedDependencies.count(d.name));
      for (auto &[alias, args] : p.dependencyArguments)
        for (auto &t : args.terms)
          term(t, locals);
      if (p.body)
        body(*p.body, locals);
    }
    for (auto &i : m.libraryInterfaces)
      interface(i, {}, exported(i.name));
    for (auto &c : m.libraryComponents) {
      Names locals;
      signature = true;
      parameters(c.parameters, locals);
      name(c.interface, c, locals, ReferenceKind::Declaration,
           c.quotedInterface);
      interface(c, locals, false, true);
    }
    signature = true;
    for (auto &s : m.librarySelections)
      libraryTerm(s.target, {});
    for (auto &l : m.libraryLinks) {
      name(l.client, l, {}, ReferenceKind::Call, l.quotedClient);
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
        name(c, s, {}, ReferenceKind::Call, s.quotedConstructors.count(c));
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
      requirements(b.requirements, b.requirementTerms, locals);
    }
    for (auto &c : m.constants)
      expression(c.expression, {});
    signature = true;
    for (auto &c : m.configurations)
      name(c.base, c, {}, ReferenceKind::Declaration,
           m.quotedBases.count(c.name));
    signature = false;
    for (auto &v : m.relationViews)
      name(v.relation, v, {}, ReferenceKind::Declaration,
           m.quotedRelations.count(v.name));
    for (auto &i : m.instances) {
      // The protocol's spelling is its term's; the term keeps the quoting.
      auto term = m.instanceProtocolTerms.find(i.name);
      name(i.protocol, i, {}, ReferenceKind::Declaration,
           term != m.instanceProtocolTerms.end() &&
               term->second.root.kind == syntax::Atom::Kind::String);
      for (auto &d : i.dependencies)
        name(d.second, i, {}, ReferenceKind::Declaration,
             m.quotedInstanceDependencies.count({i.name, d.first}));
      for (auto &[key, binding] : i.parameters)
        if (auto *family = std::get_if<source::FamilyIngress>(&binding))
          for (auto &s : family->selectors)
            name(s.function, i, {}, ReferenceKind::Call,
                 m.quotedSelectors.count({i.name, key, s.role}));
    }
    for (auto &e : m.entries)
      name(e.instance, e, {}, ReferenceKind::Declaration,
           m.quotedInstances.count(e.name));
    keys(m.entryArguments, [&](auto &d) {
      for (auto &t : d.terms)
        term(t, {});
    });
    keys(m.instanceParameterAtoms, [&](auto &atoms) {
      for (auto &a : atoms)
        atom(a, {});
    });
    keys(m.instanceProtocolTerms,
         [&](auto &t) { term(t, {}, ReferenceKind::Declaration); });
    signature = true;
    keys(m.configurationTerms, [&](auto &ts) {
      for (auto &t : ts)
        term(t, {});
    });
    signature = false;
    keys(m.relationViewHeights, [&](auto &a) { atom(a, {}); });
    // Definitions are renamed only after all references have resolved in their
    // original lexical scope. The symbol is an injective projection of DeclId.
    // A definition's own name is exact, as a quoted name is, never a path.
    signature = false;
    declarations(m, [&](auto &d, auto) {
      name(d.name, d, {}, ReferenceKind::Declaration, true);
    });
    for (auto &f : m.functions)
      if (!f.generic && !f.explicitOrigin)
        if (const auto *d = context.lookup(f.name))
          f.origin = source::LogicalOrigin{d->origin, {}};
  }
};
} // namespace
void qualify(syntax::Module &m, const Context &c, const ReferenceResolver &r) {
  Qualifier(c, r).run(m);
}
} // namespace zkc::frontend::resolution
