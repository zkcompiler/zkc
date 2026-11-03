#include "zkc/Language/CommonControl.h"
#include "CommonRequirements.h"
#include "Semantics.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include <numeric>
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::language {
namespace {
// Immutable source expressions refer to separately completed loop equations.
// Availability restricts components; it never supplies an equality premise.
struct ObservationStep {
  bool payload;
  unsigned alternative, index;
  Type type;
  bool operator==(const ObservationStep &other) const {
    return payload == other.payload && alternative == other.alternative &&
           index == other.index && type == other.type;
  }
};
struct LoopSubject {
  unsigned invocation, slot, role;
  std::vector<ObservationStep> path;
};
// Checked static actuals retain the environment in which they were written.
struct StaticEnvironment {
  detail::Substitution bindings;
  std::shared_ptr<const StaticEnvironment> parent;
};
struct LexicalStatics {
  std::vector<Type> parameters;
  std::shared_ptr<const StaticEnvironment> environment;
};
struct Provenance;
using Node = std::shared_ptr<const Provenance>;
struct Provenance {
  enum class Kind {
    Input,
    Static,
    Total,
    Product,
    Variant,
    Selection,
    Extent,
    Carry,
    Exit,
    Iteration,
    Inactive,
    Unknown
  } kind;
  Type type;
  std::string identity;
  std::vector<Node> operands;
  std::optional<CommonControlComponent> input;
  std::optional<LoopSubject> loop = {};
  bool tagOnly = false;
  std::optional<unsigned> extentAxis = {};
  std::optional<uint64_t> constantCount = {};
  std::shared_ptr<const LexicalStatics> statics = {};
};
using Components = std::map<unsigned, Node>;
class Requirements {
  const std::vector<Declaration> &declarations;
  detail::Work &work;
  detail::Semantics types;
  std::vector<CommonControlRequirement> requirements;
  std::vector<Span> callSites;
  struct Loop {
    Components counts;
    std::vector<Components> initial, transition;
    bool atMostOne;
  };
  struct Demand {
    std::vector<Node> values;
    bool tagOnly;
    Span control;
    std::vector<Span> calls;
  };
  std::vector<Loop> loops;
  std::vector<Demand> demands;
  using Equation =
      std::tuple<Provenance::Kind, unsigned, unsigned, unsigned, unsigned,
                 std::string, bool, std::optional<unsigned>>;
  struct ScopedEnvironment;
  using Scoped = std::shared_ptr<const ScopedEnvironment>;
  struct Environment {
    std::shared_ptr<const StaticEnvironment> statics;
    std::vector<Scoped> scoped;
    std::vector<Components> domains;
    std::string identity;
  };
  struct ScopedEnvironment {
    const ScopedComputation *computation;
    ScopedSignature signature;
    Environment environment;
    std::vector<Components> captures;
    std::string identity;
    std::shared_ptr<const LexicalStatics> statics;
  };
  Error failure = Error::success();
  bool charge(uint64_t count, Span span) {
    if (failure)
      return false;
    if (auto error = work.charge(count, span)) {
      failure = std::move(error);
      return false;
    }
    return true;
  }
  bool capacity(Span span, StringRef message) {
    if (!failure)
      failure = detail::failure("source.limit", message, span, callSites);
    return false;
  }
  bool refuse(Span span, StringRef message) {
    if (!failure)
      failure =
          detail::failure("source.common-provenance", message, span, callSites);
    return false;
  }
  Node node(Provenance::Kind kind, const Type &type, StringRef identity = {},
            std::vector<Node> operands = {},
            std::optional<CommonControlComponent> input = {},
            std::optional<LoopSubject> loop = {}, bool tagOnly = false,
            std::optional<unsigned> extentAxis = {},
            std::optional<uint64_t> constantCount = {},
            std::shared_ptr<const LexicalStatics> statics = {}) {
    if (!charge(operands.size() + identity.size() +
                    (input ? input->path.size() : 0) +
                    (loop ? loop->path.size() : 0) + 1,
                {}))
      return std::make_shared<Provenance>(
          Provenance{Provenance::Kind::Unknown, type, {}, {}, {}});
    return std::make_shared<Provenance>(
        Provenance{kind, type, identity.str(), std::move(operands),
                   std::move(input), std::move(loop), tagOnly, extentAxis,
                   constantCount, std::move(statics)});
  }
  Node unknown(const Type &type) {
    return node(Provenance::Kind::Unknown, type);
  }
  Node at(const Components &components, unsigned role, const Type &type) {
    auto found = components.find(role);
    return found == components.end() ? unknown(type) : found->second;
  }
  bool chargeStaticType(const Type &type, Span span) {
    if (types.chargeType(type, span))
      return true;
    if (types.diagnostic && !failure)
      failure = make_error<DiagnosticError>(*types.diagnostic);
    return false;
  }
  bool staticReferences(const Type &type, std::set<std::string> &references,
                        Span span, unsigned depth = 1) {
    if (!charge(type.domain.size() + type.arguments.size() + 1, span))
      return false;
    if (depth > work.limits.typeDepth)
      return capacity(span, "common static type depth exceeded");
    if (type.symbolic && !type.domain.empty())
      references.insert(type.domain);
    for (const auto &[factors, coefficient] : type.dimension.terms()) {
      (void)coefficient;
      if (!charge(factors.size() + 1, span))
        return false;
      for (const auto &factor : factors) {
        if (!charge(factor.name.size() + 1, span))
          return false;
        references.insert(factor.name);
      }
    }
    for (const auto &argument : type.arguments)
      if (!staticReferences(argument, references, span, depth + 1))
        return false;
    return true;
  }
  struct StaticBinding {
    const Type *value;
    std::shared_ptr<const StaticEnvironment> parent;
    unsigned depth;
  };
  std::optional<StaticBinding>
  staticBinding(StringRef name,
                std::shared_ptr<const StaticEnvironment> environment, Span span,
                unsigned depth = 0) {
    for (auto frame = environment; frame; frame = frame->parent) {
      if (!charge(name.size() + 1, span))
        return {};
      if (++depth > work.limits.callDepth) {
        capacity(span, "common static environment depth exceeded");
        return {};
      }
      auto found = frame->bindings.find(name.str());
      if (found != frame->bindings.end())
        return StaticBinding{&found->second, frame->parent, depth};
    }
    return {};
  }
  Type substitute(const Type &type,
                  std::shared_ptr<const StaticEnvironment> environment,
                  Span span, unsigned depth = 0) {
    if (!environment || failure)
      return type;
    // A whole symbolic term is replaced before inspecting its formal arguments,
    // just as in Semantics::substitute. They are not extra actual dependencies.
    if (type.symbolic && !type.domain.empty()) {
      auto binding = staticBinding(type.domain, environment, span, depth);
      if (failure)
        return type;
      if (binding)
        return substitute(*binding->value, binding->parent, span,
                          binding->depth);
    }
    std::set<std::string> references;
    if (!staticReferences(type, references, span))
      return type;
    detail::Substitution bindings;
    for (const auto &name : references) {
      auto binding = staticBinding(name, environment, span, depth);
      if (failure)
        return type;
      if (!binding)
        continue;
      // Close an actual in its defining caller before normalizing the
      // containing observation: pow2(N), N := pow2(M), M := 5 becomes pow2(32).
      auto actual =
          substitute(*binding->value, binding->parent, span, binding->depth);
      if (failure)
        return type;
      bindings.emplace(name, std::move(actual));
    }
    auto result = types.substitute(type, bindings, span);
    if (!result) {
      if (types.diagnostic && !failure)
        failure = make_error<DiagnosticError>(*types.diagnostic);
      return type;
    }
    return std::move(*result);
  }
  Type substitute(const Type &type, const Environment &environment, Span span) {
    return substitute(type, environment.statics, span);
  }
  std::vector<Type> arguments(ArrayRef<Type> original,
                              const Environment &environment, Span span) {
    std::vector<Type> result;
    if (!charge(original.size() + 1, span))
      return result;
    for (const auto &argument : original)
      result.push_back(substitute(argument, environment, span));
    return result;
  }
  Environment
  environment(const Declaration &callee, ArrayRef<Type> arguments,
              std::optional<Type> module = {},
              std::shared_ptr<const StaticEnvironment> parent = {}) {
    auto bindings = types.substitution(callee, arguments);
    if (module && callee.parent)
      bindings.emplace(
          "self:" + declarations[callee.parent->index].qualifiedName, *module);
    if (callee.parent &&
        declarations[callee.parent->index].kind == Declaration::Kind::Module) {
      const auto &parent = declarations[callee.parent->index];
      if (parent.implementation &&
          parent.parameters.size() <= arguments.size()) {
        Type self(Type::Kind::Module, parent.qualifiedName);
        self.arguments.assign(arguments.begin(),
                              arguments.begin() + parent.parameters.size());
        bindings.emplace("self:" + parent.implementation->domain,
                         std::move(self));
      }
    }
    // A call retains checked actuals in the caller's lexical environment.
    // Eagerly composing unused actuals can leave the bounded natural algebra
    // even though each declaration and its eventual specialization are valid.
    if (!bindings.empty()) {
      for (const auto &[name, type] : bindings)
        if (!charge(name.size() + 1, callee.span) ||
            !types.chargeType(type, callee.span)) {
          if (types.diagnostic && !failure)
            failure = make_error<DiagnosticError>(*types.diagnostic);
          break;
        }
      parent = std::make_shared<StaticEnvironment>(
          StaticEnvironment{std::move(bindings), std::move(parent)});
    }
    return {std::move(parent), {}, {}, callee.qualifiedName};
  }
  DeclarationId target(DeclarationId known, std::vector<Type> &arguments,
                       const std::optional<Type> &module, Span span) {
    if (!module || declarations[known.index].origin)
      return known;
    const auto *definition = types.typeDeclaration(*module);
    if (!definition || definition->kind != Declaration::Kind::Module)
      return known;
    const auto &formal = declarations[known.index];
    for (auto member : definition->members) {
      if (!charge(1, span))
        return known;
      if (declarations[member.index].name != formal.name)
        continue;
      unsigned inherited =
          formal.parent ? declarations[formal.parent->index].parameters.size()
                        : 0;
      std::vector<Type> selected = module->arguments;
      if (arguments.size() >= inherited)
        llvm::append_range(selected, ArrayRef(arguments).drop_front(inherited));
      arguments = std::move(selected);
      return member;
    }
    return known;
  }
  std::optional<StringRef> staticAlias(const Type &type) {
    if (type.symbolic && !type.domain.empty())
      return type.domain;
    if (type.kind == Type::Kind::Natural &&
        type.dimension.terms().size() == 1) {
      const auto &[factors, coefficient] = *type.dimension.terms().begin();
      if (coefficient == 1 && factors.size() == 1 &&
          factors.front().kind == Natural::Factor::Kind::Atom)
        return factors.front().name;
    }
    return {};
  }
  bool sameStaticReference(
      StringRef left, std::shared_ptr<const StaticEnvironment> leftEnvironment,
      StringRef right,
      std::shared_ptr<const StaticEnvironment> rightEnvironment, Span span,
      unsigned leftDepth, unsigned rightDepth, unsigned typeDepth) {
    auto a = staticBinding(left, leftEnvironment, span, leftDepth);
    auto b = staticBinding(right, rightEnvironment, span, rightDepth);
    if (failure)
      return false;
    if (!a && !b)
      return left == right;
    if (a && b)
      return sameStatic(*a->value, a->parent, *b->value, b->parent, span,
                        a->depth, b->depth, typeDepth);
    const auto *parameter = types.parameter(a ? right : left);
    if (!parameter ||
        !charge(parameter->atom.size() + parameter->arguments.size() + 1, span))
      return false;
    for (const auto &argument : parameter->arguments)
      if (!chargeStaticType(argument, span))
        return false;
    auto formal = detail::parameterType(*parameter);
    return a ? sameStatic(*a->value, a->parent, formal, rightEnvironment, span,
                          a->depth, rightDepth, typeDepth)
             : sameStatic(formal, leftEnvironment, *b->value, b->parent, span,
                          leftDepth, b->depth, typeDepth);
  }
  bool
  sameStaticNatural(const Natural &left,
                    std::shared_ptr<const StaticEnvironment> leftEnvironment,
                    const Natural &right,
                    std::shared_ptr<const StaticEnvironment> rightEnvironment,
                    Span span, unsigned leftDepth, unsigned rightDepth,
                    unsigned typeDepth) {
    if (!charge(left.terms().size() + right.terms().size() + 1, span) ||
        left.terms().size() != right.terms().size())
      return false;
    // Source normal forms sort declaration-qualified names. Lexical aliases
    // can change that order; compare the suspended monomials as multisets.
    std::vector<bool> matched(right.terms().size());
    for (const auto &[factors, coefficient] : left.terms()) {
      bool found = false;
      unsigned term = 0;
      for (const auto &[others, otherCoefficient] : right.terms()) {
        unsigned index = term++;
        if (!charge(others.size() + 1, span))
          return false;
        if (matched[index] || coefficient != otherCoefficient ||
            factors.size() != others.size())
          continue;
        std::vector<bool> used(others.size());
        bool equal = true;
        for (const auto &factor : factors) {
          bool selected = false;
          for (unsigned i = 0; i < others.size(); ++i) {
            const auto &other = others[i];
            if (!charge(factor.member.size() + other.member.size() + 1, span))
              return false;
            if (!used[i] && factor.kind == other.kind &&
                factor.member == other.member &&
                sameStaticReference(factor.name, leftEnvironment, other.name,
                                    rightEnvironment, span, leftDepth,
                                    rightDepth, typeDepth)) {
              used[i] = true;
              selected = true;
              break;
            }
            if (failure)
              return false;
          }
          if (!selected) {
            equal = false;
            break;
          }
        }
        if (equal) {
          matched[index] = true;
          found = true;
          break;
        }
      }
      if (!found)
        return false;
    }
    return true;
  }
  bool sameStatic(const Type &left,
                  std::shared_ptr<const StaticEnvironment> leftEnvironment,
                  const Type &right,
                  std::shared_ptr<const StaticEnvironment> rightEnvironment,
                  Span span, unsigned leftDepth = 0, unsigned rightDepth = 0,
                  unsigned typeDepth = 1) {
    if (!charge(1, span))
      return false;
    if (typeDepth > work.limits.typeDepth)
      return capacity(span, "common static comparison type depth exceeded");
    if (auto alias = staticAlias(left)) {
      auto binding = staticBinding(*alias, leftEnvironment, span, leftDepth);
      if (failure)
        return false;
      if (binding)
        return sameStatic(*binding->value, binding->parent, right,
                          rightEnvironment, span, binding->depth, rightDepth,
                          typeDepth);
    }
    if (auto alias = staticAlias(right)) {
      auto binding = staticBinding(*alias, rightEnvironment, span, rightDepth);
      if (failure)
        return false;
      if (binding)
        return sameStatic(left, leftEnvironment, *binding->value,
                          binding->parent, span, leftDepth, binding->depth,
                          typeDepth);
    }
    if (!chargeStaticType(left, span) || !chargeStaticType(right, span) ||
        left.kind != right.kind ||
        (left.kind != Type::Kind::Natural &&
         (left.domain != right.domain || left.sort != right.sort ||
          left.symbolic != right.symbolic)) ||
        left.arguments.size() != right.arguments.size() ||
        !sameStaticNatural(left.dimension, leftEnvironment, right.dimension,
                           rightEnvironment, span, leftDepth, rightDepth,
                           typeDepth))
      return false;
    for (auto [a, b] : llvm::zip(left.arguments, right.arguments))
      if (!sameStatic(a, leftEnvironment, b, rightEnvironment, span, leftDepth,
                      rightDepth, typeDepth + 1))
        return false;
    return true;
  }
  bool closedStatic(const Type &type,
                    std::shared_ptr<const StaticEnvironment> environment,
                    Span span, unsigned depth = 0) {
    if (auto alias = staticAlias(type)) {
      auto binding = staticBinding(*alias, environment, span, depth);
      if (failure)
        return false;
      if (binding)
        return closedStatic(*binding->value, binding->parent, span,
                            binding->depth);
    }
    std::set<std::string> references;
    if (!staticReferences(type, references, span))
      return false;
    for (const auto &name : references) {
      auto binding = staticBinding(name, environment, span, depth);
      if (!binding ||
          !closedStatic(*binding->value, binding->parent, span, binding->depth))
        return false;
    }
    return true;
  }
  bool sameStatics(const std::shared_ptr<const LexicalStatics> &left,
                   const std::shared_ptr<const LexicalStatics> &right,
                   Span span) {
    if (!charge(1, span))
      return false;
    if (left == right)
      return true;
    if (!left || !right || left->parameters.size() != right->parameters.size())
      return false;
    for (auto [a, b] : llvm::zip(left->parameters, right->parameters)) {
      if (sameStatic(a, left->environment, b, right->environment, span))
        continue;
      if (failure || !closedStatic(a, left->environment, span) ||
          !closedStatic(b, right->environment, span))
        return false;
      auto actualLeft = substitute(a, left->environment, span);
      auto actualRight = substitute(b, right->environment, span);
      if (failure || actualLeft != actualRight)
        return false;
    }
    return true;
  }
  std::shared_ptr<const LexicalStatics>
  lexicalStatics(ArrayRef<Type> parameters, const Environment &context,
                 Span span, const std::optional<Type> &module = {}) {
    if (!charge(parameters.size() + 1, span))
      return {};
    auto result = std::make_shared<LexicalStatics>();
    result->environment = context.statics;
    for (const auto &parameter : parameters) {
      if (!chargeStaticType(parameter, span))
        return {};
      result->parameters.push_back(parameter);
    }
    if (module) {
      if (!chargeStaticType(*module, span))
        return {};
      result->parameters.push_back(*module);
    }
    return result;
  }
  Expected<std::optional<uint64_t>>
  constantCount(const MathValue &math, const Environment &context, Span span) {
    if (math.identity != MathematicalIdentity::IndexConstant)
      return std::optional<uint64_t>{};
    uint64_t number;
    if (!math.literal.empty() &&
        !StringRef(math.literal).getAsInteger(10, number))
      return std::optional<uint64_t>{number};
    if (math.staticArguments.empty() ||
        math.staticArguments.front().kind != Type::Kind::Natural)
      return std::optional<uint64_t>{};
    const auto &argument = math.staticArguments.front();
    // Identity may remain open even when composing its checked lexical stages
    // would leave Natural's bounded algebra. Only closed counts are evaluated;
    // an evaluation failure is an error, never an absent count.
    bool closed = closedStatic(argument, context.statics, span);
    if (failure)
      return std::move(failure);
    if (!closed)
      return std::optional<uint64_t>{};
    auto actual = substitute(argument, context, span);
    if (failure)
      return std::move(failure);
    return std::optional<uint64_t>{actual.dimension.closedValue()};
  }
  // This is exact expression identity within one role. It creates no input
  // obligations and never unfolds a loop equation or assumes commonness.
  bool same(Node left, Node right, Span span, unsigned depth,
            std::set<std::pair<Node, Node>> &seen) {
    if (!charge(left->identity.size() + left->operands.size() +
                    (left->input ? left->input->path.size() : 0) +
                    (left->loop ? left->loop->path.size() : 0) + 1,
                span))
      return false;
    if (depth > work.limits.expressionDepth)
      return capacity(span, "common result identity depth exceeded");
    if (left == right)
      return true;
    if (left->kind == Provenance::Kind::Unknown ||
        right->kind == Provenance::Kind::Unknown || left->kind != right->kind ||
        left->type != right->type || left->identity != right->identity ||
        left->tagOnly != right->tagOnly ||
        left->extentAxis != right->extentAxis ||
        left->operands.size() != right->operands.size() ||
        !(left->input == right->input) || bool(left->loop) != bool(right->loop))
      return false;
    if (left->loop && (left->loop->invocation != right->loop->invocation ||
                       left->loop->slot != right->loop->slot ||
                       left->loop->role != right->loop->role ||
                       left->loop->path != right->loop->path))
      return false;
    if (!sameStatics(left->statics, right->statics, span))
      return false;
    if (!seen.insert({left, right}).second)
      return true;
    for (auto [a, b] : llvm::zip(left->operands, right->operands))
      if (!same(a, b, span, depth + 1, seen))
        return false;
    return true;
  }
  Node selection(const Type &type, StringRef identity,
                 std::vector<Node> children, Span span) {
    if (children.size() > 1) {
      std::set<std::pair<Node, Node>> seen;
      bool identical = true;
      for (unsigned i = 2; i < children.size(); ++i)
        identical &= same(children[1], children[i], span, 0, seen);
      if (identical)
        return children[1];
    }
    return node(Provenance::Kind::Selection, type, identity,
                std::move(children));
  }
  Type componentType(const Components &values) {
    return values.empty() ? Type{} : values.begin()->second->type;
  }
  Components domain(ArrayRef<DomainBinding> bindings, unsigned index,
                    ArrayRef<Components> data, const Environment &context,
                    ArrayRef<unsigned> roles, unsigned depth) {
    if (!charge(1, {}) || depth > work.limits.callDepth) {
      capacity({}, "common domain environment depth exceeded");
      return {};
    }
    if (index >= bindings.size()) {
      refuse({}, "common domain edge is outside its checked body");
      return {};
    }
    const auto &binding = bindings[index];
    if (binding.parameter) {
      if (*binding.parameter < context.domains.size())
        return context.domains[*binding.parameter];
      Components result;
      for (auto role : roles)
        result[role] = unknown(substitute(binding.item, context, binding.span));
      return result;
    }
    std::vector<Components> operands;
    for (auto value : binding.operands)
      operands.push_back(data[value.index]);
    std::vector<Components> children;
    for (auto child : binding.children)
      children.push_back(
          domain(bindings, child, data, context, roles, depth + 1));
    auto kind = binding.kind;
    auto axis = binding.axis;
    auto type = substitute(binding.item, context, binding.span);
    if (binding.factory) {
      auto statics = binding.arguments;
      std::optional<Type> module;
      if (binding.factory->module)
        module = substitute(*binding.factory->module, context, binding.span);
      auto selected =
          target(binding.factory->declaration, statics, module, binding.span);
      const auto &callee = declarations[selected.index];
      if (!callee.domainDefinition) {
        if (callee.kind != Declaration::Kind::DomainFunction ||
            !callee.abstract) {
          refuse(binding.span,
                 "common domain factory has no checked definition");
          return {};
        }
        // An abstract factory has the same total, static selection contract
        // as an abstract Math helper. Preserve its complete actual arguments;
        // its implementation is resolved again at closed specialization.
        std::string identity = "domain-call:" + callee.qualifiedName;
        auto payload = lexicalStatics(statics, context, binding.span, module);
        llvm::append_range(operands, children);
        Components result;
        for (auto role : roles) {
          std::vector<Node> inputs;
          for (const auto &part : operands)
            inputs.push_back(at(part, role, componentType(part)));
          result[role] =
              node(Provenance::Kind::Total, type, identity, std::move(inputs),
                   {}, {}, false, {}, {}, payload);
        }
        return result;
      }
      const auto &definition = *callee.domainDefinition;
      if (!definition.constructor) {
        auto nested = environment(callee, statics, module, context.statics);
        nested.domains = std::move(children);
        std::vector<Components> history;
        for (unsigned i = 0; i < definition.bindings.size(); ++i)
          history.push_back(domain(definition.bindings, i, operands, nested,
                                   roles, depth + 1));
        if (definition.result >= history.size()) {
          refuse(binding.span, "common domain factory result differs");
          return {};
        }
        // Preserve eager admission dependencies of every retained constructor,
        // including constructors not used by the factory's final result.
        Components result;
        for (auto role : roles) {
          std::vector<Node> inputs;
          for (const auto &part : history)
            inputs.push_back(at(part, role, componentType(part)));
          result[role] =
              node(Provenance::Kind::Total, type,
                   "domain-factory:" + std::to_string(definition.result),
                   std::move(inputs));
        }
        return result;
      }
      kind = *definition.constructor;
      axis = definition.axis;
    }
    llvm::append_range(operands, children);
    Components result;
    for (auto role : roles) {
      std::vector<Node> inputs;
      for (const auto &part : operands)
        inputs.push_back(at(part, role, componentType(part)));
      result[role] = node(Provenance::Kind::Total, type,
                          "domain:" + std::to_string(unsigned(kind)) + ":" +
                              std::to_string(axis),
                          std::move(inputs));
    }
    return result;
  }
  Scoped scoped(const Body &source, unsigned index, ArrayRef<Components> values,
                const Environment &context, ArrayRef<unsigned> roles,
                unsigned depth) {
    if (!charge(1, {}) || depth > work.limits.callDepth) {
      capacity({}, "common scoped environment depth exceeded");
      return {};
    }
    const auto &binding = source.scopedBindings.at(index);
    if (binding.parameter && *binding.parameter < context.scoped.size())
      return context.scoped[*binding.parameter];
    Environment nested{context.statics, {}, {}, context.identity};
    std::vector<Components> captures;
    for (auto capture : binding.captures)
      captures.push_back(values[capture.index]);
    for (auto capture : binding.scopedCaptures)
      nested.scoped.push_back(
          scoped(source, capture, values, context, roles, depth + 1));
    for (auto capture : binding.domainCaptures)
      nested.domains.push_back(domain(source.domainBindings, capture, values,
                                      context, roles, depth + 1));
    std::string identity =
        context.identity + ":scoped:" + std::to_string(index);
    if (binding.computation)
      identity =
          declarations[binding.computation->lexicalOwner.index].qualifiedName +
          ":lambda:" + std::to_string(binding.computation->expression);
    auto statics = std::make_shared<LexicalStatics>();
    statics->environment = context.statics;
    if (binding.computation) {
      const auto &owner = declarations[binding.computation->lexicalOwner.index];
      // Retain only the lexical telescope, without forcing unused symbolic
      // actuals. Comparison follows aliases or evaluates closed bindings.
      for (const auto &parameter : owner.parameters) {
        if (!charge(parameter.atom.size() + parameter.arguments.size() + 1,
                    binding.span))
          return {};
        for (const auto &argument : parameter.arguments)
          if (!chargeStaticType(argument, binding.span))
            return {};
        statics->parameters.push_back(detail::parameterType(parameter));
      }
      if (owner.parent) {
        const auto &parent = declarations[owner.parent->index];
        if (parent.kind == Declaration::Kind::Module ||
            parent.kind == Declaration::Kind::Interface) {
          if (!charge(parent.qualifiedName.size() + 6, binding.span))
            return {};
          Type self(Type::Kind::Module, "self:" + parent.qualifiedName);
          self.symbolic = true;
          statics->parameters.push_back(std::move(self));
        }
      }
    }
    auto signature = binding.signature;
    signature.inputs = arguments(signature.inputs, context, binding.span);
    signature.result = substitute(signature.result, context, binding.span);
    return std::make_shared<ScopedEnvironment>(ScopedEnvironment{
        binding.computation.get(), std::move(signature), std::move(nested),
        std::move(captures), std::move(identity), std::move(statics)});
  }
  Node scopedValue(const Scoped &binding, unsigned role, unsigned depth) {
    if (!binding || !charge(1, {}) || depth > work.limits.callDepth) {
      if (depth > work.limits.callDepth)
        capacity({}, "common scoped observation depth exceeded");
      return unknown(Type{});
    }
    if (!binding->computation ||
        binding->signature.mode != ScopedSignature::Mode::Math)
      return unknown(binding->signature.result);
    std::vector<Node> operands;
    for (const auto &capture : binding->captures)
      operands.push_back(at(capture, role, componentType(capture)));
    for (const auto &domain : binding->environment.domains)
      operands.push_back(at(domain, role, componentType(domain)));
    for (const auto &nested : binding->environment.scoped)
      operands.push_back(scopedValue(nested, role, depth + 1));
    return node(Provenance::Kind::Total, binding->signature.result,
                binding->identity, std::move(operands), {}, {}, false, {}, {},
                binding->statics);
  }
  Node field(Node value, unsigned index, Span span, unsigned depth) {
    if (!charge(1, span) || depth > work.limits.typeDepth) {
      capacity(span, "common component projection depth exceeded");
      return unknown(value->type);
    }
    Type type;
    if (value->type.kind == Type::Kind::Array) {
      if (value->type.arguments.size() != 1 ||
          (value->type.dimension.isClosed() &&
           index >= value->type.dimension.closedValue())) {
        refuse(span, "common array component is outside its schema");
        return unknown(value->type);
      }
      // Body checking has discharged the closed index or retained index+1<=N
      // as the declaration's generic bound. Observing that checked operation
      // needs one element type, not an expansion of the array's whole layout.
      type = value->type.arguments.front();
      if (!types.chargeType(type, span)) {
        if (types.diagnostic && !failure)
          failure = make_error<DiagnosticError>(*types.diagnostic);
        return unknown(type);
      }
    } else {
      auto fields = types.fields(value->type, span);
      if (!fields || index >= fields->size()) {
        if (types.diagnostic && !failure)
          failure = make_error<DiagnosticError>(*types.diagnostic);
        refuse(span, "common component field is outside its schema");
        return unknown(value->type);
      }
      type = (*fields)[index].type;
    }
    if (value->kind == Provenance::Kind::Product &&
        index < value->operands.size())
      return value->operands[index];
    if (value->kind == Provenance::Kind::Input) {
      auto input = *value->input;
      input.path.push_back({CommonControlStep::Kind::Field, index});
      return node(Provenance::Kind::Input, type, {}, {}, input);
    }
    if (value->kind == Provenance::Kind::Carry ||
        value->kind == Provenance::Kind::Exit) {
      auto subject = *value->loop;
      subject.path.push_back({false, 0, index, type});
      return node(value->kind, type, {}, {}, {}, std::move(subject));
    }
    // Exact forwarding through a selection projects every alternative's yield.
    if (value->kind == Provenance::Kind::Selection) {
      auto children = value->operands;
      for (unsigned i = 1; i < children.size(); ++i)
        children[i] = field(children[i], index, span, depth + 1);
      return selection(type, value->identity, std::move(children), span);
    }
    if (value->kind == Provenance::Kind::Inactive)
      return node(value->kind, type, value->identity);
    if (value->kind == Provenance::Kind::Unknown)
      return unknown(type);
    return node(Provenance::Kind::Total, type, "field:" + std::to_string(index),
                {value});
  }
  Node payload(Node value, unsigned alternative, unsigned index,
               const Type &type, Span span, unsigned depth = 0) {
    if (!charge(1, span) || depth > work.limits.typeDepth) {
      capacity(span, "common payload projection depth exceeded");
      return unknown(type);
    }
    if (value->kind == Provenance::Kind::Variant) {
      if (value->identity != std::to_string(alternative))
        return node(Provenance::Kind::Inactive, type,
                    value->identity + ":" + std::to_string(alternative) + ":" +
                        std::to_string(index));
      return index < value->operands.size() ? value->operands[index]
                                            : unknown(type);
    }
    if (value->kind == Provenance::Kind::Input) {
      auto input = *value->input;
      input.path.push_back({CommonControlStep::Kind::Alternative, alternative});
      input.path.push_back({CommonControlStep::Kind::Payload, index});
      return node(Provenance::Kind::Input, type, {}, {}, input);
    }
    if (value->kind == Provenance::Kind::Carry ||
        value->kind == Provenance::Kind::Exit) {
      auto subject = *value->loop;
      subject.path.push_back({true, alternative, index, type});
      return node(value->kind, type, {}, {}, {}, std::move(subject));
    }
    if (value->kind == Provenance::Kind::Selection) {
      auto children = value->operands;
      for (unsigned i = 1; i < children.size(); ++i)
        children[i] =
            payload(children[i], alternative, index, type, span, depth + 1);
      return selection(type, value->identity, std::move(children), span);
    }
    if (value->kind == Provenance::Kind::Inactive)
      return node(value->kind, type, value->identity);
    if (value->kind == Provenance::Kind::Unknown)
      return unknown(type);
    return node(Provenance::Kind::Total, type,
                "payload:" + std::to_string(alternative) + ":" +
                    std::to_string(index),
                {value});
  }
  Node facet(Node value, bool tagOnly, std::optional<unsigned> axis, Span span,
             unsigned depth = 0) {
    if (!tagOnly && !axis)
      return value;
    if (!charge(1, span) || depth > work.limits.expressionDepth) {
      capacity(span, "common observation depth exceeded");
      return unknown(value->type);
    }
    if (value->kind == Provenance::Kind::Input ||
        value->kind == Provenance::Kind::Carry ||
        value->kind == Provenance::Kind::Exit)
      return node(value->kind, value->type, value->identity, value->operands,
                  value->input, value->loop, tagOnly, axis);
    if (tagOnly && value->kind == Provenance::Kind::Variant)
      return node(Provenance::Kind::Static, value->type,
                  "tag:" + value->identity);
    if (value->kind == Provenance::Kind::Selection) {
      auto children = value->operands;
      for (unsigned i = 1; i < children.size(); ++i)
        children[i] = facet(children[i], tagOnly, axis, span, depth + 1);
      return selection(value->type, value->identity, std::move(children), span);
    }
    if (value->kind == Provenance::Kind::Unknown ||
        value->kind == Provenance::Kind::Inactive)
      return value;
    return node(Provenance::Kind::Total, value->type,
                tagOnly ? "tag" : "extent:" + std::to_string(*axis), {value});
  }
  Node observe(Node value, const Provenance &observation, Span span) {
    for (const auto &step : observation.loop->path)
      value = step.payload ? payload(value, step.alternative, step.index,
                                     step.type, span)
                           : field(value, step.index, span, 0);
    return facet(value, observation.tagOnly, observation.extentAxis, span);
  }
  bool demand(std::vector<Node> values, bool tagOnly, Span span) {
    if (!charge(values.size() + callSites.size() + 1, span))
      return false;
    demands.push_back({std::move(values), tagOnly, span, callSites});
    return true;
  }
  bool agree(ArrayRef<Node> values, Span span, std::set<Equation> &hypotheses,
             unsigned depth = 0) {
    if (!charge(values.size() + 1, span))
      return false;
    if (depth > work.limits.expressionDepth)
      return capacity(span, "common derivation depth exceeded");
    if (values.size() < 2)
      return true;
    const auto &first = *values.front();
    for (const auto &value : values)
      if (value->kind == Provenance::Kind::Unknown ||
          value->type != first.type || value->tagOnly != first.tagOnly ||
          value->extentAxis != first.extentAxis)
        return refuse(span, "shared control depends on Local, received, or "
                            "otherwise unknown provenance");
    if (llvm::all_of(values, [](const Node &value) {
          return value->kind == Provenance::Kind::Input;
        })) {
      using K = Type::Kind;
      if (!first.tagOnly && !first.extentAxis &&
          (first.type.kind == K::Tuple || first.type.kind == K::Record ||
           first.type.kind == K::LogicalRecord ||
           first.type.kind == K::Array)) {
        auto fields = types.fields(first.type, span);
        if (!fields)
          return refuse(span, "common input product has no admitted schema");
        for (unsigned i = 0; i < fields->size(); ++i) {
          std::vector<Node> children;
          for (const auto &value : values)
            children.push_back(field(value, i, span, depth + 1));
          if (!agree(children, span, hypotheses, depth + 1))
            return false;
        }
        return true;
      }
      CommonControlRequirement requirement{
          {}, first.type, first.tagOnly, span, first.extentAxis};
      for (const auto &value : values)
        if (!llvm::is_contained(requirement.components, *value->input))
          requirement.components.push_back(*value->input);
      for (unsigned i = 1; i < requirement.components.size(); ++i) {
        CommonControlRequirement pair{
            {requirement.components.front(), requirement.components[i]},
            first.type,
            first.tagOnly,
            span,
            first.extentAxis};
        bool known = false;
        for (const auto &prior : requirements) {
          if (!charge(prior.components.size() + 1, span))
            return false;
          known |= prior.type == pair.type && prior.tagOnly == pair.tagOnly &&
                   prior.extentAxis == pair.extentAxis &&
                   prior.components.size() == 2 &&
                   ((prior.components[0] == pair.components[0] &&
                     prior.components[1] == pair.components[1]) ||
                    (prior.components[0] == pair.components[1] &&
                     prior.components[1] == pair.components[0]));
        }
        if (!known)
          requirements.push_back(std::move(pair));
      }
      return true;
    }
    for (const auto &value : values)
      if (value->kind != first.kind || value->identity != first.identity ||
          value->operands.size() != first.operands.size() ||
          value->tagOnly != first.tagOnly ||
          value->extentAxis != first.extentAxis ||
          !sameStatics(value->statics, first.statics, span))
        return refuse(span,
                      "shared components lack congruent total derivations");
    if (first.loop) {
      // Compared by lookup keys; local to this one requirement.
      std::string path;
      for (const auto &step : first.loop->path) {
        detail::frame(path, step.payload ? "payload" : "field");
        detail::frame(path, std::to_string(step.alternative));
        detail::frame(path, std::to_string(step.index));
        detail::frame(path, typeIdentity(step.type));
      }
      if (!charge(path.size() + 1, span))
        return false;
      for (unsigned i = 1; i < values.size(); ++i) {
        const auto &other = *values[i];
        if (!other.loop || first.loop->invocation != other.loop->invocation ||
            first.loop->slot != other.loop->slot ||
            first.loop->path != other.loop->path)
          return refuse(span, "common recurrence subjects differ");
        if (first.kind == Provenance::Kind::Iteration)
          continue; // The exact invocation's count has its own demand.
        Equation equation{first.kind,       first.loop->invocation,
                          first.loop->slot, first.loop->role,
                          other.loop->role, path,
                          first.tagOnly,    first.extentAxis};
        if (!charge(hypotheses.size() + 1, span))
          return false;
        if (!hypotheses.insert(std::move(equation)).second)
          continue;
        // Introduce the complete base and transition obligations before any
        // repeated subject is allowed to close a simultaneous hypothesis.
        const auto &loop = loops[first.loop->invocation];
        auto check = [&](const Components &components) {
          std::vector<Node> pair{
              observe(at(components, first.loop->role, first.type), first,
                      span),
              observe(at(components, other.loop->role, other.type), other,
                      span)};
          return agree(pair, span, hypotheses, depth + 1);
        };
        if (!check(loop.initial[first.loop->slot]) ||
            ((first.kind == Provenance::Kind::Exit || !loop.atMostOne) &&
             !check(loop.transition[first.loop->slot])))
          return false;
        if (first.kind == Provenance::Kind::Exit) {
          std::vector<Node> counts{
              at(loop.counts, first.loop->role, Type(Type::Kind::Index)),
              at(loop.counts, other.loop->role, Type(Type::Kind::Index))};
          if (!agree(counts, span, hypotheses, depth + 1))
            return false;
        }
      }
      return true;
    }
    for (unsigned i = 0; i < first.operands.size(); ++i) {
      std::vector<Node> operands;
      for (const auto &value : values)
        operands.push_back(first.kind == Provenance::Kind::Extent
                               ? facet(value->operands[i], false, 0, span)
                               : value->operands[i]);
      if (!agree(operands, span, hypotheses, depth + 1))
        return false;
    }
    return true;
  }
  std::vector<Components> body(const Body &source, ArrayRef<Components> inputs,
                               ArrayRef<unsigned> roles, unsigned callDepth,
                               const Environment &context,
                               unsigned regionDepth = 1) {
    if (!charge(source.values.size() + source.operations.size() + 1, {}))
      return {};
    if (callDepth > work.limits.callDepth) {
      capacity({}, "common callable depth exceeded");
      return {};
    }
    if (regionDepth > work.limits.expressionDepth) {
      capacity({}, "common region depth exceeded");
      return {};
    }
    if (inputs.size() != source.inputs) {
      refuse({}, "common body input association differs");
      return {};
    }
    std::vector<Type> valueTypes;
    for (const auto &value : source.values)
      valueTypes.push_back(substitute(value.type, context, value.span));
    if (failure)
      return {};
    std::vector<Components> values(source.values.size());
    llvm::copy(inputs, values.begin());
    auto mappedRoles = [&](ArrayRef<unsigned> selected) {
      std::vector<unsigned> result;
      for (auto role : selected) {
        if (role >= roles.size()) {
          refuse({}, "common role substitution is outside its telescope");
          break;
        }
        result.push_back(roles[role]);
      }
      return result;
    };
    auto gather = [&](ArrayRef<ValueId> operands) {
      std::vector<Components> result;
      for (auto value : operands)
        result.push_back(values.at(value.index));
      return result;
    };
    for (const auto &op : source.operations) {
      if (!charge(1, op.span))
        return {};
      std::vector<Components> results(op.results.size());
      auto each = [&](auto &&build) {
        for (unsigned i = 0; i < op.results.size(); ++i)
          for (auto role : roles)
            results[i][role] = build(i, role, valueTypes[op.results[i].index]);
      };
      if (const auto *projection = std::get_if<Projection>(&op.action)) {
        each([&](unsigned, unsigned role, const Type &) {
          auto result = at(values[projection->input.index], role,
                           valueTypes[projection->input.index]);
          for (auto index : projection->path)
            result = field(result, index, op.span, 0);
          return result;
        });
      } else if (const auto *restriction =
                     std::get_if<Restriction>(&op.action)) {
        results.front() = values[restriction->input.index];
        auto selected = mappedRoles(restriction->roles);
        for (auto it = results.front().begin(); it != results.front().end();)
          if (!llvm::is_contained(selected, it->first))
            it = results.front().erase(it);
          else
            ++it;
      } else if (const auto *assembly = std::get_if<RoleAssembly>(&op.action)) {
        for (unsigned i = 0; i < assembly->roles.size(); ++i) {
          unsigned role = roles[assembly->roles[i]];
          results.front()[role] = at(values[assembly->operands[i].index], role,
                                     valueTypes[op.results.front().index]);
        }
      } else if (const auto *math = std::get_if<MathValue>(&op.action)) {
        std::string identity =
            "math:" + std::to_string(unsigned(math->identity)) + ":" +
            math->literal;
        auto statics = lexicalStatics(math->staticArguments, context, op.span);
        auto count = constantCount(*math, context, op.span);
        if (!count) {
          failure = count.takeError();
          return {};
        }
        for (const auto &parameter : math->parameters)
          detail::frame(identity, parameter);
        each([&](unsigned, unsigned role, const Type &type) {
          std::vector<Node> operands;
          for (auto input : math->operands)
            operands.push_back(
                at(values[input.index], role, valueTypes[input.index]));
          if (math->identity == MathematicalIdentity::VectorLength)
            return node(Provenance::Kind::Extent, type, "0",
                        std::move(operands));
          return node(operands.empty() ? Provenance::Kind::Static
                                       : Provenance::Kind::Total,
                      type, identity, std::move(operands), {}, {}, false, {},
                      *count, statics);
        });
      } else if (const auto *construct = std::get_if<Construct>(&op.action)) {
        each([&](unsigned, unsigned role, const Type &type) {
          std::vector<Node> operands;
          for (auto input : construct->operands)
            operands.push_back(
                at(values[input.index], role, valueTypes[input.index]));
          if (construct->kind == Construct::Kind::Aggregate)
            return node(Provenance::Kind::Product, type, {},
                        std::move(operands));
          if (construct->kind == Construct::Kind::Variant) {
            auto alternatives = types.alternatives(type, op.span);
            if (alternatives)
              for (unsigned i = 0; i < alternatives->size(); ++i)
                if ((*alternatives)[i].name == construct->alternative)
                  return node(Provenance::Kind::Variant, type,
                              std::to_string(i), std::move(operands));
          }
          return unknown(type);
        });
      } else if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
        auto binding =
            scoped(source, invoke->binding, values, context, roles, callDepth);
        if (!binding || !binding->computation || !binding->computation->body ||
            binding->signature.mode != ScopedSignature::Mode::Math) {
          each([&](unsigned, unsigned, const Type &type) {
            return unknown(type);
          });
        } else {
          auto inputs = gather(invoke->operands);
          llvm::append_range(inputs, binding->captures);
          results = body(*binding->computation->body, inputs, roles,
                         callDepth + 1, binding->environment);
        }
      } else if (const auto *finite =
                     std::get_if<FiniteApplication>(&op.action)) {
        auto descriptor = domain(source.domainBindings, finite->domain, values,
                                 context, roles, callDepth);
        auto callback =
            scoped(source, finite->body, values, context, roles, callDepth);
        Scoped predicate;
        if (finite->predicate)
          predicate = scoped(source, *finite->predicate, values, context, roles,
                             callDepth);
        each([&](unsigned, unsigned role, const Type &type) {
          if (source.mode != Body::Mode::Math)
            return unknown(type);
          std::vector<Node> inputs{
              at(descriptor, role, componentType(descriptor))};
          for (auto input : finite->operands)
            inputs.push_back(
                at(values[input.index], role, valueTypes[input.index]));
          inputs.push_back(scopedValue(callback, role, callDepth));
          if (finite->predicate)
            inputs.push_back(scopedValue(predicate, role, callDepth));
          return node(Provenance::Kind::Total, type,
                      "finite:" + std::to_string(unsigned(finite->kind)),
                      std::move(inputs));
        });
      } else if (const auto *finite =
                     std::get_if<FiniteComputation>(&op.action)) {
        each([&](unsigned, unsigned role, const Type &type) {
          if (source.mode != Body::Mode::Math)
            return unknown(type);
          std::vector<ValueId> inputs = finite->domainOperands;
          llvm::append_range(inputs, finite->operands);
          llvm::append_range(inputs, finite->body.captures);
          if (finite->predicate)
            llvm::append_range(inputs, finite->predicate->captures);
          std::vector<Node> operands;
          for (auto input : inputs)
            operands.push_back(
                at(values[input.index], role, valueTypes[input.index]));
          std::string identity = finite->domain->identity;
          detail::frame(identity,
                        declarations[finite->body.helper.index].symbol);
          if (finite->predicate)
            detail::frame(identity,
                          declarations[finite->predicate->helper.index].symbol);
          return node(Provenance::Kind::Total, type, identity,
                      std::move(operands));
        });
      } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
        auto statics = call->arguments;
        std::optional<Type> module;
        if (call->module)
          module = substitute(*call->module, context, op.span);
        auto selected = target(call->callee, statics, module, op.span);
        const auto &callee = declarations.at(selected.index);
        auto nested = environment(callee, statics, module, context.statics);
        for (auto index : call->scopedArguments)
          nested.scoped.push_back(
              scoped(source, index, values, context, roles, callDepth));
        for (auto index : call->domainArguments)
          nested.domains.push_back(domain(source.domainBindings, index, values,
                                          context, roles, callDepth));
        if (callee.kind == Declaration::Kind::Math && callee.body) {
          callSites.push_back(op.span);
          auto restore = llvm::scope_exit([&] { callSites.pop_back(); });
          results = body(*callee.body, gather(call->operands), roles,
                         callDepth + 1, nested);
        } else if (callee.kind == Declaration::Kind::Math && callee.abstract) {
          auto payload = lexicalStatics(statics, context, op.span, module);
          each([&](unsigned, unsigned role, const Type &type) {
            std::vector<Node> inputs;
            for (auto input : call->operands)
              inputs.push_back(
                  at(values[input.index], role, valueTypes[input.index]));
            for (const auto &domain : nested.domains)
              inputs.push_back(at(domain, role, componentType(domain)));
            for (const auto &binding : nested.scoped)
              inputs.push_back(scopedValue(binding, role, callDepth));
            std::string identity = callee.qualifiedName;
            return node(Provenance::Kind::Total, type, identity,
                        std::move(inputs), {}, {}, false, {}, {}, payload);
          });
        } else
          each([&](unsigned, unsigned, const Type &type) {
            return unknown(type);
          });
      } else if (const auto *call =
                     std::get_if<ProtocolApplication>(&op.action)) {
        const auto &callee = declarations.at(call->callee.index);
        if (!callee.body) {
          // An abstract Protocol signature supplies no common-result rule.
          // Closed specialization must replay the actual implementation.
          each([&](unsigned, unsigned, const Type &type) {
            return unknown(type);
          });
        } else {
          auto selected = mappedRoles(call->roles);
          callSites.push_back(op.span);
          auto restore = llvm::scope_exit([&] { callSites.pop_back(); });
          results = body(
              *callee.body, gather(call->operands), selected, callDepth + 1,
              environment(callee, call->arguments, {}, context.statics));
        }
      } else if (const auto *control = std::get_if<Control>(&op.action)) {
        if (source.mode == Body::Mode::Local ||
            control->kind == Control::Kind::For) {
          each([&](unsigned, unsigned, const Type &type) {
            return unknown(type);
          });
        } else {
          const auto selector = control->operands.front();
          const bool match = control->kind == Control::Kind::Match;
          if (source.mode == Body::Mode::Protocol) {
            std::vector<Node> selected;
            for (auto role : mappedRoles(control->roles))
              selected.push_back(
                  at(values[selector.index], role, valueTypes[selector.index]));
            if (!demand(std::move(selected), match, op.span))
              return {};
          }
          std::vector<std::vector<Components>> arms;
          unsigned captures = control->operands.size() - 1;
          for (unsigned arm = 0; arm < control->regions.size(); ++arm) {
            const auto &region = *control->regions[arm];
            std::vector<Components> arguments(region.inputs - captures);
            for (unsigned i = 0; i < arguments.size(); ++i)
              for (auto role : roles)
                arguments[i][role] = payload(
                    at(values[selector.index], role,
                       valueTypes[selector.index]),
                    arm, i, substitute(region.values[i].type, context, op.span),
                    op.span);
            auto captured = gather(ArrayRef(control->operands).drop_front());
            llvm::append_range(arguments, captured);
            arms.push_back(body(region, arguments, roles, callDepth, context,
                                regionDepth + 1));
          }
          each([&](unsigned result, unsigned role, const Type &type) {
            auto subject =
                at(values[selector.index], role, valueTypes[selector.index]);
            std::optional<unsigned> selected;
            if (subject->kind == Provenance::Kind::Static) {
              auto boolean = "math:" +
                             std::to_string(unsigned(
                                 MathematicalIdentity::BooleanConstant)) +
                             ":";
              if (subject->identity == boolean + "true")
                selected = 0;
              else if (subject->identity == boolean + "false")
                selected = 1;
            } else if (subject->kind == Provenance::Kind::Variant) {
              unsigned ordinal;
              if (!StringRef(subject->identity).getAsInteger(10, ordinal))
                selected = ordinal;
            }
            if (selected && *selected < arms.size() &&
                result < arms[*selected].size())
              return at(arms[*selected][result], role, type);
            std::vector<Node> children{facet(subject, match, {}, op.span)};
            for (const auto &arm : arms) {
              if (result >= arm.size())
                return unknown(type);
              children.push_back(at(arm[result], role, type));
            }
            return selection(type, match ? "match" : "if", std::move(children),
                             op.span);
          });
        }
      } else if (const auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        auto selected = mappedRoles(repeat->roles);
        auto countType = valueTypes[repeat->count.index];
        std::vector<Node> counts;
        Type bound(Type::Kind::Natural);
        bound.dimension = repeat->maximum;
        auto maximum = substitute(bound, context, op.span).dimension;
        bool atMostOne = maximum.isClosed() && maximum.closedValue() <= 1;
        bool smallCount = true;
        for (auto role : selected) {
          auto value = at(values[repeat->count.index], role, countType);
          smallCount &= value->constantCount && *value->constantCount <= 1;
          counts.push_back(value);
        }
        atMostOne |= smallCount;
        if (!demand(std::move(counts), false, op.span))
          return {};
        if (!charge(selected.size() * (repeat->carried.size() + 1) + 1,
                    op.span))
          return {};
        unsigned invocation = loops.size();
        loops.push_back({values[repeat->count.index],
                         gather(repeat->carried),
                         {},
                         atMostOne});
        Components index;
        for (auto role : selected)
          index[role] =
              node(Provenance::Kind::Iteration, Type(Type::Kind::Index), {}, {},
                   {}, LoopSubject{invocation, 0, role, {}});
        std::vector<Components> arguments{std::move(index)};
        for (unsigned slot = 0; slot < repeat->carried.size(); ++slot) {
          Components carried;
          auto type = valueTypes[repeat->carried[slot].index];
          for (auto role : selected)
            carried[role] = node(Provenance::Kind::Carry, type, {}, {}, {},
                                 LoopSubject{invocation, slot, role, {}});
          arguments.push_back(std::move(carried));
        }
        llvm::append_range(arguments, gather(repeat->captures));
        auto successors = body(*repeat->region, arguments, roles, callDepth,
                               context, regionDepth + 1);
        if (failure)
          return {};
        loops[invocation].transition = std::move(successors);
        each([&](unsigned slot, unsigned role, const Type &type) {
          const auto &loop = loops[invocation];
          if (slot >= loop.transition.size())
            return unknown(type);
          auto count = at(loop.counts, role, countType)->constantCount;
          if ((count && *count == 0) ||
              (maximum.isClosed() && maximum.closedValue() == 0))
            return at(loop.initial[slot], role, type);
          if (count && *count == 1)
            return at(loop.transition[slot], role, type);
          return node(Provenance::Kind::Exit, type, {}, {}, {},
                      LoopSubject{invocation, slot, role, {}});
        });
      } else if (const auto *completion =
                     std::get_if<ProtocolCompletion>(&op.action)) {
        for (unsigned i = 0; i < completion->values.size(); ++i)
          results[i] = values[completion->values[i].index];
      } else {
        each([&](unsigned, unsigned, const Type &type) {
          return unknown(type);
        });
      }
      if (failure)
        return {};
      if (results.size() != op.results.size()) {
        refuse(op.span, "common result association differs");
        return {};
      }
      for (unsigned i = 0; i < results.size(); ++i) {
        if (source.mode == Body::Mode::Protocol) {
          auto available =
              mappedRoles(source.values[op.results[i].index].components);
          for (auto it = results[i].begin(); it != results[i].end();)
            if (!llvm::is_contained(available, it->first))
              it = results[i].erase(it);
            else
              ++it;
        }
        values[op.results[i].index] = std::move(results[i]);
      }
    }
    return gather(source.results);
  }

public:
  Requirements(const std::vector<Declaration> &declarations,
               ArrayRef<Asset> assets, detail::Work &work)
      : declarations(declarations), work(work),
        types(declarations, assets, work) {
    (void)!!failure;
  }
  /// One semantic index may serve several targets; each run starts from an
  /// empty requirement, call-site, loop and demand state.
  Expected<std::vector<CommonControlRequirement>> run(DeclarationId target) {
    requirements.clear();
    callSites.clear();
    loops.clear();
    demands.clear();
    if (target.index >= declarations.size() || !declarations[target.index].body)
      return detail::failure("source.common-provenance",
                             "common target has no checked body");
    const auto &decl = declarations[target.index];
    if (!charge(decl.roles.size() + decl.inputs.size() + 1, decl.span))
      return std::move(failure);
    std::vector<unsigned> roles(decl.roles.size());
    std::iota(roles.begin(), roles.end(), 0);
    std::vector<Components> inputs(decl.inputs.size());
    for (unsigned i = 0; i < decl.inputs.size(); ++i)
      for (auto role : decl.inputs[i].roles) {
        auto value = node(Provenance::Kind::Input, decl.inputs[i].type, {}, {},
                          CommonControlComponent{i, role, {}});
        if (failure)
          return std::move(failure);
        inputs[i].emplace(role, std::move(value));
      }
    body(*decl.body, inputs, roles, 1, environment(decl, {}));
    if (failure)
      return std::move(failure);
    if (types.diagnostic)
      return make_error<DiagnosticError>(*types.diagnostic);
    for (const auto &demand : demands) {
      callSites = demand.calls;
      std::vector<Node> observed;
      for (const auto &value : demand.values)
        observed.push_back(facet(value, demand.tagOnly, {}, demand.control));
      std::set<Equation> hypotheses;
      if (!agree(observed, demand.control, hypotheses))
        return std::move(failure);
    }
    if (failure)
      return std::move(failure);
    return std::move(requirements);
  }
};
// Preflight the borrowed metadata before constructing Semantics' indices.
Expected<std::vector<CommonControlRequirement>>
deriveRequirements(const std::vector<Declaration> &declarations,
                   ArrayRef<Asset> assets, detail::Work &work,
                   DeclarationId target) {
  if (auto e = detail::chargeSemanticIndex(declarations, work))
    return e;
  return Requirements(declarations, assets, work).run(target);
}
} // namespace
namespace detail {
Error checkCommonControlRequirements(
    const std::vector<Declaration> &declarations, ArrayRef<Asset> assets,
    Work &work) {
  // The semantic index is built and charged once for the whole project; each
  // Protocol then pays only for its own derivation.
  std::optional<Requirements> derivation;
  for (const auto &decl : declarations) {
    if (decl.kind != Declaration::Kind::Protocol || !decl.body)
      continue;
    // Descriptor/callback specialization supplies a concrete immutable input
    // environment. Its required invariants are replayed at closure below.
    if (!decl.domainInputs.empty() || decl.body->parameterizedSummary)
      continue;
    if (!derivation) {
      if (auto e = chargeSemanticIndex(declarations, work))
        return e;
      derivation.emplace(declarations, assets, work);
    }
    auto requirements = derivation->run(decl.id);
    if (!requirements)
      return requirements.takeError();
  }
  return Error::success();
}
Error retainCommonControlRequirements(const ClosedEntry &entry,
                                      ClosedStorage &storage, Work &work) {
  const auto &declarations = detail::DeclarationAccess::get(entry);
  std::optional<Requirements> derivation;
  for (const auto &decl : declarations) {
    if (auto error = work.charge(1, decl.span))
      return error;
    if (!isClosedConcreteProtocol(decl))
      continue;
    if (!derivation) {
      if (auto error = chargeSemanticIndex(declarations, work))
        return error;
      derivation.emplace(declarations, entry.project().assets(), work);
    }
    auto requirements = derivation->run(decl.id);
    if (!requirements)
      return requirements.takeError();
    storage.commonInputs.emplace(decl.id.index, std::move(*requirements));
  }
  return Error::success();
}
} // namespace detail
Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const CheckedProject &project,
                                DeclarationId target, const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  const auto &declarations = detail::DeclarationAccess::get(project);
  detail::Work work{limits};
  return deriveRequirements(declarations, project.assets(), work, target);
}
bool isClosedConcreteProtocol(const Declaration &decl) {
  return decl.kind == Declaration::Kind::Protocol && decl.body &&
         !decl.abstract && decl.parameters.empty() &&
         decl.scopedInputs.empty() && decl.domainInputs.empty();
}

} // namespace zkc::language
