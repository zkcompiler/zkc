#include "zkc/Language/CommonControl.h"
#include "CommonRequirements.h"
#include "CommonSummary.h"
#include "Semantics.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include <cstdint>
#include <deque>
#include <numeric>
#include <set>
#include <tuple>
#include <unordered_map>

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
struct CommonCall;
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
    Unknown,
    Formal,
    Call,
    Field,
    Payload,
    Facet,
    Branch,
    RepeatResult,
    Deferred
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
  // Recipe coordinates have meaning only in their immutable instance.
  unsigned slot = 0, role = 0, alternative = 0;
  Span span = {};
  std::shared_ptr<const CommonCall> call = {};
};
using Components = std::map<unsigned, Node>;
struct CommonLoop {
  Components counts;
  std::vector<Components> initial, transition;
  bool atMostOne;
  Natural maximum;
};
struct CommonDemand {
  std::vector<Node> values;
  bool tagOnly;
  Span control;
  std::vector<Span> calls;
  std::shared_ptr<const CommonCall> call = {};
};
// A checked body is the template authority. Instances contain its immutable
// products in a lexical specialization, never the first caller's judgment.
struct CommonTemplate {
  const Body *body;
  const Declaration *declaration;
  const ScopedComputation *computation;
};
struct CommonInstance {
  std::shared_ptr<const CommonTemplate> source;
  std::vector<Components> results;
  std::vector<CommonLoop> loops;
  std::vector<CommonDemand> demands;
  unsigned operands = 0, callHeight = 1, regionHeight = 1;
  bool fresh = false;
};
struct CommonCall {
  std::shared_ptr<const CommonInstance> instance;
  std::vector<Components> operands;
  std::vector<unsigned> roles;
  Span span;
};
class Requirements {
  const std::vector<Declaration> &declarations;
  detail::Work &work;
  detail::Semantics types;
  detail::CommonSummaryObservation &observation;
  std::vector<CommonControlRequirement> requirements;
  std::vector<Span> callSites;
  std::vector<CommonLoop> loops;
  std::vector<CommonDemand> demands;
  using TemplateKey =
      std::tuple<const Body *, const Declaration *, const ScopedComputation *>;
  std::map<TemplateKey, std::shared_ptr<const CommonTemplate>> templates;
  using InstanceKey =
      std::tuple<TemplateKey, const StaticEnvironment *, unsigned, std::string>;
  std::map<InstanceKey, std::shared_ptr<const CommonInstance>> instances;
  std::set<InstanceKey> constructing;
  std::map<std::string, std::shared_ptr<const StaticEnvironment>> staticFrames;
  CommonInstance *building = nullptr;
  struct Evaluated {
    Node value;
    unsigned height;
  };
  struct Application {
    // Semantic bindings are immutable; only demanded-product caches grow.
    const std::shared_ptr<const CommonInstance> instance;
    const std::vector<Components> operands;
    const std::vector<unsigned> roles, loops;
    const std::vector<Span> sites;
    const unsigned callDepth, occurrence;
    std::unordered_map<const Provenance *, Evaluated> memo;
    std::unordered_map<const Provenance *, Node> deferred;
    std::map<const CommonCall *, std::shared_ptr<Application>> calls;
    Application(std::shared_ptr<const CommonInstance> instance,
                std::vector<Components> operands, std::vector<unsigned> roles,
                std::vector<unsigned> loops, std::vector<Span> sites,
                unsigned callDepth, unsigned occurrence)
        : instance(std::move(instance)), operands(std::move(operands)),
          roles(std::move(roles)), loops(std::move(loops)),
          sites(std::move(sites)), callDepth(callDepth),
          occurrence(occurrence) {}
  };
  using ApplicationKey =
      std::tuple<const CommonInstance *, std::vector<const Provenance *>,
                 std::vector<unsigned>>;
  std::map<ApplicationKey, std::shared_ptr<Application>> applications;
  // Deferred nodes contain an owner-relative index, never a shared_ptr back
  // into their application. This arena makes ownership acyclic and explicit.
  // Recursive evaluation may append applications while borrowing an owner.
  std::deque<std::shared_ptr<Application>> activeApplications;
  std::vector<std::pair<std::shared_ptr<Application>, unsigned>> loopOwners;
  std::vector<std::set<unsigned>> boundLoops;
  std::vector<std::set<unsigned>> boundTransitions;
  std::vector<unsigned> expressionHeights;
  uint64_t applicationCount = 0;
  // These caches own their nodes until the current root completes. Reusable
  // agreement is published only after the enclosing demand is grounded.
  using Agreement = std::vector<Node>;
  std::map<Agreement, unsigned> established, pending;
  std::vector<unsigned> agreementHeights;
  std::vector<bool> conditionalAgreement;
  Agreement completedDemand;
  unsigned completedDemandHeight = 0;
  using RequirementKey = std::tuple<std::string, bool, std::optional<unsigned>,
                                    std::string, std::string>;
  std::set<RequirementKey> requirementIndex;
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
  // Fixed-width snapshot-local identities keep charged key size independent
  // of allocator addresses. The pointed-to objects outlive this owner.
  void identity(std::string &key, const void *pointer) {
    auto bits = reinterpret_cast<uintptr_t>(pointer);
    for (unsigned i = 0; i < sizeof(bits); ++i)
      key.push_back(char(bits >> (i * 8)));
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
  Node recipe(Provenance::Kind kind, const Type &type,
              std::vector<Node> operands = {}, unsigned slot = 0,
              unsigned role = 0, unsigned alternative = 0, Span span = {},
              std::shared_ptr<const CommonCall> call = {}, bool tag = false,
              std::optional<unsigned> axis = {}) {
    auto result = std::make_shared<Provenance>(
        *node(kind, type, {}, std::move(operands), {}, {}, tag, axis));
    result->slot = slot;
    result->role = role;
    result->alternative = alternative;
    result->span = span;
    result->call = std::move(call);
    return result;
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
      std::string key;
      bool closed = true;
      for (const auto &[name, type] : bindings)
        if (!charge(name.size() + 1, callee.span) ||
            !types.chargeType(type, callee.span)) {
          if (types.diagnostic && !failure)
            failure = make_error<DiagnosticError>(*types.diagnostic);
          break;
        } else {
          std::set<std::string> references;
          staticReferences(type, references, callee.span);
          closed &= references.empty();
          detail::frame(key, name);
          detail::frame(key, typeIdentity(type));
        }
      if (failure)
        return {};
      if (closed)
        parent.reset();
      identity(key, parent.get());
      if (!charge(key.size() + 1, callee.span))
        return {};
      auto found = staticFrames.find(key);
      if (found != staticFrames.end())
        parent = found->second;
      else {
        parent = std::make_shared<StaticEnvironment>(
            StaticEnvironment{std::move(bindings), std::move(parent)});
        staticFrames.emplace(std::move(key), parent);
      }
    }
    return {std::move(parent), {}, {}, callee.qualifiedName};
  }
  std::optional<DeclarationId> target(DeclarationId known,
                                      std::vector<Type> &arguments,
                                      const std::optional<Type> &module,
                                      const Environment &context, Span span) {
    auto actual = arguments;
    const auto parent = declarations[known.index].parent;
    if (module && !module->symbolic && parent &&
        declarations[parent->index].kind == Declaration::Kind::Interface) {
      // Only the inherited interface prefix participates in dispatch. Own
      // statics retain their lexical frame until an observation needs them.
      const auto inherited = declarations[parent->index].parameters.size();
      for (unsigned i = 0; i < std::min(inherited, actual.size()); ++i)
        actual[i] = substitute(actual[i], context, span);
    }
    if (failure)
      return {};
    auto selected = types.dispatch(module, known, actual, span);
    if (!selected) {
      if (types.diagnostic && !failure)
        failure = make_error<DiagnosticError>(*types.diagnostic);
      return {};
    }
    arguments = std::move(selected->arguments);
    return selected->declaration;
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
    left = force(left, depth);
    right = force(right, depth);
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
                 std::vector<Node> children, Span span, unsigned depth = 0) {
    if (children.size() > 1) {
      std::set<std::pair<Node, Node>> seen;
      bool identical = true;
      for (unsigned i = 2; i < children.size(); ++i)
        identical &= same(children[1], children[i], span, depth, seen);
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
    if (building)
      building->callHeight = std::max(building->callHeight, depth);
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
      auto selected = target(binding.factory->declaration, statics, module,
                             context, binding.span);
      if (!selected)
        return {};
      const auto &callee = declarations[selected->index];
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
    if (building)
      building->callHeight = std::max(building->callHeight, depth);
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
    if (building)
      building->callHeight = std::max(building->callHeight, depth);
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
  Components formals(const Components &actual,
                     std::vector<Components> &operands,
                     ArrayRef<unsigned> roles, std::string &key, Span span) {
    if (!charge(actual.size() + roles.size() + 1, span))
      return {};
    unsigned slot = operands.size();
    operands.push_back(actual);
    Components result;
    detail::frame(key, std::to_string(actual.size()));
    for (unsigned r = 0; r < roles.size(); ++r) {
      auto found = actual.find(roles[r]);
      if (found == actual.end())
        continue;
      const auto &type = found->second->type;
      if (!chargeStaticType(type, span))
        return {};
      detail::frame(key, std::to_string(r));
      detail::frame(key, typeIdentity(type));
      result[r] = recipe(Provenance::Kind::Formal, type, {}, slot, r);
    }
    detail::frame(key, "end");
    return result;
  }
  Environment formalEnvironment(const Environment &context,
                                std::vector<Components> &operands,
                                ArrayRef<unsigned> roles, std::string &key,
                                Span span, unsigned depth = 0) {
    Environment result{context.statics, {}, {}, context.identity};
    if (!charge(context.scoped.size() + context.domains.size() + 1, span) ||
        depth > work.limits.callDepth) {
      capacity(span, "common summary environment depth exceeded");
      return result;
    }
    identity(key, context.statics.get());
    detail::frame(key, std::to_string(context.domains.size()));
    for (const auto &domain : context.domains)
      result.domains.push_back(formals(domain, operands, roles, key, span));
    detail::frame(key, std::to_string(context.scoped.size()));
    for (const auto &binding : context.scoped) {
      if (!binding) {
        detail::frame(key, "absent");
        result.scoped.push_back({});
        continue;
      }
      identity(key, binding->computation);
      detail::frame(key, std::to_string(unsigned(binding->signature.mode)));
      detail::frame(key, std::to_string(binding->signature.allowance.mayStop));
      detail::frame(key, std::to_string(binding->signature.allowance.opaque));
      detail::frame(key, std::to_string(binding->signature.inputs.size()));
      for (const auto &type : binding->signature.inputs) {
        if (!chargeStaticType(type, span))
          return result;
        detail::frame(key, typeIdentity(type));
      }
      if (!chargeStaticType(binding->signature.result, span))
        return result;
      detail::frame(key, typeIdentity(binding->signature.result));
      detail::frame(key, binding->statics ? "statics" : "no-statics");
      if (binding->statics) {
        identity(key, binding->statics->environment.get());
        detail::frame(key, std::to_string(binding->statics->parameters.size()));
        for (const auto &type : binding->statics->parameters) {
          if (!chargeStaticType(type, span))
            return result;
          detail::frame(key, typeIdentity(type));
        }
      }
      auto nested = formalEnvironment(binding->environment, operands, roles,
                                      key, span, depth + 1);
      std::vector<Components> captures;
      detail::frame(key, std::to_string(binding->captures.size()));
      for (const auto &capture : binding->captures)
        captures.push_back(formals(capture, operands, roles, key, span));
      result.scoped.push_back(std::make_shared<ScopedEnvironment>(
          ScopedEnvironment{binding->computation, binding->signature,
                            std::move(nested), std::move(captures),
                            binding->identity, binding->statics}));
    }
    return result;
  }
  std::shared_ptr<const CommonCall>
  summarize(const Body &source, ArrayRef<Components> inputs,
            ArrayRef<unsigned> roles, const Environment &context, Span span,
            unsigned callDepth, const Declaration *declaration,
            const ScopedComputation *computation = nullptr) {
    if (!charge(inputs.size() + roles.size() + 1, span))
      return {};
    std::vector<Components> operands, parameters;
    std::string shape;
    for (const auto &input : inputs)
      parameters.push_back(formals(input, operands, roles, shape, span));
    auto nested = formalEnvironment(context, operands, roles, shape, span);
    // Formal construction already charges each structural type and operand.
    // A coefficient's decimal spelling must not price unobserved capacity.
    if (failure || !charge(1, span))
      return {};
    TemplateKey templateKey{&source, declaration, computation};
    InstanceKey key{templateKey, context.statics.get(), roles.size(),
                    std::move(shape)};
    auto found = instances.find(key);
    std::shared_ptr<const CommonInstance> instance;
    if (found != instances.end()) {
      ++observation.instanceHits;
      instance = found->second;
    } else {
      if (constructing.size() >= work.limits.callDepth) {
        capacity(span, "common callable depth exceeded");
        return {};
      }
      if (!constructing.insert(key).second) {
        refuse(span, "common summary requires an acyclic checked call closure");
        return {};
      }
      auto remove = llvm::scope_exit([&] { constructing.erase(key); });
      if (instances.size() + constructing.size() > work.limits.instances) {
        capacity(span, "common summary instance limit exceeded");
        return {};
      }
      auto &sourceTemplate = templates[templateKey];
      if (!sourceTemplate) {
        ++observation.templates;
        sourceTemplate = std::make_shared<CommonTemplate>(
            CommonTemplate{&source, declaration, computation});
      }
      ++observation.instances;
      auto product = std::make_shared<CommonInstance>();
      product->source = sourceTemplate;
      product->operands = operands.size();
      auto *parent = building;
      auto outerLoops = std::move(loops);
      auto outerDemands = std::move(demands);
      auto outerSites = std::move(callSites);
      loops.clear();
      demands.clear();
      callSites.clear();
      building = product.get();
      std::vector<unsigned> localRoles(roles.size());
      std::iota(localRoles.begin(), localRoles.end(), 0);
      product->results = body(source, parameters, localRoles, 1, nested);
      product->loops = std::move(loops);
      product->demands = std::move(demands);
      product->fresh |= !product->loops.empty();
      loops = std::move(outerLoops);
      demands = std::move(outerDemands);
      callSites = std::move(outerSites);
      building = parent;
      if (failure)
        return {};
      instance = std::move(product);
      // Keep the active key intact until the scope guard removes it.
      instances.emplace(key, instance);
    }
    if (callDepth + instance->callHeight > work.limits.callDepth ||
        instance->regionHeight > work.limits.expressionDepth) {
      capacity(span, "common cached callable or region depth exceeded");
      return {};
    }
    if (building) {
      building->callHeight =
          std::max(building->callHeight, callDepth + instance->callHeight);
      building->regionHeight =
          std::max(building->regionHeight, instance->regionHeight);
      building->fresh |= instance->fresh;
    }
    return std::make_shared<CommonCall>(
        CommonCall{std::move(instance), std::move(operands),
                   std::vector<unsigned>(roles.begin(), roles.end()), span});
  }
  std::vector<Components>
  delayed(const std::shared_ptr<const CommonCall> &call) {
    if (!call)
      return {};
    // A call's demand edge is retained once, without flattening its closure.
    if (!call->instance->demands.empty())
      demands.push_back({{}, false, call->span, callSites, call});
    std::vector<Components> results(call->instance->results.size());
    for (unsigned i = 0; i < results.size(); ++i)
      for (auto [role, value] : call->instance->results[i])
        results[i][call->roles[role]] =
            recipe(Provenance::Kind::Call, value->type, {}, i, role, 0,
                   call->span, call);
    return results;
  }
  std::vector<Components> evaluate(ArrayRef<Components> values,
                                   const std::shared_ptr<Application> &app,
                                   unsigned depth) {
    std::vector<Components> result;
    for (const auto &components : values) {
      Components mapped;
      for (auto [role, value] : components)
        mapped[app->roles.at(role)] = defer(value, app);
      result.push_back(std::move(mapped));
    }
    (void)depth;
    return result;
  }
  std::shared_ptr<Application>
  apply(const std::shared_ptr<const CommonInstance> &instance,
        std::vector<Components> operands, std::vector<unsigned> roles,
        unsigned callDepth, std::vector<Span> sites) {
    Span span = sites.empty() ? Span{} : sites.back();
    if (!charge(operands.size() + roles.size() + sites.size() +
                    instance->loops.size() + 1,
                span))
      return {};
    if (callDepth == 0 ||
        callDepth - 1 + instance->callHeight > work.limits.callDepth ||
        instance->regionHeight > work.limits.expressionDepth) {
      capacity(span, "common applied callable or region depth exceeded");
      return {};
    }
    if (operands.size() != instance->operands) {
      refuse(span, "common summary operand association differs");
      return {};
    }
    ApplicationKey key;
    bool reusable = !instance->fresh && instance->demands.empty();
    if (reusable) {
      std::vector<const Provenance *> nodes;
      for (const auto &components : operands) {
        // Include missing-role coordinates as well as exact actual origins.
        for (auto role : roles) {
          auto found = components.find(role);
          nodes.push_back(found == components.end() ? nullptr
                                                    : found->second.get());
        }
      }
      if (!charge(nodes.size() + 1, span))
        return {};
      key = {instance.get(), std::move(nodes), roles};
      auto found = applications.find(key);
      if (found != applications.end()) {
        ++observation.applicationHits;
        return found->second;
      }
    }
    if (applicationCount >= work.limits.operations) {
      capacity(span, "common summary application limit exceeded");
      return {};
    }
    ++applicationCount;
    ++observation.applications;
    std::vector<unsigned> loopBindings(instance->loops.size());
    std::iota(loopBindings.begin(), loopBindings.end(), loops.size());
    auto app = std::make_shared<Application>(
        instance, std::move(operands), std::move(roles),
        std::move(loopBindings), std::move(sites), callDepth,
        activeApplications.size());
    activeApplications.push_back(app);
    for (unsigned i = 0; i < instance->loops.size(); ++i) {
      if (!charge(1, span) || loops.size() >= work.limits.operations) {
        capacity(span, "common fresh recurrence limit exceeded");
        return {};
      }
      ++observation.loopNamespaces;
      loops.push_back({{}, {}, {}, false, {}});
      loopOwners.emplace_back(app, i);
      boundLoops.emplace_back();
      boundTransitions.emplace_back();
    }
    if (reusable)
      applications.emplace(std::move(key), app);
    // Source formation demands include dormant arms and zero-trip regions.
    for (const auto &demand : instance->demands) {
      if (!charge(demand.values.size() + demand.calls.size() + 1,
                  demand.control))
        return {};
      if (demand.call) {
        if (!application(demand.call, app, 0))
          return {};
        continue;
      }
      std::vector<Node> values;
      for (const auto &value : demand.values)
        values.push_back(defer(value, app));
      auto calls = app->sites;
      llvm::append_range(calls, demand.calls);
      demands.push_back({std::move(values), demand.tagOnly, demand.control,
                         std::move(calls)});
    }
    return app;
  }
  std::shared_ptr<Application>
  application(const std::shared_ptr<const CommonCall> &call,
              const std::shared_ptr<Application> &parent, unsigned depth) {
    if (!charge(1, call->span))
      return {};
    auto found = parent->calls.find(call.get());
    if (found != parent->calls.end())
      return found->second;
    auto operands = evaluate(call->operands, parent, depth);
    std::vector<unsigned> roles;
    for (auto role : call->roles)
      roles.push_back(parent->roles.at(role));
    auto sites = parent->sites;
    sites.push_back(call->span);
    auto result = apply(call->instance, std::move(operands), std::move(roles),
                        parent->callDepth + 1, std::move(sites));
    if (result)
      parent->calls.emplace(call.get(), result);
    return result;
  }
  void bindLoop(unsigned invocation, unsigned slot, unsigned depth,
                bool needTransition = false) {
    if (failure)
      return;
    auto [app, local] = loopOwners.at(invocation);
    const auto &source = app->instance->loops[local];
    if (boundLoops[invocation].empty()) {
      auto values = evaluate({source.counts}, app, depth);
      bool small = true;
      for (auto [role, value] : values.front()) {
        (void)role;
        value = force(value);
        small &= value->constantCount && *value->constantCount <= 1;
      }
      bool atMostOne = small || (source.maximum.isClosed() &&
                                 source.maximum.closedValue() <= 1);
      loops[invocation] = {std::move(values.front()),
                           std::vector<Components>(source.initial.size()),
                           std::vector<Components>(source.transition.size()),
                           atMostOne, source.maximum};
    }
    if (boundLoops[invocation].insert(slot).second) {
      auto initial = evaluate({source.initial.at(slot)}, app, depth);
      loops[invocation].initial.at(slot) = std::move(initial.front());
    }
    if (needTransition && boundTransitions[invocation].insert(slot).second) {
      auto transition = evaluate({source.transition.at(slot)}, app, depth);
      loops[invocation].transition.at(slot) = std::move(transition.front());
    }
  }
  Node branch(const Type &type, Node subject, std::vector<Node> arms,
              bool match, Span span, unsigned depth) {
    subject = force(subject, depth + 1);
    std::optional<unsigned> selected;
    if (subject->kind == Provenance::Kind::Static) {
      auto boolean =
          "math:" +
          std::to_string(unsigned(MathematicalIdentity::BooleanConstant)) + ":";
      if (subject->identity == boolean + "true")
        selected = 0;
      else if (subject->identity == boolean + "false")
        selected = 1;
    } else if (subject->kind == Provenance::Kind::Variant) {
      unsigned ordinal;
      if (!StringRef(subject->identity).getAsInteger(10, ordinal))
        selected = ordinal;
    }
    if (selected && *selected < arms.size())
      return arms[*selected];
    std::vector<Node> children{facet(subject, match, {}, span, depth + 1)};
    llvm::append_range(children, arms);
    return selection(type, match ? "match" : "if", std::move(children), span,
                     depth + 1);
  }
  Node defer(Node value, const std::shared_ptr<Application> &app) {
    if (!charge(1, value->span))
      return unknown(value->type);
    if (value->kind == Provenance::Kind::Formal)
      return at(app->operands.at(value->slot), app->roles.at(value->role),
                value->type);
    auto found = app->deferred.find(value.get());
    if (found != app->deferred.end())
      return found->second;
    auto result = recipe(Provenance::Kind::Deferred, value->type, {value},
                         app->occurrence);
    app->deferred.emplace(value.get(), result);
    return result;
  }
  Node force(Node value, unsigned depth = 0) {
    while (!failure && value->kind == Provenance::Kind::Deferred)
      value = evaluate(value->operands.front(),
                       activeApplications.at(value->slot), depth);
    return value;
  }
  Node evaluate(Node value, const std::shared_ptr<Application> &app,
                unsigned depth) {
    if (!charge(1, value->span) || failure)
      return unknown(value->type);
    if (depth > work.limits.expressionDepth) {
      capacity(value->span, "common applied expression depth exceeded");
      return unknown(value->type);
    }
    auto found = app->memo.find(value.get());
    if (found != app->memo.end()) {
      if (found->second.height > work.limits.expressionDepth - depth) {
        capacity(value->span, "common cached expression depth exceeded");
        return unknown(value->type);
      }
      if (!expressionHeights.empty())
        expressionHeights.back() =
            std::max(expressionHeights.back(), depth + found->second.height);
      return found->second.value;
    }
    ++observation.expressions;
    expressionHeights.push_back(depth);
    auto restore = llvm::scope_exit([&] {
      auto height = expressionHeights.back();
      expressionHeights.pop_back();
      if (!expressionHeights.empty())
        expressionHeights.back() = std::max(expressionHeights.back(), height);
    });
    using K = Provenance::Kind;
    Node result;
    if (value->kind == K::Formal)
      result = at(app->operands.at(value->slot), app->roles.at(value->role),
                  value->type);
    else if (value->kind == K::Call) {
      auto child = application(value->call, app, depth);
      if (!child)
        return unknown(value->type);
      result =
          evaluate(child->instance->results.at(value->slot).at(value->role),
                   child, depth);
    } else if (value->kind == K::RepeatResult) {
      unsigned invocation = app->loops.at(value->slot);
      const auto &source = app->instance->loops.at(value->slot);
      auto role = app->roles.at(value->role);
      auto sourceCount =
          at(source.counts, value->role, Type(Type::Kind::Index));
      auto count = force(defer(sourceCount, app), depth + 1)->constantCount;
      if (value->alternative >= source.transition.size())
        result = unknown(value->type);
      else if ((count && *count == 0) ||
               (source.maximum.isClosed() && source.maximum.closedValue() == 0))
        result = defer(
            at(source.initial[value->alternative], value->role, value->type),
            app);
      else if (count && *count == 1)
        result = defer(
            at(source.transition[value->alternative], value->role, value->type),
            app);
      else
        result = node(K::Exit, value->type, {}, {}, {},
                      LoopSubject{invocation, value->alternative, role, {}});
    } else if (value->loop) {
      auto subject = *value->loop;
      subject.invocation = app->loops.at(subject.invocation);
      subject.role = app->roles.at(subject.role);
      result = node(value->kind, value->type, value->identity, {}, {},
                    std::move(subject), value->tagOnly, value->extentAxis,
                    value->constantCount, value->statics);
    } else {
      std::vector<Node> operands;
      for (const auto &operand : value->operands)
        operands.push_back(defer(operand, app));
      if (value->kind == K::Field)
        result =
            field(operands.front(), value->slot, value->span, 0, depth + 1);
      else if (value->kind == K::Payload)
        result = payload(operands.front(), value->alternative, value->slot,
                         value->type, value->span, 0, depth + 1);
      else if (value->kind == K::Facet)
        result = facet(operands.front(), value->tagOnly, value->extentAxis,
                       value->span, depth + 1);
      else if (value->kind == K::Branch) {
        auto subject = operands.front();
        operands.erase(operands.begin());
        result = branch(value->type, subject, std::move(operands),
                        value->tagOnly, value->span, depth);
      } else
        result = node(value->kind, value->type, value->identity,
                      std::move(operands), value->input, {}, value->tagOnly,
                      value->extentAxis, value->constantCount, value->statics);
    }
    if (!failure)
      app->memo.emplace(value.get(),
                        Evaluated{result, expressionHeights.back() - depth});
    return result;
  }
  Node field(Node value, unsigned index, Span span, unsigned depth,
             unsigned expressionDepth = 0) {
    value = force(value, expressionDepth);
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
    if (building)
      return recipe(Provenance::Kind::Field, type, {value}, index, 0, 0, span);
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
        children[i] =
            field(children[i], index, span, depth + 1, expressionDepth + 1);
      return selection(type, value->identity, std::move(children), span,
                       expressionDepth);
    }
    if (value->kind == Provenance::Kind::Inactive)
      return node(value->kind, type, value->identity);
    if (value->kind == Provenance::Kind::Unknown)
      return unknown(type);
    return node(Provenance::Kind::Total, type, "field:" + std::to_string(index),
                {value});
  }
  Node payload(Node value, unsigned alternative, unsigned index,
               const Type &type, Span span, unsigned depth = 0,
               unsigned expressionDepth = 0) {
    value = force(value, expressionDepth);
    if (!charge(1, span) || depth > work.limits.typeDepth) {
      capacity(span, "common payload projection depth exceeded");
      return unknown(type);
    }
    if (building)
      return recipe(Provenance::Kind::Payload, type, {value}, index, 0,
                    alternative, span);
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
        children[i] = payload(children[i], alternative, index, type, span,
                              depth + 1, expressionDepth + 1);
      return selection(type, value->identity, std::move(children), span,
                       expressionDepth);
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
    value = force(value, depth);
    if (!charge(1, span) || depth > work.limits.expressionDepth) {
      capacity(span, "common observation depth exceeded");
      return unknown(value->type);
    }
    if (building)
      return recipe(Provenance::Kind::Facet, value->type, {value}, 0, 0, 0,
                    span, {}, tagOnly, axis);
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
      return selection(value->type, value->identity, std::move(children), span,
                       depth);
    }
    if (value->kind == Provenance::Kind::Unknown ||
        value->kind == Provenance::Kind::Inactive)
      return value;
    return node(Provenance::Kind::Total, value->type,
                tagOnly ? "tag" : "extent:" + std::to_string(*axis), {value});
  }
  Node observe(Node value, const Provenance &observation, Span span,
               unsigned depth) {
    for (const auto &step : observation.loop->path)
      value = step.payload ? payload(value, step.alternative, step.index,
                                     step.type, span, 0, depth)
                           : field(value, step.index, span, 0, depth);
    return facet(value, observation.tagOnly, observation.extentAxis, span,
                 depth);
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
    Agreement key;
    for (const auto &value : values)
      key.push_back(force(value, depth));
    auto completed = established.find(key);
    auto local = pending.find(key);
    auto height = completed != established.end()
                      ? std::optional<unsigned>(completed->second)
                  : local != pending.end()
                      ? std::optional<unsigned>(local->second)
                      : std::nullopt;
    if (depth > work.limits.expressionDepth)
      return capacity(span, "common cached derivation depth exceeded");
    if (height && *height <= work.limits.expressionDepth - depth) {
      if (!agreementHeights.empty())
        agreementHeights.back() =
            std::max(agreementHeights.back(), *height + 1);
      else {
        completedDemand = key;
        completedDemandHeight = *height;
      }
      return true;
    }
    // A current recurrence context can have a shorter grounded derivation.
    // Recheck it instead of either hiding cached height or over-refusing.
    agreementHeights.push_back(0);
    conditionalAgreement.push_back(false);
    bool success = agreeImpl(key, span, hypotheses, depth);
    unsigned used = agreementHeights.back();
    bool conditional = conditionalAgreement.back();
    agreementHeights.pop_back();
    conditionalAgreement.pop_back();
    if (!agreementHeights.empty())
      agreementHeights.back() = std::max(agreementHeights.back(), used + 1);
    if (!conditionalAgreement.empty())
      conditionalAgreement.back() = conditionalAgreement.back() || conditional;
    if (success && agreementHeights.empty()) {
      completedDemand = key;
      completedDemandHeight = used;
    }
    // A cycle-closing hypothesis is not a completed subproof, including for
    // depth accounting. Only the entire grounded demand may publish it.
    if (success && !conditional)
      pending.emplace(std::move(key), used);
    return success;
  }
  bool agreeImpl(ArrayRef<Node> values, Span span,
                 std::set<Equation> &hypotheses, unsigned depth = 0) {
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
      std::set<std::string> components;
      std::vector<std::string> componentKeys;
      for (const auto &value : values) {
        const auto &component = *value->input;
        std::string key;
        detail::frame(key, std::to_string(component.input));
        detail::frame(key, std::to_string(component.role));
        for (const auto &step : component.path) {
          detail::frame(key, std::to_string(unsigned(step.kind)));
          detail::frame(key, std::to_string(step.index));
        }
        if (!charge(key.size() + 1, span))
          return false;
        if (components.insert(key).second) {
          requirement.components.push_back(component);
          componentKeys.push_back(std::move(key));
        }
      }
      if (!chargeStaticType(first.type, span))
        return false;
      auto type = typeIdentity(first.type);
      for (unsigned i = 1; i < requirement.components.size(); ++i) {
        auto left = componentKeys.front();
        auto right = componentKeys[i];
        if (right < left)
          std::swap(left, right);
        if (!charge(type.size() + left.size() + right.size() + 1, span))
          return false;
        if (requirementIndex
                .emplace(type, first.tagOnly, first.extentAxis, std::move(left),
                         std::move(right))
                .second)
          requirements.push_back(
              {{requirement.components.front(), requirement.components[i]},
               first.type,
               first.tagOnly,
               span,
               first.extentAxis});
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
        if (!hypotheses.insert(std::move(equation)).second) {
          conditionalAgreement.back() = true;
          continue;
        }
        // Introduce the complete base and transition obligations before any
        // repeated subject is allowed to close a simultaneous hypothesis.
        bindLoop(first.loop->invocation, first.loop->slot, 0);
        if (failure)
          return false;
        if (first.kind == Provenance::Kind::Exit ||
            !loops[first.loop->invocation].atMostOne)
          bindLoop(first.loop->invocation, first.loop->slot, 0, true);
        if (failure)
          return false;
        const auto loop = loops[first.loop->invocation];
        auto check = [&](const Components &components) {
          std::vector<Node> pair{
              observe(at(components, first.loop->role, first.type), first, span,
                      depth + 1),
              observe(at(components, other.loop->role, other.type), other, span,
                      depth + 1)};
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
        operands.push_back(
            first.kind == Provenance::Kind::Extent
                ? facet(value->operands[i], false, 0, span, depth + 1)
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
    ++observation.bodyTraversals;
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
    if (building)
      building->regionHeight = std::max(building->regionHeight, regionDepth);
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
          results = delayed(summarize(
              *binding->computation->body, inputs, roles, binding->environment,
              op.span, callDepth, nullptr, binding->computation));
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
        auto selected = target(call->callee, statics, module, context, op.span);
        if (!selected)
          return {};
        const auto &callee = declarations.at(selected->index);
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
          results =
              delayed(summarize(*callee.body, gather(call->operands), roles,
                                nested, op.span, callDepth, &callee));
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
          results = delayed(summarize(
              *callee.body, gather(call->operands), selected,
              environment(callee, call->arguments, {}, context.statics),
              op.span, callDepth, &callee));
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
            std::vector<Node> children{subject};
            for (const auto &arm : arms) {
              if (result >= arm.size())
                return unknown(type);
              children.push_back(at(arm[result], role, type));
            }
            return recipe(Provenance::Kind::Branch, type, std::move(children),
                          0, 0, 0, op.span, {}, match);
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
        Components loopCounts;
        for (auto role : selected)
          loopCounts[role] = at(values[repeat->count.index], role, countType);
        loops.push_back({std::move(loopCounts),
                         gather(repeat->carried),
                         {},
                         atMostOne,
                         maximum});
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
          return recipe(Provenance::Kind::RepeatResult, type, {}, invocation,
                        role, slot, op.span);
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
               ArrayRef<Asset> assets, detail::Work &work,
               detail::CommonSummaryObservation &observation)
      : declarations(declarations), work(work),
        types(declarations, assets, work), observation(observation) {
    (void)!!failure;
  }
  /// One semantic index may serve several targets; each run starts from an
  /// empty requirement, call-site, loop and demand state.
  Expected<std::vector<CommonControlRequirement>> run(DeclarationId target) {
    requirements.clear();
    requirementIndex.clear();
    established.clear();
    pending.clear();
    completedDemand.clear();
    applications.clear();
    activeApplications.clear();
    loopOwners.clear();
    boundLoops.clear();
    boundTransitions.clear();
    expressionHeights.clear();
    applicationCount = 0;
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
    auto root = summarize(*decl.body, inputs, roles, environment(decl, {}),
                          decl.span, 0, &decl);
    if (root)
      apply(root->instance, root->operands, root->roles, 1, {});
    if (failure)
      return std::move(failure);
    if (types.diagnostic)
      return make_error<DiagnosticError>(*types.diagnostic);
    for (unsigned i = 0; i < demands.size(); ++i) {
      const auto demand = demands[i];
      callSites = demand.calls;
      std::vector<Node> observed;
      for (const auto &value : demand.values)
        observed.push_back(facet(value, demand.tagOnly, {}, demand.control));
      std::set<Equation> hypotheses;
      pending.clear();
      if (!agree(observed, demand.control, hypotheses))
        return std::move(failure);
      // Every base and sibling transition opened by this demand succeeded.
      established.merge(pending);
      established.emplace(std::move(completedDemand), completedDemandHeight);
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
  detail::CommonSummaryObservation observation;
  return Requirements(declarations, assets, work, observation).run(target);
}
} // namespace
namespace detail {
Error checkCommonControlRequirements(
    const std::vector<Declaration> &declarations, ArrayRef<Asset> assets,
    Work &work) {
  CommonSummaryObservation observation;
  return checkCommonSummaryRequirements(declarations, assets, work,
                                        observation);
}
Expected<std::vector<CommonControlRequirement>> deriveCommonSummaryRequirements(
    const std::vector<Declaration> &declarations, ArrayRef<Asset> assets,
    Work &work, DeclarationId target, CommonSummaryObservation &observation) {
  if (auto e = chargeSemanticIndex(declarations, work))
    return e;
  return Requirements(declarations, assets, work, observation).run(target);
}
Error checkCommonSummaryRequirements(
    const std::vector<Declaration> &declarations, ArrayRef<Asset> assets,
    Work &work, CommonSummaryObservation &observation) {
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
      derivation.emplace(declarations, assets, work, observation);
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
  CommonSummaryObservation observation;
  std::optional<Requirements> derivation;
  for (const auto &decl : declarations) {
    if (auto error = work.charge(1, decl.span))
      return error;
    if (!isClosedConcreteProtocol(decl))
      continue;
    if (!derivation) {
      if (auto error = chargeSemanticIndex(declarations, work))
        return error;
      derivation.emplace(declarations, entry.project().assets(), work,
                         observation);
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
