#include "BodySummary.h"
#include "llvm/ADT/ScopeExit.h"
#include <algorithm>
#include <unordered_map>
using namespace llvm;
namespace zkc::language::detail {
namespace {
std::optional<Dependencies> join(Semantics &types,
                                 ArrayRef<Dependencies> values) {
  Dependencies result;
  for (const auto &value : values) {
    if (!types.charge(value.inputs.size() + 1, {}))
      return {};
    result.parameterized |= value.parameterized;
    result.inputs.insert(result.inputs.end(), value.inputs.begin(),
                         value.inputs.end());
  }
  uint64_t levels = 1;
  for (auto count = result.inputs.size(); count > 1; count >>= 1)
    ++levels;
  if (!types.charge(result.inputs.size() * levels, {}))
    return {};
  llvm::sort(result.inputs);
  result.inputs.erase(std::unique(result.inputs.begin(), result.inputs.end()),
                      result.inputs.end());
  return result;
}
bool chargeBinding(Semantics &types, const ScopedSummaryBinding &binding,
                   unsigned depth, Span span) {
  if (depth > types.work.limits.callDepth)
    return types.fail("source.limit", "scoped summary copy depth", span);
  if (!types.charge(binding.signature.inputs.size() + binding.captures.size() +
                        binding.scoped.size() + binding.domains.size() +
                        binding.statics.size() + 1,
                    span) ||
      !types.chargeType(binding.signature.result, span))
    return false;
  for (const auto &input : binding.signature.inputs)
    if (!types.chargeType(input, span))
      return false;
  for (const auto &[name, value] : binding.statics)
    if (!types.charge(name.size() + 1, span) || !types.chargeType(value, span))
      return false;
  for (const auto &capture : binding.captures)
    if (!types.charge(capture.inputs.size() + 1, span))
      return false;
  for (const auto &domain : binding.domains)
    if (!types.charge(domain.inputs.size() + 1, span))
      return false;
  for (const auto &nested : binding.scoped)
    if (!chargeBinding(types, nested, depth + 1, span))
      return false;
  return true;
}
} // namespace

namespace {
using StaticFrame = std::vector<std::pair<std::string, std::string>>;
using StaticContext = std::vector<StaticFrame>;
using LexicalStatics = std::shared_ptr<const BodySummaryStatics>;

bool staticReferences(Semantics &types, const Type &type,
                      std::set<std::string> &references, unsigned depth = 1) {
  if (depth > types.work.limits.typeDepth)
    return types.fail("source.limit", "summary static type depth exceeded", {});
  if (!types.charge(type.domain.size() + type.arguments.size() + 1, {}))
    return false;
  if (type.symbolic && !type.domain.empty())
    references.insert(type.domain);
  for (const auto &[factors, coefficient] : type.dimension.terms()) {
    (void)coefficient;
    if (!types.charge(factors.size() + 1, {}))
      return false;
    for (const auto &factor : factors) {
      if (!types.charge(factor.name.size() + 1, {}))
        return false;
      references.insert(factor.name);
    }
  }
  for (const auto &argument : type.arguments)
    if (!staticReferences(types, argument, references, depth + 1))
      return false;
  return true;
}

/// Only a dispatch observation demands normalization. Resolve each actual in
/// its defining parent before substituting it into the containing expression.
std::optional<Type> substituteStatic(Semantics &types, const Type &type,
                                     LexicalStatics environment, Span span,
                                     BodySummaryCache *retained,
                                     unsigned depth = 0) {
  if (!environment)
    return type;
  struct Actual {
    const Type *type;
    LexicalStatics parent;
    unsigned depth;
  };
  auto lookup = [&](StringRef name) -> std::optional<Actual> {
    unsigned nesting = depth;
    for (auto frame = environment; frame; frame = frame->parent) {
      if (++nesting > types.work.limits.callDepth) {
        types.fail("source.limit", "summary static environment depth exceeded",
                   span);
        return {};
      }
      if (!types.charge(name.size() + 1, span))
        return {};
      auto found = frame->bindings.find(name.str());
      if (found != frame->bindings.end())
        return Actual{&found->second, frame->parent, nesting};
    }
    return {};
  };
  if (type.symbolic && !type.domain.empty()) {
    auto actual = lookup(type.domain);
    if (types.diagnostic)
      return {};
    if (actual)
      return substituteStatic(types, *actual->type, actual->parent, span,
                              retained, actual->depth);
  }
  std::set<std::string> references;
  if (!staticReferences(types, type, references))
    return {};
  Substitution bindings;
  for (const auto &name : references) {
    auto actual = lookup(name);
    if (types.diagnostic)
      return {};
    if (!actual)
      continue;
    auto value = substituteStatic(types, *actual->type, actual->parent, span,
                                  retained, actual->depth);
    if (!value)
      return {};
    bindings.emplace(name, std::move(*value));
  }
  auto result = types.substitute(type, bindings, span);
  if (result && retained && !retained->observeType(types, *result, span))
    return {};
  return result;
}

struct CallbackContext {
  const ScopedComputation *computation;
  ScopedSignature::Mode mode;
  bool mayStop, opaque;
  std::vector<std::string> signature;
  StaticContext statics;
  unsigned captures, domains;
  std::vector<CallbackContext> scoped;
  bool operator<(const CallbackContext &other) const {
    if (computation != other.computation)
      return std::less<const ScopedComputation *>{}(computation,
                                                    other.computation);
    return std::tie(mode, mayStop, opaque, signature, statics, captures,
                    domains, scoped) <
           std::tie(other.mode, other.mayStop, other.opaque, other.signature,
                    other.statics, other.captures, other.domains, other.scoped);
  }
};
struct InstanceContext {
  const Body *body;
  StaticContext statics;
  std::vector<CallbackContext> scoped;
  unsigned domains;
  bool operator<(const InstanceContext &other) const {
    if (body != other.body)
      return std::less<const Body *>{}(body, other.body);
    return std::tie(statics, scoped, domains) <
           std::tie(other.statics, other.scoped, other.domains);
  }
};
uint64_t contextWidth(const StaticContext &context) {
  uint64_t width = 1;
  for (const auto &frame : context)
    for (const auto &[name, type] : frame)
      width += name.size() + type.size() + 1;
  return width;
}
uint64_t contextWidth(const CallbackContext &context) {
  uint64_t width = contextWidth(context.statics) + 1;
  for (const auto &type : context.signature)
    width += type.size() + 1;
  for (const auto &nested : context.scoped)
    width += contextWidth(nested);
  return width;
}
bool staticFrame(Semantics &types, const Substitution &statics,
                 StaticFrame &key) {
  for (const auto &[name, value] : statics) {
    if (!types.charge(name.size() + 1, {}) || !types.chargeType(value, {}))
      return false;
    key.emplace_back(name, typeIdentity(value));
    if (!types.charge(key.back().second.size() + 1, {}))
      return false;
  }
  return true;
}
bool staticContext(Semantics &types, const Substitution &statics,
                   LexicalStatics parent, StaticContext &key) {
  StaticFrame local;
  if (!staticFrame(types, statics, local))
    return false;
  key.push_back(std::move(local));
  std::set<std::string> references;
  for (const auto &[name, value] : statics)
    if (!staticReferences(types, value, references))
      return false;
  unsigned depth = 0;
  // Unreferenced callers are not part of an instance. Besides reducing keys,
  // this makes re-entry with the same concrete actuals the same cycle subject.
  for (auto frame = parent; frame && !references.empty();
       frame = frame->parent) {
    if (++depth > types.work.limits.callDepth)
      return types.fail("source.limit", "summary lexical key depth exceeded",
                        {});
    Substitution selected;
    for (auto it = references.begin(); it != references.end();) {
      if (!types.charge(it->size() + 1, {}))
        return false;
      auto found = frame->bindings.find(*it);
      if (found == frame->bindings.end()) {
        ++it;
        continue;
      }
      selected.insert(*found);
      it = references.erase(it);
    }
    StaticFrame context;
    if (!staticFrame(types, selected, context))
      return false;
    if (!context.empty())
      key.push_back(std::move(context));
    for (const auto &[name, value] : selected)
      if (!staticReferences(types, value, references))
        return false;
  }
  return true;
}
bool normalizeFormation(Semantics &types,
                        std::vector<Dependencies> &formation) {
  uint64_t width = 1, levels = 1;
  for (const auto &requirement : formation)
    width = std::max(width, uint64_t(requirement.inputs.size() + 1));
  for (auto count = formation.size(); count > 1; count >>= 1)
    ++levels;
  if (!types.charge(formation.size() * levels * width, {}))
    return false;
  llvm::sort(formation, [](const auto &a, const auto &b) {
    return std::tie(a.inputs, a.parameterized) <
           std::tie(b.inputs, b.parameterized);
  });
  formation.erase(std::unique(formation.begin(), formation.end(),
                              [](const auto &a, const auto &b) {
                                return a.inputs == b.inputs &&
                                       a.parameterized == b.parameterized;
                              }),
                  formation.end());
  return true;
}
} // namespace

struct BodySummaryCache::Storage {
  /// This template borrows the checked Body rather than duplicating its SSA
  /// graph. Ordinary static-independent Math already has boundary products.
  struct Template {
    const Body *body;
    bool completedDependencies;
    unsigned height = 1, callHeight = 1;
    // Local region nesting composes through region edges. A callee starts its
    // own region stack, whose maximum must not be shifted by caller nesting.
    unsigned regionHeight = 1, calledRegionHeight = 1;
    uint64_t typeDepth = 0, typeNodes = 0, operations = 0;
  };
  struct Instance {
    BodySummaryApplication contract;
    Template requirements;
  };
  struct Construction {
    InstanceContext context;
    unsigned depth, height = 1;
    Template requirements;
  };
  std::unordered_map<const Body *, Template> templates;
  // A body's application cost depends on its own specialization population,
  // independently of how many other bodies or regions have been summarized.
  std::unordered_map<const Body *, std::map<InstanceContext, Instance>>
      instances;
  std::unordered_map<const ScopedComputation *,
                     std::shared_ptr<const ScopedComputation>>
      callbackOwners;
  std::set<const Body *> formingTemplates;
  std::vector<Construction> constructing;

  bool bounds(Semantics &types, const Template &body, unsigned depth,
              unsigned regionDepth = 1) {
    return (depth && depth <= types.work.limits.callDepth &&
            body.height <= types.work.limits.callDepth - depth + 1 &&
            regionDepth && regionDepth <= types.work.limits.expressionDepth &&
            body.regionHeight <=
                types.work.limits.expressionDepth - regionDepth + 1 &&
            body.calledRegionHeight <= types.work.limits.expressionDepth &&
            body.typeDepth <= types.work.limits.typeDepth &&
            body.typeNodes <= types.work.limits.typeNodes &&
            body.operations <= types.work.limits.operations) ||
           types.fail("source.limit", "retained body summary bounds exceeded",
                      {});
  }
  const Template *getTemplate(Semantics &types,
                              ArrayRef<Declaration> declarations,
                              const Body &body, unsigned depth,
                              unsigned regionDepth = 1) {
    if (!depth || depth > types.work.limits.callDepth || !regionDepth ||
        regionDepth > types.work.limits.expressionDepth ||
        !types.charge(1, {})) {
      if (!types.diagnostic)
        types.fail("source.limit", "body template depth exceeded", {});
      return nullptr;
    }
    if (formingTemplates.count(&body)) {
      types.fail("source.cycle", "recursive body summary", {});
      return nullptr;
    }
    if (auto found = templates.find(&body); found != templates.end())
      return bounds(types, found->second, depth, regionDepth) ? &found->second
                                                              : nullptr;
    formingTemplates.insert(&body);
    auto leave = llvm::scope_exit([&] { formingTemplates.erase(&body); });
    Template result{
        &body, body.mode == Body::Mode::Math && !body.parameterizedSummary &&
                   body.scopedBindings.empty() && body.domainBindings.empty()};
    result.operations = body.operations.size();
    if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
      return nullptr;
    if (body.inputs > body.values.size()) {
      types.fail("source.scoped-summary", "invalid completed body inputs", {});
      return nullptr;
    }
    auto type = [&](const Type &value) {
      if (!types.chargeType(value, {}))
        return false;
      uint64_t nodes = 0, height = 0;
      std::function<void(const Type &, unsigned)> visit = [&](const Type &term,
                                                              unsigned depth) {
        ++nodes;
        height = std::max(height, uint64_t(depth));
        for (const auto &argument : term.arguments)
          visit(argument, depth + 1);
      };
      visit(value, 1);
      result.typeNodes = std::max(result.typeNodes, nodes);
      result.typeDepth = std::max(result.typeDepth, height);
      return true;
    };
    auto child = [&](const Body &nested, unsigned callEdge = 1) {
      // A region remains inside its callable. A call starts a new body's
      // expression nesting while consuming exactly one callable frame.
      const auto *summary =
          getTemplate(types, declarations, nested, depth + callEdge,
                      callEdge ? 1 : regionDepth + 1);
      if (!summary)
        return false;
      result.height = std::max(result.height, summary->height + callEdge);
      if (callEdge)
        result.calledRegionHeight =
            std::max(result.calledRegionHeight, summary->regionHeight);
      else
        result.regionHeight =
            std::max(result.regionHeight, summary->regionHeight + 1);
      result.calledRegionHeight =
          std::max(result.calledRegionHeight, summary->calledRegionHeight);
      result.callHeight =
          std::max(result.callHeight, summary->callHeight + callEdge);
      result.typeDepth = std::max(result.typeDepth, summary->typeDepth);
      result.typeNodes = std::max(result.typeNodes, summary->typeNodes);
      result.operations = std::max(result.operations, summary->operations);
      result.completedDependencies &= summary->completedDependencies;
      return true;
    };
    for (const auto &value : body.values)
      if (!type(value.type))
        return nullptr;
    for (const auto &binding : body.scopedBindings) {
      if (!types.charge(binding.signature.inputs.size() + 1, binding.span) ||
          !type(binding.signature.result))
        return nullptr;
      for (const auto &input : binding.signature.inputs)
        if (!type(input))
          return nullptr;
      if (binding.computation &&
          (!binding.computation->body || !child(*binding.computation->body)))
        return nullptr;
    }
    for (const auto &domain : body.domainBindings) {
      if (!types.charge(domain.arguments.size() + 1, domain.span) ||
          !type(domain.item))
        return nullptr;
      for (const auto &argument : domain.arguments)
        if (!type(argument))
          return nullptr;
      if (domain.factory && domain.factory->module &&
          !type(*domain.factory->module))
        return nullptr;
    }
    for (const auto &op : body.operations) {
      bool valid = std::visit(
          [&](const auto &action) {
            using T = std::decay_t<decltype(action)>;
            if constexpr (std::is_same_v<T, MathValue> ||
                          std::is_same_v<T, LocalPrimitive>)
              for (const auto &argument : action.staticArguments)
                if (!type(argument))
                  return false;
            return true;
          },
          op.action);
      if (!valid)
        return nullptr;
      if (const auto *call = std::get_if<HelperCall>(&op.action)) {
        if (call->callee.index >= declarations.size()) {
          types.fail("source.scoped-summary", "invalid summary callee",
                     op.span);
          return nullptr;
        }
        const auto &callee = declarations[call->callee.index];
        const bool abstractDispatch =
            call->module && callee.parent &&
            callee.parent->index < declarations.size() &&
            declarations[callee.parent->index].kind ==
                Declaration::Kind::Interface;
        result.completedDependencies &= !abstractDispatch &&
                                        call->scopedArguments.empty() &&
                                        call->domainArguments.empty();
        for (const auto &argument : call->arguments)
          if (!type(argument))
            return nullptr;
        if (call->module && !type(*call->module))
          return nullptr;
        if (callee.body && !child(*callee.body))
          return nullptr;
      } else if (const auto *control = std::get_if<Control>(&op.action)) {
        for (const auto &region : control->regions)
          if (!region || !child(*region, 0))
            return nullptr;
      } else if (std::holds_alternative<ScopedInvoke>(op.action) ||
                 std::holds_alternative<FiniteApplication>(op.action) ||
                 std::holds_alternative<FiniteComputation>(op.action) ||
                 std::holds_alternative<OracleSourceQuery>(op.action))
        result.completedDependencies = false;
    }
    if (!bounds(types, result, depth, regionDepth))
      return nullptr;
    return &templates.emplace(&body, std::move(result)).first->second;
  }
};

BodySummaryCache::BodySummaryCache() : storage(std::make_unique<Storage>()) {}
BodySummaryCache::~BodySummaryCache() = default;
std::optional<Substitution>
bodySummaryFrame(Semantics &types, ArrayRef<Declaration> declarations,
                 const Declaration &callee, ArrayRef<Type> arguments,
                 const std::optional<Type> &module) {
  auto frame = types.substitution(callee, arguments);
  auto parent = callee.parent;
  if (module && parent && parent->index < declarations.size())
    frame.emplace("self:" + declarations[parent->index].qualifiedName, *module);
  unsigned depth = 0;
  while (parent) {
    if (++depth > types.work.limits.callDepth ||
        parent->index >= declarations.size()) {
      types.fail("source.limit", "summary lexical parent depth exceeded", {});
      return {};
    }
    if (!types.charge(1, {}))
      return {};
    const auto &owner = declarations[parent->index];
    if (owner.kind == Declaration::Kind::Module) {
      if (owner.implementation) {
        if (arguments.size() < owner.parameters.size()) {
          types.fail("source.scoped-summary", "summary module arguments differ",
                     callee.span);
          return {};
        }
        Type self(Type::Kind::Module, owner.qualifiedName);
        self.arguments.assign(arguments.begin(),
                              arguments.begin() + owner.parameters.size());
        frame.emplace("self:" + owner.implementation->domain, std::move(self));
      }
      break;
    }
    parent = owner.parent;
  }
  return frame;
}
std::optional<bool> BodySummaryCache::staticIndependent(
    Semantics &types, ArrayRef<Declaration> declarations, const Body &body,
    unsigned depth, unsigned *callHeight) {
  const auto *definition =
      storage->getTemplate(types, declarations, body, depth);
  if (!definition)
    return {};
  if (callHeight)
    *callHeight = definition->callHeight;
  return definition->completedDependencies;
}
void BodySummaryCache::observeDepth(unsigned depth) {
  for (auto &construction : storage->constructing)
    if (depth >= construction.depth)
      construction.height =
          std::max(construction.height, depth - construction.depth + 1);
}
bool BodySummaryCache::observeType(Semantics &types, const Type &type,
                                   Span span) {
  if (!types.chargeType(type, span))
    return false;
  uint64_t nodes = 0, height = 0;
  std::function<void(const Type &, unsigned)> visit = [&](const Type &term,
                                                          unsigned depth) {
    ++nodes;
    height = std::max(height, uint64_t(depth));
    for (const auto &argument : term.arguments)
      visit(argument, depth + 1);
  };
  visit(type, 1);
  for (auto &construction : storage->constructing) {
    auto &bounds = construction.requirements;
    bounds.typeDepth = std::max(bounds.typeDepth, height);
    bounds.typeNodes = std::max(bounds.typeNodes, nodes);
  }
  return true;
}
std::optional<BodySummaryApplication>
BodySummaryCache::apply(Semantics &types, ArrayRef<Declaration> declarations,
                        const Body &body, const Substitution &statics,
                        ArrayRef<Dependencies> inputs,
                        ArrayRef<ScopedSummaryBinding> environment,
                        unsigned depth, ArrayRef<Dependencies> domains,
                        LexicalStatics lexical, unsigned sourceDepth) {
  if (inputs.size() != body.inputs) {
    types.fail("source.scoped-summary", "summary input arity differs", {});
    return {};
  }
  const auto *definition =
      storage->getTemplate(types, declarations, body, depth);
  if (!definition)
    return {};
  auto observeRequirements = [&](const Storage::Template &requirements) {
    for (auto &active : storage->constructing) {
      auto &target = active.requirements;
      target.typeDepth = std::max(target.typeDepth, requirements.typeDepth);
      target.typeNodes = std::max(target.typeNodes, requirements.typeNodes);
      target.operations = std::max(target.operations, requirements.operations);
      target.calledRegionHeight =
          std::max({target.calledRegionHeight, requirements.regionHeight,
                    requirements.calledRegionHeight});
    }
  };
  observeRequirements(*definition);
  observeDepth(depth + definition->height - 1);

  InstanceContext key{&body, {}, {}, unsigned(domains.size())};
  if (!staticContext(types, statics, lexical, key.statics))
    return {};
  std::vector<Dependencies> actuals;
  auto slot = [&](const Dependencies &actual) -> std::optional<Dependencies> {
    if (!types.charge(actual.inputs.size() + 1, {}))
      return {};
    auto index = unsigned(actuals.size());
    actuals.push_back(actual);
    return Dependencies{{index}, false};
  };
  std::vector<Dependencies> formalInputs, formalDomains;
  for (const auto &input : inputs) {
    auto formal = slot(input);
    if (!formal)
      return {};
    formalInputs.push_back(std::move(*formal));
  }
  std::function<std::optional<ScopedSummaryBinding>(
      const ScopedSummaryBinding &, CallbackContext &, unsigned)>
      callback = [&](const ScopedSummaryBinding &binding, CallbackContext &key,
                     unsigned nesting) -> std::optional<ScopedSummaryBinding> {
    if (nesting > types.work.limits.callDepth) {
      types.fail("source.limit", "summary callback context depth exceeded", {});
      return {};
    }
    observeDepth(nesting);
    if (!chargeBinding(types, binding, nesting, {}))
      return {};
    key.computation = binding.computation;
    if (binding.owner) {
      if (binding.owner.get() != binding.computation) {
        types.fail("source.scoped-summary", "callback lifetime owner differs",
                   {});
        return {};
      }
      storage->callbackOwners.emplace(binding.computation, binding.owner);
    }
    key.mode = binding.signature.mode;
    key.mayStop = binding.signature.allowance.mayStop;
    key.opaque = binding.signature.allowance.opaque;
    for (const auto &input : binding.signature.inputs)
      key.signature.push_back(typeIdentity(input));
    key.signature.push_back(typeIdentity(binding.signature.result));
    for (const auto &type : key.signature)
      if (!types.charge(type.size() + 1, {}))
        return {};
    if (!staticContext(types, binding.statics, binding.lexical, key.statics))
      return {};
    key.captures = binding.captures.size();
    key.domains = binding.domains.size();
    ScopedSummaryBinding formal{
        binding.computation, binding.signature, binding.statics, {}, {}, {}};
    formal.owner = binding.owner;
    formal.lexical = binding.lexical;
    for (const auto &capture : binding.captures) {
      auto input = slot(capture);
      if (!input)
        return {};
      formal.captures.push_back(std::move(*input));
    }
    for (const auto &domain : binding.domains) {
      auto input = slot(domain);
      if (!input)
        return {};
      formal.domains.push_back(std::move(*input));
    }
    for (const auto &nested : binding.scoped) {
      CallbackContext context;
      auto selected = callback(nested, context, nesting + 1);
      if (!selected)
        return {};
      key.scoped.push_back(std::move(context));
      formal.scoped.push_back(std::move(*selected));
    }
    return formal;
  };
  std::vector<ScopedSummaryBinding> formalEnvironment;
  for (const auto &binding : environment) {
    CallbackContext context;
    auto formal = callback(binding, context, depth);
    if (!formal)
      return {};
    key.scoped.push_back(std::move(context));
    formalEnvironment.push_back(std::move(*formal));
  }
  // Every domain fact read by this product is a dependency slot. Descriptor,
  // cardinality and item-origin judgments belong to FiniteContracts; none are
  // cached here. In particular, equal domain counts never imply equal items.
  for (const auto &domain : domains) {
    auto formal = slot(domain);
    if (!formal)
      return {};
    formalDomains.push_back(std::move(*formal));
  }
  auto project =
      [&](const Dependencies &dependency) -> std::optional<Dependencies> {
    std::vector<Dependencies> selected;
    if (!types.charge(dependency.inputs.size() + 1, {}))
      return {};
    for (auto input : dependency.inputs) {
      if (input >= actuals.size()) {
        types.fail("source.scoped-summary", "invalid retained dependency slot",
                   {});
        return {};
      }
      if (!types.charge(actuals[input].inputs.size() + 1, {}))
        return {};
      selected.push_back(actuals[input]);
    }
    auto result = join(types, selected);
    if (result)
      result->parameterized |= dependency.parameterized;
    return result;
  };
  auto application = [&](const BodySummaryApplication &contract)
      -> std::optional<BodySummaryApplication> {
    BodySummaryApplication result;
    result.callHeight = contract.callHeight;
    for (auto products :
         {std::make_pair(&contract.results, &result.results),
          std::make_pair(&contract.formation, &result.formation)})
      for (const auto &dependency : *products.first) {
        auto actual = project(dependency);
        if (!actual)
          return {};
        result.parameterized |= actual->parameterized;
        products.second->push_back(std::move(*actual));
      }
    result.parameterized |= contract.parameterized;
    if (!normalizeFormation(types, result.formation))
      return {};
    return result;
  };
  // No second dependency product for ordinary Math: the completed Body is the
  // immutable template. Static arguments are keyed but need not be normalized
  // when this product cannot inspect them (e.g. an unused staged pow2 actual).
  if (definition->completedDependencies && environment.empty() &&
      domains.empty()) {
    BodySummaryApplication contract;
    contract.callHeight = definition->callHeight;
    for (auto result : body.results) {
      if (result.index >= body.values.size()) {
        types.fail("source.scoped-summary", "invalid retained body result", {});
        return {};
      }
      const auto &indices = body.values[result.index].components;
      if (!types.charge(indices.size() + 1, {}))
        return {};
      contract.results.push_back({indices, false});
    }
    for (const auto &indices : body.formationRequirements) {
      if (!types.charge(indices.size() + 1, {}))
        return {};
      contract.formation.push_back({indices, false});
    }
    return application(contract);
  }
  // Dependency inputs remain formal slots and cannot select an instance. The
  // lexical static and callback context can: the same Body may be entered with
  // a different implementation or with a different nested finite callback.
  uint64_t width = contextWidth(key.statics) + 1;
  for (const auto &context : key.scoped)
    width += contextWidth(context);
  if (!types.charge(width, {}))
    return {};
  for (const auto &active : storage->constructing) {
    if (!types.charge(active.context.body == &body ? width : 1, {}))
      return {};
    if (!(active.context < key) && !(key < active.context)) {
      types.fail("source.cycle", "recursive body summary application", {});
      return {};
    }
  }
  auto population = storage->instances.find(&body);
  uint64_t levels = 1;
  for (auto count = population == storage->instances.end()
                        ? 0
                        : population->second.size();
       count > 1; count >>= 1)
    ++levels;
  if (!types.charge((actuals.size() + width) * levels, {}))
    return {};
  if (population != storage->instances.end()) {
    auto found = population->second.find(key);
    if (found != population->second.end()) {
      if (!storage->bounds(types, found->second.requirements, depth))
        return {};
      observeDepth(depth + found->second.requirements.height - 1);
      observeRequirements(found->second.requirements);
      return application(found->second.contract);
    }
  }
  if (!types.charge(width, {}))
    return {};
  storage->constructing.push_back(
      {key, depth, definition->height, *definition});
  auto leave = llvm::scope_exit([&] { storage->constructing.pop_back(); });
  auto derived = summarizeBody(types, declarations, body, statics, formalInputs,
                               formalEnvironment, depth, formalDomains, this,
                               lexical, sourceDepth ? sourceDepth : depth);
  if (!derived)
    return {};
  BodySummaryApplication contract{std::move(derived->results),
                                  std::move(derived->formation),
                                  derived->parameterized, derived->callHeight};
  auto result = application(contract);
  if (!result)
    return {};
  auto height = storage->constructing.back().height;
  auto requirements = storage->constructing.back().requirements;
  requirements.height = height;
  storage->instances[&body].emplace(
      std::move(key), Storage::Instance{std::move(contract), requirements});
  return result;
}

std::optional<Dependencies>
summarizeDomainBinding(Semantics &types, const Body &body, unsigned index,
                       ArrayRef<Dependencies> values,
                       ArrayRef<Dependencies> environment, unsigned depth,
                       bool identityValues) {
  std::set<unsigned> seen;
  std::vector<unsigned> pending{index};
  std::vector<Dependencies> dependencies;
  if (depth > types.work.limits.callDepth) {
    types.fail("source.limit", "domain summary depth exceeded", {});
    return {};
  }
  while (!pending.empty()) {
    auto current = pending.back();
    pending.pop_back();
    if (!types.charge(1, {}))
      return {};
    if (!seen.insert(current).second)
      continue;
    if (current >= body.domainBindings.size()) {
      types.fail("source.finite-domain", "domain summary edge outside body",
                 {});
      return {};
    }
    const auto &binding = body.domainBindings[current];
    if (!types.charge(binding.operands.size() + binding.children.size() + 1,
                      binding.span))
      return {};
    if (binding.kind == DomainBinding::Kind::Parameter) {
      if (!binding.parameter) {
        types.fail("source.finite-domain", "domain formal has no parameter",
                   binding.span);
        return {};
      }
      if (*binding.parameter < environment.size()) {
        const auto &dependency = environment[*binding.parameter];
        if (!types.charge(dependency.inputs.size() + 1, binding.span))
          return {};
        dependencies.push_back(dependency);
      } else
        dependencies.push_back({{}, true});
    }
    for (auto operand : binding.operands) {
      if (operand.index >=
          (identityValues ? body.values.size() : values.size())) {
        types.fail("source.finite-domain",
                   "domain summary operand outside body", binding.span);
        return {};
      }
      if (identityValues)
        dependencies.push_back({{operand.index}, false});
      else {
        if (!types.charge(values[operand.index].inputs.size() + 1,
                          binding.span))
          return {};
        dependencies.push_back(values[operand.index]);
      }
    }
    pending.insert(pending.end(), binding.children.begin(),
                   binding.children.end());
  }
  return join(types, dependencies);
}
std::optional<ScopedSummaryBinding>
summarizeScopedBinding(Semantics &types, const Body &body, unsigned index,
                       const Substitution &statics,
                       ArrayRef<Dependencies> values,
                       ArrayRef<ScopedSummaryBinding> environment,
                       unsigned depth, bool identityValues,
                       ArrayRef<Dependencies> domains, LexicalStatics lexical) {
  if (index >= body.scopedBindings.size() ||
      depth > types.work.limits.callDepth) {
    types.fail("source.limit", "scoped summary depth exceeded", {});
    return {};
  }
  const auto &binding = body.scopedBindings[index];
  if (!types.charge(binding.captures.size() + binding.scopedCaptures.size() + 1,
                    binding.span))
    return {};
  if (binding.parameter) {
    if (*binding.parameter < environment.size()) {
      if (!chargeBinding(types, environment[*binding.parameter], depth,
                         binding.span))
        return {};
      return environment[*binding.parameter];
    }
    ScopedSummaryBinding unresolved{nullptr, binding.signature, statics, {}, {},
                                    {}};
    unresolved.lexical = lexical;
    return unresolved;
  }
  ScopedSummaryBinding result{
      binding.computation.get(), binding.signature, statics, {}, {}, {}};
  result.owner = binding.computation;
  result.lexical = lexical;
  for (auto capture : binding.captures) {
    if (capture.index >=
        (identityValues ? body.values.size() : values.size())) {
      types.fail("source.scoped-summary", "invalid capture mapping",
                 binding.span);
      return {};
    }
    if (identityValues)
      result.captures.push_back({{capture.index}, false});
    else {
      if (!types.charge(values[capture.index].inputs.size() + 1, binding.span))
        return {};
      result.captures.push_back(values[capture.index]);
    }
  }
  for (auto capture : binding.scopedCaptures) {
    auto nested = summarizeScopedBinding(types, body, capture, statics, values,
                                         environment, depth + 1, identityValues,
                                         domains, lexical);
    if (!nested)
      return {};
    result.scoped.push_back(std::move(*nested));
  }
  for (auto capture : binding.domainCaptures) {
    auto domain = summarizeDomainBinding(types, body, capture, values, domains,
                                         depth + 1, identityValues);
    if (!domain)
      return {};
    result.domains.push_back(std::move(*domain));
  }
  return result;
}
static std::optional<BodySummary>
summarizeBodyImpl(Semantics &types, ArrayRef<Declaration> declarations,
                  const Body &body, const Substitution &statics,
                  ArrayRef<Dependencies> inputs,
                  ArrayRef<ScopedSummaryBinding> environment, unsigned depth,
                  ArrayRef<Dependencies> domains, BodySummaryCache *retained,
                  LexicalStatics lexical, unsigned sourceDepth,
                  BodySummaryCache &definitions) {
  if (retained)
    retained->observeDepth(depth);
  if (depth > types.work.limits.callDepth || inputs.size() != body.inputs) {
    types.fail("source.limit", "body summary depth or input bound exceeded",
               {});
    return {};
  }
  LexicalStatics current = lexical;
  if (!statics.empty()) {
    for (const auto &[name, value] : statics)
      if (!types.charge(name.size() + 1, {}) || !types.chargeType(value, {}))
        return {};
    current = std::make_shared<BodySummaryStatics>(
        BodySummaryStatics{statics, lexical});
  }
  auto nestedSummary =
      [&](const Body &nested, const Substitution &frame,
          ArrayRef<Dependencies> arguments,
          ArrayRef<ScopedSummaryBinding> callbacks, unsigned nesting,
          ArrayRef<Dependencies> domainArguments = {},
          LexicalStatics parent = {},
          unsigned sourceEdge = 1) -> std::optional<BodySummaryApplication> {
    if (retained)
      return retained->apply(types, declarations, nested, frame, arguments,
                             callbacks, nesting, domainArguments, parent,
                             sourceDepth + sourceEdge);
    auto summary =
        summarizeBodyImpl(types, declarations, nested, frame, arguments,
                          callbacks, nesting, domainArguments, nullptr, parent,
                          sourceDepth + sourceEdge, definitions);
    if (!summary)
      return {};
    return BodySummaryApplication{std::move(summary->results),
                                  std::move(summary->formation),
                                  summary->parameterized, summary->callHeight};
  };
  BodySummary result;
  if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
    return {};
  result.values.resize(body.values.size());
  for (const auto &input : inputs)
    if (!types.charge(input.inputs.size() + 1, {}))
      return {};
  std::copy(inputs.begin(), inputs.end(), result.values.begin());
  auto gather = [&](ArrayRef<ValueId> operands)
      -> std::optional<std::vector<Dependencies>> {
    std::vector<Dependencies> values;
    for (auto operand : operands) {
      if (operand.index >= result.values.size()) {
        types.fail("source.scoped-summary", "invalid SSA operand", {});
        return {};
      }
      if (!types.charge(result.values[operand.index].inputs.size() + 1, {}))
        return {};
      values.push_back(result.values[operand.index]);
    }
    return values;
  };
  std::function<bool(const ScopedSummaryBinding &, std::vector<Dependencies> &)>
      captureDependencies = [&](const ScopedSummaryBinding &binding,
                                std::vector<Dependencies> &values) {
        for (const auto &capture : binding.captures)
          if (!types.charge(capture.inputs.size() + 1, {}))
            return false;
        values.insert(values.end(), binding.captures.begin(),
                      binding.captures.end());
        for (const auto &domain : binding.domains) {
          if (!types.charge(domain.inputs.size() + 1, {}))
            return false;
          values.push_back(domain);
        }
        if (!binding.computation)
          values.push_back({{}, true});
        for (const auto &nested : binding.scoped)
          if (!captureDependencies(nested, values))
            return false;
        return true;
      };
  auto absorb = [&](const BodySummaryApplication &nested, unsigned edge = 1) {
    for (const auto &formation : nested.formation)
      if (!types.charge(formation.inputs.size() + 1, {}))
        return false;
    result.formation.insert(result.formation.end(), nested.formation.begin(),
                            nested.formation.end());
    result.parameterized |= nested.parameterized;
    result.callHeight = std::max(result.callHeight, nested.callHeight + edge);
    return true;
  };
  for (const auto &op : body.operations) {
    if (!types.charge(1, op.span))
      return {};
    Dependencies dependencies;
    if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
      auto binding = summarizeScopedBinding(types, body, invoke->binding,
                                            statics, result.values, environment,
                                            depth, false, domains, lexical);
      auto operands = gather(invoke->operands);
      if (!binding || !operands)
        return {};
      if (binding->computation) {
        operands->insert(operands->end(), binding->captures.begin(),
                         binding->captures.end());
        auto nested = nestedSummary(
            *binding->computation->body, binding->statics, *operands,
            binding->scoped, depth + 1, binding->domains, binding->lexical);
        if (!nested)
          return {};
        if (!absorb(*nested))
          return {};
        auto combined = join(types, nested->results);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        auto combined = join(types, *operands);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
        dependencies.parameterized = true;
      }
    } else if (std::holds_alternative<FiniteApplication>(op.action) ||
               std::holds_alternative<FiniteComputation>(op.action)) {
      const auto *open = std::get_if<FiniteApplication>(&op.action);
      const auto *closed = std::get_if<FiniteComputation>(&op.action);
      std::optional<Dependencies> domain;
      if (open)
        domain = summarizeDomainBinding(types, body, open->domain,
                                        result.values, domains, depth);
      else {
        auto inputs = gather(closed->domainOperands);
        if (inputs)
          domain = join(types, *inputs);
      }
      const auto kind = open ? open->kind : closed->kind;
      auto operands = gather(open ? open->operands : closed->operands);
      if (!domain || !operands ||
          operands->size() != unsigned(kind == FiniteApplication::Kind::Fold))
        return {};
      // Item/cardinality facts have the domain's dependencies. Concrete
      // callbacks refine result dependencies; formation remains independent.
      Dependencies admission = *domain;
      result.formation.push_back(admission);
      auto invoke =
          [&](bool predicate,
              std::vector<Dependencies> inputs) -> std::optional<Dependencies> {
        std::optional<BodySummaryApplication> nested;
        if (closed) {
          const auto &selected = predicate ? *closed->predicate : closed->body;
          auto captures = gather(selected.captures);
          if (!captures || selected.helper.index >= declarations.size())
            return {};
          const auto &helper = declarations[selected.helper.index];
          if (!helper.body || !helper.parameters.empty() ||
              !helper.scopedInputs.empty() || !helper.domainInputs.empty())
            return {};
          inputs.insert(inputs.end(), captures->begin(), captures->end());
          nested = nestedSummary(*helper.body, {}, inputs, {}, depth + 1);
        } else {
          auto binding = summarizeScopedBinding(
              types, body, predicate ? *open->predicate : open->body, statics,
              result.values, environment, depth, false, domains, lexical);
          if (!binding)
            return {};
          if (!binding->computation) {
            auto result = join(types, inputs);
            if (result)
              result->parameterized = true;
            return result;
          }
          inputs.insert(inputs.end(), binding->captures.begin(),
                        binding->captures.end());
          nested = nestedSummary(*binding->computation->body, binding->statics,
                                 inputs, binding->scoped, depth + 1,
                                 binding->domains, binding->lexical);
        }
        if (!nested || !absorb(*nested))
          return {};
        return join(types, nested->results);
      };
      if (open ? bool(open->predicate) : bool(closed->predicate)) {
        auto predicate = invoke(true, {*domain});
        auto combined =
            predicate ? join(types, {admission, *predicate}) : std::nullopt;
        if (!combined)
          return {};
        admission = std::move(*combined);
      }
      if (kind == FiniteApplication::Kind::Collect) {
        auto item = invoke(false, {*domain});
        auto combined = item ? join(types, {admission, *item}) : std::nullopt;
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        dependencies = operands->front();
        for (;;) {
          auto step = invoke(false, {dependencies, *domain});
          auto next = step ? join(types, {dependencies, admission, *step})
                           : std::nullopt;
          if (!next)
            return {};
          if (dependencies.inputs == next->inputs &&
              dependencies.parameterized == next->parameterized)
            break;
          dependencies = std::move(*next);
        }
      }
    } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
      auto operands = gather(call->operands);
      if (!operands || call->callee.index >= declarations.size())
        return {};
      std::vector<Dependencies> selectedDomains;
      for (auto domain : call->domainArguments) {
        auto dependency = summarizeDomainBinding(types, body, domain,
                                                 result.values, domains, depth);
        if (!dependency)
          return {};
        selectedDomains.push_back(std::move(*dependency));
      }
      std::vector<ScopedSummaryBinding> selected;
      for (auto scoped : call->scopedArguments) {
        auto binding =
            summarizeScopedBinding(types, body, scoped, statics, result.values,
                                   environment, depth, false, domains, lexical);
        if (!binding)
          return {};
        selected.push_back(std::move(*binding));
      }
      const auto &known = declarations[call->callee.index];
      // Static-independent ordinary Math does not demand its unused static
      // expressions. All other paths select the recorded implementation before
      // looking up a retained instance. The source route remains on the call.
      bool ordinary = !call->module && known.kind == Declaration::Kind::Math &&
                      known.body && !known.body->parameterizedSummary &&
                      selected.empty() && selectedDomains.empty();
      unsigned ordinaryHeight = 1;
      if (ordinary) {
        auto independent = definitions.staticIndependent(
            types, declarations, *known.body, depth + 1, &ordinaryHeight);
        if (!independent)
          return {};
        ordinary = *independent;
      }
      if (ordinary) {
        std::optional<BodySummaryApplication> nested;
        if (retained)
          nested = nestedSummary(*known.body, {}, *operands, {}, depth + 1);
        else {
          // Independent reconstruction derives the current body's operations.
          // Its already checked ordinary callees keep their existing contract
          // boundary, rather than expanding a shared helper DAG into a tree.
          auto project =
              [&](ArrayRef<unsigned> indices) -> std::optional<Dependencies> {
            std::vector<Dependencies> values;
            for (auto index : indices) {
              if (index >= operands->size()) {
                types.fail("source.scoped-summary",
                           "invalid checked dependency", op.span);
                return {};
              }
              if (!types.charge((*operands)[index].inputs.size() + 1, op.span))
                return {};
              values.push_back((*operands)[index]);
            }
            return join(types, values);
          };
          nested.emplace();
          nested->callHeight = ordinaryHeight;
          for (auto value : known.body->results) {
            if (value.index >= known.body->values.size())
              return {};
            auto dependency =
                project(known.body->values[value.index].components);
            if (!dependency)
              return {};
            nested->results.push_back(std::move(*dependency));
          }
          for (const auto &requirement : known.body->formationRequirements) {
            auto dependency = project(requirement);
            if (!dependency)
              return {};
            nested->formation.push_back(std::move(*dependency));
          }
        }
        if (!nested || !absorb(*nested))
          return {};
        auto combined = join(types, nested->results);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        // Keep unused actuals in their defining frame. Composing pow2(N),
        // N := pow2(M) before M is concrete is outside the natural algebra.
        std::vector<Type> arguments = call->arguments;
        std::optional<Type> module = call->module;
        auto target = call->callee;
        // Direct calls already name their implementation in this declaration
        // inventory. An independent candidate witness may use Semantics over
        // the source type declarations, which do not contain generated helpers.
        if (module && known.parent &&
            known.parent->index < declarations.size() &&
            declarations[known.parent->index].kind ==
                Declaration::Kind::Interface) {
          module = substituteStatic(types, *module, current, op.span, retained);
          if (!module ||
              (retained && !retained->observeType(types, *module, op.span)))
            return {};
          const auto inherited =
              declarations[known.parent->index].parameters.size();
          // A member's own generic schema is an abstract call boundary, not
          // an unused static of a known body. Preserve its natural-formation
          // checks even while the implementing module remains symbolic.
          for (unsigned i = inherited; i < arguments.size(); ++i) {
            auto actual = substituteStatic(types, arguments[i], current,
                                           op.span, retained);
            if (!actual)
              return {};
            arguments[i] = std::move(*actual);
          }
          if (!module->symbolic) {
            for (unsigned i = 0; i < std::min(inherited, arguments.size());
                 ++i) {
              auto actual = substituteStatic(types, arguments[i], current,
                                             op.span, retained);
              if (!actual)
                return {};
              arguments[i] = std::move(*actual);
            }
          }
          auto dispatch =
              types.dispatch(module, target, arguments, op.span, sourceDepth);
          if (!dispatch || dispatch->declaration.index >= declarations.size())
            return {};
          target = dispatch->declaration;
          arguments = std::move(dispatch->arguments);
          if (retained)
            for (const auto &argument : arguments)
              if (!retained->observeType(types, argument, op.span))
                return {};
        }
        const auto &callee = declarations[target.index];
        if (callee.body && callee.kind == Declaration::Kind::Math) {
          auto frame =
              bodySummaryFrame(types, declarations, callee, arguments, module);
          if (!frame)
            return {};
          auto nested = nestedSummary(*callee.body, *frame, *operands, selected,
                                      depth + 1, selectedDomains, current);
          if (!nested || !absorb(*nested))
            return {};
          auto combined = join(types, nested->results);
          if (!combined)
            return {};
          dependencies = std::move(*combined);
        } else {
          operands->insert(operands->end(), selectedDomains.begin(),
                           selectedDomains.end());
          for (const auto &binding : selected)
            if (!captureDependencies(binding, *operands))
              return {};
          auto combined = join(types, *operands);
          if (!combined)
            return {};
          dependencies = std::move(*combined);
          dependencies.parameterized |=
              (!selected.empty() || !selectedDomains.empty()) &&
              callee.kind == Declaration::Kind::Math;
        }
      }
    } else if (const auto *query = std::get_if<OracleSourceQuery>(&op.action)) {
      auto operands = gather({ValueId{query->source}, query->position});
      auto combined = operands ? join(types, *operands) : std::nullopt;
      if (!combined || op.results.size() != 1)
        return {};
      dependencies = std::move(*combined);
      // These markers are separate from constructor/query input dependencies.
      // Checked helper summaries propagate only actual answer dependencies.
      dependencies.inputs.push_back(body.inputs + op.results.front().index);
      llvm::sort(dependencies.inputs);
    } else {
      std::vector<ValueId> operands;
      std::visit(
          [&](const auto &action) {
            using T = std::decay_t<decltype(action)>;
            if constexpr (std::is_same_v<T, MathValue> ||
                          std::is_same_v<T, BulkApplication> ||
                          std::is_same_v<T, ProtocolApplication> ||
                          std::is_same_v<T, OracleInstantiation> ||
                          std::is_same_v<T, HostInvocation> ||
                          std::is_same_v<T, Construct> ||
                          std::is_same_v<T, RoleAssembly> ||
                          std::is_same_v<T, LocalPrimitive> ||
                          std::is_same_v<T, Control>)
              operands = action.operands;
            else if constexpr (std::is_same_v<T, Projection> ||
                               std::is_same_v<T, Consume> ||
                               std::is_same_v<T, Restriction> ||
                               std::is_same_v<T, OracleContents> ||
                               std::is_same_v<T, OracleRows> ||
                               std::is_same_v<T, OracleForgetRows> ||
                               std::is_same_v<T, OracleSequenceLength>)
              operands = {action.input};
            else if constexpr (std::is_same_v<T, OracleSend>)
              operands = {action.data, action.rows};
            else if constexpr (std::is_same_v<T, OracleQuery>)
              operands = {action.handle, action.position};
            else if constexpr (std::is_same_v<T, OracleSequenceAppend>)
              operands = {action.prefix, action.element};
            else if constexpr (std::is_same_v<T, OracleSequenceAt>)
              operands = {action.input, action.position};
            else if constexpr (std::is_same_v<T, Require>)
              operands = {action.condition};
            else if constexpr (std::is_same_v<T, Exchange>)
              operands = {action.payload};
          },
          op.action);
      auto values = gather(operands);
      if (!values)
        return {};
      if (const auto *control = std::get_if<Control>(&op.action)) {
        std::vector<Dependencies> selectedDomains;
        for (auto domain : control->domainArguments) {
          auto dependency = summarizeDomainBinding(
              types, body, domain, result.values, domains, depth);
          if (!dependency)
            return {};
          selectedDomains.push_back(*dependency);
        }

        // Formation checks include dormant arms. Payloads depend on the
        // selector; capture associations remain ordered and exact.
        if (body.mode == Body::Mode::Math &&
            control->kind != Control::Kind::For) {
          const unsigned captures = control->operands.size() - 1;
          for (const auto &region : control->regions) {
            if (region->inputs < captures)
              return {};
            std::vector<Dependencies> nestedInputs(
                region->inputs - captures,
                result.values[control->operands.front().index]);
            for (auto capture : ArrayRef(control->operands).drop_front())
              nestedInputs.push_back(result.values[capture.index]);
            auto nested =
                nestedSummary(*region, statics, nestedInputs, environment,
                              depth + 1, selectedDomains, lexical, 0);
            if (!nested || !absorb(*nested, 0))
              return {};
          }
        }
        for (auto domain : control->domainArguments) {
          auto dependency = summarizeDomainBinding(
              types, body, domain, result.values, domains, depth);
          if (!dependency)
            return {};
          values->push_back(std::move(*dependency));
        }
        for (const auto &binding : environment)
          if (!captureDependencies(binding, *values))
            return {};
        if (environment.empty())
          for (const auto &region : control->regions)
            if (region->parameterizedSummary)
              values->push_back({{}, true});
      }
      auto combined = join(types, *values);
      if (!combined)
        return {};
      dependencies = std::move(*combined);
    }
    result.parameterized |= dependencies.parameterized;
    if (body.mode == Body::Mode::Math)
      result.formation.push_back(dependencies);
    for (auto value : op.results) {
      if (value.index >= result.values.size()) {
        types.fail("source.scoped-summary", "invalid result mapping", op.span);
        return {};
      }
      result.values[value.index] = dependencies;
    }
  }
  for (auto value : body.results) {
    if (value.index >= result.values.size()) {
      types.fail("source.scoped-summary", "invalid body result", {});
      return {};
    }
    if (!types.charge(result.values[value.index].inputs.size() + 1, {}))
      return {};
    result.results.push_back(result.values[value.index]);
  }
  // Formation is a set of obligations, not an expansion trace. Deduplication
  // preserves dead-intermediate checks without exponential summary growth in
  // a shared call DAG. Operation coverage is checked separately.
  if (!normalizeFormation(types, result.formation))
    return {};
  for (const auto &requirement : result.formation)
    result.parameterized |= requirement.parameterized;
  return result;
}
std::optional<BodySummary>
summarizeBody(Semantics &types, ArrayRef<Declaration> declarations,
              const Body &body, const Substitution &statics,
              ArrayRef<Dependencies> inputs,
              ArrayRef<ScopedSummaryBinding> environment, unsigned depth,
              ArrayRef<Dependencies> domains, BodySummaryCache *retained,
              LexicalStatics lexical, unsigned sourceDepth) {
  // Independent reconstruction shares only a private structural index. It
  // derives the current body's values/formation from operations and cannot
  // read or populate the producer's retained application contracts.
  BodySummaryCache independentDefinitions;
  return summarizeBodyImpl(types, declarations, body, statics, inputs,
                           environment, depth, domains, retained, lexical,
                           sourceDepth,
                           retained ? *retained : independentDefinitions);
}
} // namespace zkc::language::detail
