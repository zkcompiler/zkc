#include "Checker.h"
#include "ConstructionWitness.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/ScopeExit.h"
#include <map>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
namespace {
// These frames refer to the actual checked body, not to a source selector
// spelling. Selected arms have separate lexical site namespaces.
struct ConstructionFrame {
  enum class Kind { Application, Repeat, Arm } kind;
  const Operation *operation;
  unsigned arm = 0;
  bool operator==(const ConstructionFrame &other) const {
    return kind == other.kind && operation == other.operation &&
           arm == other.arm;
  }
};
struct ConstructionSite {
  ConstructionRule::Kind kind;
  std::vector<std::string> path;
  bool labelled;
  Type payload;
  std::optional<Natural> bound;
  bool proofMessage = false;
  bool indexBlock = false;
  std::vector<ConstructionFrame> ancestry;
};
struct ConstructionCall {
  std::vector<std::string> path;
  bool labelled;
  DeclarationId target;
  std::vector<Type> arguments;
  std::vector<unsigned> services, roles;
  std::vector<ConstructionFrame> ancestry;
};
struct ConstructionOccurrence {
  std::optional<unsigned> index;
  bool ambiguous = false;
  void add(unsigned occurrence) {
    ambiguous |= index.has_value();
    index = occurrence;
  }
};
struct ConstructionPath {
  ConstructionOccurrence message, query, call;
  std::optional<unsigned> application;
  bool writtenApplication = false;
  // These maps have at most the seven existing construction rule kinds.
  std::map<ConstructionRule::Kind, unsigned> rules;
  std::set<ConstructionRule::Kind> written;
  std::optional<Type> chunks;
};
bool within(ArrayRef<ConstructionFrame> path,
            ArrayRef<ConstructionFrame> parent) {
  return path.size() >= parent.size() &&
         equal(path.take_front(parent.size()), parent);
}
} // namespace

bool Checker::constructions() {
  if (constructionsReady)
    return true;
  std::vector<unsigned> state(output.declarations.size());
  std::vector<unsigned> height(output.declarations.size());
  std::function<bool(DeclarationId, unsigned)> check;
  check = [&](DeclarationId id, unsigned depth) {
    if (!signature(id))
      return false;
    auto &decl = output.declarations[id.index];
    if (decl.target && !body(*decl.target, 1))
      return false;
    if (depth > work.limits.typeDepth ||
        height[id.index] > work.limits.typeDepth - depth)
      return types.fail("source.limit", "construction inheritance depth",
                        decl.span);
    if (state[id.index] == 2)
      return true;
    if (state[id.index] == 1)
      return types.fail("source.construction", "cyclic construction selection",
                        decl.span);
    state[id.index] = 1;
    auto freezeContract = scope_exit([&] { inferredContracts.erase(&decl); });
    const auto &syntax = *sources[id.index]->construction;
    auto retainSource = [&] {
      if (!types.charge(1, decl.span))
        return false;
      output.constructionSources.emplace(
          id.index,
          std::make_shared<const ConstructionSource>(ConstructionSource{
              syntax.parent, syntax.provider, syntax.codec}));
      return true;
    };
    const auto &target = output.declarations[decl.target->index];
    // Protocol bodies have now completed their inferred contracts. Signature
    // formation alone cannot validate a construction's target application.
    if (!types.checkArguments(target, decl.staticArguments, decl.span, &decl))
      return false;
    auto substitution = types.substitution(target, decl.staticArguments);
    for (const auto &bound : target.bounds)
      if (!types.assumptions(decl, bound, substitution, decl.span))
        return false;
    ConstructionDefinition result;
    result.base = syntax.base;
    if (syntax.parent) {
      SaveAndRestore site(referenceSite, syntax.parent->referenceSite);
      auto parent = resolve(decl, syntax.parent->name, syntax.parent->span);
      if (!parent || !signature(*parent))
        return false;
      const auto &base = output.declarations[parent->index];
      if (base.kind != Declaration::Kind::Construction || !base.target ||
          base.target->index != decl.target->index)
        return types.fail("source.construction",
                          "base must target the same protocol",
                          syntax.parent->span);
      if (!check(*parent, depth + 1))
        return false;
      height[id.index] = std::max(height[id.index], 1 + height[parent->index]);
      auto arguments =
          this->arguments(decl, base, syntax.parent->arguments,
                          syntax.parent->span, syntax.parent->labels);
      if (!arguments)
        return false;
      auto bindings = types.substitution(base, *arguments);
      for (auto [expected, actual] :
           zip(base.staticArguments, decl.staticArguments)) {
        auto selected =
            types.substitute(expected, bindings, syntax.parent->span);
        if (!selected || *selected != actual)
          return types.diagnostic
                     ? false
                     : types.fail("source.construction",
                                  "base specialization differs from protocol",
                                  syntax.parent->span);
      }
      if (!types.chargeConstruction(*base.construction, syntax.parent->span))
        return false;
      result = *base.construction;
      result.base = ConstructionDefinition::Base::Named;
      result.parent = *parent;
      result.arguments = std::move(*arguments);
      auto replace = [&](Type &value) {
        auto selected = types.substitute(value, bindings, decl.span);
        if (!selected)
          return false;
        value = std::move(*selected);
        return true;
      };
      for (auto *value : {&result.provider, &result.state})
        if (*value && !replace(**value))
          return false;
      if (result.initializer && result.initializer->module &&
          !replace(*result.initializer->module))
        return false;
      for (auto &argument : result.initializerArguments)
        if (!replace(argument))
          return false;
      for (auto &application : result.applications)
        for (auto &argument : application.arguments)
          if (!replace(argument))
            return false;
      for (auto &rule : result.rules) {
        for (auto &argument : rule.arguments)
          if (!replace(argument))
            return false;
        for (auto *value : {&rule.payload, &rule.chunks})
          if (*value && !replace(**value))
            return false;
      }
      if (result.codec) {
        if (sources[id.index]->proofFormat)
          return types.fail("source.construction",
                            "an inherited record format cannot be replaced",
                            decl.span);
        auto &codec = *result.codec;
        if (!replace(codec.provider) || !replace(codec.record))
          return false;
        for (auto *method : {&codec.initialize, &codec.write, &codec.finish}) {
          if (method->target.module && !replace(*method->target.module))
            return false;
          for (auto &argument : method->arguments)
            if (!replace(argument))
              return false;
        }
      }
      if (!decl.proofFormat)
        decl.proofFormat = base.proofFormat;
      if (syntax.provider || !syntax.services.empty())
        return types.fail(
            "source.construction",
            "a derived construction inherits its provider and authority",
            decl.span);
    }
    if (syntax.base == ConstructionDefinition::Base::Authored ||
        (syntax.base == ConstructionDefinition::Base::Named &&
         result.root == ConstructionDefinition::Root::None)) {
      if (syntax.provider || !syntax.services.empty() || syntax.codec ||
          !syntax.rules.empty() || !syntax.applications.empty())
        return types.fail("source.construction",
                          "authored base accepts only a proof format",
                          decl.span);
      decl.construction = std::move(result);
      if (!retainSource())
        return false;
      state[id.index] = 2;
      return true;
    }
    if (syntax.base == ConstructionDefinition::Base::Native) {
      if (syntax.provider)
        return types.fail("source.construction",
                          "native base fixes its transcript provider",
                          decl.span);
      result.root = ConstructionDefinition::Root::Host;
      result.suite = syntax.suite;
      result.nativeBase = true;
      if (protocol::nativeChallengeField(result.suite).empty())
        return types.fail("source.construction",
                          "unknown native transcript suite", decl.span);
      result.provider = domainType("Transcript", result.suite);
      auto nativeState = builtinType("transcript", {*result.provider});
      if (!nativeState)
        return types.accept(nativeState.takeError(), decl.span);
      result.state = std::move(*nativeState);
    }
    for (const auto &service : syntax.services) {
      for (const auto &port : target.services)
        if (!types.charge(port.name.size() + service.name.size() + 1,
                          service.span))
          return false;
      auto found = llvm::find_if(target.services, [&](const ServicePort &port) {
        return port.name == service.name;
      });
      if (found == target.services.end())
        return types.fail("source.construction",
                          "replacement names no managed protocol port",
                          service.span);
      auto port = unsigned(found - target.services.begin());
      if (!types.charge(result.services.size() + 1, service.span))
        return false;
      if (is_contained(result.services, port))
        return types.fail("source.construction",
                          "duplicate replacement authority", service.span);
      result.services.push_back(port);
    }
    llvm::sort(result.services);
    if (syntax.provider) {
      SaveAndRestore site(referenceSite, syntax.provider->referenceSite);
      auto provider = type(decl, *syntax.provider);
      if (!provider)
        return false;
      if (domainSort(*provider) == "Transcript" && provider->symbolic)
        return types.fail(
            "source.construction",
            "managed transcript provider must select a closed suite",
            syntax.provider->span);
      if (domainSort(*provider) == "Transcript" && !provider->symbolic) {
        result.provider = *provider;
        result.suite = provider->domain;
        if (protocol::nativeChallengeField(result.suite).empty())
          return types.fail("source.construction",
                            "unknown managed transcript suite", decl.span);
        auto nativeState = builtinType("transcript", {*provider});
        if (!nativeState)
          return types.accept(nativeState.takeError(), decl.span);
        result.state = std::move(*nativeState);
        result.root = ConstructionDefinition::Root::Host;
      } else {
        if (provider->kind != Type::Kind::Module)
          return types.fail("source.construction",
                            "transcript requires a module provider",
                            syntax.provider->span);
        auto state = constructionMember(
            decl, *provider, "State", syntax.provider->span,
            typeReferences.count(syntax.provider->referenceSite)
                ? std::optional(
                      typeReferences.at(syntax.provider->referenceSite))
                : std::nullopt);
        if (!state)
          return false;
        auto stateType = types.associated(*provider, state->declaration,
                                          syntax.provider->span);
        if (!stateType)
          return false;
        auto permissions = types.permissions(*stateType, decl.span, &decl);
        if (!permissions)
          return false;
        if (!permissions->copy || !permissions->drop)
          return types.fail(
              "source.construction",
              "source-created transcript state requires Copy and Drop",
              decl.span);
        auto member = constructionMember(
            decl, *provider, "initialize", decl.span,
            typeReferences.count(syntax.provider->referenceSite)
                ? std::optional(
                      typeReferences.at(syntax.provider->referenceSite))
                : std::nullopt);
        if (!member)
          return false;
        const auto &factory = output.declarations[member->declaration.index];
        auto bindings =
            types.boundMemberSubstitution(factory, *provider, decl.span);
        if (!bindings)
          return false;
        if (factory.kind != Declaration::Kind::Local ||
            !factory.inputOrder.empty() || factory.outputs.size() != 1 ||
            factory.parameters.size() !=
                output.declarations[factory.parent->index].parameters.size())
          return types.fail(
              "source.construction",
              "initialize must be a Local factory with no call arguments",
              decl.span);
        auto output = types.substitute(factory.outputs.front().type, *bindings,
                                       decl.span);
        if (!output || *output != *stateType)
          return types.diagnostic
                     ? false
                     : types.fail("source.construction",
                                  "initialize must return provider State",
                                  decl.span);
        result.provider = std::move(*provider);
        result.root = ConstructionDefinition::Root::Local;
        result.state = std::move(*stateType);
        result.initializer = *member;
        for (const auto &parameter : factory.parameters)
          result.initializerArguments.push_back(bindings->at(parameter.atom));
      }
    }
    if (result.services.empty() || (!result.provider && result.suite.empty()))
      return types.fail("source.construction",
                        "construction requires a transcript provider and "
                        "replacement authority",
                        decl.span);
    auto verifier = target.services[result.services.front()].owner;
    if (!types.charge(result.services.size(), decl.span))
      return false;
    if (any_of(result.services, [&](unsigned port) {
          return target.services[port].owner != verifier;
        }))
      return types.fail("source.construction",
                        "replacement authorities require one owner", decl.span);
    if (!constructionCodec(decl, syntax, result, substitution))
      return false;
    if (result.codec && target.roles.size() != 2)
      return types.fail("source.construction",
                        "record codecs require two participants", decl.span);

    if (!types.charge(target.services.size() + result.services.size(),
                      decl.span))
      return false;
    std::vector<bool> replaced(target.services.size());
    for (auto port : result.services)
      replaced[port] = true;
    std::vector<ConstructionSite> sites;
    std::vector<ConstructionCall> calls;
    std::function<bool(const Body &, const Substitution &, ArrayRef<unsigned>,
                       ArrayRef<unsigned>, ArrayRef<std::string>, bool,
                       ArrayRef<ConstructionFrame>, unsigned)>
        collect;
    collect = [&](const Body &body, const Substitution &bindings,
                  ArrayRef<unsigned> services, ArrayRef<unsigned> roles,
                  ArrayRef<std::string> prefix, bool labelled,
                  ArrayRef<ConstructionFrame> ancestry, unsigned depth) {
      if (depth > work.limits.callDepth)
        return types.fail("source.limit", "construction occurrence depth",
                          decl.span);
      for (const auto &operation : body.operations) {
        if (!types.charge(ancestry.size() + 1, operation.span))
          return false;
        for (const auto &part : prefix)
          if (!types.charge(part.size() + 1, operation.span))
            return false;
        std::vector<std::string> path;
        path.reserve(prefix.size() + 1);
        path.assign(prefix.begin(), prefix.end());
        if (operation.site) {
          if (!types.charge(operation.site->size() + 1, operation.span))
            return false;
          path.push_back(*operation.site);
        }
        auto validPath = labelled && operation.site.has_value();
        std::vector<ConstructionFrame> nested;
        nested.reserve(ancestry.size() + 1);
        nested.assign(ancestry.begin(), ancestry.end());
        if (auto repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
          if (!types.charge(repeat->services.size() + 1, operation.span))
            return false;
          std::vector<unsigned> captured;
          captured.reserve(repeat->services.size());
          for (auto service : repeat->services)
            captured.push_back(services[service.index]);
          nested.push_back({ConstructionFrame::Kind::Repeat, &operation});
          if (!collect(*repeat->region, bindings, captured, roles, prefix,
                       labelled, nested, depth + 1))
            return false;
        } else if (auto control = std::get_if<Control>(&operation.action)) {
          if (!types.charge(control->services.size(), operation.span))
            return false;
          std::vector<unsigned> captured;
          captured.reserve(control->services.size());
          for (auto service : control->services)
            captured.push_back(services[service.index]);
          nested.push_back({ConstructionFrame::Kind::Arm, &operation});
          // Control roles are a roster in the enclosing declaration's role
          // coordinates. Only the managed-service slots are compacted in an
          // arm; static substitutions and the call's role mapping stay intact.
          for (auto [arm, region] : enumerate(control->regions)) {
            if (!types.charge(nested.size(), operation.span))
              return false;
            nested.back().arm = arm;
            if (!collect(*region, bindings, captured, roles, prefix, labelled,
                         nested, depth + 1))
              return false;
          }
        } else if (auto call =
                       std::get_if<ProtocolApplication>(&operation.action)) {
          if (!types.charge(call->arguments.size() + call->services.size() +
                                call->roles.size() + 1,
                            operation.span))
            return false;
          std::vector<Type> actual;
          actual.reserve(call->arguments.size());
          for (const auto &argument : call->arguments) {
            auto value = types.substitute(argument, bindings, operation.span);
            if (!value)
              return false;
            actual.push_back(std::move(*value));
          }
          std::optional<Type> module;
          if (operation.binding && operation.binding->target.module) {
            module = types.substitute(*operation.binding->target.module,
                                      bindings, operation.span);
            if (!module)
              return false;
          }
          auto selected =
              types.dispatch(module, call->callee, actual, operation.span);
          if (!selected || !this->body(selected->declaration, 1))
            return false;
          const auto &callee = output.declarations[selected->declaration.index];
          if (!callee.body)
            return types.fail("source.construction",
                              "construction site traversal needs a selected "
                              "protocol implementation",
                              operation.span);
          actual = std::move(selected->arguments);
          std::vector<unsigned> captured;
          captured.reserve(call->services.size());
          for (auto service : call->services)
            captured.push_back(services[service.index]);
          std::vector<unsigned> mappedRoles;
          mappedRoles.reserve(call->roles.size());
          for (auto role : call->roles)
            mappedRoles.push_back(roles[role]);
          nested.push_back({ConstructionFrame::Kind::Application, &operation});
          // Retention copies all maps, types, path labels and typed frames.
          // Keep the local maps alive while recursive collection grows calls.
          if (!types.charge(captured.size() + mappedRoles.size() +
                                nested.size() + path.size() + 1,
                            operation.span))
            return false;
          for (const auto &part : path)
            if (!types.charge(part.size() + 1, operation.span))
              return false;
          for (const auto &argument : actual)
            if (!types.chargeType(argument, operation.span))
              return false;
          calls.push_back({path, validPath, callee.id, actual, captured,
                           mappedRoles, nested});
          if (!types.charge(actual.size(), operation.span))
            return false;
          for (const auto &argument : actual)
            if (!types.chargeType(argument, operation.span))
              return false;
          // Each expanded call rebuilds a string-keyed red-black tree. Charge
          // the formal key copies and a conservative insertion comparison
          // depth before constructing it. A comparison reads at most this
          // key's bytes, even when the other key has a longer common prefix.
          for (size_t i = 0; i < actual.size() && i < callee.parameters.size();
               ++i) {
            const auto &key = callee.parameters[i].atom;
            if (!types.charge(key.size(), operation.span))
              return false;
            unsigned comparisons = 4;
            for (auto size = i; size; size >>= 1)
              comparisons += 4;
            // Separate byte and comparison debits avoid multiplying a source
            // width by a tree depth (or adding to that width) before charging.
            for (unsigned comparison = 0; comparison < comparisons;
                 ++comparison)
              if (!types.charge(key.size(), operation.span) ||
                  !types.charge(1, operation.span))
                return false;
          }
          if (!collect(*callee.body, types.substitution(callee, actual),
                       captured, mappedRoles, path, validPath, nested,
                       depth + 1))
            return false;
        } else if (auto message = std::get_if<Exchange>(&operation.action)) {
          auto payload =
              types.substitute(body.values[message->payload.index].type,
                               bindings, operation.span);
          if (!payload)
            return false;
          sites.push_back({ConstructionRule::Kind::Message,
                           std::move(path),
                           validPath,
                           std::move(*payload),
                           {},
                           roles[message->receiver] == verifier &&
                               roles[message->sender] != verifier,
                           false,
                           std::move(nested)});
        } else if (auto query = std::get_if<ServiceQuery>(&operation.action)) {
          if (!types.charge(1, operation.span))
            return false;
          if (!replaced[services[query->service.index]])
            continue;
          auto payload = types.substitute(
              body.values[operation.results.front().index].type, bindings,
              operation.span);
          if (!payload)
            return false;
          sites.push_back({ConstructionRule::Kind::Query, std::move(path),
                           validPath, std::move(*payload), query->bound, false,
                           query->count.has_value(), std::move(nested)});
        }
      }
      return true;
    };
    if (!types.charge(target.services.size() + target.roles.size(), decl.span))
      return false;
    std::vector<unsigned> services(target.services.size());
    std::vector<unsigned> roles(target.roles.size());
    std::iota(services.begin(), services.end(), 0);
    std::iota(roles.begin(), roles.end(), 0);
    if (!collect(*target.body, substitution, services, roles, {}, true, {}, 1))
      return false;
    // Intern complete paths from the immutable checked occurrences. Charge a
    // red-black tree's worst-case comparison depth and all compared bytes,
    // including component boundaries and the retained key copy. Rule-kind
    // tables below have a fixed maximum width of seven.
    std::map<std::vector<std::string>, ConstructionPath> paths;
    auto indexedPath = [&](ArrayRef<std::string> path,
                           Span span) -> ConstructionPath * {
      uint64_t width = 1;
      for (const auto &part : path)
        width += part.size() + 1;
      if (!types.charge(8 * width + 32, span))
        return nullptr;
      for (auto size = paths.size(); size; size >>= 1)
        if (!types.charge(4 * width, span))
          return nullptr;
      return &paths[std::vector<std::string>(path.begin(), path.end())];
    };
    std::vector<ConstructionPath *> sitePaths;
    if (!types.charge(sites.size() + calls.size(), decl.span))
      return false;
    sitePaths.reserve(sites.size());
    for (auto [index, site] : enumerate(sites)) {
      auto *path = indexedPath(site.path, decl.span);
      if (!path)
        return false;
      sitePaths.push_back(path);
      if (site.labelled)
        (site.kind == ConstructionRule::Kind::Message ? path->message
                                                      : path->query)
            .add(index);
    }
    for (auto [index, call] : enumerate(calls)) {
      auto *path = indexedPath(call.path, decl.span);
      if (!path)
        return false;
      if (call.labelled)
        path->call.add(index);
    }
    for (auto [index, rule] : enumerate(result.rules)) {
      auto *path = indexedPath(rule.path, rule.span);
      if (!path)
        return false;
      path->rules[rule.kind] = index;
      if (rule.chunks) {
        if (!types.chargeType(*rule.chunks, rule.span))
          return false;
        path->chunks = *rule.chunks;
      }
    }
    for (auto [index, application] : enumerate(result.applications)) {
      auto *path = indexedPath(application.path, application.span);
      if (!path)
        return false;
      path->application = index;
    }
    for (const auto &source : syntax.applications) {
      ConstructionApplication application;
      application.span = source.span;
      for (const auto &part : source.path) {
        if (!types.charge(part.name.size() + 1, source.span))
          return false;
        application.path.push_back(part.name);
      }
      auto *path = indexedPath(application.path, source.span);
      if (!path)
        return false;
      if (path->writtenApplication)
        return types.fail("source.construction",
                          "duplicate construction application", source.span);
      path->writtenApplication = true;
      SaveAndRestore site(referenceSite, source.construction.referenceSite);
      auto selected = resolve(decl, source.construction.name, source.span);
      if (!selected || !signature(*selected))
        return false;
      const auto &child = output.declarations[selected->index];
      if (child.kind != Declaration::Kind::Construction || !child.target)
        return types.fail("source.construction",
                          "apply requires a construction", source.span);
      if (!check(*selected, depth + 1))
        return false;
      height[id.index] =
          std::max(height[id.index], 1 + height[selected->index]);
      auto arguments =
          this->arguments(decl, child, source.construction.arguments,
                          source.span, source.construction.labels);
      if (!arguments)
        return false;
      application.construction = *selected;
      application.arguments = std::move(*arguments);
      if (!path->application) {
        path->application = result.applications.size();
        result.applications.push_back(std::move(application));
      } else
        result.applications[*path->application] = std::move(application);
    }
    std::vector<const ConstructionCall *> delegatedCalls;
    for (const auto &application : result.applications) {
      auto *path = indexedPath(application.path, application.span);
      if (!path)
        return false;
      if (path->call.ambiguous)
        return types.fail("source.construction",
                          "construction application names multiple occurrences",
                          application.span);
      const auto &child = output.declarations[application.construction.index];
      if (!path->call.index ||
          calls[*path->call.index].target.index != child.target->index)
        return types.fail("source.construction",
                          "child does not target the selected protocol call",
                          application.span);
      const auto *call = &calls[*path->call.index];
      for (const auto *other : delegatedCalls) {
        if (!types.charge(call->ancestry.size() + other->ancestry.size() + 1,
                          application.span))
          return false;
        if (within(call->ancestry, other->ancestry) ||
            within(other->ancestry, call->ancestry))
          return types.fail("source.construction",
                            "construction applications overlap",
                            application.span);
      }
      auto bindings = types.substitution(child, application.arguments);
      if (child.staticArguments.size() != call->arguments.size())
        return types.fail("source.construction",
                          "child specialization differs from the protocol call",
                          application.span);
      for (auto [formal, actual] :
           zip(child.staticArguments, call->arguments)) {
        auto closed = types.substitute(formal, bindings, application.span);
        if (!closed)
          return false;
        if (*closed != actual)
          return types.fail(
              "source.construction",
              "child specialization differs from the protocol call",
              application.span);
      }
      const auto &childPlan = *child.construction;
      if (child.proofFormat || childPlan.codec || childPlan.nativeBase ||
          childPlan.root == ConstructionDefinition::Root::None)
        return types.fail("source.construction",
                          "child requires a root-only format or construction",
                          application.span);
      for (auto [childType, parentType] :
           {std::make_pair(&childPlan.provider, &result.provider),
            std::make_pair(&childPlan.state, &result.state)}) {
        if (!*childType || !*parentType)
          return types.fail("source.construction",
                            "child has no transcript state", application.span);
        auto closed = types.substitute(**childType, bindings, application.span);
        if (!closed)
          return false;
        if (*closed != **parentType)
          return types.fail("source.construction",
                            "child transcript provider or state differs",
                            application.span);
      }
      const auto &childTarget = output.declarations[child.target->index];
      if (target.roles.size() != 2 || childPlan.root != result.root ||
          childPlan.suite != result.suite || childPlan.services.empty() ||
          call->roles.size() != 2 ||
          call->roles[childTarget.services[childPlan.services.front()].owner] !=
              verifier)
        return types.fail(
            "source.construction",
            "child transcript authority or participant mapping differs",
            application.span);
      if (!types.charge(childTarget.services.size() +
                            childPlan.services.size() + call->services.size() +
                            1,
                        application.span))
        return false;
      std::vector<bool> childReplaced(childTarget.services.size());
      for (auto port : childPlan.services)
        childReplaced[port] = true;
      for (auto [port, mapped] : enumerate(call->services))
        if (replaced[mapped] != childReplaced[port])
          return types.fail("source.construction",
                            "child replacement must select exactly the ports "
                            "mapped to replaced authorities",
                            application.span);
      delegatedCalls.push_back(call);
    }
    auto delegatedOccurrence =
        [&](const ConstructionSite &site) -> std::optional<bool> {
      for (const auto *call : delegatedCalls) {
        if (!types.charge(site.ancestry.size() + call->ancestry.size() + 1,
                          decl.span))
          return {};
        if (within(site.ancestry, call->ancestry))
          return true;
      }
      return false;
    };
    auto bytes = builtinType("bytes", {});
    if (!bytes)
      return types.accept(bytes.takeError(), decl.span);
    auto validChunks = [&](auto &&self, const Type &value,
                           unsigned depth) -> bool {
      if (!types.charge(1, decl.span) || depth > work.limits.typeDepth)
        return false;
      return value == *bytes ||
             (value.kind == Type::Kind::Tuple && !value.arguments.empty() &&
              all_of(value.arguments, [&](const Type &part) {
                return self(self, part, depth + 1);
              }));
    };
    for (const auto &source : syntax.rules) {
      if (source.kind != ConstructionRule::Kind::Decode)
        continue;
      if (!result.codec || source.parameters.size() != 1)
        return types.fail("source.construction",
                          "decode requires a record format and one byte input",
                          source.span);
      auto &handler = output.declarations[decl.members[source.member].index];
      if (!signature(handler.id))
        return false;
      const auto &annotation = sources[handler.id.index]->inputs.front().type;
      std::optional<Type> selected = *bytes;
      if (!annotation.name.empty() || annotation.kind != SyntaxType::Kind::Name)
        selected = type(handler, annotation);
      if (!selected)
        return false;
      if (!validChunks(validChunks, *selected, 1))
        return types.diagnostic ? false
                                : types.fail("source.construction",
                                             "decode input must be Bytes or a "
                                             "nonempty product of Bytes",
                                             source.span);
      std::vector<std::string> path;
      for (const auto &part : source.path) {
        if (!types.charge(part.name.size() + 1, source.span))
          return false;
        path.push_back(part.name);
      }
      auto *indexed = indexedPath(path, source.span);
      if (!indexed)
        return false;
      if (indexed->chunks && *indexed->chunks != *selected)
        return types.fail("source.construction",
                          "an inherited wire shape cannot be replaced",
                          source.span);
      indexed->chunks = std::move(*selected);
    }
    auto ranges = [&](auto &&self, const Type &value) -> Type {
      Type result(Type::Kind::Tuple);
      if (value == *bytes)
        result.arguments = {Type(Type::Kind::Index), Type(Type::Kind::Index)};
      else
        for (const auto &part : value.arguments)
          result.arguments.push_back(self(self, part));
      return result;
    };
    for (const auto &source : syntax.rules) {
      ConstructionRule rule{source.kind, {}, decl.members[source.member],
                            {},          {}, source.span,
                            {},          {}};
      for (const auto &part : source.path) {
        if (!types.charge(part.name.size() + 1, source.span))
          return false;
        rule.path.push_back(part.name);
      }
      auto *path = indexedPath(rule.path, source.span);
      if (!path)
        return false;
      if (!path->written.insert(rule.kind).second)
        return types.fail("source.construction",
                          "duplicate construction selector", source.span);
      std::vector<Type> inputs{*result.state}, outputs{*result.state};
      if (rule.kind == ConstructionRule::Kind::Start) {
        if (source.parameters.empty())
          return types.fail("source.construction",
                            "start handler requires a state parameter",
                            source.span);
        for (const auto &parameter :
             ArrayRef<SyntaxName>(source.parameters).drop_front()) {
          if (!types.charge(target.inputs.size(), parameter.span))
            return false;
          auto found = llvm::find_if(target.inputs, [&](const Port &port) {
            return port.name == parameter.name;
          });
          if (found == target.inputs.end())
            return types.fail("source.construction",
                              "start selects no protocol input",
                              parameter.span);
          if (found->roles.size() != target.roles.size())
            return types.fail(
                "source.construction",
                "start input must be available to both participants",
                parameter.span);
          auto value =
              types.substitute(found->type, substitution, parameter.span);
          if (!value)
            return false;
          inputs.push_back(std::move(*value));
          rule.inputs.push_back(unsigned(found - target.inputs.begin()));
        }
      } else {
        const auto &occurrence = rule.kind == ConstructionRule::Kind::Query
                                     ? path->query
                                     : path->message;
        if (occurrence.ambiguous)
          return types.fail("source.construction",
                            "selector names multiple occurrences of this kind "
                            "and authority",
                            source.span);
        if (!occurrence.index)
          return types.fail(
              "source.construction",
              "selector names no occurrence of this kind and authority",
              source.span);
        const auto *site = &sites[*occurrence.index];
        if (!protocol::isCodecRule(rule.kind)) {
          auto owned = delegatedOccurrence(*site);
          if (!owned)
            return false;
          if (*owned)
            return types.fail("source.construction",
                              "a child owns this complete construction subtree",
                              source.span);
        }
        if (site->indexBlock)
          return types.fail("source.construction",
                            "index blocks require the native transcript "
                            "transition rather than a custom query handler",
                            source.span);
        rule.payload = site->payload;
        if (protocol::isCodecRule(rule.kind)) {
          if (!result.codec || !site->proofMessage)
            return types.fail(
                "source.construction",
                "codec rule requires a producer message and record format",
                source.span);
          rule.chunks = path->chunks ? *path->chunks : *bytes;
          auto pair = [](const Type &first, const Type &second) {
            Type value(Type::Kind::Tuple);
            value.arguments = {first, second};
            return value;
          };
          switch (rule.kind) {
          case ConstructionRule::Kind::Encode:
            inputs = {result.codec->record, site->payload};
            outputs = {pair(result.codec->record, *rule.chunks)};
            break;
          case ConstructionRule::Kind::Receive:
            inputs = {result.codec->record, *bytes};
            outputs = {
                pair(result.codec->record, ranges(ranges, *rule.chunks))};
            break;
          case ConstructionRule::Kind::Decode:
            inputs = {*rule.chunks};
            outputs = {site->payload};
            break;
          case ConstructionRule::Kind::Wire:
            inputs = {*result.state, *rule.chunks};
            break;
          default:
            llvm_unreachable("checked codec rule");
          }
        } else if (rule.kind == ConstructionRule::Kind::Message)
          inputs.push_back(site->payload);
        else {
          if (site->bound)
            inputs.emplace_back(Type::Kind::Index);
          // Source handlers return (state, value). Native lowering adapts
          // this ordinary source signature to its selected state-slot
          // convention.
          Type pair(Type::Kind::Tuple);
          pair.arguments = {*result.state, site->payload};
          outputs = {std::move(pair)};
        }
      }
      auto &handler = output.declarations[rule.handler.index];
      if (!signature(handler.id))
        return false;
      if (source.parameters.size() != inputs.size())
        return types.fail("source.construction",
                          "handler parameter count differs from its occurrence",
                          source.span);
      std::set<std::string> names;
      const auto &ports = sources[handler.id.index]->inputs;
      for (auto [index, parameter] : enumerate(source.parameters)) {
        if (!names.insert(parameter.name).second)
          return types.fail("source.construction",
                            "duplicate handler parameter", parameter.span);
        if (!ports[index].type.name.empty() ||
            ports[index].type.kind != SyntaxType::Kind::Name) {
          auto annotation = type(handler, ports[index].type);
          if (!annotation)
            return false;
          if (*annotation != inputs[index])
            return types.fail("source.construction",
                              "handler annotation differs from its occurrence",
                              parameter.span);
        }
        handler.inputs.push_back(
            {parameter.name, inputs[index], {}, parameter.span});
      }
      for (const auto &value : outputs)
        handler.outputs.push_back({"result", value, {}, source.span});
      if (!body(handler.id, 1))
        return false;
      for (const auto &parameter : handler.parameters)
        rule.arguments.push_back(parameterType(parameter));
      auto prior = path->rules.find(rule.kind);
      if (prior == path->rules.end()) {
        path->rules[rule.kind] = result.rules.size();
        result.rules.push_back(std::move(rule));
      } else
        result.rules[prior->second] = std::move(rule);
    }
    for (const auto &rule : result.rules)
      if (!protocol::isCodecRule(rule.kind) &&
          rule.kind != ConstructionRule::Kind::Start) {
        auto *path = indexedPath(rule.path, rule.span);
        if (!path)
          return false;
        const auto &occurrence = rule.kind == ConstructionRule::Kind::Query
                                     ? path->query
                                     : path->message;
        if (!occurrence.index || occurrence.ambiguous)
          return types.fail("source.construction",
                            "inherited selector requires a unique occurrence",
                            rule.span);
        auto owned = delegatedOccurrence(sites[*occurrence.index]);
        if (!owned)
          return false;
        if (*owned)
          return types.fail(
              "source.construction",
              "an inherited rule overlaps a construction application",
              rule.span);
      }
    if (result.codec) {
      for (auto [index, site] : enumerate(sites)) {
        if (!site.proofMessage)
          continue;
        for (auto kind :
             {ConstructionRule::Kind::Encode, ConstructionRule::Kind::Receive,
              ConstructionRule::Kind::Decode}) {
          if (!types.charge(8, decl.span))
            return false;
          if (!site.labelled || !sitePaths[index]->rules.count(kind))
            return types.fail(
                "source.construction",
                "record codec does not cover every producer message",
                decl.span);
        }
      }
    }
    if (!result.nativeBase) {
      if (llvm::none_of(result.rules, [](const ConstructionRule &rule) {
            return rule.kind == ConstructionRule::Kind::Start;
          }))
        return types.fail("source.construction",
                          "construction requires on start", decl.span);
      for (auto [index, site] : enumerate(sites)) {
        auto owned = delegatedOccurrence(site);
        if (!owned)
          return false;
        if (site.labelled && *owned)
          continue;
        if (!types.charge(8, decl.span))
          return false;
        if (!site.labelled || !sitePaths[index]->rules.count(site.kind))
          return types.fail(
              "source.construction",
              "construction does not cover every message and selected query",
              decl.span);
      }
    }
    if (height[id.index] > work.limits.typeDepth - depth)
      return types.fail("source.limit", "construction selection depth",
                        decl.span);
    decl.construction = std::move(result);
    if (!retainSource())
      return false;
    state[id.index] = 2;
    return true;
  };
  for (const auto &decl : output.declarations)
    if (decl.kind == Declaration::Kind::Construction && !check(decl.id, 1))
      return false;
  constructionsReady = true;
  return true;
}
} // namespace zkc::language::detail
