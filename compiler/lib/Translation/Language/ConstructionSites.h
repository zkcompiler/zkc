#ifndef ZKC_TRANSLATION_LANGUAGE_CONSTRUCTIONSITES_H
#define ZKC_TRANSLATION_LANGUAGE_CONSTRUCTIONSITES_H

#include "zkc/Dialect/Mathematical.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include <map>
#include <numeric>

namespace zkc::language::detail {
/// Recovered from the checked source, never from emitted sites or a candidate
/// construction record. Each consumer builds its own inventory. Scoped source
/// elaboration/specialization witnesses authenticate these bodies and captures.
class ConstructionSites {
  enum class Kind { Call, Message, Query };
  struct Occurrence {
    Kind kind;
    std::vector<std::string> path;
    std::string prefix, site;
    const ProtocolApplication *call = nullptr;
    std::vector<unsigned> services, roles;
    bool proofMessage = false;
  };
  using Scope = std::optional<std::pair<std::string, std::string>>;
  const ClosedEntry &project;
  const Limits &limits;
  uint64_t &remaining;
  // Initialization order matters: every observation shares the exact enclosing
  // allowance, which is already alive before this observer is constructed.
  Layouts layouts;
  const Declaration &target;
  const ConstructionDefinition &plan;
  std::vector<Occurrence> occurrences;
  using Key = std::pair<Kind, std::vector<std::string>>;
  // A disengaged index records ambiguity, rather than silently picking a site.
  std::map<Key, std::optional<unsigned>> index;
  std::vector<bool> replaced;

  bool charge(uint64_t count) {
    if (count > remaining)
      return false;
    remaining -= count;
    return true;
  }
  llvm::Error limit() const {
    return error("source.limit",
                 "construction site resolution work limit exceeded");
  }
  bool chargePath(llvm::ArrayRef<std::string> path) {
    uint64_t width = 1;
    for (const auto &part : path)
      width += part.size() + 1;
    // Cover the retained/query key copy and both string comparisons per
    // component at every possible red-black tree comparison level.
    if (!charge(8 * width + 1))
      return false;
    for (auto size = index.size(); size; size >>= 1)
      if (!charge(4 * width))
        return false;
    return true;
  }
  llvm::Expected<std::string> expand(llvm::StringRef prefix,
                                     llvm::StringRef site) {
    if (!charge(prefix.size() + site.size() + 1))
      return limit();
    return prefix.empty() ? site.str()
                          : mathematical::expandedApplicationSite(prefix, site);
  }
  llvm::Error walk(const Body &body, llvm::ArrayRef<unsigned> services,
                   llvm::ArrayRef<unsigned> roles,
                   llvm::ArrayRef<std::string> prefix,
                   llvm::StringRef nativePrefix, const Scope &scope,
                   bool labelled, uint64_t &ordinal, unsigned depth) {
    if (depth > limits.callDepth)
      return error("source.limit", "construction occurrence depth exceeded");
    // Charge all arms and every operation, including operations without a
    // selector. They advance the same definition-local ordinal as body().
    for (const auto &op : body.operations) {
      llvm::StringRef label =
          op.site ? llvm::StringRef(*op.site) : llvm::StringRef();
      if (!charge(label.size() + 1))
        return limit();
      auto site = nativeSiteName(label, ordinal++);
      if (!charge(site.size() + 1))
        return limit();
      if (scope) {
        if (!charge(scope->first.size() + scope->second.size() + site.size() +
                    1))
          return limit();
        site = nativeSelectedSite(scope->first, scope->second, site);
      }
      if (auto repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        if (!charge(repeat->services.size() + 1))
          return limit();
        std::vector<unsigned> captured;
        captured.reserve(repeat->services.size());
        for (auto service : repeat->services)
          captured.push_back(services[service.index]);
        if (auto e = walk(*repeat->region, captured, roles, prefix,
                          nativePrefix, scope, labelled, ordinal, depth + 1))
          return e;
      } else if (auto control = std::get_if<Control>(&op.action)) {
        if (!charge(control->services.size() + control->regions.size() + 1))
          return limit();
        std::vector<unsigned> captured;
        captured.reserve(control->services.size());
        for (auto service : control->services)
          captured.push_back(services[service.index]);
        std::vector<std::string> alternatives;
        if (control->kind == Control::Kind::Match) {
          auto subject =
              layouts.get(body.values[control->operands.front().index].type);
          if (!subject)
            return subject.takeError();
          for (const auto &name : control->alternatives) {
            bool found = false;
            for (auto [i, alternative] :
                 llvm::enumerate((**subject).alternatives)) {
              if (!charge(name.size() + alternative.name.size() + 1))
                return limit();
              if (alternative.name == name) {
                alternatives.push_back(nativeAlternativeName(i));
                found = true;
                break;
              }
            }
            if (!found)
              return error("source.construction",
                           "unknown checked match alternative");
          }
        } else if (control->kind == Control::Kind::If)
          alternatives = {"then", "else"};
        else
          return error("source.construction",
                       "unsupported protocol construction control");
        if (alternatives.size() != control->regions.size())
          return error("source.construction",
                       "incomplete checked construction arms");
        for (auto [arm, region] : llvm::enumerate(control->regions)) {
          if (!charge(site.size() + alternatives[arm].size() + 1))
            return limit();
          Scope selected = std::pair(site, alternatives[arm]);
          // A roster does not renumber roles; only service slots are compacted.
          if (auto e = walk(*region, captured, roles, prefix, nativePrefix,
                            selected, labelled, ordinal, depth + 1))
            return e;
        }
      } else {
        const auto *call = std::get_if<ProtocolApplication>(&op.action);
        const auto *message = std::get_if<Exchange>(&op.action);
        const auto *query = std::get_if<ServiceQuery>(&op.action);
        if (!call && !message && !query)
          continue;
        if (query && !charge(1))
          return limit();
        bool selected = !query || replaced[services[query->service.index]];
        if (!charge(prefix.size() + nativePrefix.size() + site.size() + 1))
          return limit();
        for (const auto &part : prefix)
          if (!charge(part.size() + 1))
            return limit();
        if (op.site && !charge(op.site->size() + 1))
          return limit();
        std::vector<std::string> path;
        path.reserve(prefix.size() + 1);
        path.assign(prefix.begin(), prefix.end());
        if (op.site)
          path.push_back(*op.site);
        bool validPath = labelled && op.site.has_value();
        Occurrence occurrence{call    ? Kind::Call
                              : query ? Kind::Query
                                      : Kind::Message,
                              std::move(path),
                              nativePrefix.str(),
                              std::move(site),
                              nullptr,
                              {},
                              {},
                              false};
        if (call) {
          if (!charge(call->services.size() + call->roles.size() + 1))
            return limit();
          occurrence.call = call;
          occurrence.services.reserve(call->services.size());
          occurrence.roles.reserve(call->roles.size());
          for (auto service : call->services)
            occurrence.services.push_back(services[service.index]);
          for (auto role : call->roles)
            occurrence.roles.push_back(roles[role]);
          auto nestedPrefix = expand(nativePrefix, occurrence.site);
          if (!nestedPrefix)
            return nestedPrefix.takeError();
          const auto &callee = project.declarations()[call->callee.index];
          // A call is emitted in its caller, but its body has its own ordinal
          // and selected scope. Only actual calls contribute this prefix.
          uint64_t calleeOrdinal = 0;
          if (auto e = walk(*callee.body, occurrence.services, occurrence.roles,
                            occurrence.path, *nestedPrefix, {}, validPath,
                            calleeOrdinal, depth + 1))
            return e;
        } else if (message) {
          auto verifier = target.services[plan.services.front()].owner;
          occurrence.proofMessage = roles[message->receiver] == verifier &&
                                    roles[message->sender] != verifier;
        }
        if (validPath && selected) {
          if (!chargePath(occurrence.path))
            return limit();
          auto [position, inserted] = index.emplace(
              Key(occurrence.kind, occurrence.path), occurrences.size());
          if (!inserted)
            position->second.reset();
          occurrences.push_back(std::move(occurrence));
        }
      }
    }
    if (body.stopped) {
      if (!charge(1))
        return limit();
      ++ordinal;
    }
    return llvm::Error::success();
  }
  llvm::Expected<const Occurrence &> find(llvm::ArrayRef<std::string> path,
                                          Kind kind) {
    if (!chargePath(path))
      return limit();
    auto found = index.find(
        Key(kind, std::vector<std::string>(path.begin(), path.end())));
    if (found == index.end())
      return error("source.construction",
                   "missing checked construction occurrence or authority");
    if (!found->second)
      return error("source.construction",
                   "ambiguous checked construction selector");
    return occurrences[*found->second];
  }

public:
  ConstructionSites(const ClosedEntry &project, const Limits &limits,
                    uint64_t &remaining, const Declaration &definition)
      : project(project), limits(limits), remaining(remaining),
        layouts(project, limits, remaining),
        target(project.declarations()[definition.target->index]),
        plan(*definition.construction) {}

  Layouts &observer() { return layouts; }

  llvm::Error collect() {
    if (!charge(plan.rules.size() + 1))
      return limit();
    if (plan.applications.empty() &&
        llvm::all_of(plan.rules, [](const auto &rule) {
          return rule.kind == ConstructionRule::Kind::Start;
        }))
      return llvm::Error::success();
    if (!charge(2 * target.services.size() + target.roles.size() +
                plan.services.size() + 1))
      return limit();
    replaced.resize(target.services.size());
    for (auto port : plan.services)
      replaced[port] = true;
    std::vector<unsigned> services(target.services.size()),
        roles(target.roles.size());
    std::iota(services.begin(), services.end(), 0);
    std::iota(roles.begin(), roles.end(), 0);
    uint64_t ordinal = 0;
    return walk(*target.body, services, roles, {}, {}, {}, true, ordinal, 1);
  }
  llvm::Expected<std::string>
  application(const ConstructionApplication &selection) {
    auto occurrence = find(selection.path, Kind::Call);
    if (!occurrence)
      return occurrence.takeError();
    const auto &child = project.declarations()[selection.construction.index];
    if (occurrence->call->callee.index != child.target->index)
      return error("source.construction", "construction call target differs");
    const auto &childPlan = *child.construction;
    const auto &callee = project.declarations()[child.target->index];
    if (!charge(callee.services.size() + childPlan.services.size() +
                occurrence->services.size() + 1))
      return limit();
    std::vector<bool> childReplaced(callee.services.size());
    for (auto port : childPlan.services)
      childReplaced[port] = true;
    for (auto [port, root] : llvm::enumerate(occurrence->services)) {
      if (replaced[root] != childReplaced[port])
        return error("source.construction",
                     "construction call authority differs");
    }
    if (!charge(1))
      return limit();
    if (occurrence->roles[callee.services[childPlan.services.front()].owner] !=
        target.services[plan.services.front()].owner)
      return error("source.construction", "construction call owner differs");
    return expand(occurrence->prefix, occurrence->site);
  }
  llvm::Expected<std::vector<std::string>> rule(const ConstructionRule &rule,
                                                unsigned lanes) {
    auto occurrence = find(rule.path, rule.kind == ConstructionRule::Kind::Query
                                          ? Kind::Query
                                          : Kind::Message);
    if (!occurrence)
      return occurrence.takeError();
    if (protocol::isCodecRule(rule.kind) && !occurrence->proofMessage)
      return error("source.construction",
                   "codec selector is not a producer message");
    std::vector<std::string> sites;
    unsigned count = rule.kind == ConstructionRule::Kind::Query ? 1 : lanes;
    for (unsigned i = 0; i < count; ++i) {
      if (!charge(occurrence->site.size() + 1))
        return limit();
      auto local = occurrence->site;
      if (rule.kind != ConstructionRule::Kind::Query)
        local += "_" + std::to_string(i);
      auto site = expand(occurrence->prefix, local);
      if (!site)
        return site.takeError();
      sites.push_back(std::move(*site));
    }
    return sites;
  }
};
} // namespace zkc::language::detail
#endif
