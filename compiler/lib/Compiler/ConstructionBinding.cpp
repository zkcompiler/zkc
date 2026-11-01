#include "ConstructionBinding.h"
#include "zkc/Analysis/CanonicalEncoding.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
using Analysis = CanonicalEncodingAnalysis;
using Id = Analysis::Id;
using Kind = Analysis::Kind;
using Rule = protocol::ConstructionRule;
class Checker {
  Analysis encoding;
  SymbolTable symbols;
  ArrayRef<Type> sourceInputs;
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan &plan;
  bool history;
  SmallVector<Id> required, state;
  std::string primitive;
  SmallVector<std::pair<std::string, bool>> tags;
  json::Array transitions;
  Error refuse(const Twine &detail) {
    return error("construction-binding-coverage", detail);
  }
  Expected<SmallVector<Id>> call(FlatSymbolRefAttr handler,
                                 ArrayRef<Id> inputs) {
    return encoding.apply(symbols.lookup<func::FuncOp>(handler.getValue()),
                          inputs);
  }
  Expected<Id> atom(Type type, const Twine &name, bool digest = false) {
    return encoding.input(type, name.str(), digest);
  }
  Expected<Id> digest(Id value, ArrayRef<Id> expected, StringRef site,
                      bool query) {
    const auto &node = encoding.node(value);
    if (node.kind != Kind::Hash)
      return refuse("state or query is not a full hash digest at " + site);
    if (primitive.empty())
      primitive = node.name;
    if (node.name != primitive)
      return refuse("hash transition changes the selected primitive at " +
                    site);
    auto layout = encoding.encoding(node.inputs.front());
    if (!layout)
      return layout.takeError();
    if (layout->tag.empty() || layout->inputs != expected)
      return refuse("missing, reordered or noncanonical whole inputs at " +
                    site);
    for (const auto &[tag, wasQuery] : tags)
      if ((tag == layout->tag && wasQuery != query) ||
          (tag != layout->tag && (StringRef(tag).starts_with(layout->tag) ||
                                  StringRef(layout->tag).starts_with(tag))))
        return refuse("ambiguous transition domain tags at " + site);
    tags.emplace_back(layout->tag, query);
    json::Array inputs;
    for (Id input : expected)
      inputs.push_back(encoding.node(input).name);
    transitions.push_back(json::Object{{"site", site.str()},
                                       {"digest", value},
                                       {"inputs", std::move(inputs)},
                                       {"tag_hex", toHex(layout->tag)},
                                       {"query", query}});
    return value;
  }
  Expected<Id> challenge(Id value, StringRef site) {
    const auto &node = encoding.node(value);
    if (node.kind != Kind::Reduce || node.inputs.size() != 1 ||
        encoding.node(node.inputs[0]).kind != Kind::Hash)
      return refuse("challenge is not the selected digest conversion at " +
                    site);
    return node.inputs[0];
  }
  Expected<SmallVector<Id>> stateArguments() {
    if (!history)
      return state;
    auto value = atom(plan.state[0], "previous-state", true);
    if (!value)
      return value.takeError();
    return SmallVector<Id>{*value};
  }

public:
  Checker(ModuleOp candidate, ArrayRef<Type> sourceInputs,
          const NativeProofPolicy &policy,
          const protocol::ConstructionPlan &plan, bool history)
      : encoding(candidate), symbols(&candidate.getBody()->front()),
        sourceInputs(sourceInputs), policy(policy), plan(plan),
        history(history) {}
  Expected<json::Value> run(ArrayRef<NativeTranscriptEvent> events) {
    if (plan.root != protocol::ConstructionPlan::Root::Local ||
        plan.nativeBase || plan.codec || !plan.applications.empty() ||
        plan.state.empty() || (history && plan.state.size() != 1))
      return refuse(
          "profile requires an unreset local data-state construction");
    auto initialized = call(plan.initializer, {});
    if (!initialized)
      return initialized.takeError();
    state = std::move(*initialized);
    if (state.size() != plan.state.size())
      return refuse("initializer state ABI");
    if (history) {
      auto checked = digest(state[0], {}, "initialize", false);
      if (!checked)
        return checked.takeError();
    }
    SmallVector<Id> publicValues;
    for (unsigned port : policy.publicInputs) {
      auto value = atom(sourceInputs[port], "input." + Twine(port));
      if (!value)
        return value.takeError();
      publicValues.push_back(*value);
    }
    required = publicValues;
    unsigned starts = 0;
    std::map<std::string, const Rule *> rules;
    for (const auto &rule : plan.rules) {
      if (rule.kind == Rule::Kind::Start) {
        if (++starts != 1 || !llvm::equal(rule.inputs, policy.publicInputs))
          return refuse(
              "root start must cover the exact ordered public inventory");
        auto arguments = stateArguments();
        if (!arguments)
          return arguments.takeError();
        append_range(*arguments, publicValues);
        auto result = call(rule.handler, *arguments);
        if (!result)
          return result.takeError();
        if (result->size() != state.size())
          return refuse("start state ABI");
        if (history) {
          auto checked = digest(result->front(), *arguments, "start", false);
          if (!checked)
            return checked.takeError();
        }
        state = std::move(*result);
      } else if (rule.kind == Rule::Kind::Message ||
                 rule.kind == Rule::Kind::Query) {
        for (const auto &site : rule.sites)
          rules.emplace(site, &rule);
      } else
        return refuse("custom codec or wire observation requires its own rule");
    }
    if (starts != 1)
      return refuse("missing exact public-input start");
    json::Array terminal;
    for (unsigned i = 0; i < events.size();) {
      const auto &event = events[i];
      if (event.startInputs || (!history && event.depth) || event.bound ||
          event.count || event.difficulty)
        return refuse(
            "unsupported child reset, repeated explicit input or query law");
      auto found = rules.find(event.site);
      if (found == rules.end())
        return refuse("missing selected handler");
      const auto &rule = *found->second;
      if (rule.sites.empty() || rule.sites.front() != event.site ||
          i + rule.sites.size() > events.size())
        return refuse("message grouping differs");
      bool delivery = false;
      for (const auto &draw : policy.draws)
        delivery |= draw.second == event.site;
      auto arguments = stateArguments();
      if (!arguments)
        return arguments.takeError();
      if (!event.query) {
        for (unsigned j = 0; j < rule.sites.size(); ++j) {
          if (rule.sites[j] != events[i + j].site || events[i + j].query)
            return refuse("ordered payload grouping differs");
          auto value =
              atom(events[i + j].payload, "message." + events[i + j].site);
          if (!value)
            return value.takeError();
          arguments->push_back(*value);
          if (!delivery) {
            required.push_back(*value);
            terminal.push_back(events[i + j].site);
          }
        }
      }
      auto result = call(rule.handler, *arguments);
      if (!result)
        return result.takeError();
      if (result->size() != state.size() + unsigned(event.query))
        return refuse("handler state ABI differs");
      if (history) {
        if (delivery && result->front() == arguments->front()) {
          // Exact delivery is already coupled to the selected query by the
          // independent transcript correspondence checker.
        } else {
          auto checked =
              digest(result->front(), *arguments, event.site, event.query);
          if (!checked)
            return checked.takeError();
        }
      }
      if (event.query) {
        auto hash = challenge(result->back(), event.site);
        if (!hash)
          return hash.takeError();
        if (history) {
          if (*hash != result->front())
            return refuse("discarded query state successor");
        } else {
          auto checked = digest(*hash, required, event.site, true);
          if (!checked)
            return checked.takeError();
        }
        result->pop_back();
        terminal.clear();
      }
      state = std::move(*result);
      i += rule.sites.size();
    }
    auto graph = encoding.exportGraph();
    if (!graph)
      return graph.takeError();
    if (history)
      terminal.clear();
    return json::Value(
        json::Object{{"hash", primitive},
                     {"transitions", std::move(transitions)},
                     {"encoding_graph", std::move(*graph)},
                     {"terminal_outside_query", std::move(terminal)}});
  }
};
} // namespace
Expected<json::Value>
analyzeConstructionBinding(ModuleOp candidate, ArrayRef<Type> sourceInputs,
                           const NativeProofPolicy &policy,
                           NativeProofBindingProfile profile,
                           ArrayRef<NativeTranscriptEvent> events,
                           const protocol::ConstructionPlan *plan) {
  json::Value coverage = json::Object{};
  StringRef name;
  if (profile == NativeProofBindingProfile::NativeHistory) {
    name = "native-history";
    if (policy.suite.empty() ||
        (plan && (!plan->nativeBase || !plan->rules.empty() || plan->codec ||
                  !plan->applications.empty())))
      return error("construction-binding-profile",
                   "native history has custom handlers");
    coverage = json::Object{{"suite", policy.suite},
                            {"root", "installed-host-invocation"},
                            {"terminal_observations", "all-ordered-messages"}};
  } else if (profile == NativeProofBindingProfile::CanonicalHashHistory ||
             profile == NativeProofBindingProfile::ExplicitInput) {
    bool history = profile == NativeProofBindingProfile::CanonicalHashHistory;
    name = history ? "canonical-hash-history" : "explicit-input";
    if (!plan)
      return error("construction-binding-profile",
                   "missing selected local handlers");
    auto checked =
        Checker(candidate, sourceInputs, policy, *plan, history).run(events);
    if (!checked)
      return checked.takeError();
    coverage = std::move(*checked);
  } else
    return error("construction-binding-profile");
  json::Array occurrences;
  for (const auto &event : events) {
    auto type = exportLogicalTypeData(event.payload);
    if (!type)
      return type.takeError();
    json::Object item{
        {"site", event.site},          {"origin", event.origin},
        {"type", std::move(*type)},    {"query", event.query},
        {"repeat_depth", event.depth}, {"reconstructed", event.reconstructed}};
    if (event.bound)
      item["bound"] = *event.bound;
    if (event.count)
      item["count"] = *event.count;
    if (event.difficulty)
      item["difficulty"] = *event.difficulty;
    occurrences.push_back(std::move(item));
  }
  json::Array primitives;
  for (auto binding : candidate.getBody()
                          ->front()
                          .getRegion(0)
                          .front()
                          .getOps<runtime::BindingOp>()) {
    auto exported = exportBindingData(binding);
    if (!exported)
      return exported.takeError();
    primitives.push_back(std::move(*exported));
  }
  return json::Value(json::Object{
      {"format", "zkc.construction-binding/0"},
      {"profile", name},
      {"coverage", std::move(coverage)},
      {"occurrences", std::move(occurrences)},
      {"primitive_inventory", std::move(primitives)},
      {"premises", json::Array{"installed-primitive-and-codec-meaning",
                               "hash-collision-and-challenge-law",
                               "fixed-authenticated-program",
                               "no-independent-oracles-from-role-labels",
                               "original-acceptance-correspondence-only"}}});
}
} // namespace zkc::detail
