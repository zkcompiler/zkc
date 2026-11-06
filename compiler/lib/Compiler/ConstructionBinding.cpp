#include "ConstructionBinding.h"
#include "zkc/Analysis/CanonicalEncoding.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <map>
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
using Analysis = CanonicalEncodingAnalysis;
using Id = Analysis::Id;
using Kind = Analysis::Kind;
using Rule = protocol::ConstructionRule;
namespace pir = protocol_ir;

// This walks borrowed native regions, not a second representation of control.
class TerminalSummary {
  using Pending = SmallVector<unsigned, 0>;
  struct DrawSite {
    StringRef site;
    bool query;
    bool seen = false;
  };
  SmallVector<DrawSite, 0> draws;
  ArrayRef<NativeTranscriptEvent> events;
  uint64_t remaining;
  unsigned next = 0;
  bool selectedControl = false;

  Error capacity() { return error("construction-binding-capacity"); }
  Error coverage() {
    return error("construction-binding-coverage",
                 "prepared source/event site, kind or order differs");
  }
  bool charge(uint64_t amount = 1) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
  // A small sorted index of borrowed draw names, with every comparison and
  // insertion shift metered. No hashing, pointer order or unmetered sorting.
  Expected<size_t> lower(StringRef site) {
    size_t first = 0, last = draws.size();
    while (first != last) {
      size_t middle = first + (last - first) / 2;
      if (!charge(1 + std::min(site.size(), draws[middle].site.size())))
        return capacity();
      if (draws[middle].site < site)
        first = middle + 1;
      else
        last = middle;
    }
    return first;
  }
  Expected<DrawSite *> find(StringRef site) {
    auto at = lower(site);
    if (!at)
      return at.takeError();
    if (!charge(1 + site.size()))
      return capacity();
    if (*at == draws.size() || draws[*at].site != site)
      return nullptr;
    return &draws[*at];
  }
  Error insert(StringRef site, bool query) {
    if (!charge(1 + site.size()))
      return capacity();
    if (site.empty())
      return coverage();
    auto at = lower(site);
    if (!at)
      return at.takeError();
    // Includes equality, shifts, and possible vector growth/copy.
    if (!charge(1 + site.size() + 2 * draws.size()))
      return capacity();
    if (*at != draws.size() && draws[*at].site == site)
      return coverage();
    draws.insert(draws.begin() + *at, DrawSite{site, query});
    return Error::success();
  }
  Error region(Region &region, Pending &pending, unsigned depth,
               unsigned repeatDepth) {
    if (depth > 64 || !charge())
      return capacity();
    if (!hasSingleElement(region))
      return coverage();
    for (Operation &op : region.front()) {
      if (!charge())
        return capacity();
      if (auto branch = dyn_cast<pir::BranchOp>(op)) {
        selectedControl = true;
        Pending joined;
        for (Region &arm : branch.getArms()) {
          if (!charge(1 + pending.size()))
            return capacity();
          Pending local(pending);
          if (auto e = this->region(arm, local, depth + 1, repeatDepth))
            return e;
          // Both lists are in static event order. Account for reserve, reads,
          // comparisons and writes before building the union.
          if (!charge(1 + 4 * (joined.size() + local.size())))
            return capacity();
          Pending merged;
          merged.reserve(joined.size() + local.size());
          auto left = joined.begin(), right = local.begin();
          while (left != joined.end() || right != local.end()) {
            if (right == local.end() ||
                (left != joined.end() && *left < *right))
              merged.push_back(*left++);
            else if (left == joined.end() || *right < *left)
              merged.push_back(*right++);
            else {
              merged.push_back(*left++);
              ++right;
            }
          }
          joined = std::move(merged);
        }
        pending = std::move(joined);
        continue;
      }
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e = this->region(repeat.getBody(), pending, depth + 1,
                                  repeatDepth + 1))
          return e;
        continue;
      }
      auto query = dyn_cast<pir::QueryOp>(op);
      auto message = dyn_cast<pir::ExchangeOp>(op);
      auto start = dyn_cast<pir::ConstructionStartOp>(op);
      if (query || message || start) {
        auto site = op.getAttrOfType<StringAttr>("site");
        if (!site)
          return coverage();
        auto draw = find(site.getValue());
        if (!draw)
          return draw.takeError();
        // Private service queries do not enter the transcript inventory.
        if (query && !*draw)
          continue;
        if (next == events.size())
          return coverage();
        const auto &event = events[next];
        if (!charge(1 + site.getValue().size()))
          return capacity();
        if (event.site != site.getValue() || event.query != bool(query) ||
            event.startInputs.has_value() != bool(start) ||
            event.depth != repeatDepth)
          return coverage();
        if (*draw) {
          if ((*draw)->seen || (*draw)->query != bool(query) || start)
            return coverage();
          (*draw)->seen = true;
        }
        if (start) {
          if (!charge(1 + start.getNumOperands()))
            return capacity();
          if (event.payload ||
              !llvm::equal(*event.startInputs, start.getOperandTypes()))
            return coverage();
          // A start is an invocation boundary, not a message or a query.
        } else if (query) {
          if (query.getNumResults() != 1 ||
              event.payload != query.getResult(0).getType())
            return coverage();
          if (!charge(pending.size()))
            return capacity();
          pending.clear();
        } else {
          if (event.payload != message.getInput().getType())
            return coverage();
          if (!*draw) {
            if (!charge(1 + (pending.size() == pending.capacity()
                                 ? pending.size()
                                 : 0)))
              return capacity();
            pending.push_back(next);
          }
        }
        ++next;
        continue;
      }
      // Preparation must have expanded protocol applications. Other nested
      // regions are pure Math/Local structure: formation excludes protocol
      // events there, but their traversal still consumes work.
      if (isa<pir::ApplyOp>(op))
        return coverage();
      for (Region &nested : op.getRegions())
        if (auto e = this->region(nested, pending, depth + 1, repeatDepth))
          return e;
    }
    return Error::success();
  }

public:
  TerminalSummary(ArrayRef<NativeTranscriptEvent> events, uint64_t budget)
      : events(events), remaining(std::min<uint64_t>(budget, 100000)) {}
  Expected<ConstructionTerminalSummary>
  run(pir::MathematicalOp source,
      ArrayRef<std::pair<std::string, std::string>> deliveries) {
    if (!source)
      return coverage();
    if (!charge(events.size()) || !charge(deliveries.size()))
      return capacity();
    for (const auto &event : events) {
      if (!charge(1 + event.site.size()))
        return capacity();
      if (event.site.empty() || (event.startInputs && event.query))
        return coverage();
    }
    for (const auto &[query, delivery] : deliveries) {
      if (auto e = insert(query, true))
        return e;
      if (auto e = insert(delivery, false))
        return e;
    }
    Pending pending;
    if (auto e = region(source.getBody(), pending, 0, 0))
      return e;
    if (next != events.size())
      return coverage();
    for (const auto &draw : draws) {
      if (!charge())
        return capacity();
      if (!draw.seen)
        return coverage();
    }
    if (!charge(pending.size()))
      return capacity();
    // Account for materializing the terminal site names in the report too.
    for (unsigned index : pending)
      if (!charge(1 + events[index].site.size()))
        return capacity();
    return ConstructionTerminalSummary{
        SmallVector<unsigned>(pending.begin(), pending.end()), selectedControl};
  }
};

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
  Expected<json::Value> run(ArrayRef<NativeTranscriptEvent> events,
                            json::Array terminal) {
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
      auto isDelivery = [&](StringRef site) {
        return llvm::any_of(policy.draws, [&](const auto &draw) {
          return draw.second == site;
        });
      };
      bool delivery = !event.query;
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
          bool selectedDelivery = isDelivery(events[i + j].site);
          delivery &= selectedDelivery;
          if (!selectedDelivery) {
            required.push_back(*value);
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
      }
      state = std::move(*result);
      i += rule.sites.size();
    }
    auto graph = encoding.exportGraph();
    if (!graph)
      return graph.takeError();
    return json::Value(
        json::Object{{"hash", primitive},
                     {"transitions", std::move(transitions)},
                     {"encoding_graph", std::move(*graph)},
                     {"terminal_outside_query", std::move(terminal)}});
  }
};
} // namespace
Expected<ConstructionTerminalSummary> summarizeConstructionTerminal(
    pir::MathematicalOp preparedSource, ArrayRef<NativeTranscriptEvent> events,
    ArrayRef<std::pair<std::string, std::string>> draws, uint64_t workBudget) {
  return TerminalSummary(events, workBudget).run(preparedSource, draws);
}
Expected<json::Value> analyzeConstructionBinding(
    ModuleOp candidate, pir::MathematicalOp preparedSource,
    ArrayRef<Type> sourceInputs, const NativeProofPolicy &policy,
    NativeProofBindingProfile profile, ArrayRef<NativeTranscriptEvent> events,
    const protocol::ConstructionPlan *plan) {
  auto summary =
      summarizeConstructionTerminal(preparedSource, events, policy.draws);
  if (!summary)
    return summary.takeError();
  if (profile == NativeProofBindingProfile::ExplicitInput &&
      summary->selectedControl)
    return error("construction-binding-selected-control");
  json::Array terminal;
  for (unsigned index : summary->pending)
    terminal.push_back(events[index].site);
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
                            {"terminal_observations", "all-ordered-messages"},
                            {"terminal_outside_query", std::move(terminal)}};
  } else if (profile == NativeProofBindingProfile::CanonicalHashHistory ||
             profile == NativeProofBindingProfile::ExplicitInput) {
    bool history = profile == NativeProofBindingProfile::CanonicalHashHistory;
    name = history ? "canonical-hash-history" : "explicit-input";
    if (!plan)
      return error("construction-binding-profile",
                   "missing selected local handlers");
    auto checked = Checker(candidate, sourceInputs, policy, *plan, history)
                       .run(events, std::move(terminal));
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
  json::Array premises{"installed-primitive-and-codec-meaning",
                       "hash-collision-and-challenge-law",
                       "fixed-authenticated-program",
                       "no-independent-oracles-from-role-labels"};
  if (profile == NativeProofBindingProfile::NativeHistory)
    premises.push_back("installed-host-invocation-initialization");
  return json::Value(
      json::Object{{"format", "zkc.construction-binding/0"},
                   {"profile", name},
                   {"coverage", std::move(coverage)},
                   {"occurrences", std::move(occurrences)},
                   {"primitive_inventory", std::move(primitives)},
                   {"premises", std::move(premises)}});
}
} // namespace zkc::detail
