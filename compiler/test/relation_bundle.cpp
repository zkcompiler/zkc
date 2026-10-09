#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
#include <map>

using namespace llvm;
using namespace zkc::relation;
using N = AIRNode;

// Independent checks record a failure and continue, so one broken case does
// not hide the others. A value needed to continue is fatal.
static unsigned checks = 0, failures = 0;
static void check(bool ok, StringRef message) {
  ++checks;
  if (!ok) {
    ++failures;
    errs() << "FAILED: " << message << '\n';
  }
}
static std::string code(Error error) {
  std::string result;
  handleAllErrors(
      std::move(error), [&](const zkc::Refusal &r) { result = r.code; },
      [&](const ErrorInfoBase &e) { result = e.message(); });
  return result;
}
template <typename T> static T value(Expected<T> result, StringRef where) {
  if (!result) {
    errs() << "FATAL " << where << ": " << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
template <typename T>
static void refuses(Expected<T> result, StringRef expected, StringRef message) {
  ++checks;
  if (result) {
    ++failures;
    errs() << "FAILED: " << message << ": accepted, expected " << expected
           << '\n';
    return;
  }
  auto actual = code(result.takeError());
  if (actual != expected) {
    ++failures;
    errs() << "FAILED: " << message << ": expected " << expected << ", got "
           << actual << '\n';
  }
}
static void refuses(Error error, StringRef expected, StringRef message) {
  ++checks;
  if (!error) {
    ++failures;
    errs() << "FAILED: " << message << ": accepted, expected " << expected
           << '\n';
    return;
  }
  auto actual = code(std::move(error));
  if (actual != expected) {
    ++failures;
    errs() << "FAILED: " << message << ": expected " << expected << ", got "
           << actual << '\n';
  }
}

static const std::string KB = "koala-bear", EXT = "koala-bear.ext8-binomial3";
static const std::string P_MINUS_ONE = "2130706432";

/// Small arena builder: equal bindings share one ring input.
struct Arena {
  std::vector<zkc::ring::Input> inputs;
  std::vector<BundleInput> bindings;
  std::vector<zkc::ring::Node> nodes;
  std::vector<uint32_t> outputs;
  uint32_t bind(const std::string &field, BundleInput binding) {
    for (uint32_t i = 0; i < bindings.size(); ++i)
      if (bindings[i].kind == binding.kind &&
          bindings[i].index == binding.index &&
          bindings[i].offset == binding.offset &&
          bindings[i].column == binding.column) {
        nodes.push_back(zkc::ring::Node::slot(i));
        return nodes.size() - 1;
      }
    inputs.push_back({field});
    bindings.push_back(binding);
    nodes.push_back(zkc::ring::Node::slot(inputs.size() - 1));
    return nodes.size() - 1;
  }
  uint32_t read(const std::string &field, uint32_t group, int32_t offset,
                uint32_t column = 0) {
    return bind(field, BundleInput::read(group, offset, column));
  }
  uint32_t pub(const std::string &field, uint32_t slot) {
    return bind(field, BundleInput::publicSlot(slot));
  }
  uint32_t lit(const std::string &field, std::string natural) {
    nodes.push_back(zkc::ring::Node::literal(field, std::move(natural)));
    return nodes.size() - 1;
  }
  uint32_t push(zkc::ring::Node node) {
    nodes.push_back(std::move(node));
    return nodes.size() - 1;
  }
  uint32_t add(uint32_t a, uint32_t b) {
    return push(zkc::ring::Node::add(a, b));
  }
  uint32_t mul(uint32_t a, uint32_t b) {
    return push(zkc::ring::Node::mul(a, b));
  }
  uint32_t neg(uint32_t a) { return push(zkc::ring::Node::neg(a)); }
  uint32_t sub(uint32_t a, uint32_t b) { return add(a, neg(b)); }
  uint32_t embed(const std::string &field, uint32_t a) {
    return push(zkc::ring::Node::embed(field, a));
  }
  uint32_t out(uint32_t node) {
    outputs.push_back(node);
    return outputs.size() - 1;
  }
  zkc::ring::Expression build() const {
    return value(zkc::ring::Expression::create(inputs, nodes, outputs),
                 "arena");
  }
};
static BundleTable table(std::string name, const Arena &arena,
                         std::vector<BundleGroup> groups, BundleHeight height,
                         BundleReadModel model = BundleReadModel::Finite,
                         bool optional = false) {
  return {std::move(name), optional,       height, model, std::move(groups),
          arena.build(),   arena.bindings, {},     {}};
}
static BundleHeight instanceHeight(uint32_t min, uint32_t max,
                                   bool pow2 = false) {
  return {BundleHeightAuthority::Instance, min, max, pow2};
}
static BundleHeight fixedHeight(uint32_t h) {
  return {BundleHeightAuthority::Fixed, h, h, false};
}
static BundleScope scope(BundleScopeKind kind, uint32_t a = 0, uint32_t b = 0) {
  return {kind, a, b};
}
static BundleInteraction fieldBalance(uint32_t channel,
                                      std::vector<uint32_t> tuple,
                                      uint32_t count,
                                      BundleLocality locality = {}) {
  BundleInteraction i;
  i.kind = BundleChannelKind::FieldBalance;
  i.channel = channel;
  i.locality = locality;
  i.tuple = std::move(tuple);
  i.count = count;
  return i;
}
static BundleInteraction multiset(uint32_t channel, BundleSide side,
                                  std::vector<uint32_t> tuple, uint32_t count,
                                  uint64_t bound,
                                  BundleLocality locality = {}) {
  auto i = fieldBalance(channel, std::move(tuple), count, locality);
  i.kind = BundleChannelKind::Multiset;
  i.side = side;
  i.bound = bound;
  return i;
}
static BundleColumns column(std::vector<uint64_t> values) {
  BundleColumns result;
  for (auto v : values)
    result.push_back(std::to_string(v));
  return result;
}
/// Data for a bundle whose tables carry the given per-table group arrays.
struct Data {
  BundleConfiguration config;
  BundleInstance instance;
  BundleWitness witness;
};
static Data data(const Bundle &bundle) {
  std::string id = bundle.identity().str();
  Data d;
  d.config.relation = d.instance.relation = d.witness.relation = id;
  d.config.tables.resize(bundle.tables().size());
  d.instance.tables.resize(bundle.tables().size());
  d.witness.tables.resize(bundle.tables().size());
  return d;
}
static BundleEvaluation evaluate(const Bundle &bundle, const Data &d,
                                 StringRef where) {
  return value(bundle.evaluate(d.config, d.instance, d.witness), where);
}

//===----------------------------------------------------------------------===//
// Finite AIR embedding
//===----------------------------------------------------------------------===//
static AIRConstraint constraint(AIRScopeKind kind, std::vector<N> nodes,
                                uint32_t lookahead = 0) {
  return {{kind, lookahead}, std::move(nodes), std::nullopt, std::nullopt};
}
static AIR recurrence(StringRef field) {
  // x[r+1] - x[r]^2 = 0; x[0] = public[0]; x[last] = public[1].
  auto transition = constraint(
      AIRScopeKind::Transition,
      {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)}, 1);
  auto first =
      constraint(AIRScopeKind::First,
                 {N::read(0, 0), N::publicInput(0), N::neg(1), N::add(0, 2)});
  auto last = constraint(AIRScopeKind::Last, {N::read(0, 0), N::publicInput(1),
                                              N::neg(1), N::add(0, 2)});
  auto every = constraint(AIRScopeKind::Every,
                          {N::read(0, 1), N::read(0, 1), N::mul(0, 1),
                           N::neg(1), N::add(2, 3)}); // y^2 - y = 0
  return value(AIR::create(field.str(), 3, 2, {transition, first, last, every}),
               "recurrence");
}
static AIRTrace recurrenceTrace(StringRef field, uint32_t height) {
  AIRTrace t{{field.str(), height, 3},
             std::vector<std::string>(height * 3, "7")};
  uint64_t x = 2;
  for (uint32_t r = 0; r < height; ++r) {
    t.cells[r * 3] = std::to_string(x);
    t.cells[r * 3 + 1] = r % 2 ? "1" : "0";
    x = x * x; // Stays below every admitted modulus for height <= 5.
  }
  return t;
}
static std::string lastValue(uint32_t height) {
  uint64_t x = 2;
  for (uint32_t r = 1; r < height; ++r)
    x *= x;
  return std::to_string(x);
}
static bool sameResiduals(const AIREvaluation &air, const BundleEvaluation &b) {
  if (air.satisfied != b.satisfied ||
      air.residuals.size() != b.residuals.size())
    return false;
  for (size_t i = 0; i < air.residuals.size(); ++i) {
    const auto &a = air.residuals[i];
    const auto &r = b.residuals[i];
    if (r.table != 0 || a.row != r.row || a.constraint != r.assertion ||
        r.value != BundleColumns{a.value})
      return false;
  }
  return b.balances.empty() && b.rangeFailures.empty();
}
static void airEmbedding() {
  for (auto field : {"koala-bear", "bls12-381.fr", "ristretto255.scalar"}) {
    auto air = recurrence(field);
    auto bundle = value(embedAIR(air), "embed");
    check(bundle.tables().size() == 1 &&
              bundle.tables()[0].assertions.size() == 4 &&
              bundle.tables()[0].assertions[0].scope.kind ==
                  BundleScopeKind::Interior &&
              bundle.tables()[0].assertions[0].scope.second == 1,
          "embedding shape and transition scope");
    check(bundle.facts()[0][0].degree == 2 &&
              bundle.facts()[0][1].degree == 1 &&
              bundle.facts()[0][0].reads ==
                  std::vector<BundleRead>{{0, 0, 0}, {0, 1, 0}},
          "embedded degree and read facts");
    for (uint32_t height = 1; height <= 5; ++height) {
      auto trace = recurrenceTrace(field, height);
      std::vector<std::string> statement{"2", lastValue(height)};
      auto expected = value(air.evaluate(trace, statement), "air evaluate");
      auto d = embedAIRData(bundle, trace, statement);
      auto actual = value(
          bundle.evaluate(d.configuration, d.instance, d.witness), "bundle");
      check(expected.satisfied && sameResiduals(expected, actual),
            "honest embedded residuals equal AIR row by row");
      // Invalid traces: every mutation yields identical residuals.
      std::vector<std::pair<std::vector<std::string>, AIRTrace>> mutations;
      auto t = trace;
      t.cells[0] = "3";
      mutations.push_back({statement, t});
      t = trace;
      t.cells[(height - 1) * 3 + 1] = "2";
      mutations.push_back({statement, t});
      t = trace;
      t.cells[2] = "5"; // Unused column: still satisfied in both.
      mutations.push_back({statement, t});
      mutations.push_back({{"2", "5"}, trace});
      mutations.push_back({{lastValue(height), "2"}, trace});
      check(
          !value(air.evaluate(mutations[0].second, statement), "air bad")
                  .satisfied &&
              value(air.evaluate(mutations[2].second, statement), "air unused")
                  .satisfied,
          "mutations include violations and an irrelevant change");
      for (auto &[s, m] : mutations) {
        auto e = value(air.evaluate(m, s), "air mutation");
        auto md = embedAIRData(bundle, m, s);
        auto a =
            value(bundle.evaluate(md.configuration, md.instance, md.witness),
                  "bundle mutation");
        check(sameResiduals(e, a), "mutated embedded residuals equal AIR");
      }
    }
    // Identity, codec and data carrier round trips.
    auto text = zkc::printJson(bundle.encode());
    auto reread = value(readBundleText(text), "reread");
    check(reread.identity() == bundle.identity() &&
              zkc::printJson(reread.encode()) == text,
          "bundle codec round trip");
    auto trace = recurrenceTrace(field, 4);
    auto d = embedAIRData(bundle, trace, {"2", lastValue(4)});
    auto witness =
        value(readBundleWitness(
                  bundle, value(readBundleDataJson(zkc::printJson(
                                    encodeBundleWitness(bundle, d.witness))),
                                "witness json")),
              "witness reread");
    auto instance =
        value(readBundleInstance(
                  bundle, value(readBundleDataJson(zkc::printJson(
                                    encodeBundleInstance(bundle, d.instance))),
                                "instance json")),
              "instance reread");
    auto config = value(
        readBundleConfiguration(
            bundle,
            value(readBundleDataJson(zkc::printJson(
                      encodeBundleConfiguration(bundle, d.configuration))),
                  "config json")),
        "config reread");
    check(value(bundle.evaluate(config, instance, witness), "reread data")
              .satisfied,
          "data carrier round trip");
  }

  // Window, height and value refusals coincide with the AIR's.
  auto air = recurrence(KB);
  auto bundle = value(embedAIR(air), "embed");
  auto trace = recurrenceTrace(KB, 2);
  auto d = embedAIRData(bundle, trace, {"2", "4"});
  d.instance.tables[0].height = 0;
  refuses(bundle.admit(d.configuration, d.instance, d.witness), "bundle-height",
          "zero height refused like air-height");
  check(code(air.compile(0).takeError()) == "air-height", "AIR zero height");
  d = embedAIRData(bundle, trace, {"2", "4"});
  d.witness.tables[0]->front()[3] = "01";
  refuses(bundle.admit(d.configuration, d.instance, d.witness), "bundle-value",
          "noncanonical cell refused");
  d = embedAIRData(bundle, trace, {"2", "4"});
  d.instance.publics[1] = {"2130706433"};
  refuses(bundle.admit(d.configuration, d.instance, d.witness), "bundle-value",
          "public at modulus refused");

  auto firstWindow = value(
      AIR::create(KB, 1, 0, {constraint(AIRScopeKind::First, {N::read(2, 0)})}),
      "first window");
  auto firstBundle = value(embedAIR(firstWindow), "embed first window");
  for (uint32_t height : {1u, 2u, 3u, 4u}) {
    AIRTrace t{{KB, height, 1}, std::vector<std::string>(height, "0")};
    auto airResult = firstWindow.evaluate(t, {});
    auto fd = embedAIRData(firstBundle, t, {});
    auto bundleResult =
        firstBundle.evaluate(fd.configuration, fd.instance, fd.witness);
    bool airRefused = !airResult, bundleRefused = !bundleResult;
    if (airRefused)
      check(code(airResult.takeError()) == "air-window-out-of-range",
            "AIR window refusal");
    if (bundleRefused)
      check(code(bundleResult.takeError()) == "bundle-window",
            "bundle window refusal");
    check(airRefused == bundleRefused && airRefused == (height < 3),
          "first-row window refusal coincides at every height");
  }
  // Undefined at every height: AIR defers to compile, the bundle refuses at
  // formation. Both are unsatisfiable for every height.
  for (auto kind : {AIRScopeKind::Every, AIRScopeKind::Last}) {
    auto never = value(
        AIR::create(KB, 1, 0, {constraint(kind, {N::read(1, 0)})}), "never");
    check(code(never.compile(4).takeError()) == "air-window-out-of-range",
          "AIR refuses at compile");
    refuses(embedAIR(never), "bundle-window", "embedding refuses at formation");
  }
  // A short trace activates no transition row in either relation.
  auto longTransition = value(
      AIR::create(
          KB, 1, 0,
          {constraint(AIRScopeKind::Transition,
                      {N::read(2, 0), N::constant("1"), N::add(0, 1)}, 2)}),
      "long transition");
  auto longBundle = value(embedAIR(longTransition), "embed long");
  AIRTrace one{{KB, 1, 1}, {"9"}};
  auto od = embedAIRData(longBundle, one, {});
  check(value(longBundle.evaluate(od.configuration, od.instance, od.witness),
              "vacuous")
                .satisfied &&
            value(longTransition.evaluate(one, {}), "air vacuous").satisfied,
        "vacuous transition on a short trace");
  // No columns and no constraints.
  auto empty = value(AIR::create(KB, 0, 0, {}), "empty");
  auto emptyBundle = value(embedAIR(empty), "embed empty");
  AIRTrace none{{KB, 1, 0}, {}};
  auto ed = embedAIRData(emptyBundle, none, {});
  check(value(emptyBundle.evaluate(ed.configuration, ed.instance, ed.witness),
              "empty")
            .satisfied,
        "empty relation embeds");
}

//===----------------------------------------------------------------------===//
// A two-table machine with public/config authority and an optional table
//===----------------------------------------------------------------------===//
enum Channel { Range = 0, Trace = 1, Spare = 2 };
struct MachineOptions {
  uint32_t rangeChannel = Range;
  BundleLocality cpuLocality, romLocality;
  bool stepInRangeTuple = false;
  std::string requestCount = "1";
  std::optional<uint64_t> declared;
};
/// cpu (required, instance height in [1,16], power of two): witness x, public
/// column step; x[0] = start, x[r+1] = x[r] + step[r], x[last] = final; looks
/// up x in the rom and pushes (x, step) on a multiset channel.
/// rom (required, fixed height 8): config values, witness multiplicities.
/// log (optional, instance height): pulls (a, b) pairs.
static Bundle machine(const MachineOptions &o = {}) {
  std::vector<BundleSlot> publics{{"start", KB}, {"final", KB}};
  std::vector<BundleChannel> channels{
      {"range", BundleChannelKind::FieldBalance, {KB}, KB},
      {"trace", BundleChannelKind::Multiset, {KB, KB}, KB},
      {"spare", BundleChannelKind::FieldBalance, {KB}, KB}};
  Arena cpu;
  uint32_t x = cpu.read(KB, 0, 0), next = cpu.read(KB, 0, 1);
  uint32_t step = cpu.read(KB, 1, 0);
  uint32_t first = cpu.out(cpu.sub(x, cpu.pub(KB, 0)));
  uint32_t transition = cpu.out(cpu.sub(next, cpu.add(x, step)));
  uint32_t last = cpu.out(cpu.sub(x, cpu.pub(KB, 1)));
  uint32_t xOut = cpu.out(x), stepOut = cpu.out(step);
  uint32_t request = cpu.out(cpu.lit(KB, o.requestCount));
  uint32_t one = cpu.out(cpu.lit(KB, "1"));
  auto cpuTable = table("cpu", cpu,
                        {{"x", BundleAuthority::Witness, KB, 1},
                         {"step", BundleAuthority::Public, KB, 1}},
                        instanceHeight(1, 16, true));
  cpuTable.assertions = {{first, scope(BundleScopeKind::First)},
                         {transition, scope(BundleScopeKind::Interior, 0, 1)},
                         {last, scope(BundleScopeKind::Last)}};
  auto lookup =
      fieldBalance(o.rangeChannel, {o.stepInRangeTuple ? stepOut : xOut},
                   request, o.cpuLocality);
  lookup.bound = o.declared;
  cpuTable.interactions = {
      lookup, multiset(Trace, BundleSide::Push, {xOut, stepOut}, one, 1)};
  Arena rom;
  uint32_t entry = rom.out(rom.read(KB, 0, 0));
  uint32_t provided = rom.out(rom.neg(rom.read(KB, 1, 0)));
  auto romTable = table("rom", rom,
                        {{"values", BundleAuthority::Config, KB, 1},
                         {"multiplicity", BundleAuthority::Witness, KB, 1}},
                        fixedHeight(8));
  romTable.interactions = {
      fieldBalance(Range, {entry}, provided, o.romLocality)};
  Arena log;
  uint32_t a = log.out(log.read(KB, 0, 0, 0)),
           b = log.out(log.read(KB, 0, 0, 1));
  uint32_t once = log.out(log.lit(KB, "1"));
  auto logTable =
      table("log", log, {{"pairs", BundleAuthority::Witness, KB, 2}},
            instanceHeight(1, 16), BundleReadModel::Finite, true);
  logTable.interactions = {multiset(Trace, BundleSide::Pull, {a, b}, once, 1)};
  std::vector<BundleTable> tables;
  tables.push_back(std::move(cpuTable));
  tables.push_back(std::move(romTable));
  tables.push_back(std::move(logTable));
  return value(Bundle::create(std::move(publics), std::move(channels),
                              std::move(tables)),
               "machine");
}
static Data machineData(const Bundle &bundle) {
  auto d = data(bundle);
  // x = 0,1,3,6 with steps 1,2,3,9 (the last step is unused by the window).
  d.instance.publics = {{"0"}, {"6"}};
  d.instance.tables[0] = {true, 4, {column({1, 2, 3, 9})}};
  d.instance.tables[1] = {true, std::nullopt, {}};
  d.instance.tables[2] = {true, 4, {}};
  d.config.tables[1].groups = {column({0, 1, 2, 3, 4, 5, 6, 7})};
  d.witness.tables[0] = std::vector<BundleColumns>{column({0, 1, 3, 6})};
  d.witness.tables[1] =
      std::vector<BundleColumns>{column({1, 1, 0, 1, 0, 0, 1, 0})};
  d.witness.tables[2] =
      std::vector<BundleColumns>{column({3, 3, 0, 1, 6, 9, 1, 2})};
  return d;
}
static void machineTests() {
  auto bundle = machine();
  auto honest = evaluate(bundle, machineData(bundle), "honest machine");
  check(honest.satisfied && honest.rangeFailures.empty(), "honest machine");
  bool sawMultiset = false;
  for (const auto &b : honest.balances)
    if (b.kind == BundleChannelKind::Multiset)
      sawMultiset |= b.push == 1 && b.pull == 1 && b.balanced;
  check(sawMultiset, "multiset push/pull totals recorded");
  auto text = zkc::printJson(bundle.encode());
  check(value(readBundleText(text), "machine reread").identity() ==
            bundle.identity(),
        "machine codec round trip");

  auto refusesData = [&](std::function<void(Data &)> mutate, StringRef expected,
                         StringRef message) {
    auto d = machineData(bundle);
    mutate(d);
    refuses(bundle.admit(d.config, d.instance, d.witness), expected, message);
  };
  auto rejects = [&](std::function<void(Data &)> mutate, StringRef message) {
    auto d = machineData(bundle);
    mutate(d);
    check(!evaluate(bundle, d, message).satisfied, message);
  };
  // Authority: configuration-fixed values, instance-chosen heights and public
  // columns cannot be supplied or overridden by another party.
  rejects([](Data &d) { d.config.tables[1].groups[0][3] = "9"; },
          "configuration rom change unbalances the lookup");
  rejects([](Data &d) { d.instance.tables[0].groups[0][1] = "5"; },
          "public column change violates the transition");
  rejects([](Data &d) { d.instance.publics[1] = {"7"}; },
          "public final value change");
  refusesData([](Data &d) { d.config.tables[1].height = 8; },
              "bundle-height-authority",
              "configuration cannot choose a fixed height");
  refusesData([](Data &d) { d.instance.tables[1].height = 8; },
              "bundle-height-authority",
              "instance cannot override a fixed height");
  refusesData([](Data &d) { d.config.tables[0].height = 4; },
              "bundle-height-authority",
              "configuration cannot choose an instance height");
  refusesData([](Data &d) { d.instance.tables[0].height.reset(); },
              "bundle-height-authority", "instance height is required");
  refusesData(
      [](Data &d) {
        d.witness.tables[1]->insert(d.witness.tables[1]->begin(),
                                    column({0, 1, 2, 3, 4, 5, 6, 7}));
      },
      "bundle-group-count", "witness cannot supply configuration columns");
  refusesData(
      [](Data &d) { d.witness.tables[0]->push_back(column({1, 2, 3, 9})); },
      "bundle-group-count", "witness cannot supply public columns");
  refusesData(
      [](Data &d) { d.instance.tables[1].groups.push_back(column({1})); },
      "bundle-group-count", "instance cannot override configuration columns");
  refusesData([](Data &d) { d.config.tables[1].groups[0].pop_back(); },
              "bundle-group-shape", "configuration rom has its fixed height");
  refusesData([](Data &d) { d.witness.relation = std::string(64, '0'); },
              "bundle-relation", "witness for another relation");
  refusesData([](Data &d) { d.config.relation = std::string(64, '0'); },
              "bundle-relation", "configuration for another relation");
  // Presence and heights.
  refusesData([](Data &d) { d.instance.tables[0] = {false, std::nullopt, {}}; },
              "bundle-table-missing", "required table cannot be absent");
  refusesData([](Data &d) { d.instance.tables[2] = {false, std::nullopt, {}}; },
              "bundle-witness-presence", "absent table with witness data");
  refusesData(
      [](Data &d) {
        d.instance.tables[2] = {false, 4, {}};
        d.witness.tables[2].reset();
      },
      "bundle-absent-data", "absent table with a height");
  refusesData([](Data &d) { d.witness.tables[0].reset(); },
              "bundle-witness-presence", "present table without witness");
  refusesData(
      [](Data &d) {
        d.instance.tables[0].height = 3;
        d.instance.tables[0].groups[0].pop_back();
        d.witness.tables[0]->front().pop_back();
      },
      "bundle-height", "power-of-two height policy");
  refusesData([](Data &d) { d.instance.tables[0].height = 32; },
              "bundle-height", "height above the declared maximum");
  refusesData([](Data &d) { d.witness.tables[0]->front().pop_back(); },
              "bundle-group-shape", "witness height mismatch");
  refusesData([](Data &d) { d.instance.tables[0].groups[0].push_back("1"); },
              "bundle-group-shape", "public column height mismatch");
  refusesData([](Data &d) { d.instance.tables[2].height = 3; },
              "bundle-group-shape", "optional table height mismatch");
  refusesData([](Data &d) { d.instance.publics.pop_back(); },
              "bundle-public-shape", "public slot count");
  refusesData([](Data &d) { d.witness.tables.pop_back(); }, "bundle-data-shape",
              "table count");
  {
    // Optional absence removes the table's rows: its pulls disappear, so the
    // cpu's pushes are unmatched. It is never read as required-missing.
    auto d = machineData(bundle);
    d.instance.tables[2] = {false, std::nullopt, {}};
    d.witness.tables[2].reset();
    auto result = evaluate(bundle, d, "absent log");
    unsigned unmatched = 0;
    for (const auto &b : result.balances)
      unmatched += b.kind == BundleChannelKind::Multiset && b.push == 1 &&
                   b.pull == 0 && !b.balanced;
    check(!result.satisfied && unmatched == 4,
          "optional absence contributes nothing");
  }
  {
    // A heavier trace of 8 rows still balances when every party agrees.
    auto d = machineData(bundle);
    d.instance.publics = {{"0"}, {"7"}};
    d.instance.tables[0] = {true, 8, {column({1, 1, 1, 1, 1, 1, 1, 0})}};
    d.witness.tables[0] =
        std::vector<BundleColumns>{column({0, 1, 2, 3, 4, 5, 6, 7})};
    d.witness.tables[1] =
        std::vector<BundleColumns>{column({1, 1, 1, 1, 1, 1, 1, 1})};
    d.instance.tables[2] = {true, 8, {}};
    d.witness.tables[2] = std::vector<BundleColumns>{
        column({0, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 6, 1, 7, 0})};
    check(evaluate(bundle, d, "eight rows").satisfied, "eight-row machine");
  }

  // Interaction meanings: channel, locality, tuple and weight mutations.
  auto evaluateWith = [&](
                          MachineOptions o,
                          std::function<void(Data &)> mutate = [](Data &) {}) {
    auto variant = machine(o);
    auto d = machineData(variant);
    mutate(d);
    return evaluate(variant, d, "variant");
  };
  MachineOptions o;
  o.rangeChannel = Spare;
  check(!evaluateWith(o).satisfied, "requests moved to another channel");
  o = {};
  o.rangeChannel = Trace;
  refuses(Bundle::create({{"start", KB}, {"final", KB}},
                         machine().channels().vec(),
                         [&] {
                           auto b = machine();
                           std::vector<BundleTable> tables(b.tables().begin(),
                                                           b.tables().end());
                           tables[0].interactions[0].channel = Trace;
                           return tables;
                         }()),
          "bundle-interaction-kind", "field balance on a multiset channel");
  o = {};
  o.cpuLocality = {true, 0};
  o.romLocality = {true, 0};
  check(!evaluateWith(o).satisfied, "local scopes do not cancel across tables");
  o = {};
  o.cpuLocality = {true, 0};
  check(!evaluateWith(o).satisfied, "local request against global provider");
  o = {};
  o.stepInRangeTuple = true;
  check(!evaluateWith(o).satisfied, "tuple mutation");
  o = {};
  o.requestCount = "2";
  check(!evaluateWith(o).satisfied, "weight mutation");
  check(evaluateWith(o,
                     [](Data &d) {
                       d.witness.tables[1] = std::vector<BundleColumns>{
                           column({2, 2, 0, 2, 0, 0, 2, 0})};
                     })
            .satisfied,
        "field weights balance with matching provider counts");
  o = {};
  o.declared = 1;
  auto declared = machine(o);
  check(declared.identity() != bundle.identity() &&
            evaluateWith(o).satisfied == honest.satisfied,
        "declared count bound is a recorded premise, not satisfaction");
  // A provider count p-1 is the field element -1: two requests against a
  // provider of -1 and a direct +1 contribution balance in the field.
  check(evaluateWith({},
                     [](Data &d) {
                       d.witness.tables[1] = std::vector<BundleColumns>{
                           column({1, 1, 0, 1, 0, 0, 1, 0})};
                     })
            .satisfied,
        "baseline field balance");
}

//===----------------------------------------------------------------------===//
// Natural multiplicities versus field weights
//===----------------------------------------------------------------------===//
static Bundle counts(BundleChannelKind kind, uint64_t bound = 3,
                     std::string countField = KB) {
  std::vector<BundleChannel> channels{{"bus", kind, {KB}, countField}};
  Arena arena;
  uint32_t t = arena.out(arena.read(KB, 0, 0, 0));
  uint32_t c = arena.read(KB, 0, 0, 1);
  if (countField != KB)
    c = arena.embed(countField, c);
  uint32_t count = arena.out(c);
  auto push = table("push", arena, {{"rows", BundleAuthority::Witness, KB, 2}},
                    instanceHeight(1, 8));
  auto pull = table("pull", arena, {{"rows", BundleAuthority::Witness, KB, 2}},
                    instanceHeight(1, 8));
  if (kind == BundleChannelKind::Multiset) {
    push.interactions = {multiset(0, BundleSide::Push, {t}, count, bound)};
    pull.interactions = {multiset(0, BundleSide::Pull, {t}, count, bound)};
  } else {
    push.interactions = {fieldBalance(0, {t}, count)};
    pull.interactions = {fieldBalance(0, {t}, count)};
  }
  std::vector<BundleTable> tables;
  tables.push_back(std::move(push));
  tables.push_back(std::move(pull));
  return value(Bundle::create({}, std::move(channels), std::move(tables)),
               "counts");
}
static BundleEvaluation countRows(const Bundle &bundle,
                                  std::vector<std::string> push,
                                  std::vector<std::string> pull) {
  auto d = data(bundle);
  auto rows = [](std::vector<std::string> cells) {
    return std::vector<BundleColumns>{cells};
  };
  d.instance.tables[0] = {true, uint32_t(push.size() / 2), {}};
  d.instance.tables[1] = {true, uint32_t(pull.size() / 2), {}};
  d.witness.tables[0] = rows(push);
  d.witness.tables[1] = rows(pull);
  return evaluate(bundle, d, "counts");
}
static void countTests() {
  auto field = counts(BundleChannelKind::FieldBalance);
  auto natural = counts(BundleChannelKind::Multiset);
  // Field weights: -1 and +1 cancel; p-1 is never a natural count.
  check(countRows(field, {"5", P_MINUS_ONE}, {"5", "1"}).satisfied,
        "field weights p-1 and 1 cancel");
  auto wrapped = countRows(natural, {"5", P_MINUS_ONE}, {"5", "1"});
  check(!wrapped.satisfied && wrapped.rangeFailures.size() == 1 &&
            wrapped.rangeFailures[0].table == 0,
        "multiset multiplicity p-1 is a range failure, not -1");
  check(countRows(natural, {"5", "2"}, {"5", "1", "5", "1"}).satisfied,
        "natural push 2 equals two pulls of 1");
  check(!countRows(natural, {"5", "2"}, {"5", "1"}).satisfied,
        "natural imbalance");
  check(countRows(natural, {"5", "3"}, {"5", "3"}).satisfied,
        "multiplicity at the bound");
  auto over = countRows(natural, {"5", "4"}, {"5", "4"});
  check(!over.satisfied && over.rangeFailures.size() == 2,
        "multiplicity above the bound fails on both sides");
  check(!countRows(natural, {"5", "1"}, {"6", "1"}).satisfied,
        "tuple mismatch is an imbalance");
  check(countRows(field, {"5", "2"}, {"5", "1", "5", "1"}).satisfied == false,
        "field balance sums signs: two positive contributions do not cancel");
  check(countRows(field, {"5", "0"}, {"6", "0"}).satisfied,
        "zero field weights balance");
  refuses(
      Bundle::create({}, {{"bus", BundleChannelKind::Multiset, {KB}, EXT}}, {}),
      "bundle-tables", "a bundle needs a table");
  refuses(Bundle::create({}, {{"bus", BundleChannelKind::Multiset, {KB}, EXT}},
                         [] {
                           std::vector<BundleTable> t;
                           t.push_back(table("t", Arena{}, {}, fixedHeight(1)));
                           return t;
                         }()),
          "bundle-multiset-field", "multiset counts are prime-field naturals");
  for (uint64_t bound :
       {uint64_t(0), uint64_t(2130706433), uint64_t(1) << 33}) {
    std::vector<BundleChannel> channels{
        {"bus", BundleChannelKind::Multiset, {KB}, KB}};
    Arena arena;
    uint32_t t = arena.out(arena.read(KB, 0, 0));
    auto rows = table("t", arena, {{"rows", BundleAuthority::Witness, KB, 1}},
                      fixedHeight(1));
    rows.interactions = {multiset(0, BundleSide::Push, {t}, t, bound)};
    std::vector<BundleTable> tables;
    tables.push_back(std::move(rows));
    refuses(Bundle::create({}, channels, std::move(tables)),
            "bundle-multiset-bound", "multiset bound in [1, p)");
  }
}

//===----------------------------------------------------------------------===//
// Signed finite and cyclic windows
//===----------------------------------------------------------------------===//
static Expected<Bundle> window(BundleReadModel model, BundleScope s,
                               int32_t offset, BundleHeight height,
                               bool hidden = false) {
  // x[r + offset] - y[r] = 0, optionally hidden as 0 * x[r + offset].
  Arena arena;
  uint32_t x = arena.read(KB, 0, offset), y = arena.read(KB, 1, 0);
  uint32_t lhs = hidden ? arena.mul(arena.lit(KB, "0"), x) : x;
  uint32_t out =
      arena.out(hidden ? arena.add(lhs, arena.mul(y, arena.lit(KB, "0")))
                       : arena.sub(lhs, y));
  auto t = table("w", arena,
                 {{"x", BundleAuthority::Witness, KB, 1},
                  {"y", BundleAuthority::Witness, KB, 1}},
                 height, model);
  t.assertions = {{out, s}};
  std::vector<BundleTable> tables;
  tables.push_back(std::move(t));
  return Bundle::create({}, {}, std::move(tables));
}
static Error windowData(const Bundle &bundle, std::vector<uint64_t> x,
                        std::vector<uint64_t> y, bool *satisfied) {
  auto d = data(bundle);
  d.instance.tables[0] = {true, uint32_t(x.size()), {}};
  d.witness.tables[0] = std::vector<BundleColumns>{column(x), column(y)};
  auto result = bundle.evaluate(d.config, d.instance, d.witness);
  if (!result)
    return result.takeError();
  *satisfied = result->satisfied;
  return Error::success();
}
static void windowTests() {
  using K = BundleScopeKind;
  auto h = instanceHeight(1, 8);
  // Finite windows undefined at every height refuse at formation; 0 * read
  // cannot hide the read.
  refuses(window(BundleReadModel::Finite, scope(K::All), 1, h), "bundle-window",
          "all-rows next read");
  refuses(window(BundleReadModel::Finite, scope(K::All), -1, h),
          "bundle-window", "all-rows previous read");
  refuses(window(BundleReadModel::Finite, scope(K::All), 1, h, true),
          "bundle-window", "zero product does not hide a read");
  refuses(window(BundleReadModel::Finite, scope(K::First), -1, h),
          "bundle-window", "first-row previous read");
  refuses(window(BundleReadModel::Finite, scope(K::Last), 1, h),
          "bundle-window", "last-row next read");
  refuses(window(BundleReadModel::Finite, scope(K::Interior, 0, 0), -1, h),
          "bundle-window", "interior without left margin");
  refuses(window(BundleReadModel::Finite, scope(K::Interior, 0, 1), 2, h),
          "bundle-window", "interior right margin too small");
  // Signed windows inside their margins.
  bool ok = false;
  auto previous =
      value(window(BundleReadModel::Finite, scope(K::Interior, 1, 0), -1, h),
            "previous");
  check(!windowData(previous, {4, 5, 6}, {9, 4, 5}, &ok) && ok,
        "previous-row read on interior(1,0)");
  check(!windowData(previous, {4, 5, 6}, {9, 4, 4}, &ok) && !ok,
        "previous-row violation");
  auto next = value(
      window(BundleReadModel::Finite, scope(K::Interior, 0, 1), 1, h), "next");
  check(!windowData(next, {4, 5, 6}, {5, 6, 0}, &ok) && ok,
        "next-row read leaves the last row unconstrained");
  // Height-dependent windows refuse at admission.
  auto firstAhead = value(
      window(BundleReadModel::Finite, scope(K::First), 2, h), "first ahead");
  refuses(windowData(firstAhead, {1, 2}, {3, 0}, &ok), "bundle-window",
          "first-row read beyond a short table");
  check(!windowData(firstAhead, {1, 2, 3}, {3, 0, 0}, &ok) && ok,
        "first-row read on a long enough table");
  auto lastBehind = value(
      window(BundleReadModel::Finite, scope(K::Last), -2, h), "last behind");
  refuses(windowData(lastBehind, {1, 2}, {0, 1}, &ok), "bundle-window",
          "last-row read before a short table");
  auto interval =
      value(window(BundleReadModel::Finite, scope(K::Interval, 0, 3), 1, h),
            "interval");
  refuses(windowData(interval, {1, 2, 3}, {2, 3, 0}, &ok), "bundle-window",
          "interval next read at its end");
  check(!windowData(interval, {1, 2, 3, 4}, {2, 3, 4, 0}, &ok) && ok,
        "interval next read with room");
  auto far = value(
      window(BundleReadModel::Finite, scope(K::Interval, 2, 6), 0, h), "far");
  refuses(windowData(far, {1, 2, 3, 4}, {1, 2, 3, 4}, &ok),
          "bundle-scope-height", "interval beyond the table");
  check(!windowData(far, {1, 2, 3, 4, 5, 6}, {0, 0, 3, 4, 5, 6}, &ok) && ok,
        "interval inside the table");
  // Cyclic windows wrap modulo the actual height in both directions.
  auto rotate =
      value(window(BundleReadModel::Cyclic, scope(K::All), 1, h), "rotate");
  check(!windowData(rotate, {1, 2, 3, 4}, {2, 3, 4, 1}, &ok) && ok,
        "cyclic next read wraps to row zero");
  check(!windowData(rotate, {1, 2, 3, 4}, {2, 3, 4, 0}, &ok) && !ok,
        "wraparound mistake detected");
  auto back =
      value(window(BundleReadModel::Cyclic, scope(K::All), -1, h), "back");
  check(!windowData(back, {1, 2, 3, 4}, {4, 1, 2, 3}, &ok) && ok,
        "cyclic previous read wraps to the last row");
  check(!windowData(back, {1, 2, 3, 4}, {2, 3, 4, 1}, &ok) && !ok,
        "direction mistake detected");
  check(!windowData(back, {7}, {7}, &ok) && ok,
        "cyclic singleton reads itself");
  auto far5 =
      value(window(BundleReadModel::Cyclic, scope(K::All), 5, h), "far5");
  check(!windowData(far5, {1, 2, 3}, {3, 1, 2}, &ok) && ok,
        "cyclic offset beyond the height reduces modulo the height");
}

//===----------------------------------------------------------------------===//
// Mixed base/extension values
//===----------------------------------------------------------------------===//
static void extensionTests() {
  // X^8 = 3 in the ascending basis; e - embed(b) - public = 0.
  Arena arena;
  uint32_t e = arena.read(EXT, 0, 0);
  uint32_t power = e;
  for (int i = 0; i < 3; ++i)
    power = arena.mul(power, power);
  uint32_t eighth =
      arena.out(arena.sub(power, arena.embed(EXT, arena.lit(KB, "3"))));
  uint32_t shift = arena.out(arena.sub(
      arena.read(EXT, 1, 0),
      arena.add(arena.embed(EXT, arena.read(KB, 2, 0)), arena.pub(EXT, 0))));
  auto t = table("ext", arena,
                 {{"generator", BundleAuthority::Witness, EXT, 1},
                  {"sum", BundleAuthority::Witness, EXT, 1},
                  {"base", BundleAuthority::Witness, KB, 1}},
                 fixedHeight(1));
  t.assertions = {{eighth, scope(BundleScopeKind::All)},
                  {shift, scope(BundleScopeKind::All)}};
  std::vector<BundleTable> tables;
  tables.push_back(std::move(t));
  auto bundle = value(Bundle::create({{"offset", EXT}}, {}, std::move(tables)),
                      "extension");
  auto d = data(bundle);
  d.instance.publics = {{"1", "2", "3", "4", "5", "6", "7", "8"}};
  d.instance.tables[0] = {true, std::nullopt, {}};
  d.witness.tables[0] =
      std::vector<BundleColumns>{{"0", "1", "0", "0", "0", "0", "0", "0"},
                                 {"11", "2", "3", "4", "5", "6", "7", "8"},
                                 {"10"}};
  check(evaluate(bundle, d, "extension").satisfied,
        "extension multiplication and base embedding");
  auto bad = d;
  (*bad.witness.tables[0])[0] = {"0", "0", "1", "0", "0", "0", "0", "0"};
  check(!evaluate(bundle, bad, "bad generator").satisfied,
        "X^2 has eighth power 9");
  auto text = zkc::printJson(encodeBundleWitness(bundle, d.witness));
  auto reread =
      value(readBundleWitness(bundle, value(readBundleDataJson(text), "json")),
            "ext witness");
  check(reread.tables == d.witness.tables, "extension witness codec");
  auto wrong = text;
  wrong.replace(wrong.find("[\"0\",\"1\""), 1, "[\"0\",");
  refuses(readBundleWitness(bundle, value(readBundleDataJson(wrong), "json")),
          "bundle-value", "extension element with nine coordinates");
}

//===----------------------------------------------------------------------===//
// Staged challenge-dependent program
//===----------------------------------------------------------------------===//
static const uint64_t P = 2130706433;
static uint64_t mulmod(uint64_t a, uint64_t b) { return a % P * (b % P) % P; }
static uint64_t inverse(uint64_t a) {
  uint64_t result = 1, base = a % P;
  for (uint64_t e = P - 2; e; e >>= 1, base = mulmod(base, base))
    if (e & 1)
      result = mulmod(result, base);
  return result;
}
/// A LogUp-style staged program for the machine's range lookup: phase 1 draws
/// alpha, commits per-row inverses and running sums, and receives the two
/// table sums as claims. It is a separate subject from the machine relation.
static Expected<StagedProgram> logup(const Bundle &bundle,
                                     bool readLater = false,
                                     bool challengeLater = false,
                                     bool globalRead = false) {
  // Inputs are written directly because staged bindings have phases.
  auto build = [&](bool rom) {
    std::vector<zkc::ring::Input> inputs;
    std::vector<StagedInput> bindings;
    std::vector<zkc::ring::Node> nodes;
    auto in = [&](StagedInput b) {
      inputs.push_back({KB});
      bindings.push_back(b);
      nodes.push_back(zkc::ring::Node::slot(inputs.size() - 1));
      return uint32_t(nodes.size() - 1);
    };
    auto push = [&](zkc::ring::Node n) {
      nodes.push_back(std::move(n));
      return uint32_t(nodes.size() - 1);
    };
    using SK = StagedInput::Kind;
    uint32_t alpha = in({SK::Challenge, challengeLater ? 2u : 1u, 0, 0, 0});
    uint32_t entry = in({SK::Read, 0, 0, 0, 0});
    uint32_t inv = in({SK::Read, readLater ? 2u : 1u, 0, 0, 0});
    uint32_t acc = in({SK::Read, 1, 1, 0, 0});
    uint32_t accNext = in({SK::Read, 1, 1, 1, 0});
    uint32_t invNext = in({SK::Read, 1, 0, 1, 0});
    uint32_t claim = in({SK::Claim, 1, rom ? 1u : 0u, 0, 0});
    uint32_t denominator =
        push(zkc::ring::Node::add(alpha, push(zkc::ring::Node::neg(entry))));
    uint32_t product = push(zkc::ring::Node::mul(inv, denominator));
    uint32_t numerator;
    if (rom) // inv * (alpha - v) + multiplicity = 0
      numerator = in({SK::Read, 0, 1, 0, 0});
    else
      numerator =
          push(zkc::ring::Node::neg(push(zkc::ring::Node::literal(KB, "1"))));
    uint32_t term = push(zkc::ring::Node::add(product, numerator));
    uint32_t start =
        push(zkc::ring::Node::add(acc, push(zkc::ring::Node::neg(inv))));
    uint32_t step = push(zkc::ring::Node::add(
        accNext,
        push(zkc::ring::Node::neg(push(zkc::ring::Node::add(acc, invNext))))));
    uint32_t end =
        push(zkc::ring::Node::add(acc, push(zkc::ring::Node::neg(claim))));
    std::vector<uint32_t> outputs{term, start, step, end, denominator};
    auto arena = value(zkc::ring::Expression::create(inputs, nodes, outputs),
                       "staged arena");
    return StagedTable{{{"inverse", KB, 1}, {"sum", KB, 1}},
                       std::move(arena),
                       bindings,
                       {{0, scope(BundleScopeKind::All)},
                        {1, scope(BundleScopeKind::First)},
                        {2, scope(BundleScopeKind::Interior, 0, 1)},
                        {3, scope(BundleScopeKind::Last)}}};
  };
  auto emptyTable = [] {
    return StagedTable{
        {}, value(zkc::ring::Expression::create({}, {}, {}), "empty"), {}, {}};
  };
  std::vector<StagedPhase> phases;
  StagedPhase one{{{"alpha", KB}}, {{"cpu_sum", KB}, {"rom_sum", KB}}, {}};
  one.tables.push_back(build(false));
  one.tables.push_back(build(true));
  one.tables.push_back(emptyTable());
  phases.push_back(std::move(one));
  if (readLater || challengeLater) {
    StagedPhase two{{{"beta", KB}}, {}, {}};
    for (int i = 0; i < 3; ++i)
      two.tables.push_back(
          StagedTable{i == 0 ? std::vector<StagedGroup>{{"later", KB, 1}}
                             : std::vector<StagedGroup>{},
                      value(zkc::ring::Expression::create({}, {}, {}), "empty"),
                      {},
                      {}});
    phases.push_back(std::move(two));
  }
  // Global: cpu_sum + rom_sum = 0.
  std::vector<StagedInput> globalInputs{
      {StagedInput::Kind::Claim, 1, 0, 0, 0},
      {globalRead ? StagedInput::Kind::Read : StagedInput::Kind::Claim, 1,
       globalRead ? 0u : 1u, 0, 0}};
  auto global = value(zkc::ring::Expression::create(
                          {{KB}, {KB}},
                          {zkc::ring::Node::slot(0), zkc::ring::Node::slot(1),
                           zkc::ring::Node::add(0, 1)},
                          {2}),
                      "global");
  std::vector<StagedPremise> premises{
      {StagedPremise::Kind::Nonzero,
       1,
       0,
       {4},
       scope(BundleScopeKind::All),
       "",
       0},
      {StagedPremise::Kind::Nonzero,
       1,
       1,
       {4},
       scope(BundleScopeKind::All),
       "",
       0},
      {StagedPremise::Kind::CharacteristicExceeds, 0, 0, {}, {}, KB, 64}};
  return StagedProgram::create(bundle, std::move(phases),
                               {std::move(global), globalInputs, {0}},
                               std::move(premises));
}
static StagedAssignment logupData(const StagedProgram &program, uint64_t alpha,
                                  const Data &d) {
  auto rows = [&](const BundleColumns &values, const BundleColumns *mult,
                  uint64_t &total) {
    BundleColumns inv, acc;
    total = 0;
    for (size_t i = 0; i < values.size(); ++i) {
      uint64_t v = std::stoull(values[i]);
      uint64_t numerator = mult ? (P - std::stoull((*mult)[i])) % P : 1;
      uint64_t term = mulmod(numerator, inverse((alpha + P - v) % P));
      total = (total + term) % P;
      inv.push_back(std::to_string(term));
      acc.push_back(std::to_string(total));
    }
    return std::vector<BundleColumns>{inv, acc};
  };
  uint64_t cpuTotal = 0, romTotal = 0;
  StagedAssignment a;
  a.program = program.identity();
  StagedAssignment::Phase phase;
  phase.challenges = {{std::to_string(alpha)}};
  phase.tables.push_back(rows(d.witness.tables[0]->front(), nullptr, cpuTotal));
  phase.tables.push_back(rows(d.config.tables[1].groups[0],
                              &d.witness.tables[1]->front(), romTotal));
  phase.tables.push_back(std::vector<BundleColumns>{});
  phase.claims = {{std::to_string(cpuTotal)}, {std::to_string(romTotal)}};
  a.phases.push_back(std::move(phase));
  return a;
}
static void stagedTests() {
  auto bundle = machine();
  auto d = machineData(bundle);
  auto program = value(logup(bundle), "logup");
  auto honest = logupData(program, 1000, d);
  auto result =
      value(program.evaluate(bundle, d.config, d.instance, d.witness, honest),
            "staged honest");
  check(result.satisfied && result.global.size() == 1 &&
            result.global[0] == BundleColumns{"0"},
        "honest staged predicate");
  // The predicate is indexed by the actual challenge: the same auxiliary
  // columns do not satisfy it for another challenge value.
  auto other = honest;
  other.phases[0].challenges = {{"1001"}};
  check(!value(program.evaluate(bundle, d.config, d.instance, d.witness, other),
               "other challenge")
             .satisfied,
        "auxiliary values are challenge-indexed");
  check(value(program.evaluate(bundle, d.config, d.instance, d.witness,
                               logupData(program, 1001, d)),
              "recomputed")
            .satisfied,
        "recomputed auxiliary values for another challenge");
  auto claim = honest;
  claim.phases[0].claims[0] = {"5"};
  auto claimResult =
      value(program.evaluate(bundle, d.config, d.instance, d.witness, claim),
            "claim");
  check(!claimResult.satisfied, "received claim is checked as sent");
  // The deterministic relation is unchanged by the staged program: same
  // identity, and evaluation takes no challenge.
  check(evaluate(bundle, d, "base").satisfied &&
            machine().identity() == bundle.identity(),
        "bundle meaning independent of the staged program");
  // A machine whose lookup is unbalanced stays unsatisfied as a bundle even
  // when a staged assignment for some challenge happens to pass its checks.
  auto unbalanced = d;
  unbalanced.witness.tables[1] =
      std::vector<BundleColumns>{column({1, 1, 0, 1, 0, 0, 0, 1})};
  check(!evaluate(bundle, unbalanced, "unbalanced").satisfied,
        "unbalanced machine relation");
  auto text = zkc::printJson(program.encode());
  auto reread = value(
      readStagedProgram(
          bundle,
          value(zkc::parseNaturalJson(text, BundleLimits::bytes, 16, "x", "y"),
                "staged json")),
      "staged reread");
  check(reread.identity() == program.identity(), "staged codec round trip");
  auto assignmentText =
      zkc::printJson(encodeStagedAssignment(bundle, program, honest));
  auto rereadAssignment =
      value(readStagedAssignment(
                bundle, program,
                value(readBundleDataJson(assignmentText), "assignment json")),
            "assignment reread");
  check(value(program.evaluate(bundle, d.config, d.instance, d.witness,
                               rereadAssignment),
              "reread assignment")
            .satisfied,
        "staged assignment codec round trip");
  // Phase order and leakage.
  refuses(logup(bundle, true), "staged-phase-order",
          "phase one cannot read a phase-two group");
  refuses(logup(bundle, false, true), "staged-phase-order",
          "phase one cannot use a phase-two challenge");
  refuses(logup(bundle, false, false, true), "staged-global-read",
          "global checks are scalar");
  auto absent = d;
  absent.instance.tables[2] = {false, std::nullopt, {}};
  absent.witness.tables[2].reset();
  refuses(program.evaluate(bundle, absent.config, absent.instance,
                           absent.witness, honest),
          "staged-presence", "staged data for an absent table");
  auto forged = honest;
  forged.program = std::string(64, '0');
  refuses(program.evaluate(bundle, d.config, d.instance, d.witness, forged),
          "staged-program", "assignment for another staged program");
  // A deterministic bundle cannot name a challenge, claim or selector.
  auto encoded = zkc::printJson(bundle.encode());
  for (StringRef kind : {"challenge", "claim", "selector"}) {
    auto leaked = encoded;
    auto at = leaked.find("[\"public\",0]");
    leaked.replace(at, 12, "[\"" + kind.str() + "\",1,0]");
    refuses(readBundleText(leaked), "bundle-input-kind",
            "deterministic input kinds are closed");
  }
}

//===----------------------------------------------------------------------===//
// Formation, schema and resource preflight
//===----------------------------------------------------------------------===//
static Expected<Bundle>
single(Arena arena, std::vector<BundleGroup> groups,
       std::vector<BundleAssertion> assertions,
       BundleHeight height = {BundleHeightAuthority::Instance, 1, 8, false},
       std::vector<BundleSlot> publics = {}) {
  std::vector<BundleTable> tables;
  tables.push_back(table("t", arena, std::move(groups), height));
  tables.back().assertions = std::move(assertions);
  return Bundle::create(std::move(publics), {}, std::move(tables));
}
static void formationTests() {
  using K = BundleScopeKind;
  std::vector<BundleGroup> one{{"x", BundleAuthority::Witness, KB, 1}};
  auto x = [] {
    Arena a;
    a.out(a.read(KB, 0, 0));
    return a;
  };
  check(bool(single(x(), one, {{0, scope(K::All)}})), "minimal bundle");
  refuses(single(x(), one, {}), "bundle-unused-output", "unreferenced output");
  {
    Arena a = x();
    a.inputs.push_back({KB});
    a.bindings.push_back(BundleInput::read(0, 1, 0));
    refuses(single(a, one, {{0, scope(K::All)}}), "bundle-unused-input",
            "unused binding");
  }
  {
    Arena a;
    a.inputs = {{KB}, {KB}};
    a.bindings = {BundleInput::read(0, 0, 0), BundleInput::read(0, 0, 0)};
    a.nodes = {zkc::ring::Node::slot(0), zkc::ring::Node::slot(1),
               zkc::ring::Node::add(0, 1)};
    a.outputs = {2};
    refuses(single(a, one, {{0, scope(K::All)}}), "bundle-duplicate-input",
            "duplicate binding");
  }
  {
    Arena a;
    a.out(a.read(EXT, 0, 0));
    refuses(single(a, one, {{0, scope(K::All)}}), "bundle-input-field",
            "binding field differs from its group");
  }
  {
    Arena a;
    a.out(a.read(KB, 1, 0));
    refuses(single(a, one, {{0, scope(K::All)}}), "bundle-input",
            "unknown group");
    Arena b;
    b.out(b.read(KB, 0, 0, 1));
    refuses(single(b, one, {{0, scope(K::All)}}), "bundle-input",
            "unknown column");
    Arena c;
    c.out(c.pub(KB, 0));
    refuses(single(c, one, {{0, scope(K::All)}}), "bundle-input",
            "unknown public");
    Arena e;
    e.out(e.read(KB, 0, int32_t(BundleLimits::offset) + 1));
    refuses(single(e, one, {{0, scope(K::Interior, 0, BundleLimits::height)}}),
            "bundle-input", "offset beyond limit");
  }
  refuses(single(x(), {{"x", BundleAuthority::Config, KB, 1}},
                 {{0, scope(K::All)}}),
          "bundle-config-height", "configuration data needs a known height");
  check(bool(single(x(), {{"x", BundleAuthority::Config, KB, 1}},
                    {{0, scope(K::All)}}, fixedHeight(4))),
        "configuration data with a fixed height");
  refuses(single(x(), {{"x", BundleAuthority::Witness, KB, 0}},
                 {{0, scope(K::All)}}),
          "bundle-width", "zero width");
  refuses(single(x(), {{"x", BundleAuthority::Witness, "unknown", 1}},
                 {{0, scope(K::All)}}),
          "bundle-field", "unknown field");
  refuses(single(x(), one, {{0, scope(K::All)}},
                 {BundleHeightAuthority::Instance, 0, 4}),
          "bundle-height", "zero minimum height");
  refuses(
      single(x(), one, {{0, scope(K::All)}},
             {BundleHeightAuthority::Instance, 1, BundleLimits::height + 1}),
      "bundle-height", "maximum above limit");
  refuses(single(x(), one, {{0, scope(K::All)}},
                 {BundleHeightAuthority::Instance, 5, 7, true}),
          "bundle-height", "no power of two in range");
  refuses(single(x(), one, {{0, scope(K::All)}},
                 {BundleHeightAuthority::Fixed, 2, 3}),
          "bundle-height", "fixed height range");
  refuses(single(x(), one, {{0, scope(K::Interval, 3, 2)}}), "bundle-scope",
          "reversed interval");
  refuses(single(x(), one, {{0, scope(K::First, 1)}}), "bundle-scope",
          "first with parameters");
  refuses(single(x(),
                 {{"x", BundleAuthority::Witness, KB, 1},
                  {"x", BundleAuthority::Witness, KB, 1}},
                 {{0, scope(K::All)}}),
          "bundle-duplicate-name", "duplicate group names");
  refuses(single(x(), {{"", BundleAuthority::Witness, KB, 1}},
                 {{0, scope(K::All)}}),
          "bundle-name", "empty name");
  refuses(single(x(), one, {{0, scope(K::All)}},
                 {BundleHeightAuthority::Instance, 1, 8},
                 {{"p", KB}, {"p", KB}}),
          "bundle-duplicate-name", "duplicate public names");
  {
    std::vector<BundleTable> tables;
    for (uint32_t i = 0; i <= BundleLimits::tables; ++i)
      tables.push_back(
          table("t" + std::to_string(i), Arena{}, {}, fixedHeight(1)));
    refuses(Bundle::create({}, {}, std::move(tables)), "bundle-limit",
            "table count");
  }
  // Text schema: exact arity, closed tags, canonical signed offsets.
  auto bundle = value(single(x(), one, {{0, scope(K::All)}}), "schema base");
  auto text = zkc::printJson(bundle.encode());
  auto mutate = [&](StringRef from, StringRef to) {
    auto result = text;
    auto at = result.find(from.str());
    if (at == std::string::npos) {
      errs() << "fixture lacks " << from << '\n';
      std::exit(1);
    }
    result.replace(at, from.size(), to.str());
    return result;
  };
  refuses(
      readBundleText(mutate("zkc.relation-bundle/0", "zkc.relation-bundle/1")),
      "bundle-schema", "version tag");
  refuses(readBundleText(mutate("\"finite\"", "\"finite\",0")), "bundle-schema",
          "extra table field");
  refuses(readBundleText(mutate("[\"all\"]", "[\"all\",0]")), "bundle-scope",
          "scope arity");
  refuses(readBundleText(mutate("[\"all\"]", "[\"every\"]")), "bundle-scope",
          "unknown scope");
  for (StringRef offset : {"+0", "-0", "01", "65537", "1.0", ""})
    refuses(readBundleText(mutate("\"read\",0,\"0\"",
                                  ("\"read\",0,\"" + offset + "\"").str())),
            "bundle-input", "noncanonical signed offset");
  refuses(readBundleText(mutate("\"read\",0,\"0\",0", "\"read\",0,0,0")),
          "bundle-input", "offset must be a signed decimal string");
  refuses(readBundleText(
              mutate("[\"instance\",1,8,false]", "[\"instance\",01,8,false]")),
          "bundle-schema", "noncanonical JSON natural");
  refuses(readBundleText(mutate("\"witness\"", "\"prover\"")), "bundle-schema",
          "unknown authority");
}
static void preflightTests() {
  using K = BundleScopeKind;
  // Read domains are refused before any value is parsed.
  auto shifted = value(
      window(BundleReadModel::Finite, scope(K::First), 2, instanceHeight(1, 8)),
      "shifted");
  auto d = data(shifted);
  d.instance.tables[0] = {true, 2, {}};
  d.witness.tables[0] = std::vector<BundleColumns>{{"01", "1"}, {"0", "0"}};
  refuses(shifted.admit(d.config, d.instance, d.witness), "bundle-window",
          "window refusal precedes value parsing");
  // Work is bounded from heights and arena size before parsing or evaluation.
  Arena chain;
  uint32_t node = chain.read(KB, 0, 0);
  for (int i = 0; i < 70; ++i)
    node = chain.add(node, node);
  chain.out(node);
  auto heavy = value(single(chain, {{"x", BundleAuthority::Witness, KB, 1}},
                            {{0, scope(K::All)}},
                            instanceHeight(1, BundleLimits::height)),
                     "heavy");
  auto h = data(heavy);
  h.instance.tables[0] = {true, BundleLimits::height, {}};
  h.witness.tables[0] =
      std::vector<BundleColumns>{BundleColumns(BundleLimits::height, "x")};
  refuses(heavy.admit(h.config, h.instance, h.witness), "bundle-work-limit",
          "work preflight precedes value parsing");
  h.instance.tables[0].height = 1u << 16;
  h.witness.tables[0] =
      std::vector<BundleColumns>{BundleColumns(1u << 16, "0")};
  check(!heavy.admit(h.config, h.instance, h.witness),
        "the same arena within the work limit");
  // Contribution count is bounded before balance maps are built.
  std::vector<BundleChannel> channels{
      {"bus", BundleChannelKind::FieldBalance, {}, KB}};
  Arena many;
  uint32_t c = many.out(many.read(KB, 0, 0));
  std::vector<BundleTable> tables;
  tables.push_back(table("t", many, {{"x", BundleAuthority::Witness, KB, 1}},
                         instanceHeight(1, BundleLimits::height)));
  for (int i = 0; i < 5; ++i)
    tables.back().interactions.push_back(fieldBalance(0, {}, c));
  auto bus = value(Bundle::create({}, channels, std::move(tables)), "bus");
  auto b = data(bus);
  b.instance.tables[0] = {true, BundleLimits::height, {}};
  b.witness.tables[0] =
      std::vector<BundleColumns>{BundleColumns(BundleLimits::height, "0")};
  refuses(bus.admit(b.config, b.instance, b.witness),
          "bundle-contribution-limit", "contribution preflight");
}

//===----------------------------------------------------------------------===//
// Shared hand-authored fixture: the Rust runtime asserts the same outcomes
//===----------------------------------------------------------------------===//
// Hand-authored fixture shared verbatim with
// crates/zkc-runtime/src/relation_tests.rs. The identity was computed
// independently with Python hashlib over this text.
static const char *SHARED_BUNDLE =
    R"FX(["zkc.relation-bundle/0",[["start","koala-bear"],["final","koala-bear"]],[["range","field-balance",["koala-bear"],"koala-bear"],["trace","multiset",["koala-bear","koala-bear"],"koala-bear"]],[["cpu","required",["instance",1,16,true],"finite",[["x","witness","koala-bear",1],["step","public","koala-bear",1]],["zkc.ring/0",["koala-bear","koala-bear","koala-bear","koala-bear","koala-bear"],[["input",0],["input",3],["neg",1],["add",0,2],["input",1],["input",2],["add",0,5],["neg",6],["add",4,7],["input",4],["neg",9],["add",0,10],["constant","koala-bear","1"]],[3,8,11,0,5,12]],[["read",0,"0",0],["read",0,"1",0],["read",1,"0",0],["public",0],["public",1]],[[0,["first"]],[1,["interior",0,1]],[2,["last"]]],[["field-balance",0,["global"],["all"],[3],5,null],["multiset",1,["global"],["all"],"push",[3,4],5,1]]],["rom","required",["fixed",8],"cyclic",[["values","config","koala-bear",1],["multiplicity","witness","koala-bear",1]],["zkc.ring/0",["koala-bear","koala-bear","koala-bear"],[["input",0],["input",1],["neg",1],["input",2],["neg",0],["constant","koala-bear","1"],["neg",5],["add",3,4],["add",7,6],["mul",8,3]],[0,2,9]],[["read",0,"0",0],["read",1,"0",0],["read",0,"1",0]],[[2,["all"]]],[["field-balance",0,["global"],["all"],[0],1,null]]],["log","optional",["instance",1,16,false],"finite",[["pairs","witness","koala-bear",2]],["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["input",1],["constant","koala-bear","1"]],[0,1,2]],[["read",0,"0",0],["read",0,"0",1]],[],[["multiset",1,["global"],["all"],"pull",[0,1],2,1]]]]])FX";
static const char *SHARED_IDENTITY =
    "7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc";
static const char *SHARED_CONFIG =
    R"FX(["zkc.relation-configuration/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",[[null,[]],[null,[["0","1","2","3","4","5","6","7"]]],[null,[]]]])FX";
static const char *SHARED_INSTANCE =
    R"FX(["zkc.relation-instance/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",["0","6"],[["present",4,[["1","2","3","9"]]],["present",null,[]],["present",4,[]]]])FX";
static const char *SHARED_WITNESS =
    R"FX(["zkc.relation-witness/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",[[["0","1","3","6"]],[["1","1","0","1","0","0","1","0"]],[["3","3","0","1","6","9","1","2"]]]])FX";
struct Edit {
  unsigned carrier;
  const char *from, *to;
};
struct Mutation {
  const char *name;
  std::vector<Edit> edits;
  const char *expected;
};
static const std::vector<Mutation> SHARED_MUTATIONS = {
    {"honest", {}, "satisfied"},
    {"configuration rom value",
     {{1, R"FX("2","3","4")FX", R"FX("2","9","4")FX"}},
     "unsatisfied"},
    {"required table absent",
     {{2, R"FX(["present",4,[["1","2","3","9"]]])FX", R"FX(["absent"])FX"}},
     "bundle-table-missing"},
    {"optional table absent",
     {{2, R"FX(["present",4,[]]])FX", R"FX(["absent"]])FX"},
      {3, R"FX(,[["3","3","0","1","6","9","1","2"]]])FX", R"FX(,null])FX"}},
     "unsatisfied"},
    {"absent table with witness",
     {{2, R"FX(["present",4,[]]])FX", R"FX(["absent"]])FX"}},
     "bundle-witness-presence"},
    {"height policy",
     {{2, R"FX(["present",4,[["1","2","3","9"]]])FX",
       R"FX(["present",3,[["1","2","3"]]])FX"},
      {3, R"FX([["0","1","3","6"]])FX", R"FX([["0","1","3"]])FX"}},
     "bundle-height"},
    {"height mismatch",
     {{3, R"FX([["0","1","3","6"]])FX", R"FX([["0","1","3"]])FX"}},
     "bundle-group-shape"},
    {"fixed height override",
     {{2, R"FX(["present",null,[]])FX", R"FX(["present",8,[]])FX"}},
     "bundle-height-authority"},
    {"witness supplies configuration",
     {{3, R"FX([["1","1","0","1","0","0","1","0"]])FX",
       R"FX([["0","1","2","3","4","5","6","7"],["1","1","0","1","0","0","1","0"]])FX"}},
     "bundle-group-count"},
    {"transition read on every row",
     {{0, R"FX([1,["interior",0,1]])FX", R"FX([1,["all"]])FX"}},
     "bundle-window"},
    {"finite rom wraparound",
     {{0, R"FX("cyclic")FX", R"FX("finite")FX"}},
     "bundle-window"},
    {"multiset bound at characteristic",
     {{0, R"FX("push",[3,4],5,1])FX", R"FX("push",[3,4],5,2130706433])FX"}},
     "bundle-multiset-bound"},
    {"challenge in deterministic relation",
     {{0, R"FX(["public",0])FX", R"FX(["challenge",1,0])FX"}},
     "bundle-input-kind"},
    {"witness for another relation",
     {{3,
       R"FX(7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc)FX",
       R"FX(0000000000000000000000000000000000000000000000000000000000000000)FX"}},
     "bundle-relation"},
    {"pulled tuple", {{3, R"FX("6","9")FX", R"FX("6","8")FX"}}, "unsatisfied"},
    {"multiplicity above bound",
     {{0, R"FX(["input",1],["constant","koala-bear","1"]],[0,1,2]])FX",
       R"FX(["input",1],["constant","koala-bear","2"]],[0,1,2]])FX"}},
     "unsatisfied"},
    {"noncanonical value",
     {{3, R"FX("1","1","0","1")FX", R"FX("1","01","0","1")FX"}},
     "bundle-value"},
    {"local request scope",
     {{0, R"FX(["field-balance",0,["global"],["all"],[3],5,null])FX",
       R"FX(["field-balance",0,["local",0],["all"],[3],5,null])FX"}},
     "unsatisfied"},
    {"cpu request weight",
     {{0, R"FX(["constant","koala-bear","1"]],[3,8,11)FX",
       R"FX(["constant","koala-bear","2"]],[3,8,11)FX"}},
     "unsatisfied"},
    {"unknown channel",
     {{0, R"FX(["field-balance",0,["global"],["all"],[3],5,null])FX",
       R"FX(["field-balance",3,["global"],["all"],[3],5,null])FX"}},
     "bundle-channel"},
    {"tuple arity",
     {{0, R"FX(["field-balance",0,["global"],["all"],[3],5,null])FX",
       R"FX(["field-balance",0,["global"],["all"],[3,3],5,null])FX"}},
     "bundle-tuple-arity"},
    {"tuple field",
     {{0, R"FX(["range","field-balance",["koala-bear"],"koala-bear"])FX",
       R"FX(["range","field-balance",["koala-bear.ext8-binomial3"],"koala-bear"])FX"}},
     "bundle-tuple-field"},
    {"count field",
     {{0, R"FX(["range","field-balance",["koala-bear"],"koala-bear"])FX",
       R"FX(["range","field-balance",["koala-bear"],"koala-bear.ext8-binomial3"])FX"}},
     "bundle-count-field"},
    {"unknown side",
     {{0, R"FX("push",[3,4])FX", R"FX("sideways",[3,4])FX"}},
     "bundle-side"},
    {"local key limit",
     {{0, R"FX(["field-balance",0,["global"],["all"],[3],5,null])FX",
       R"FX(["field-balance",0,["local",5000],["all"],[3],5,null])FX"}},
     "bundle-locality"},
    {"binding count",
     {{0, R"FX(,["public",1]],[[0,["first"]])FX", R"FX(],[[0,["first"]])FX"}},
     "bundle-input-count"},
    {"assertion output",
     {{0, R"FX([[0,["first"]])FX", R"FX([[9,["first"]])FX"}},
     "bundle-output"},
    {"witness tag",
     {{3, R"FX(zkc.relation-witness/0)FX", R"FX(zkc.relation-witness/1)FX"}},
     "bundle-data-schema"},
    {"configuration table count",
     {{1, R"FX(,[null,[]]]])FX", R"FX(]])FX"}},
     "bundle-data-schema"},
    {"public value count",
     {{2, R"FX(["0","6"])FX", R"FX(["0"])FX"}},
     "bundle-public-shape"},
    {"empty table name",
     {{0, R"FX(["cpu","required")FX", R"FX(["","required")FX"}},
     "bundle-name"},
    {"non-field public slot",
     {{0, R"FX(["start","koala-bear"])FX", R"FX(["start","bn254.g1"])FX"}},
     "bundle-field"},
};
static std::string sharedOutcome(const std::vector<std::string> &texts) {
  auto bundle = readBundleText(texts[0]);
  if (!bundle)
    return code(bundle.takeError());
  std::vector<std::string> carriers;
  for (size_t i = 1; i < texts.size(); ++i) {
    // A mutated relation has a new identity; its carriers name it.
    std::string text = texts[i];
    for (size_t at = text.find(SHARED_IDENTITY); at != std::string::npos;
         at = text.find(SHARED_IDENTITY, at + 64))
      text.replace(at, 64, bundle->identity().str());
    carriers.push_back(std::move(text));
  }
  auto parsed = [&](size_t i) { return readBundleDataJson(carriers[i]); };
  auto c = parsed(0), in = parsed(1), w = parsed(2);
  if (!c)
    return code(c.takeError());
  if (!in)
    return code(in.takeError());
  if (!w)
    return code(w.takeError());
  auto config = readBundleConfiguration(*bundle, *c);
  if (!config)
    return code(config.takeError());
  auto instance = readBundleInstance(*bundle, *in);
  if (!instance)
    return code(instance.takeError());
  auto witness = readBundleWitness(*bundle, *w);
  if (!witness)
    return code(witness.takeError());
  auto result = bundle->evaluate(*config, *instance, *witness);
  if (!result)
    return code(result.takeError());
  return result->satisfied ? "satisfied" : "unsatisfied";
}
static void sharedFixtureTests() {
  auto bundle = value(readBundleText(SHARED_BUNDLE), "shared bundle");
  check(zkc::printJson(bundle.encode()) == SHARED_BUNDLE,
        "shared fixture canonical encoding");
  check(bundle.identity() == SHARED_IDENTITY,
        "shared fixture identity computed independently");
  for (const auto &mutation : SHARED_MUTATIONS) {
    std::vector<std::string> texts{SHARED_BUNDLE, SHARED_CONFIG,
                                   SHARED_INSTANCE, SHARED_WITNESS};
    bool found = true;
    for (const auto &edit : mutation.edits) {
      auto at = texts[edit.carrier].find(edit.from);
      found &= at != std::string::npos;
      if (at != std::string::npos)
        texts[edit.carrier].replace(at, StringRef(edit.from).size(), edit.to);
    }
    auto actual = sharedOutcome(texts);
    if (!found || actual != mutation.expected)
      errs() << mutation.name << ": expected " << mutation.expected << ", got "
             << actual << '\n';
    check(found && actual == mutation.expected, mutation.name);
  }
  auto config =
      value(readBundleConfiguration(
                bundle, value(readBundleDataJson(SHARED_CONFIG), "c")),
            "config");
  auto instance =
      value(readBundleInstance(bundle,
                               value(readBundleDataJson(SHARED_INSTANCE), "i")),
            "instance");
  auto witness = value(
      readBundleWitness(bundle, value(readBundleDataJson(SHARED_WITNESS), "w")),
      "witness");
  check(zkc::printJson(encodeBundleConfiguration(bundle, config)) ==
                SHARED_CONFIG &&
            zkc::printJson(encodeBundleInstance(bundle, instance)) ==
                SHARED_INSTANCE &&
            zkc::printJson(encodeBundleWitness(bundle, witness)) ==
                SHARED_WITNESS,
        "shared carriers re-encode canonically");
  auto result =
      value(bundle.evaluate(config, instance, witness), "shared honest");
  unsigned multiset = 0, field = 0;
  for (const auto &b : result.balances) {
    multiset += b.kind == BundleChannelKind::Multiset && b.push == 1 &&
                b.pull == 1 && b.balanced;
    field += b.kind == BundleChannelKind::FieldBalance &&
             b.sum == BundleColumns{"0"};
  }
  check(result.satisfied && result.residuals.size() == 13 && multiset == 4 &&
            field == 8,
        "shared honest evaluation details match the Rust reference");
}

//===----------------------------------------------------------------------===//
// Remaining refusal identifiers
//===----------------------------------------------------------------------===//
static void refusalTests() {
  using K = BundleScopeKind;
  // Declared heights and widths bound the data before lengths are compared.
  Arena one;
  one.out(one.read(KB, 0, 0));
  auto wide = value(single(one, {{"x", BundleAuthority::Witness, KB, 8}},
                           {{0, scope(K::All)}},
                           instanceHeight(1, BundleLimits::height)),
                    "wide");
  auto w = data(wide);
  w.instance.tables[0] = {true, BundleLimits::height, {}};
  w.witness.tables[0] = std::vector<BundleColumns>{BundleColumns{}};
  refuses(wide.admit(w.config, w.instance, w.witness), "bundle-data-limit",
          "declared shape above the coordinate limit");
  // Programmatic interaction records.
  auto machineWith = [](std::function<void(std::vector<BundleTable> &)> edit) {
    auto b = machine();
    std::vector<BundleTable> tables(b.tables().begin(), b.tables().end());
    edit(tables);
    return Bundle::create(b.publics().vec(), b.channels().vec(),
                          std::move(tables));
  };
  refuses(
      machineWith([](auto &t) { t[0].interactions[0].locality = {false, 3}; }),
      "bundle-locality", "a global record carries no local key");
  refuses(machineWith([](auto &t) {
            t[0].interactions[0].locality = {true, BundleLimits::checks + 1};
          }),
          "bundle-locality", "local key limit");
  refuses(machineWith(
              [](auto &t) { t[0].interactions[0].side = BundleSide::Pull; }),
          "bundle-interaction-kind", "field balance has no side");
  refuses(machineWith([](auto &t) { t[0].interactions[0].channel = 7; }),
          "bundle-channel", "unknown channel");
  refuses(machineWith([](auto &t) { t[0].inputs.pop_back(); }),
          "bundle-input-count", "binding count");
  refuses(machineWith([](auto &t) { t[0].assertions[0].output = 99; }),
          "bundle-output", "assertion output position");
  refuses(machineWith([](auto &t) { t[0].interactions[1].bound.reset(); }),
          "bundle-multiset-bound", "multiset bound is required");
  // Data carrier schema.
  auto bundle = machine();
  auto d = machineData(bundle);
  auto text = zkc::printJson(encodeBundleWitness(bundle, d.witness));
  auto at = text.find("zkc.relation-witness/0");
  text.replace(at, 22, "zkc.relation-witness/1");
  refuses(readBundleWitness(bundle, value(readBundleDataJson(text), "json")),
          "bundle-data-schema", "witness tag");
  refuses(
      readBundleWitness(
          bundle, value(readBundleDataJson("[\"zkc.relation-witness/0\",{}]"),
                        "object")),
      "bundle-data-schema", "witness root arity");
  // Staged formation.
  auto program = value(logup(bundle), "logup");
  auto rebuild =
      [&](std::function<void(std::vector<StagedPhase> &, StagedGlobal &,
                             std::vector<StagedPremise> &)>
              edit) {
        std::vector<StagedPhase> phases(program.phases().begin(),
                                        program.phases().end());
        StagedGlobal global = program.global();
        std::vector<StagedPremise> premises(program.premises().begin(),
                                            program.premises().end());
        edit(phases, global, premises);
        return StagedProgram::create(bundle, std::move(phases),
                                     std::move(global), std::move(premises));
      };
  refuses(rebuild([](auto &p, auto &, auto &) { p.clear(); }), "staged-phases",
          "a staged program has a phase");
  refuses(rebuild([](auto &p, auto &, auto &) {
            p.assign(BundleLimits::phases + 1, p.front());
          }),
          "staged-limit", "phase limit");
  refuses(rebuild([](auto &p, auto &, auto &) { p[0].tables.pop_back(); }),
          "staged-tables", "one staged table per bundle table");
  refuses(rebuild([](auto &p, auto &, auto &) {
            p[0].tables[0].inputs.pop_back();
          }),
          "staged-input-count", "staged binding count");
  refuses(
      rebuild([](auto &p, auto &, auto &) { p[0].challenges[0].field = EXT; }),
      "staged-input-field", "challenge field differs from its input");
  refuses(rebuild([](auto &p, auto &, auto &) {
            p[0].tables[0].inputs[1] = p[0].tables[0].inputs[0];
          }),
          "staged-duplicate-input", "duplicate staged binding");
  refuses(rebuild([](auto &p, auto &, auto &) {
            p[0].tables[0].inputs[0].phase = 0;
          }),
          "staged-input", "phase zero has no challenges");
  refuses(rebuild([](auto &, auto &, auto &q) {
            q.push_back({StagedPremise::Kind::Nonzero, 1, 0, {99}, {}, "", 0});
          }),
          "staged-premise", "premise subject out of range");
  refuses(rebuild([](auto &, auto &, auto &q) {
            q.push_back({StagedPremise::Kind::AtMostOne, 1, 0, {}, {}, "", 0});
          }),
          "staged-premise", "at-most-one needs subjects");
  auto encoded = zkc::printJson(program.encode());
  encoded.replace(encoded.find("zkc.relation-staged/0"), 21,
                  "zkc.relation-staged/1");
  refuses(readStagedProgram(
              bundle, value(zkc::parseNaturalJson(encoded, BundleLimits::bytes,
                                                  16, "x", "y"),
                            "json")),
          "staged-schema", "staged tag");
  // Staged assignment shape.
  auto honest = logupData(program, 1000, d);
  auto slots = honest;
  slots.phases[0].challenges.clear();
  refuses(program.evaluate(bundle, d.config, d.instance, d.witness, slots),
          "staged-slot-shape", "missing challenge value");
  auto phases = honest;
  phases.phases.push_back(phases.phases[0]);
  refuses(program.evaluate(bundle, d.config, d.instance, d.witness, phases),
          "staged-data-shape", "phase count");
  auto assignment =
      zkc::printJson(encodeStagedAssignment(bundle, program, honest));
  assignment.replace(assignment.find("zkc.relation-staged-assignment/0"), 32,
                     "zkc.relation-staged-assignment/1");
  refuses(readStagedAssignment(bundle, program,
                               value(readBundleDataJson(assignment), "json")),
          "staged-data-schema", "staged assignment tag");
}

int main() {
  airEmbedding();
  machineTests();
  countTests();
  windowTests();
  extensionTests();
  stagedTests();
  formationTests();
  preflightTests();
  sharedFixtureTests();
  refusalTests();
  outs() << checks << " checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
