#include "../lib/Transforms/OracleLayout.h"
#include "../lib/Transforms/OracleSchedule.h"
#include "support/NativeCases.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include <limits>
#include <set>
#include <string>
#include <vector>

using namespace llvm;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
using Summary = OracleObservationSummary;
using Traces = std::vector<std::string>;
Summary events(StringRef word) {
  Summary result;
  for (char event : word)
    result = result.then(event == 'Q'   ? Summary::query()
                         : event == 'D' ? Summary::draw()
                         : event == 'S' ? Summary::stop()
                                        : Summary());
  return result;
}
bool queryThenDraw(StringRef word) {
  bool queried = false;
  for (char event : word) {
    if (event == 'S')
      return false;
    if (event == 'D' && queried)
      return true;
    queried |= event == 'Q';
  }
  return false;
}
Summary choices(const Traces &traces) {
  require(!traces.empty(), "test requires a nonempty choice");
  auto result = events(traces.front());
  for (const auto &trace : ArrayRef(traces).drop_front())
    result = result.either(events(trace));
  return result;
}
void refuses(Error error, StringRef expected) {
  require(bool(error), "malformed layout accepted");
  bool matched = false;
  handleAllErrors(std::move(error), [&](const zkc::Refusal &refusal) {
    matched = refusal.code == expected;
  });
  require(matched, "wrong layout diagnostic");
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "antipodal grouping and permutation have independent known layouts", [&] {
        const std::vector<std::vector<uint64_t>> natural{
            {0, 4}, {1, 5}, {2, 6}, {3, 7}};
        const std::vector<std::vector<uint64_t>> reversed{
            {0, 4}, {2, 6}, {1, 5}, {3, 7}};
        for (auto order :
             {OracleLeafOrder::Natural, OracleLeafOrder::BitReversed}) {
          auto layout = take(OracleTableLayout::create(
              8, OracleLeafGrouping::AntipodalPairs, order));
          const auto &expected =
              order == OracleLeafOrder::Natural ? natural : reversed;
          for (unsigned leaf = 0; leaf < expected.size(); ++leaf)
            for (unsigned slot = 0; slot < 2; ++slot) {
              require(take(layout.logicalRow({leaf, slot})) ==
                          expected[leaf][slot],
                      "leaf does not contain the expected antipodal row");
              require(take(layout.locate(expected[leaf][slot])) ==
                          OracleLeafPosition{leaf, slot},
                      "query selects the wrong leaf or payload slot");
            }
        }
        auto individual = take(OracleTableLayout::create(
            8, OracleLeafGrouping::Individual, OracleLeafOrder::BitReversed));
        const uint64_t expected[] = {0, 4, 2, 6, 1, 5, 3, 7};
        for (unsigned position = 0; position < 8; ++position)
          require(take(individual.locate(position)) ==
                      OracleLeafPosition{expected[position], 0},
                  "single-leaf permutation differs from bit reversal");
      });
  cases.run(
      "every small row maps bijectively without allocating large tables", [&] {
        for (unsigned power = 0; power <= 10; ++power)
          for (auto grouping : {OracleLeafGrouping::Individual,
                                OracleLeafGrouping::AntipodalPairs})
            for (auto order :
                 {OracleLeafOrder::Natural, OracleLeafOrder::BitReversed}) {
              if (!power && grouping == OracleLeafGrouping::AntipodalPairs)
                continue;
              auto layout = take(
                  OracleTableLayout::create(1ull << power, grouping, order));
              std::set<std::pair<uint64_t, unsigned>> seen;
              for (uint64_t row = 0; row < layout.rows(); ++row) {
                auto position = take(layout.locate(row));
                require(position.leaf < layout.leaves() &&
                            position.slot < layout.width(),
                        "mapping escaped the physical layout");
                require(seen.emplace(position.leaf, position.slot).second,
                        "two logical rows share a payload slot");
                require(take(layout.logicalRow(position)) == row,
                        "inverse mapping changed a logical row");
              }
            }
        const uint64_t maximum = 1ull << 63;
        auto layout = take(OracleTableLayout::create(
            maximum, OracleLeafGrouping::AntipodalPairs,
            OracleLeafOrder::BitReversed));
        require(take(layout.locate(maximum / 2 + 1)) ==
                    OracleLeafPosition{1ull << 61, 1},
                "large pair mapping truncated its index");
        require(take(layout.logicalRow({maximum / 2 - 1, 1})) == maximum - 1,
                "large pair inverse overflowed");
      });
  cases.run("shape, kind, row and payload refusals are explicit", [&] {
    for (uint64_t rows : {0ull, 3ull, 6ull, ~0ull})
      refuses(OracleTableLayout::create(rows, OracleLeafGrouping::Individual,
                                        OracleLeafOrder::Natural)
                  .takeError(),
              "oracle-layout-shape");
    refuses(OracleTableLayout::create(1, OracleLeafGrouping::AntipodalPairs,
                                      OracleLeafOrder::Natural)
                .takeError(),
            "oracle-layout-pair");
    refuses(OracleTableLayout::create(8, OracleLeafGrouping(17),
                                      OracleLeafOrder::Natural)
                .takeError(),
            "oracle-layout-kind");
    refuses(OracleTableLayout::create(8, OracleLeafGrouping::Individual,
                                      OracleLeafOrder(17))
                .takeError(),
            "oracle-layout-kind");
    auto layout = take(OracleTableLayout::create(
        8, OracleLeafGrouping::AntipodalPairs, OracleLeafOrder::Natural));
    refuses(layout.locate(8).takeError(), "oracle-layout-position");
    refuses(layout.logicalRow({4, 0}).takeError(), "oracle-layout-position");
    refuses(layout.logicalRow({0, 2}).takeError(), "oracle-layout-position");
  });
  cases.run("observation summary agrees with every short reached event trace",
            [&] {
              // Independent concrete execution over all words through length
              // seven.
              Traces words{std::string()};
              for (unsigned length = 0; length <= 7; ++length) {
                Traces next;
                for (const auto &word : words) {
                  require(events(word).queryBeforeDraw() == queryThenDraw(word),
                          "summary disagrees with a reached concrete trace");
                  if (length != 7)
                    for (char event : StringRef("QDSN"))
                      next.push_back(word + event);
                }
                words = std::move(next);
              }
            });
  cases.run(
      "branches preserve outcomes rather than crossing stopped arms", [&] {
        const std::vector<Traces> branches{
            {"QS", "D"}, {"Q", "S"}, {"DQ", "ND"}, {"QDS", "S"}, {"", "DS"}};
        for (const auto &left : branches)
          for (const auto &right : branches) {
            bool concrete = false;
            for (const auto &a : left)
              for (const auto &b : right)
                concrete |= queryThenDraw(a + b);
            require(choices(left).then(choices(right)).queryBeforeDraw() ==
                        concrete,
                    "choice invented or lost a reached query/draw path");
          }
        require(!events("QS")
                     .either(events("D"))
                     .then(events("D"))
                     .queryBeforeDraw(),
                "terminated arm constrained an unreachable later draw");
      });
  cases.run("loop summaries include zero trips, stops and backedges", [&] {
    for (StringRef body : {"DQ", "QD", "QS", "DS", "", "Q"})
      for (unsigned count = 0; count < 6; ++count) {
        std::string trace;
        bool any = false;
        for (unsigned iteration = 0; iteration < count; ++iteration) {
          trace.append(body.data(), body.size());
          any |= queryThenDraw(trace);
        }
        require(events(body).repeat(count).queryBeforeDraw() ==
                    queryThenDraw(trace),
                "exact repeat differs from reached iterations");
        require(events(body).repeatAtMost(count).queryBeforeDraw() == any,
                "bounded repeat omitted a possible count");
      }
    require(!events("DQ").repeat(1).queryBeforeDraw(),
            "single pass has no backedge");
    require(events("DQ").repeat(2).queryBeforeDraw(),
            "later iteration draws after query");
    auto maximum = std::numeric_limits<uint64_t>::max();
    require(events("DQ").repeatAtMost(maximum).queryBeforeDraw(),
            "large bound lost a backedge");
    require(!events("QS").repeatAtMost(maximum).queryBeforeDraw(),
            "large bound resumed a stopped iteration");
  });
  return cases.result();
}
