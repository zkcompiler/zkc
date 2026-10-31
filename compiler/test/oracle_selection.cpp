#include "../lib/Transforms/OracleRealizationSelection.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/OracleSelection.h"
#include <algorithm>
#include <filesystem>
#include <fstream>
using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
constexpr StringLiteral invalid = "oracle-realization-selection";
constexpr StringLiteral limit = "oracle-realization-selection-limit";
std::string encoded(const OracleRealizationPolicy &policy = {}) {
  return printJson(take(encodeOracleRealizationPolicy(policy)));
}
std::string replace(std::string text, StringRef before, StringRef after) {
  auto at = text.find(before);
  require(at != std::string::npos, "missing mutation slot");
  text.replace(at, before.size(), after.str());
  return text;
}
OwningOpRef<ModuleOp> prepared(MLIRContext &context, StringRef fixture) {
  std::ifstream input(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                      (fixture.str() + ".mlir"));
  require(bool(input), "missing fixture");
  std::string text((std::istreambuf_iterator<char>(input)), {});
  auto module = parseSourceString<ModuleOp>(text, &context);
  require(bool(module), "fixture parse failed");
  auto result = mathematical::prepareProtocol(*module, false);
  require(bool(result), "fixture preparation failed");
  return result;
}
} // namespace
int main() {
  Cases cases;
  cases.run("default and canonical round trip", [&] {
    auto policy = take(parseOracleRealizationPolicy(encoded()));
    require(policy == OracleRealizationPolicy{}, "default changed");
    require(std::holds_alternative<OracleTableRealization>(policy.roots),
            "default is not uniform");
    require(encoded(policy) == encoded(), "unstable encoding");
    require(
        encoded() ==
            R"json({"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"kind":"uniform","table":{"grouping":"individual","order":"natural","scheme":""}}})json",
        "default canonical wire encoding changed");
  });
  cases.run("exact empty remains distinct", [&] {
    OracleRealizationPolicy exact;
    exact.roots = std::vector<OracleRootSelection>{};
    require(!(exact == OracleRealizationPolicy{}), "exact collapsed");
    require(take(parseOracleRealizationPolicy(encoded(exact))) == exact,
            "exact empty round trip changed");
  });
  cases.run("strict envelope mutations", [&] {
    auto text = encoded();
    for (const auto &mutated : std::vector<std::string>{
             "[]", "null", text + "{}",
             replace(text, "zkc.oracle-selection/0", "zkc.oracle-selection/1"),
             replace(text, "\"uniform\"", "\"inferred\""),
             replace(text, "\"individual\"", "\"paired\""),
             replace(text, "\"natural\"", "\"reverse\""),
             replace(text, "\"unrestricted\"", "\"unknown\""),
             replace(text, "\"per-query\"", "\"unknown\""),
             replace(text, "\"individual\"", "\"antipodal-pairs\""),
             replace(text, "\"natural\"", "\"bit-reversed\""),
             replace(text, "\"scheme\":\"\"", "\"scheme\":null"),
             replace(text, "\"table\":{", "\"table\":{\"extra\":false,"),
             replace(text, "\"kind\":\"uniform\"",
                     "\"kind\":\"uniform\",\"kind\":\"uniform\""),
             replace(text, "\"scheme\":\"\"",
                     "\"scheme\":\"\",\"sch\\u0065me\":\"\""),
             replace(text, "{", "{\"extra\":null,"),
             replace(text, "\"scheme\":\"\"", "\"scheme\":\"\\ud800\"")})
      refuses(parseOracleRealizationPolicy(mutated), invalid);
  });
  OracleRealizationPolicy exact;
  exact.roots = std::vector<OracleRootSelection>{{"main", {0}, {}}};
  for (StringRef path : {"[]", "[-0]", "[-1]", "[+1]", "[01]", "[1.0]", "[1e0]",
                         "[4294967296]", "[true]", "[\"0\"]", "null", "{}"})
    cases.run("strict path " + path, [&] {
      refuses(parseOracleRealizationPolicy(replace(
                  encoded(exact), "\"path\":[0]", "\"path\":" + path.str())),
              invalid);
    });
  cases.run("exact selectors and unsigned maximum", [&] {
    exact.roots = std::vector<OracleRootSelection>{
        {"main", {4294967295U}, {"unknown-but-explicit/0"}}};
    require(take(parseOracleRealizationPolicy(encoded(exact))) == exact,
            "unsigned maximum narrowed");
    auto duplicate = exact;
    auto &roots = std::get<std::vector<OracleRootSelection>>(duplicate.roots);
    roots.push_back(roots.front());
    refuses(encodeOracleRealizationPolicy(duplicate), invalid);
    auto value = take(json::parse(encoded(exact)));
    auto &entries =
        *value.getAsObject()->getObject("roots")->getArray("entries");
    entries.push_back(entries.front());
    refuses(parseOracleRealizationPolicy(printJson(value)), invalid);
  });
  cases.run("typed bounds and enum mutations", [&] {
    for (unsigned mutation = 0; mutation < 7; ++mutation) {
      OracleRealizationPolicy policy;
      auto &table = std::get<OracleTableRealization>(policy.roots);
      if (mutation == 0)
        table.grouping = static_cast<OracleLeafGrouping>(99);
      if (mutation == 1)
        table.order = static_cast<OracleLeafOrder>(99);
      if (mutation == 2)
        policy.order = static_cast<OracleQueryOrder>(99);
      if (mutation == 3)
        policy.authentication = static_cast<OracleAuthentication>(99);
      if (mutation == 4)
        table.scheme.assign(4097, 'a');
      if (mutation == 5)
        policy.roots = std::vector<OracleRootSelection>{{"", {0}, {}}};
      if (mutation == 6)
        policy.roots = std::vector<OracleRootSelection>{
            {"main", std::vector<unsigned>(65), {}}};
      refuses(encodeOracleRealizationPolicy(policy), invalid);
    }
    refuses(parseOracleRealizationPolicy(std::string(1024 * 1024 + 1, ' ')),
            limit);
    refuses(parseOracleRealizationPolicy(std::string(33, '[') +
                                         std::string(33, ']')),
            limit);
  });
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  cases.run("normalize only actual frozen occurrences in source order", [&] {
    auto source = prepared(context, "common-entries");
    auto roots = take(resolveOracleRealizationSelection(*source, {}));
    require(roots.size() >= 2, "multi-entry fixture lost roots");
    OracleRealizationPolicy policy;
    policy.roots = std::vector<OracleRootSelection>{};
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
    policy.roots = roots;
    auto &inventory = std::get<std::vector<OracleRootSelection>>(policy.roots);
    std::reverse(inventory.begin(), inventory.end());
    require(take(resolveOracleRealizationSelection(*source, policy)) == roots,
            "caller order became source authority");
    inventory.pop_back();
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
    inventory = roots;
    inventory.push_back({"missing", {0}, {}});
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
    inventory = roots;
    inventory.front().path.push_back(999);
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
    policy.roots = OracleTableRealization{"explicit-scheme/0"};
    auto uniform = take(resolveOracleRealizationSelection(*source, policy));
    for (const auto &root : uniform)
      require(root.realization.scheme == "explicit-scheme/0",
              "uniform silently fell back");
  });
  cases.run("empty source validates exact coverage and malformed policy", [&] {
    auto source = prepared(context, "common-empty");
    require(take(resolveOracleRealizationSelection(*source, {})).empty(),
            "empty roots");
    OracleRealizationPolicy policy;
    policy.roots = std::vector<OracleRootSelection>{};
    require(take(resolveOracleRealizationSelection(*source, policy)).empty(),
            "exact empty");
    policy.roots = std::vector<OracleRootSelection>{{"ghost", {0}, {}}};
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
    policy.roots =
        OracleTableRealization{"", OracleLeafGrouping::AntipodalPairs};
    refuses(resolveOracleRealizationSelection(*source, policy), invalid);
  });
  return cases.result();
}
