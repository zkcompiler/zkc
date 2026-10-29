#include "support/NativeCases.h"
#include "zkc/Language/Authoring.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject check(StringRef text) {
  CaptureOptions options;
  options.format = "zkc-layout";
  return take(analyze(take(capture({{"m", text.str(), "m.zkc"}}, options)))
                  .checkedProject());
}
} // namespace
int main() {
  Cases cases;
  cases.run("authoring uses checked lexical definitions and roles", [] {
    StringRef text = "pub protocol Demo roles(P)(value: bool @P) -> bool @P:\n "
                     "   result = value\n    return result\n";
    auto project = check(text);
    Authoring authoring(project);
    auto at = text.rfind("result");
    auto target = authoring.definition({0}, at);
    require(target && target->begin == text.find("result"),
            "local reference was not resolved to its binder");
    auto hover = authoring.hover({0}, at);
    require(hover && StringRef(hover->text).contains("bool") &&
                StringRef(hover->text).contains("Available at: P"),
            "inferred role or type missing");
    auto candidates = authoring.completion({0}, at);
    require(
        any_of(candidates, [](const auto &c) { return c.name == "result"; }),
        "visible local missing");
    candidates = authoring.completion({0}, text.find("= value") + 2);
    require(
        none_of(candidates, [](const auto &c) { return c.name == "result"; }),
        "binding leaked into its own initializer");
    auto symbols = authoring.symbols({0});
    require(symbols.size() == 1 && symbols[0].name == "Demo" &&
                text.slice(symbols[0].selection.begin,
                           symbols[0].selection.end) == "Demo",
            "symbol selection differs");
  });
  cases.run("local shadowing and branch visibility use resolved scopes", [] {
    StringRef text = R"(local def select(input: bool) -> bool:
    value = input
    result = if input:
        value = false
        value
    else:
        value
    return result
)";
    Authoring authoring(check(text));
    auto inner = text.find("        value\n");
    auto outer = text.rfind("        value\n");
    require(authoring.definition({0}, inner + 8)->begin ==
                text.find("value = false"),
            "inner reference escaped shadow");
    require(authoring.definition({0}, outer + 8)->begin ==
                text.find("value = input"),
            "sibling branch inherited shadow");
    auto candidates = authoring.completion({0}, outer + 8, "val");
    require(candidates.size() == 1 &&
                candidates[0].definition.begin == text.find("value = input"),
            "completion leaked sibling binder");
  });
  cases.run("authoring signatures retain interleaved service and data inputs",
            [] {
              StringRef text = R"(domain F = field("bls12-381.fr")
pub protocol Draw roles(P)(coins: Random<F> @P; value: bool @P;
                          more: Random<F> @P; other: bool @P) -> bool @P:
    nonce <- coins.draw()
    second <- more.draw()
    return value
)";
              Authoring authoring(check(text));
              auto ordered = [](StringRef signature) {
                auto coins = signature.find("coins:");
                auto value = signature.find("value:");
                auto more = signature.find("more:");
                auto other = signature.find("other:");
                require(coins < value && value < more && more < other &&
                            other != StringRef::npos,
                        "signature reordered authored input categories");
              };
              auto hover = authoring.hover({0}, text.find("Draw"));
              require(hover.has_value(), "protocol hover missing");
              ordered(hover->text);
              for (const auto &symbol : authoring.symbols({0}))
                if (symbol.name == "Draw")
                  ordered(symbol.detail);
              for (const auto &candidate :
                   authoring.completion({0}, text.find("return"), "Draw"))
                ordered(candidate.detail);
            });
  cases.run("formatting reuses the exact retained notation environment", [] {
    Authoring authoring(check("def same(x: bool) -> bool:\n    x   // keep\n"));
    auto formatted = authoring.format({0});
    require(formatted.complete && StringRef(formatted.text).contains("// keep"),
            "formatter lost source comment");
    Authoring again(check(formatted.text));
    require(again.format({0}).text == formatted.text,
            "formatting is not idempotent");
  });
  cases.run("native cancellation never produces checked state", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto captured = take(capture(
        {{"m", "def same(x: bool) -> bool:\n    x\n", "m.zkc"}}, options));
    zkc::source::Cancellation cancelled;
    cancelled.cancel();
    auto analysis = analyze(captured, {}, cancelled);
    require(!analysis.diagnostics().empty() &&
                analysis.diagnostics()[0].code == "source.cancelled",
            "cancellation was cached as syntax or type failure");
    refuses(analysis.checkedProject(), "source.cancelled");
    take(analyze(captured).checkedProject());
  });
  cases.run(
      "imported fixity changes grouping with unchanged consumer bytes", [] {
        CaptureOptions options;
        options.format = "zkc-layout";
        auto trees = [&](StringRef fixity) {
          std::string provider =
              "pub def first(a: bool, b: bool) -> bool:\n    a\npub operator " +
              fixity.str() + " ⊕ = first\n";
          auto captured = take(capture(
              {{"ops", provider, "ops.zkc"},
               {"m",
                "use ops::{operator ⊕}\ndef choose(value: bool) -> bool:\n"
                "    value ⊕ false ⊕ true\n",
                "m.zkc"}},
              options));
          auto project = take(analyze(captured).checkedProject());
          SourceId consumer{UINT32_MAX};
          for (unsigned i = 0; i < project.sources().size(); ++i)
            if (project.sources()[i].module == "m")
              consumer.index = i;
          Authoring authoring(project);
          auto tree = *authoring.syntaxTree(consumer);
          require(authoring.format(consumer).complete,
                  "formatting lost imported notation");
          std::vector<std::string> binary;
          for (unsigned i = 0; i < tree.nodes().size(); ++i)
            if (tree.node({i}).kind == zkc::syntax::Kind::Binary)
              binary.push_back(tree.text({i}).trim().str());
          return binary;
        };
        auto left = trees("infixl(60)");
        auto right = trees("infixr(70)");
        std::string observed = "left:";
        for (const auto &value : left)
          observed += " [" + value + "]";
        observed += "; right:";
        for (const auto &value : right)
          observed += " [" + value + "]";
        require(is_contained(left, "value ⊕ false") &&
                    !is_contained(left, "false ⊕ true") &&
                    is_contained(right, "false ⊕ true") &&
                    !is_contained(right, "value ⊕ false"),
                "consumer retained stale imported grouping: " + observed);
      });
  cases.run("spec intent appears in native hover without proof success", [] {
    StringRef text =
        "pub protocol Demo roles(P)(value: bool @P) -> bool @P:\n    return "
        "value\nspec for Demo:\n    security: secure()\n";
    Authoring authoring(check(text));
    auto hover = authoring.hover({0}, text.find("Demo"));
    require(hover && StringRef(hover->text).contains("Assurance: unavailable"),
            "spec intent was hidden");
  });
  return cases.result();
}
