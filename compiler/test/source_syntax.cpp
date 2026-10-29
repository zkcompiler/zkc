#include "zkc/Syntax/Syntax.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <filesystem>
#include <random>

using namespace zkc;
using namespace zkc::syntax;
using namespace llvm;
namespace {
unsigned checks = 0, failures = 0;
void check(bool condition, StringRef name) {
  ++checks;
  if (!condition) {
    ++failures;
    if (failures < 40)
      errs() << "FAIL: " << name << '\n';
  }
}
Snapshot read(StringRef text, Budget budget = {}, Environment env = {}) {
  return parse(source::Revision({"m", text.str(), "m.zkc"}), std::move(env),
               budget);
}
void report(const Snapshot &s) {
  for (const auto &d : s.diagnostics())
    errs() << d.code << ": " << d.message << " at "
           << (d.primary ? d.primary->begin : 0) << '\n';
}
void coverage(const Snapshot &s, StringRef context) {
  uint32_t offset = 0;
  bool valid = true;
  for (const auto &token : s.tokens()) {
    if (token.synthetic())
      continue;
    valid &= token.begin == offset && token.end > token.begin &&
             token.end <= s.revision().text().size();
    offset = token.end;
  }
  check(valid && offset == s.revision().text().size(), context);
  bool bounded = true;
  for (const auto &node : s.nodes()) {
    bounded &= node.firstToken <= node.lastToken &&
               node.lastToken < s.tokens().size() && node.height <= 64;
    for (auto child : s.children({uint32_t(&node - s.nodes().data())}))
      bounded &= child.index < s.nodes().size();
  }
  check(bounded, "tree indices and height are bounded");
}
void refused(StringRef text, StringRef code, Budget budget = {}) {
  auto s = read(text, budget);
  bool found = false;
  for (const auto &d : s.diagnostics())
    found |= d.code == code;
  check(s.status() != Status::Complete && found, code);
  if (!found)
    report(s);
  coverage(s, "refused source retains bytes");
}
void positions() {
  source::Revision revision({"m", "a😀β\r\nx\n", ""}, 1);
  using E = source::PositionEncoding;
  check(revision.offset({0, 1}, E::UTF16) == 1, "UTF16 emoji start");
  check(!revision.offset({0, 2}, E::UTF16), "UTF16 surrogate split refused");
  check(revision.offset({0, 3}, E::UTF16) == 5, "UTF16 emoji end");
  check(revision.offset({0, 100}, E::UTF16) == 7,
        "overlong column clamps before CRLF");
  check(!revision.offset({0, 2}, E::UTF8), "UTF8 split refused");
  check(revision.offset({1, 0}, E::UTF16) == 9, "CRLF next line");
  for (uint32_t offset : {0, 1, 5, 7, 9, 10, 11}) {
    for (auto encoding : {E::UTF8, E::UTF16}) {
      auto p = revision.position(offset, encoding);
      check(p && revision.offset(*p, encoding) == offset,
            "position byte roundtrip");
    }
  }
  check(!revision.offset({3, 0}, E::UTF16), "nonexistent line refused");
  auto edited = revision.edit({0, 1}, {0, 3}, E::UTF16, "z", 2, 100);
  check(edited && edited->text() == "azβ\r\nx\n" &&
            revision.text() == "a😀β\r\nx\n",
        "edit creates immutable new revision");
  check(!revision.edit({0, 2}, {0, 3}, E::UTF16, "z", 2, 100),
        "invalid edit range");
  check(!revision.edit({0, 0}, {0, 1}, E::UTF16, "z", 1, 100),
        "stale edit version");
  check(!revision.edit({0, 0}, {0, 1}, E::UTF16, "zz", 2, 4),
        "edit byte limit");
}
void corpus() {
  unsigned files = 0;
  for (const auto &entry :
       std::filesystem::directory_iterator(ZKC_SYNTAX_FIXTURES)) {
    if (entry.path().extension() != ".zkc")
      continue;
    ++files;
    auto buffer = MemoryBuffer::getFile(entry.path().string());
    check(bool(buffer), "corpus file opens");
    if (!buffer)
      continue;
    auto s = read((*buffer)->getBuffer());
    check(s.status() == Status::Complete, entry.path().filename().string());
    if (s.status() != Status::Complete)
      report(s);
    coverage(s, "corpus byte coverage");
    auto headers = parseHeaders(s.revision());
    check(headers.status() == Status::Complete, "header collection succeeds");
    auto full = parseBodies(headers);
    check(equivalent(s, full), "two-stage parsing equals full parsing");
    auto formatted = format(s);
    check(formatted.complete, "format " + entry.path().filename().string());
    auto reparsed = read(formatted.text);
    check(equivalent(s, reparsed), "format parse equivalence");
    check(format(reparsed).text == formatted.text, "format idempotence");
  }
  auto metered = read("module m\ndef f():\n    x + y\n");
  check(metered.workUsed() > metered.tokens().size() &&
            metered.workUsed() <= Budget{}.work,
        "syntax work is available for project aggregate charging");
  check(files == 13, "complete accepted example corpus");
}
void designCases() {
  auto buffer =
      MemoryBuffer::getFile(std::string(ZKC_SYNTAX_FIXTURES) + "/cases.json");
  check(bool(buffer), "design cases open");
  if (!buffer)
    return;
  auto parsed = json::parse((*buffer)->getBuffer());
  if (!parsed) {
    consumeError(parsed.takeError());
    check(false, "design case JSON");
    return;
  }
  auto rows = parsed->getAsArray();
  check(rows != nullptr, "design case array");
  if (!rows)
    return;
  for (const auto &row : *rows) {
    auto object = row.getAsObject();
    if (!object) {
      check(false, "design case object");
      continue;
    }
    auto name = object->getString("name"), source = object->getString("source");
    auto expected = object->getBoolean("accepted");
    if (!name || !source || !expected) {
      check(false, "design case shape");
      continue;
    }
    auto s = read(*source);
    check((s.status() == Status::Complete) == *expected, *name);
    if ((s.status() == Status::Complete) != *expected)
      report(s);
    coverage(s, *name);
    if (*expected) {
      std::string crlf;
      for (char c : *source) {
        if (c == '\n')
          crlf += '\r';
        crlf += c;
      }
      auto converted = read(crlf);
      check(converted.status() == Status::Complete && equivalent(s, converted),
            "CRLF design equivalence");
    }
  }
}
void grammar() {
  for (StringRef text :
       {"module m\npub protocol Check<F: Field> roles(P,V)(x:F@P)->F@V:\n    y "
        "<- send x to V\n    return y\n",
        "module m\nsection <F: Field>:\n    def id(x:F)->F:\n        x\n",
        "section <\n    F: Field,\n    N: nat,\n>:\n    def id(x:F)->F:\n      "
        "  x\n",
        "def compare(section: nat, other: nat) -> bool:\n    section < other\n",
        "def compare(section: nat, other: nat) -> bool:\n    f(section < "
        "other)\n",
        "module m\ndef f(x:F)->F:\n    // retained\n    guard(x == x)\n    y = "
        "Helpers::guard(x)\n    y\n",
        "module m\nspec for P:\n    requires honest:\n        (x == y)\n    "
        "reduces r: R(x) to R(y)\n",
        "module m\ndef f(x:Vec<Vec<F,2>,3>)->F:\n    a = x[0][1]\n    a\n",
        "module m\n// comment\r\ndef f(x:F)->F:\r\n    x   \r\n",
        "module m\n// retained\n// comment\ndef f(x:F)->F:\n    x\n"}) {
    auto s = read(text);
    check(s.status() == Status::Complete, "positive grammar");
    if (s.status() != Status::Complete)
      report(s);
    coverage(s, "positive grammar coverage");
  }
  refused("module m\ndef f():\n\tx\n", "syntax.tab");
  refused("module m\ndef f():\n  x\n", "syntax.indent");
  refused("module m\ndef f():\n", "syntax.expected");
  refused("module m\ndef f():\n    x <- send y\n", "syntax.expected");
  refused("module m\ndef f():\n    a < b < c\n", "syntax.comparison");
  refused("module m\ndef f():\n    a<b\n", "syntax.expected");
  refused("module m\nimpl M:\n    x\n", "syntax.declaration");
  refused("module m\npub spec for P:\n    target R(x)\n", "syntax.spec");
  for (StringRef modifier : {"where N <= 1", "effects(stop)", "roles(P)"})
    refused(("section <N: nat> " + modifier +
             ":\n    def value() -> bool:\n        true\n")
                .str(),
            "syntax.section");
  refused("module m\ndef e\xCC\x81():\n    0\n", "source.nfc");
  refused("module m\n// \xFF\n", "source.unicode");
  refused("module m\n/*", "syntax.declaration");
  refused("module m\ndef f():\n    \"β\"\n", "source.string");
  refused("module m\ndef f():\n    \"open\n", "source.string");
  auto recovered =
      read("module m\ndef broken(x:F:\n    x\ndef good()->F:\n    0\n");
  bool good = false;
  for (uint32_t i = 0; i < recovered.nodes().size(); ++i)
    good |= recovered.nodes()[i].kind == Kind::Definition &&
            recovered.text({i}).contains("def good");
  check(good && recovered.status() == Status::Partial,
        "recover independent declaration");
  Budget budget;
  budget.nodes = 4;
  refused("module m\ndef f():\n    x + y\n", "syntax.limit", budget);
  budget = {};
  budget.tokens = 8;
  refused("module m\ndef f():\n    x + y\n", "syntax.limit", budget);
  budget = {};
  budget.work = 4;
  refused("module m\ndef f():\n    x + y\n", "syntax.limit", budget);
  source::Cancellation cancellation;
  cancellation.cancel();
  auto cancelled =
      parse(source::Revision({"m", "module m\n", ""}), {}, {}, cancellation);
  check(cancelled.status() == Status::Cancelled,
        "cancelled parse remains cancelled");
}
void notationCases() {
  using P = NotationDescriptor::Position;
  using A = NotationDescriptor::Association;
  Environment env;
  env.notation.push_back({P::Infix, A::Left, "⊙", "", 66, 2});
  env.notation.push_back({P::Prefix, A::None, "√", "", 74, 1});
  env.notation.push_back({P::Postfix, A::None, "⊤", "", 78, 1});
  env.notation.push_back({P::Delimited, A::None, "⟪", "⟫", 100, 2});
  env.notation.push_back({P::Reduction, A::None, "∑", "", 67, 2});
  env.notation.push_back({P::Index, A::None, "[]", "]", 100, 3});
  for (StringRef value :
       {"a ⊙ b + c", "√ a ⊙ b", "a⊤.field", "⟪a, b⟫", "a[i,j]",
        "∑ x in xs, x * x + c", "∑ (x ∈ xs) (y ∈ ys) with x == y, x * y"}) {
    auto input = "module m\ndef f():\n    " + value.str() + "\n";
    auto parsed = read(input, {}, env);
    check(parsed.status() == Status::Complete, value);
    if (parsed.status() != Status::Complete)
      report(parsed);
    auto formatted = format(parsed);
    check(formatted.complete &&
              equivalent(parsed, read(formatted.text, {}, env)),
          "notation formatter preserves environment");
  }
  auto low = read("module m\ndef f():\n    a ⊙ b + c\n", {}, env);
  auto higher = env;
  higher.notation[0].precedence = 64;
  auto high = read("module m\ndef f():\n    a ⊙ b + c\n", {}, higher);
  check(!equivalent(low, high),
        "same bytes with changed import change grouping");
  for (NotationDescriptor bad :
       {NotationDescriptor{P::Infix, A::Left, "+", "", 60, 2},
        {P::Infix, A::Left, "words", "", 66, 2},
        {P::Delimited, A::None, "⟪", "⟩", 100, 1},
        {P::Infix, A::Left, "⊙", "", 0, 2},
        {P::Infix, A::Left, "∑", "", 66, 2}}) {
    check(read("module m\n", {}, Environment{{bad}}).status() ==
              Status::Partial,
          "invalid imported descriptor refuses even when unused");
  }
  auto conflicting = env;
  conflicting.notation.push_back({P::Postfix, A::None, "⊙", "", 66, 1});
  check(read("module m\n", {}, conflicting).status() == Status::Partial,
        "unused conflicting imported position refuses");
  auto mixed = env;
  mixed.notation.push_back({P::Infix, A::Right, "⊗", "", 66, 2});
  check(read("module m\ndef f():\n    a ⊙ b ⊗ c\n", {}, mixed).status() ==
            Status::Partial,
        "mixed association requires grouping");
  check(read("module m\ndef f():\n    a ⊙ (b ⊗ c)\n", {}, mixed).status() ==
            Status::Complete,
        "explicit grouping allows mixed association");
  for (StringRef declaration :
       {"pub operator infixl(66) ⊙ = product", "operator + = add",
        "notation ⟪a,b⟫ = pair(a,b)", "indexing a[i,j] = lookup(a,i,j)",
        "reduction ∑ = sum, filtered_sum"}) {
    auto parsed = read("module m\n" + declaration.str() + "\n");
    check(parsed.status() == Status::Complete, declaration);
    if (parsed.status() != Status::Complete)
      report(parsed);
  }
  refused("module m\nnotation ⟪a,b⟫ = pair(b,a)\n", "syntax.notation");
  refused("module m\noperator infixl(101) ⊙ = product\n", "syntax.notation");
  auto comments = read("module m  \r\n// keep these spaces   \r\ndef f():\r\n  "
                       "  \"literal  \"  \r\n");
  auto formatted = format(comments);
  check(formatted.complete &&
            formatted.text == "module m\n// keep these spaces   \ndef f():\n   "
                              " \"literal  \"\n",
        "format preserves comment and string content");
  auto scopedHeaders = parseHeaders(source::Revision(
      {"m", "module m\nmodule N:\n    def f():\n        a ⊙ b + c\n", ""}));
  Environments scopes{{9, env}};
  auto scoped = parseBodies(scopedHeaders, {}, scopes);
  check(scoped.status() == Status::Complete && format(scoped).complete,
        "nested scope uses and retains exact imported environment");
}
void descriptorDeclarations() {
  for (StringRef declaration : {"operator infixl(60) + = add",
                                "operator ∑ = sum", "reduction + = sum"}) {
    refused("module m\n" + declaration.str() + "\n", "syntax.notation");
  }
}
void controlExpressions() {
  for (StringRef body :
       {"    x = if b:\n        1\n    else:\n        2\n    x\n",
        "    x = match v:\n        case A:\n            1\n        case B:\n   "
        "         2\n    x\n",
        "    return if b:\n        1\n    else:\n        2\n"}) {
    auto s = read("module m\ndef f():\n" + body.str());
    check(s.status() == Status::Complete, "conditional expression");
    if (s.status() != Status::Complete)
      report(s);
    check(format(s).complete, "conditional expression formatting");
  }
  refused("module m\ndef f():\n    x = if b:\n        1\n", "syntax.expected");
  for (StringRef head : {"struct S", "enum E", "type T = F", "domain D = F"}) {
    auto s = read("module m\ndef bad(:\n    x\n" + head.str() + "\n");
    check(s.diagnostics().size() < 10, "all declaration heads bound recovery");
  }
}
void formatCases() {
  auto parsed =
      read("module m\ndef f( x:F , y:F )->F:\n    z=x+y\n    f (z, y)\n");
  auto formatted = format(parsed);
  check(
      formatted.complete &&
          formatted.text ==
              "module m\ndef f(x: F, y: F) -> F:\n    z = x + y\n    f(z, y)\n",
      "format normalizes signature, binding, operators and calls");
  check(format(read(formatted.text)).text == formatted.text,
        "spacing idempotence");
  check(read("module m\ndef f():\n    guard.field\n").status() ==
            Status::Complete,
        "contextual guard can head a projection");
  refused("module m\ndef f():\n    \"\\n\"\n", "source.string");
  check(read("module m\ndef f():\n    \"tab\tcontent\"\n").status() ==
            Status::Complete,
        "explicit layout decision permits string tabs");
}
void limits() {
  for (unsigned count : {65u, 1000u, 10000u}) {
    std::string input = "module m\ndef f():\n    x";
    for (unsigned i = 0; i < count; ++i)
      input += "+x";
    refused(input + "\n", "syntax.limit");
  }
  for (uint64_t Budget::*field :
       {&Budget::bytes, &Budget::tokens, &Budget::nodes, &Budget::depth,
        &Budget::work}) {
    Budget budget;
    budget.*field = 0;
    auto s = read("module m\ndef f():\n    x\n", budget);
    check(s.status() == Status::ResourceExhausted, "zero budget stops safely");
    coverage(s, "stopped parse preserves bytes");
  }
  Budget raised;
  ++raised.depth;
  refused("module m\n", "syntax.limit", raised);
  Budget noDiagnostics;
  noDiagnostics.diagnostics = 0;
  auto partial = read("module m\n!\n", noDiagnostics);
  check(partial.status() == Status::Partial && partial.diagnostics().empty(),
        "suppressed diagnostics cannot grant complete status");
}
void mutations() {
  std::string base = "module m\nprotocol P<F: Field> roles(P,V)(x:F@P)->F@V:\n "
                     "   y <- send x to V\n    return y\n";
  for (size_t i = 0; i <= base.size(); ++i) {
    auto s = read(StringRef(base).take_front(i));
    coverage(s, "truncated editor buffer coverage");
    check(equivalent(s, read(StringRef(base).take_front(i))),
          "deterministic recovery");
  }
  std::mt19937 generator(17);
  for (unsigned i = 0; i < 2000; ++i) {
    auto changed = base;
    auto offset = generator() % changed.size();
    changed.replace(offset, generator() % 5,
                    StringRef(" :()<>\n").substr(generator() % 7, 1).str());
    auto s = read(changed);
    coverage(s, "mutated editor buffer coverage");
    if (s.status() == Status::Complete) {
      auto formatted = format(s);
      check(formatted.complete && equivalent(s, read(formatted.text)),
            "mutation formatting equivalence");
    }
  }
}
} // namespace
int main() {
  positions();
  corpus();
  designCases();
  grammar();
  notationCases();
  descriptorDeclarations();
  controlExpressions();
  formatCases();
  limits();
  mutations();
  outs() << checks << " source/syntax checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
