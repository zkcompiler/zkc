#include "support/NativeCases.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"

using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;
int main() {
  zkc::test::Cases cases;
  cases.run("captured locations, related modules, escapes and EOF", [] {
    auto capture = take(
        zkc::language::capture({{"m", "module m;\n//\t\x1b\xe2\x80\xae\r\n",
                                 "/nonexistent/source\npath"},
                                {"n", "module n;", "/nonexistent/second"}}));
    auto end = uint32_t(capture.sources()[0].text.size());
    Diagnostic diagnostic{"source.type",
                          "bad\x1b message",
                          Span{{0}, 10, 11},
                          {{{1}, 0, 6}, {{0}, end, end}, {{1}, 0, 6}}};
    auto text = formatDiagnostics(capture, {diagnostic});
    require(text.find("/nonexistent/source\\0Apath:2:1 [m]") !=
                std::string::npos,
            text);
    require(text.find("second:1:1 [n]") != std::string::npos, text);
    require(text.find("path:3:1 [m]") != std::string::npos, text);
    require(text.find('\x1b') == std::string::npos &&
                text.find('\xe2') == std::string::npos,
            text);
    require(text.find("\\09") != std::string::npos &&
                text.find("\\0D") != std::string::npos,
            text);
    auto note = text.find("note:");
    require(note != std::string::npos &&
                text.find("note:", text.find("note:", note + 1) + 1) ==
                    std::string::npos,
            text);
    for (Span span :
         {Span{{7}, 0, 0}, Span{{0}, 12, 11}, Span{{0}, end, end + 1}}) {
      diagnostic.primary = span;
      require(formatDiagnostics(capture, {diagnostic})
                      .find("invalid source span") != std::string::npos,
              "invalid location was not bounded");
    }
  });
  cases.run("long lines and diagnostic lists remain bounded", [] {
    auto captured = take(
        capture({{"m", "module m;" + std::string(900000, ' '), "missing"}}));
    Diagnostic diagnostic{
        "source.type", std::string(10000, 'x'), Span{{0}, 800000, 800001}, {}};
    auto one = formatDiagnostics(captured, {diagnostic});
    require(one.size() < 4000 && one.find('^') != std::string::npos,
            "unbounded line");
    std::vector<Diagnostic> many(10000, diagnostic);
    auto all = formatDiagnostics(captured, many);
    require(all.size() <= 64 * 1024 && all.find("omitted") != std::string::npos,
            "unbounded diagnostics");
  });
  cases.run(
      "inspection reports completed contracts without private helpers", [] {
        auto captured = take(capture({{"m", R"(module m;
      type Array<F:Field,N:nat>=builtin("field_array",F,N);
      pub math fn coefficients<F:Field,N:nat>(p:formal("polynomial",F,1))->Array<F,N>{
        return intrinsic<F,N>("poly.coefficients",p);
      }
      pub fn identity<T:Type+Copy+Drop>(x:T){return x;}
      fn private_helper(x:bool){return x;}
      pub protocol Run roles(P)(x:bool@P)->(out:bool@P){return x;}
    )",
                                       "absent"}}));
        auto project = take(analyze(captured).checkedProject());
        auto bytes = take(inspectDeclarations(project));
        auto json = take(json::parse(bytes));
        auto *items = json.getAsArray();
        require(items && items->size() == 3, bytes);
        auto *first = (*items)[0].getAsObject();
        require(first->getString("name") == "m::Run",
                "declarations are not sorted");
        require(bytes.find("private_helper") == std::string::npos &&
                    bytes.find("parameter:") == std::string::npos,
                "private implementation or internal parameter names leaked");
        require(bytes.find("\"inferred\":true") != std::string::npos,
                "completed natural bound missing");
        require(take(inspectDeclarations(project)) == bytes,
                "unstable inspection");
        Limits limits;
        limits.interfaceBytes = 16;
        zkc::test::refuses(inspectDeclarations(project, limits),
                           "source.limit");
      });
  return cases.result();
}
