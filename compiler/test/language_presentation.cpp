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
  cases.run(
      "deferred dimension conflicts locate the use and its declaration", [] {
        auto captured = take(
            capture({{"library",
                      "module library;\npub math fn dimension<F:Field,N:nat>("
                      "values:[F;pow2(N)],point:[F;N])->bool{return true;}\n",
                      "library.zkc"},
                     {"main",
                      "module main;\ndomain F=field(\"koala-bear\");\n"
                      "fn bad(x:F)->bool{return "
                      "library::dimension([x,x,x,x,x,x,x,x],[x]);}\n",
                      "main.zkc"}}));
        auto analysis = analyze(captured);
        require(analysis.diagnostics().size() == 1,
                "expected a dimension conflict");
        const auto &diagnostic = analysis.diagnostics().front();
        require(diagnostic.code == "source.type" && diagnostic.primary &&
                    diagnostic.primary->module.index == 1,
                "deferred conflict does not locate the call");
        auto text = formatDiagnostics(analysis.diagnostics(), &captured);
        require(text.find("note: related source at library.zkc:2:") !=
                    std::string::npos,
                text);
      });
  cases.run("printable source text retains quotes and backslashes", [] {
    auto captured = take(capture(
        {{"m", "module m;\ndomain F=field(\"koala-bear\");\n", "source.zkc"}}));
    Diagnostic diagnostic{
        "source.type", "literal \\\"text\\\"", Span{{0}, 10, 16}, {}};
    auto text = formatDiagnostics({diagnostic}, &captured);
    require(text.find("field(\"koala-bear\")") != std::string::npos &&
                text.find("literal \\\"text\\\"") != std::string::npos,
            text);
  });
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
    auto text = formatDiagnostics({diagnostic}, &capture);
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
      require(formatDiagnostics({diagnostic}, &capture)
                      .find("invalid source span") != std::string::npos,
              "invalid location was not bounded");
    }
  });
  cases.run("long lines and diagnostic lists remain bounded", [] {
    auto captured = take(
        capture({{"m", "module m;" + std::string(900000, ' '), "missing"}}));
    Diagnostic diagnostic{
        "source.type", std::string(10000, 'x'), Span{{0}, 800000, 800001}, {}};
    auto one = formatDiagnostics({diagnostic}, &captured);
    require(one.size() < 4000 && one.find('^') != std::string::npos,
            "unbounded line");
    std::vector<Diagnostic> many(10000, diagnostic);
    auto all = formatDiagnostics(many, &captured);
    require(all.size() <= 64 * 1024 && all.find("omitted") != std::string::npos,
            "unbounded diagnostics");
    diagnostic.message = "unlocated\x1b\n" + std::string(10000, 'x');
    diagnostic.primary.reset();
    auto unlocated = formatDiagnostics({diagnostic});
    require(unlocated.size() < 7000 &&
                unlocated.find('\x1b') == std::string::npos,
            "uncaptured diagnostics bypassed bounded escaping");
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
  cases.run("component inspection keeps abstract and inherited allowances", [] {
    auto captured = take(capture({{"m", R"(module m;
      pub interface Boxed<F:Field>{
        type State; fn make(x:F)->State; fn open(x:State)->F;
      }
      pub component Box<F:Field>:Boxed<F>{
        type State=F;
        fn make(x:F)->State{return State(x);}
        fn open(x:State)->F{return unpack(x);}
      }
      component Hidden<F:Field>:Boxed<F>{
        type State=F;
        fn make(x:F)->State{return State(x);}
        fn open(x:State)->F{return unpack(x);}
      }
    )",
                                   "absent"}}));
    auto project = take(analyze(captured).checkedProject());
    auto bytes = take(inspectDeclarations(project));
    auto value = take(json::parse(bytes));
    auto *items = value.getAsArray();
    require(items && items->size() == 4, bytes);
    for (auto &item : *items) {
      auto *decl = item.getAsObject();
      auto name = *decl->getString("name");
      bool abstract = name.starts_with("m::Boxed::");
      require(decl->getBoolean("abstract") == abstract &&
                  decl->getObject("owner")->getString("kind") ==
                      (abstract ? "interface" : "component"),
              "member owner or abstract status missing");
      auto *effects = decl->getObject("effects");
      require(effects->getBoolean("stop") == abstract &&
                  effects->getBoolean("opaque") == abstract,
              "abstract allowance and actual body effects differ");
      require(decl->getArray("parameters")->size() == 1,
              "enclosing component parameters are missing");
      require(decl->getArray("parameters")
                      ->front()
                      .getAsObject()
                      ->getArray("permissions")
                      ->size() == 2,
              "implicit Field Copy/Drop promises are missing");
      require(decl->getArray("parameters")
                      ->front()
                      .getAsObject()
                      ->getBoolean("inherited") == true,
              "owner parameter was presented as a member argument");
      if (!abstract) {
        auto *allowance = decl->getObject("effect_allowance");
        require(allowance && allowance->getBoolean("stop") == true &&
                    allowance->getBoolean("opaque") == true,
                "inherited effect allowance is missing");
      }
    }
    require(bytes.find("Hidden") == std::string::npos &&
                bytes.find("self:") == std::string::npos,
            "private component members or internal self names leaked");
  });
  cases.run(
      "resolved natural expressions retain readable mathematical structure",
      [] {
        auto n = take(Natural::atom("parameter:m::f::N"));
        auto inputs = take(Natural::projection("parameter:m::f::A", "Inputs"));
        NaturalArithmetic arithmetic;
        auto size =
            take(arithmetic.add(take(arithmetic.powerOfTwo(n)), inputs));
        require(formatNatural(size) == "pow2(N) + A::Inputs",
                formatNatural(size));
        Type array(Type::Kind::Array);
        array.arguments.push_back(Type{});
        array.dimension = size;
        require(formatType(array) == "[bool; pow2(N) + A::Inputs]",
                formatType(array));
        require(n.spelling().find("parameter:") != std::string::npos,
                "diagnostic formatting changed canonical natural identity");
        auto k = take(Natural::atom("parameter:m::f::K"));
        auto product = take(arithmetic.powerOfTwo(take(arithmetic.add(n, k))));
        require(formatNatural(product) == "pow2(K) * pow2(N)",
                formatNatural(product));
        zkc::test::refuses(arithmetic.powerOfTwo(inputs), "source.natural");
      });
  cases.run(
      "abstract member parameters are distinct from inherited parameters", [] {
        auto captured = take(capture({{"m", R"(module m;
      pub interface I<F:Field>{math fn lift<N:nat>(x:F)->[F;N];}
    )",
                                       "absent"}}));
        auto project = take(analyze(captured).checkedProject());
        auto value = take(json::parse(take(inspectDeclarations(project))));
        auto *parameters =
            value.getAsArray()->front().getAsObject()->getArray("parameters");
        require(parameters->size() == 2 &&
                    (*parameters)[0].getAsObject()->getBoolean("inherited") ==
                        true &&
                    (*parameters)[1].getAsObject()->getBoolean("inherited") ==
                        false,
                "member parameter was mislabeled as inherited");
      });
  return cases.result();
}
