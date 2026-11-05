#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Source/Source.h"
#include "zkc/Syntax/Syntax.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "callbacks.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const std::string helpers = R"(
def apply<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return f(x)
def forward<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return apply(x, f)
local def ordered(x: bool, f: local fn(bool) -> bool effects(stop)) -> bool effects(f):
    result <- f(x)
    return result
local def checked(x: bool) -> bool effects(stop):
    guard x
    return x
)";
void prepares(StringRef source) {
  auto project = take(check(source));
  auto entry = take(closeNativeRun(project, "m::Run"));
  auto original = take(prepareOriginal(entry));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
} // namespace
int main() {
  Cases cases;
  cases.run("layout Math callbacks forward captures and tuple patterns", [&] {
    prepares(helpers + R"(
pub protocol Run roles(P)(x: bool @P, y: bool @P) -> bool @P:
    return forward((x, (y, x)), fn((a, (b, c))) => a == b and c == x)
)");
  });
  cases.run("one tuple argument differs from two callback arguments", [&] {
    prepares(R"(
def apply(x: bool, y: bool, f: fn(bool, bool) -> bool) -> bool:
    return f(x, y)
pub protocol Run roles(P)(x: bool @P, y: bool @P) -> bool @P:
    return apply(x, y, fn(a, b) => a == b)
)");
    refuses(check(helpers + R"(
def bad(x: (bool, bool)) -> bool:
    return apply(x, fn(a, b) => a == b)
)"),
            "source.scoped");
  });
  cases.run("Local expected callback permits its root ordered application",
            [&] {
              prepares(helpers + R"(
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    result <- ordered(x, fn(item) => checked(item))
    return result
)");
            });
  cases.run("Local callback cannot conceal an ordered operand", [&] {
    refuses(check(helpers + R"(
local def bad(x: bool) -> bool effects(stop):
    result <- ordered(x, fn(item) => checked(checked(item)))
    return result
)"),
            "source.action");
  });
  cases.run("Math callback never retries in Local mode", [&] {
    refuses(check(helpers + R"(
def bad(x: bool) -> bool:
    return apply(x, fn(item) => checked(item))
)"),
            "source.action");
  });
  cases.run("explicit empty Local callback ceiling refuses stopping body", [&] {
    refuses(check(helpers + R"(
local def clean(x: bool, f: local fn(bool) -> bool effects()) -> bool effects():
    result <- f(x)
    return result
local def bad(x: bool) -> bool effects():
    result <- clean(x, fn(item) => checked(item))
    return result
)"),
            "source.effect");
  });
  cases.run("omitted Local ceiling retains a symbolic effect dependency", [&] {
    prepares(R"(
local def apply(x: bool, f: local fn(bool) -> bool) -> bool effects(f):
    result <- f(x)
    return result
local def clean(x: bool) -> bool effects():
    result <- apply(x, fn(item) => item)
    return result
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    result <- clean(x)
    return result
)");
  });
  cases.run(
      "callback signatures cannot be ordinary results or stored fields", [&] {
        refuses(
            check("def bad() -> fn(bool) -> bool:\n    return fn(x) => x\n"),
            "source.scoped");
        auto field = check("struct Bad:\n    callback: fn(bool) -> bool\n");
        require(!field, "stored scoped callback admitted");
        consumeError(field.takeError());
        auto array = check("type Bad = [fn(bool) -> bool; 0]\n");
        require(!array, "zero-length callback array admitted");
        consumeError(array.takeError());
      });
  cases.run("callback effect contracts retain fixed vocabulary and uniqueness",
            [&] {
              refuses(check("def bad(f: fn(bool) -> bool effects(stop)) -> "
                            "bool:\n    return true\n"),
                      "source.effect");
              refuses(check("local def bad(f: local fn(bool) -> bool "
                            "effects(stop, stop)) -> bool:\n    return true\n"),
                      "source.duplicate");
              refuses(check("local def bad(f: local fn(bool) -> bool "
                            "effects(f)) -> bool:\n    return true\n"),
                      "source.effect");
            });
  cases.run(
      "callback source capture retains names patterns and authored tokens",
      [&] {
        auto project = take(check(helpers + R"(
def capture(x: bool) -> bool:
    return apply((x, x), fn((left, right)) => left == right)
)"));
        auto written = take(inspectWrittenSource(project));
        require(StringRef(written).contains("expr.lambda"),
                "callback was erased from written source");
        require(StringRef(written).contains("left"),
                "callback binder was lost");
        require(StringRef(project.sources().front().text).contains("=>"),
                "captured source lost callback arrow");
      });
  cases.run("callback authoring survives formatting without a mode annotation",
            [&] {
              const auto source = helpers + R"(
def choose(x: bool) -> bool:
    return apply(x, fn(value) => value == x)
)";
              auto tree = zkc::syntax::parse(
                  zkc::source::Revision({"m", source, "format.zkc"}));
              require(tree.status() == zkc::syntax::Status::Complete,
                      "callback syntax incomplete");
              auto formatted = zkc::syntax::format(tree);
              require(formatted.complete, "callback formatting incomplete");
              take(check(formatted.text));
              refuses(check(helpers + R"(
def bad(x: bool) -> bool:
    return apply(x, local fn(value) => value)
)"),
                      "syntax.scoped");
            });
  cases.run(
      "callback parameters never discard formal or external modifiers", [&] {
        refuses(check("def bad(f: fn(ghost item: bool) -> bool) -> bool:\n    "
                      "return true\n"),
                "source.assurance-unavailable");
        for (StringRef modifier : {"statement", "witness", "parameter"}) {
          refuses(check("def bad(f: fn(" + modifier.str() +
                        " item: bool) -> bool) -> bool:\n    return true\n"),
                  "source.layout-unavailable");
          refuses(check(helpers +
                        "def bad(x: bool) -> bool:\n    return apply(x, fn(" +
                        modifier.str() + " item) => item)\n"),
                  "source.layout-unavailable");
        }
        take(check("def apply(x: bool, f: fn(statement: bool) -> bool) -> "
                   "bool:\n    return f(x)\ndef good(x: bool) -> bool:\n    "
                   "return apply(x, fn(statement) => statement)\n"));
      });
  cases.run("enclosing ports cannot discard external binding modifiers", [&] {
    for (StringRef modifier : {"statement", "witness", "parameter"}) {
      refuses(check("def bad(" + modifier.str() +
                    " f: fn(bool) -> bool) -> bool:\n    return true\n"),
              "source.layout-unavailable");
      refuses(check("protocol Bad roles(P)(" + modifier.str() +
                    " x: bool @P) -> bool @P:\n    return x\n"),
              "source.layout-unavailable");
    }
    take(check("def good(statement: fn(bool) -> bool) -> bool:\n    "
               "return statement(true)\n"));
  });
  cases.run("callback input labels cannot be defaults", [&] {
    auto ordinary = check("def bad(item = bool) -> bool:\n    return true\n");
    require(!ordinary, "ordinary port default was interpreted as a type");
    consumeError(ordinary.takeError());
    auto callback =
        check("def bad(f = fn(bool) -> bool) -> bool:\n    return true\n");
    require(!callback, "callback port default was interpreted as a type");
    consumeError(callback.takeError());
    refuses(check("def bad(f: fn(item = bool) -> bool) -> bool:\n    "
                  "return f(true)\n"),
            "source.scoped");
    take(check("def good(f: fn(item: bool) -> bool) -> bool:\n    "
               "return f(true)\n"));
  });
  cases.run("execution entry signatures cannot erase static callback inputs",
            [&] {
              refuses(check("protocol Bad roles(P)(f: fn(bool) -> bool) -> "
                            "bool @P:\n    return true\n"),
                      "source.scoped");
              refuses(check("entry def Bad(f: fn(bool) -> bool) -> bool:\n    "
                            "return true\n"),
                      "source.scoped");
            });
  return cases.result();
}
