#include "../lib/Compiler/Run.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Support/Json.h"
using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
constexpr StringLiteral fixture = R"(module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    %c = arith.andi %a,%b : i1
    %received = protocol.exchange %c {sender="P",receiver="V",site="message"} : i1
    protocol.guard %received {owner="V",site="check"}
    "protocol.return"(%received) : (i1)->()
  }) {sym_name="main",function_type=(i1,i1)->i1,roles=["P","V"],input_roles=[["P"],["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
int main() {
  Cases cases;
  DialectRegistry registry;
  auto compiled = take(compileRun(fixture, "source.mlir", {}, registry));
  auto physical = cast<ModuleOp>(compiled.compilation.module());
  auto source = parseSourceString<ModuleOp>(fixture, physical.getContext());
  require(bool(source), "source parse");
  cases.run("source order matches final bytes", [&] {
    if (auto e = zkc::detail::verifyRunBundle(*source, physical,
                                              compiled.bundle, "main"))
      throw std::runtime_error(toString(std::move(e)));
  });
  auto negative = [&](StringRef name,
                      llvm::function_ref<void(json::Object &)> change) {
    cases.run(name, [&] {
      auto value = take(json::parse(compiled.bundle));
      change(*value.getAsObject());
      auto e = zkc::detail::verifyRunBundle(*source, physical, printJson(value),
                                            "main");
      require(bool(e) &&
                  namesIdentifier(toString(std::move(e)), "run-correspondence"),
              "altered schedule accepted");
    });
  };
  negative("roles reordered", [](auto &o) {
    std::swap((*o.getArray("roles"))[0], (*o.getArray("roles"))[1]);
  });
  negative("source anchor changed", [](auto &o) {
    (*o.getArray("steps"))[0].getAsObject()->get("anchor")->operator=(1);
  });
  negative("calculation regrouped as an independent source action",
           [](auto &o) {
             // [L,S,R] at anchor 0 becomes [L] at 0 and [S,R] at 1.
             // Rust admits either supplied structure. Only the former matches
             // the compiler's source coordinates, despite unchanged step order.
             auto &steps = *o.getArray("steps");
             for (size_t i = 1; i < steps.size(); ++i) {
               auto *step = steps[i].getAsObject();
               if (auto anchor = step->getInteger("anchor"))
                 (*step)["anchor"] = *anchor + 1;
             }
           });
  negative("instruction coordinate changed", [](auto &o) {
    (*o.getArray("steps"))[0].getAsObject()->get("instruction")->operator=(1);
  });
  negative("source step reordered", [](auto &o) {
    std::swap((*o.getArray("steps"))[0], (*o.getArray("steps"))[1]);
  });
  negative("completion step removed",
           [](auto &o) { o.getArray("steps")->pop_back(); });
  negative("entry changed", [](auto &o) { o["entry"] = "other"; });
  cases.run("duplicate decoded object keys refused", [&] {
    auto bytes = compiled.bundle;
    bytes.insert(1, "\"entry\":\"main\",");
    auto e = zkc::detail::verifyRunBundle(*source, physical, bytes, "main");
    require(bool(e) && namesIdentifier(toString(std::move(e)), "artifact-json"),
            "duplicate key accepted");
  });
  cases.run("excessive envelope nesting refused before parsing", [&] {
    std::string bytes(257, '[');
    bytes += std::string(257, ']');
    auto e = zkc::detail::verifyRunBundle(*source, physical, bytes, "main");
    require(bool(e) &&
                namesIdentifier(toString(std::move(e)), "artifact-json-limit"),
            "depth bound missing");
  });
  return cases.result();
}
