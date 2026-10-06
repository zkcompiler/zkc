#include "zkc/Compiler/Run.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Diagnostics.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc;
namespace {
constexpr StringLiteral fixture = R"(module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%go: i1):
    protocol.guard %go {owner="solo", site="guard"}
    "protocol.return"(%go) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["solo"],
      input_roles=[["solo"]], output_roles=[["solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () })";
void require(bool ok, StringRef message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
CompiledRun compile(bool simplify, bool release) {
  // Input storage and registry die before the caller verifies the result.
  std::string text = fixture.str();
  mlir::DialectRegistry registry;
  RunOptions options;
  options.simplify = simplify;
  options.releaseStorage = release;
  auto result = compileRun(text, "native-owned.mlir", options, registry);
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
void refuses(StringRef text, const RunOptions &options, StringRef expected) {
  mlir::DialectRegistry registry;
  auto result = compileRun(text, "rejected.mlir", options, registry);
  require(!result, "invalid native invocation accepted");
  bool owned = false;
  handleAllErrors(result.takeError(), [&](const CompilationError &error) {
    owned = StringRef(error.message).contains(expected);
  });
  require(owned, "native error lost owned diagnostic");
}
} // namespace
int main() {
  for (bool simplify : {false, true})
    for (bool release : {false, true}) {
      auto result = compile(simplify, release);
      require(!result.compilation.source(),
              "MLIR invocation invented a Document");
      require(succeeded(mlir::verify(result.compilation.module())),
              "owned native IR invalid");
      auto bundle = json::parse(result.bundle);
      require(bool(bundle), "bundle is not JSON");
      auto *object = bundle->getAsObject();
      require(object && object->getString("format") == "zkc.run/1",
              "bundle version");
      auto *steps = object->getArray("steps");
      require(steps && steps->size() == 2,
              "guard became a demand prefix or was erased");
      require((*steps)[0].getAsObject()->getInteger("anchor") == 0 &&
                  (*steps)[1].getAsObject()->get("anchor")->getAsNull(),
              "guard/return anchors");
      auto second = compile(simplify, release);
      require(result.bundle == second.bundle, "nondeterministic native bundle");
      result = std::move(second);
      require(succeeded(mlir::verify(result.compilation.module())),
              "move lost module context");
    }
  refuses("module {}", {}, "run-source-profile");
  refuses("module {", {}, "error");
  RunOptions missing;
  missing.entry = "absent";
  refuses(fixture, missing, "run-entry");
  missing.entry.assign(4097, 'x');
  refuses(fixture, missing, "run-input-limit");
  std::string deep(65, '{');
  refuses(deep, {}, "run-input-limit");
  outs() << "native invocation ownership, guards and diagnostics passed\n";
}
