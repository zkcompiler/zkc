#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass refused");
}
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:i1,%b:i1):
   %both = arith.andi %a,%b : i1
   %seen = protocol.exchange %both {site="message",sender="P",receiver="V"} : i1
   "protocol.return"(%both,%seen) : (i1,i1)->()
 }) {sym_name="main",function_type=(i1,i1)->(i1,i1),roles=["P","V"],input_roles=[["P"],["P"]],output_roles=[["P"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
program::Participants readProgram(ModuleOp module) {
  auto json = take(protocol::exportModule(module));
  auto decoded = take(program::decode(json));
  return decoded;
}
program::Function &calculation(program::Participants &program) {
  for (auto &function : program.functions)
    if (function.arguments.size() == 2)
      return function;
  throw std::runtime_error("missing calculation");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  Cases cases;
  auto module = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(module), "fixture parse refused");
  run(*module, protocol::createProjectProtocolPass(false));
  run(*module, protocol::createLowerMathPass());
  require(succeeded(protocol::lowerPhysical(*module)),
          "physical lowering refused");
  auto original = readProgram(*module);
  auto encoded = [&](const program::Participants &program) {
    if (auto e = program::checkStructure(program))
      throw std::runtime_error(llvm::toString(std::move(e)));
    if (auto e = protocol::admit(program))
      throw std::runtime_error(llvm::toString(std::move(e)));
    return printJson(program::encode(program));
  };
  cases.run("actual decoded artifact", [&] {
    auto checked =
        take(protocol::verifyProgramArtifact(*module, encoded(original)));
    require(program::encode(checked) == program::encode(original),
            "verified artifact changed on return");
  });
  cases.run("unexpanded local.apply is internal to mathematical locals", [&] {
    auto candidate = original;
    auto &function = calculation(candidate);
    function.body.front().value = program::LocalApply{"callee", {}, {}};
    auto refusal = program::checkStructure(candidate);
    require(bool(refusal), "unexpanded local.apply entered physical carrier");
    llvm::consumeError(std::move(refusal));
  });
  cases.run("program codecs require defined callable bodies", [&] {
    auto json = program::encode(original);
    auto &functions = *(*json.getAsArray())[3].getAsArray();
    (*functions.front().getAsArray())[4] = "external";
    auto decoded = program::decode(json);
    require(!decoded, "undefined callable passed the physical decoder");
    require(namesIdentifier(llvm::toString(decoded.takeError()),
                            "interactive-external-body"),
            "wrong undefined callable refusal");
  });
  cases.run("decoder bounds programmatic strings before semantic admission",
            [&] {
              // Direct JSON values exercise Program's own size bound
              // independently of the text parser's byte limit. LLVM writes
              // backspace/form feed as six bytes, so these shorter strings also
              // exceed the encoded-size ceiling.
              for (char value : {'x', '\b', '\f'}) {
                auto json = program::encode(original);
                auto &functions = *(*json.getAsArray())[3].getAsArray();
                (*functions.front().getAsArray())[1] =
                    std::string(value == 'x' ? 1048576 : 174763, value);
                refuses(program::decode(json), "source-limit");
              }
            });
  cases.run("native logical origin arguments round trip", [&] {
    auto candidate = original;
    calculation(candidate).origin->arguments = {{"F", "bls12-381.fr"}};
    auto json = take(parseJson(encoded(candidate)));
    auto decoded = take(program::decode(json));
    if (auto e = protocol::admit(decoded))
      throw std::runtime_error(llvm::toString(std::move(e)));
    require(program::encode(decoded) == json, "logical arguments were lost");
  });
  auto negative =
      [&](StringRef name,
          llvm::function_ref<void(program::Participants &)> mutate) {
        cases.run(name, [&] {
          auto candidate = original;
          mutate(candidate);
          auto bytes = encoded(candidate); // Every mutant remains executable.
          auto result = protocol::verifyProgramArtifact(*module, bytes);
          require(!result, "wrong artifact passed correspondence");
          require(namesIdentifier(llvm::toString(result.takeError()),
                                  "artifact-correspondence"),
                  "wrong refusal code");
        });
      };
  negative("serialized primitive uses wrong operand", [&](auto &p) {
    for (auto &instruction : calculation(p).body)
      if (auto *operation = instruction.template get<program::Operation>()) {
        operation->inputs[1] = operation->inputs[0];
        return;
      }
    throw std::runtime_error("missing primitive");
  });
  negative("serialized local argument order changed", [&](auto &p) {
    auto &function = calculation(p);
    std::swap(function.arguments[0], function.arguments[1]);
  });
  negative("serialized local return changed", [&](auto &p) {
    auto &function = calculation(p);
    function.body.back().template get<program::Return>()->values[0] =
        function.arguments[0].name;
  });
  negative("serialized send uses local input", [&](auto &p) {
    for (auto &participant : p.participants)
      for (auto &instruction : participant.body)
        if (auto *send = instruction.template get<program::Send>()) {
          send->input = participant.arguments.front().name;
          return;
        }
    throw std::runtime_error("missing send");
  });
  negative("serialized entry renamed",
           [&](auto &p) { p.entries.front().name = "other"; });
  negative("serialized retained origin changed",
           [&](auto &p) { calculation(p).origin->definition = "other"; });
  cases.run("consistent SSA renaming is permitted", [&] {
    auto renamed = original;
    auto &function = calculation(renamed);
    auto old = function.arguments[0].name;
    function.arguments[0].name = "renamed";
    program::walk(function.body, [&](program::Instruction &instruction) {
      if (auto *op = instruction.get<program::Operation>())
        for (auto &input : op->inputs)
          if (input == old)
            input = "renamed";
    });
    take(protocol::verifyProgramArtifact(*module, encoded(renamed)));
  });
  cases.run("removed serialized storage release", [&] {
    auto released = OwningOpRef<ModuleOp>(cast<ModuleOp>((*module)->clone()));
    require(succeeded(protocol::releaseLocalStorage(*released)),
            "storage pass refused");
    auto candidate = readProgram(*released);
    bool removed = false;
    for (auto &function : candidate.functions)
      for (auto it = function.body.begin(); it != function.body.end(); ++it)
        if (it->get<program::Release>()) {
          function.body.erase(it);
          removed = true;
          break;
        }
    require(removed, "missing released value");
    auto error = protocol::verifyProgramArtifact(*released, encoded(candidate));
    require(!error && namesIdentifier(llvm::toString(error.takeError()),
                                      "artifact-correspondence"),
            "removed release escaped");
  });
  cases.run("hostile storage releases fail Program admission", [&] {
    for (unsigned mutation = 0; mutation != 5; ++mutation) {
      auto candidate = original;
      auto &function = calculation(candidate);
      const auto input = function.arguments.front().name;
      program::Instruction release{"", program::Release{{input}}};
      StringRef code;
      if (mutation == 0) {
        function.body.insert(function.body.begin(), release);
        code = "interactive-resource-reuse";
      } else if (mutation == 1) {
        function.body.insert(function.body.end() - 1, {release, release});
        code = "interactive-release-unavailable";
      } else if (mutation == 2) {
        release.get<program::Release>()->values.clear();
        function.body.insert(function.body.begin(), release);
        code = "interactive-release-empty";
      } else if (mutation == 3) {
        release.site = "unexpected";
        function.body.insert(function.body.begin(), release);
        auto refusal = program::checkStructure(candidate);
        require(bool(refusal) &&
                    namesIdentifier(llvm::toString(std::move(refusal)),
                                    "source-model-shape"),
                "unencodable release site passed structure checking");
        continue;
      } else {
        auto &body = candidate.participants.front().body;
        body.insert(body.begin(), release);
        code = "interactive-release-context";
      }
      // Exercise the portable decoder before the independent semantic gate.
      if (auto error = program::checkStructure(candidate))
        throw std::runtime_error(llvm::toString(std::move(error)));
      auto decoded = take(program::decode(program::encode(candidate)));
      auto refusal = protocol::admit(decoded);
      require(bool(refusal) &&
                  namesIdentifier(llvm::toString(std::move(refusal)), code),
              "hostile release missed its admission boundary");
    }
  });
  cases.run("program parameters are refused even without service ports", [&] {
    auto artifact = program::encode(original);
    auto &participant =
        *(*artifact.getAsArray())[4].getAsArray()->front().getAsArray();
    participant[4] = llvm::json::Array{llvm::json::Array{"n", "4"}};
    refuses(program::decode(artifact), "interactive-shape");
  });
  cases.run("participant composition opcode is not in the carrier", [&] {
    auto artifact = program::encode(original);
    auto &participant =
        *(*artifact.getAsArray())[4].getAsArray()->front().getAsArray();
    participant[7].getAsArray()->insert(participant[7].getAsArray()->begin(),
                                        llvm::json::Array{"call", "invoke", "p",
                                                          llvm::json::Array{},
                                                          llvm::json::Array{}});
    refuses(program::decode(artifact), "interactive-instruction");
  });
  return cases.result();
}
