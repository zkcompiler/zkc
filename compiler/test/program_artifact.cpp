#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
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
source::Participants program(ModuleOp module) {
  auto json = take(protocol::exportModule(module));
  auto decoded = take(source::decode(json));
  require(std::holds_alternative<source::Participants>(decoded),
          "wrong export kind");
  return std::get<source::Participants>(std::move(decoded));
}
source::Function &calculation(source::Participants &program) {
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
  auto original = program(*module);
  auto encoded = [&](const source::Participants &program) {
    if (auto e = source::checkStructure(program))
      throw std::runtime_error(llvm::toString(std::move(e)));
    if (auto e = protocol::admit(program, true))
      throw std::runtime_error(llvm::toString(std::move(e)));
    return printJson(source::encode(program));
  };
  cases.run("actual decoded artifact", [&] {
    if (auto e = protocol::verifyProgramArtifact(*module, encoded(original)))
      throw std::runtime_error(llvm::toString(std::move(e)));
  });
  auto negative = [&](StringRef name,
                      llvm::function_ref<void(source::Participants &)> mutate) {
    cases.run(name, [&] {
      auto candidate = original;
      mutate(candidate);
      auto bytes = encoded(candidate); // Every mutant remains executable.
      auto result = protocol::verifyProgramArtifact(*module, bytes);
      require(bool(result), "wrong artifact passed correspondence");
      require(namesIdentifier(llvm::toString(std::move(result)),
                              "artifact-correspondence"),
              "wrong refusal code");
    });
  };
  negative("serialized primitive uses wrong operand", [&](auto &p) {
    for (auto &instruction : *calculation(p).body)
      if (auto *operation = instruction.template get<source::Operation>()) {
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
    function.body->back().template get<source::Return>()->values[0] =
        function.arguments[0].name;
  });
  negative("serialized send uses local input", [&](auto &p) {
    for (auto &participant : p.participants)
      for (auto &instruction : participant.body)
        if (auto *send = instruction.template get<source::Send>()) {
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
    source::walk(*function.body, [&](source::Instruction &instruction) {
      if (auto *op = instruction.get<source::Operation>())
        for (auto &input : op->inputs)
          if (input == old)
            input = "renamed";
    });
    if (auto e = protocol::verifyProgramArtifact(*module, encoded(renamed)))
      throw std::runtime_error(llvm::toString(std::move(e)));
  });
  cases.run("removed serialized storage release", [&] {
    auto released = OwningOpRef<ModuleOp>(cast<ModuleOp>((*module)->clone()));
    require(succeeded(protocol::releaseLocalStorage(*released)),
            "storage pass refused");
    auto candidate = program(*released);
    bool removed = false;
    for (auto &function : candidate.functions)
      if (function.body)
        for (auto it = function.body->begin(); it != function.body->end(); ++it)
          if (it->get<source::Release>()) {
            function.body->erase(it);
            removed = true;
            break;
          }
    require(removed, "missing released value");
    auto error = protocol::verifyProgramArtifact(*released, encoded(candidate));
    require(bool(error) && namesIdentifier(llvm::toString(std::move(error)),
                                           "artifact-correspondence"),
            "removed release escaped");
  });
  cases.run("program parameters are refused even without service ports", [&] {
    auto artifact = original;
    artifact.participants.front().parameters = {{"n", std::string("4")}};
    auto e = protocol::admit(artifact, true);
    require(bool(e) && namesIdentifier(llvm::toString(std::move(e)),
                                       "service-profile-required"),
            "program admitted legacy static parameters");
  });
  cases.run(
      "program participant calls are refused even without service ports", [&] {
        auto artifact = original;
        source::Instruction instruction;
        instruction.site = "invoke";
        source::ProtocolCall call;
        call.callee = artifact.participants.back().name;
        instruction.value = call;
        artifact.participants.front().body.insert(
            artifact.participants.front().body.begin(), instruction);
        auto e = protocol::admit(artifact, true);
        require(bool(e) && namesIdentifier(
                               llvm::toString(std::move(e)),
                               "service-participant-composition-unsupported"),
                "program admitted legacy participant call");
      });
  return cases.result();
}
