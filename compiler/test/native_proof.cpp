#include "Names.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Cpu/Passes.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace mlir;
using namespace zkc;
void require(bool ok, StringRef detail) {
  if (!ok) {
    errs() << detail << '\n';
    std::exit(1);
  }
}
std::string print(ModuleOp module) {
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream);
  return text;
}
int main(int argc, char **argv) {
  require(argc == 2, "fixture argument");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = parseSourceFile<ModuleOp>(argv[1], &context);
  require(bool(source), "source parse");
  auto original = print(*source);
  auto policy = parseNativeProofPolicy(
      R"(["zkc.native-proof-policy/0", "main", "Alice", "Bob", "0", "merlin3.bls12-381.fr64be/0", ["4"], ["0", "2"], [["draw_challenge", "challenge"]], "zkc.framed/0", "", []])");
  if (!policy) {
    errs() << toString(policy.takeError());
    return 1;
  }
  for (const char *suite : {"merlin3.bls12-381.fr64be/0",
                            "spongefish0.8.0.keccak.bls12-381.fr64be/0"}) {
    policy->suite = suite;
    auto built = constructNativeProof(*source, *policy);
    if (!built) {
      errs() << toString(built.takeError());
      return 1;
    }
    if (auto e = checkNativeProof(*source, *built->module, *policy)) {
      errs() << toString(std::move(e));
      return 1;
    }
    require(print(*source) == original, "constructor mutated source");
    bool changed = false;
    built->module->walk([&](Operation *op) {
      if (!changed && op->getName().getStringRef() == "algebra.field_add") {
        op->setOperand(0, op->getOperand(1));
        changed = true;
      }
    });
    require(changed, "mutation reached actual SSA operand");
    auto refusal = checkNativeProof(*source, *built->module, *policy);
    require(bool(refusal), "changed arithmetic accepted");
    consumeError(std::move(refusal));
    built = constructNativeProof(*source, *policy);
    require(bool(built), "reconstruct");
    PassManager passes(&context);
    passes.addPass(protocol::createSimplifyParticipantPass());

    passes.addPass(protocol::createLowerMathPass());

    passes.addPass(computation::createRealizeComputationsPass());
    passes.addPass(protocol::createSelectPhysicalPass());
    require(succeeded(passes.run(*built->module)), "shared physical lowering");
    auto exported = protocol::exportModule(*built->module);
    if (!exported) {
      errs() << toString(exported.takeError());
      return 1;
    }
    outs() << printJson(*exported) << '\n';
  }
  auto valid = *policy;
  policy->publicInputs.pop_back();
  auto rejected = constructNativeProof(*source, *policy);
  require(!rejected, "missing public binding accepted");
  consumeError(rejected.takeError());
  // Typed policies are checked as typed values. The public API and the JSON
  // reader refuse each invalid policy with the same code.
  auto refusal = [](Error error) {
    return error ? toString(std::move(error)) : std::string();
  };
  using Change = void (*)(NativeProofPolicy &);
  for (auto [change, code] :
       {std::pair<Change, StringRef>{
            [](NativeProofPolicy &p) { p.validator = p.producer; },
            "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.entry = "main entry"; },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.acceptance = 1024; },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.services = {4, 4}; },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.publicInputs = {2, 0}; },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.draws.clear(); }, "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.draws.push_back(p.draws.front()); },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) { p.gates = {{"gate", 65}}; },
         "native-proof-policy"},
        {[](NativeProofPolicy &p) {
           p.format = protocol::ProofFormat::RawBytes;
         },
         "native-proof-format"}}) {
    auto invalid = valid;
    change(invalid);
    auto typed = refusal(checkNativeProofPolicy(invalid));
    auto read =
        parseNativeProofPolicy(printJson(encodeNativeProofPolicy(invalid)));
    auto built = constructNativeProof(*source, invalid);
    require(namesIdentifier(typed, code) && !read && !built,
            "invalid typed policy accepted: " + typed);
    require(namesIdentifier(refusal(read.takeError()), code) &&
                namesIdentifier(refusal(built.takeError()), code),
            "typed and decoded policies refused differently");
  }
  auto selection = valid;
  require(bool(checkNativeProofPolicy(selection, true)),
          "a selection carried draws");
  selection.draws.clear();
  require(!checkNativeProofPolicy(selection, true),
          "a selection without draws was refused");
  // The JSON text ceiling bounds only text. A typed policy whose escaped
  // encoding exceeds it reaches the source-dependent checks.
  auto oversized = valid;
  oversized.draws.clear();
  auto longName = [](char prefix, unsigned index) {
    auto suffix = std::string(1, prefix) + std::to_string(index);
    return std::string(4096 - suffix.size(), '"') + suffix;
  };
  for (unsigned i = 0; i < 64; ++i) {
    oversized.draws.emplace_back(longName('q', i), longName('d', i));
    oversized.gates.emplace_back(longName('g', i), 1);
  }
  require(!checkNativeProofPolicy(oversized),
          "valid oversized typed policy refused");
  auto text =
      parseNativeProofPolicy(printJson(encodeNativeProofPolicy(oversized)));
  require(!text && namesIdentifier(refusal(text.takeError()),
                                   "native-proof-policy-limit"),
          "policy text ceiling not applied to text");
  auto direct = constructNativeProof(*source, oversized);
  require(!direct, "unknown draw occurrences accepted");
  auto reason = refusal(direct.takeError());
  require(!namesIdentifier(reason, "native-proof-policy-limit") &&
              !namesIdentifier(reason, "native-proof-policy"),
          "typed policy passed through the JSON reader: " + reason);
}
