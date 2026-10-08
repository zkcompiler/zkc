#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace mlir;
using namespace zkc;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
std::string bytes(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out, canonicalPrintingFlags());
  return text;
}
NativeProofPolicy selection() {
  NativeProofPolicy policy;
  policy.version = 4;
  policy.entry = "main";
  policy.producer = "Alice";
  policy.validator = "Bob";
  policy.suite = "merlin3.bls12-381.fr64be/1";
  policy.service = 4;
  policy.publicInputs = {0, 2};
  return policy;
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "fixture directory argument");
  zkc::test::Cases cases;
  DialectRegistry registry;
  registerNativeDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto read = [&](StringRef name) {
    auto buffer = MemoryBuffer::getFile(Twine(argv[1]) + "/" + name + ".mlir");
    require(bool(buffer), "cannot read fixture");
    return (*buffer)->getBuffer().str();
  };
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "invalid test source");
    return module;
  };
  auto schnorr = read("schnorr-services");
  for (StringRef suite : {"merlin3.bls12-381.fr64be/1",
                          "spongefish0.7.4.keccak.bls12-381.fr64be/1"})
    for (StringRef fixture :
         {"schnorr-services", "iterated-sumcheck", "nested-schnorr"})
      cases.run(fixture + ": " + suite, [&] {
        auto module = parse(read(fixture));
        auto original = bytes(*module);
        auto policy = selection();
        policy.suite = suite.str();
        std::vector<std::pair<std::string, std::string>> expected;
        if (fixture == "schnorr-services")
          expected = {{"draw_challenge", "challenge"}};
        else {
          policy.producer = "P";
          policy.validator = "V";
          if (fixture == "iterated-sumcheck") {
            policy.publicInputs = {1, 2, 3};
            expected = {{"draw", "challenge"}};
          } else {
            policy.service = 5;
            policy.publicInputs = {0, 1, 3};
            for (StringRef call : {"first", "second"}) {
              auto prefix =
                  mathematical::expandedApplicationSite("segment", call);
              expected.emplace_back(
                  mathematical::expandedApplicationSite(prefix,
                                                        "draw_challenge"),
                  mathematical::expandedApplicationSite(prefix, "challenge"));
            }
          }
        }
        auto resolved = take(selectNativeProofDraws(*module, policy));
        require(resolved.draws == expected,
                "derived query/delivery order differs");
        policy.draws = expected;
        require(encodeNativeProofPolicy(resolved) ==
                    encodeNativeProofPolicy(policy),
                "selection changed an explicit policy choice");
        auto selected = take(constructNativeProof(*module, resolved));
        auto explicitProof = take(constructNativeProof(*module, policy));
        require(selected.descriptor == explicitProof.descriptor &&
                    bytes(*selected.module) == bytes(*explicitProof.module),
                "resolved policy changed proof construction");
        require(bytes(*module) == original, "selection mutated original");
      });
  cases.run(
      "explicit public, role, service and acceptance choices remain mandatory",
      [&] {
        auto module = parse(schnorr);
        auto policy = selection();
        policy.publicInputs.pop_back();
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-public-bindings");
        policy = selection();
        policy.service = 3;
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-verifier-service");
        policy = selection();
        policy.validator = "Nobody";
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-interface");
        policy = selection();
        policy.acceptance = 1;
        refuses(selectNativeProofDraws(*module, policy),
                "native-proof-interface");
        policy = selection();
        policy.suite = "uninstalled";
        refuses(selectNativeProofDraws(*module, policy), "native-proof-policy");
        policy = selection();
        policy.draws = {{"draw_challenge", "challenge"}};
        refuses(selectNativeProofDraws(*module, policy), "native-proof-policy");
      });
  cases.run(
      "strict policies still require exact selected occurrence names", [&] {
        auto module = parse(schnorr);
        auto policy = selection();
        refuses(constructNativeProof(*module, policy), "native-proof-policy");
        policy.draws = {{"draw_challenge", "wrong_delivery"}};
        refuses(constructNativeProof(*module, policy),
                "native-proof-reverse-message");
      });
  cases.run("derived delivery must carry the actual query result", [&] {
    auto text = schnorr;
    auto position = text.find("%challenge = protocol.exchange %c");
    require(position != std::string::npos, "missing delivery");
    text.replace(
        position, StringRef("%challenge = protocol.exchange %c").size(),
        "%altered = algebra.field_add %c, %c : "
        "(!algebra.field<\"bls12-381.fr\">, !algebra.field<\"bls12-381.fr\">) "
        "-> !algebra.field<\"bls12-381.fr\">\n%challenge = protocol.exchange "
        "%altered");
    auto module = parse(text);
    refuses(selectNativeProofDraws(*module, selection()),
            "native-proof-reverse-message");
  });
  cases.run("producer messages cannot split query and delivery", [&] {
    auto module = parse(schnorr);
    protocol_ir::ExchangeOp commitment;
    protocol_ir::QueryOp challenge;
    module->walk([&](protocol_ir::ExchangeOp op) {
      if (op.getSite() == "commitment")
        commitment = op;
    });
    module->walk([&](protocol_ir::QueryOp op) {
      if (op.getSite() == "draw_challenge")
        challenge = op;
    });
    require(bool(commitment) && bool(challenge), "missing events");
    commitment->moveAfter(challenge);
    require(succeeded(verify(*module)), "reordered source is ill formed");
    refuses(selectNativeProofDraws(*module, selection()),
            "native-proof-prefix");
  });
  cases.run(
      "owned selection captures preparation diagnostics and locations", [&] {
        // Builtin module attributes pass MLIR formation, but protocol
        // preparation must refuse preexisting projection metadata.
        StringRef text =
            R"(module attributes {pir.mathematical_interfaces = true} {
          "protocol.module"() ({
            "protocol.func"() ({^entry(%ok:i1):
              "protocol.return"(%ok):(i1)->()
            }) {sym_name="main0",function_type=(i1)->i1,roles=["P","V"],
                input_roles=[["V"]],output_roles=[["V"]]}:()->()
          }) {profile=#protocol.profile<protocol>}:()->()
        })";
        NativeProofPolicy policy;
        policy.version = 4;
        policy.entry = "main0";
        policy.producer = "P";
        policy.validator = "V";
        policy.publicInputs = {0};
        NativeProofOptions options{NativeProofSelection{policy}};
        auto result =
            compileNativeProof(text, "selection.mlir", options, registry);
        require(!result,
                "preexisting projection metadata reached construction");
        bool captured = false;
        std::string diagnostic;
        auto remaining =
            handleErrors(result.takeError(), [&](const CompilationError &e) {
              diagnostic = e.message;
              captured =
                  namesIdentifier(e.message, "native-proof-preparation") &&
                  namesIdentifier(e.message, "mathematical-module") &&
                  any_of(e.locations, [](const DiagnosticLocation &location) {
                    return location.filename == "selection.mlir" &&
                           location.line;
                  });
            });
        if (remaining)
          throw std::runtime_error(toString(std::move(remaining)));
        require(captured,
                "selection lost owned preparation diagnostics or location: " +
                    diagnostic);
      });
  cases.run("authored selection retains an empty construction explicitly", [&] {
    auto module = parse(R"(module { "protocol.module"() ({
      "protocol.func"() ({^entry(%ok:i1): "protocol.return"(%ok):(i1)->()
      }) {sym_name="main",function_type=(i1)->i1,roles=["P","V"],
          input_roles=[["V"]],output_roles=[["V"]]}:()->()
    }) {profile=#protocol.profile<protocol>}:()->() })");
    NativeProofPolicy policy;
    policy.version = 4;
    policy.entry = "main";
    policy.producer = "P";
    policy.validator = "V";
    policy.publicInputs = {0};
    auto resolved = take(selectNativeProofDraws(*module, policy));
    require(resolved.draws.empty() && resolved.suite.empty(),
            "authored policy changed");
    take(constructNativeProof(*module, resolved));
  });
  return cases.result();
}
