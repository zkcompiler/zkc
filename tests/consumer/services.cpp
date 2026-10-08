#include "zkc/Contracts/Services.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"

// Installed service support is the registered RNG contract set. Arbitrary
// request/reply families are not declarations in the current Program model.
int main() {
  for (llvm::StringRef field : {"bls12-381.fr", "ristretto255.scalar",
                                "bn254.fr", "koala-bear.ext8-binomial3"}) {
    std::string contract = ("random." + field + "/1").str();
    if (zkc::protocol::randomServiceField(contract) != field)
      return 1;
    std::string source =
        "!f = !algebra.field<\"" + field.str() +
        "\">\n"
        "!rng = !protocol.service_ref<\"" +
        contract +
        "\">\n"
        "module { \"protocol.module\"() ({\n"
        " \"protocol.func\"() ({ ^entry(%rng:!rng):\n"
        "  %a = \"protocol.query\"(%rng) "
        "{method=\"draw\",owner=\"P\",site=\"first\"} : (!rng)->!f\n"
        "  %b = \"protocol.query\"(%rng) "
        "{method=\"draw\",owner=\"P\",site=\"second\"} : (!rng)->!f\n"
        "  \"protocol.return\"(%a,%b) : (!f,!f)->()\n"
        " }) "
        "{sym_name=\"main\",function_type=(!rng)->(!f,!f),roles=[\"P\"],input_"
        "roles=[[\"P\"]],output_roles=[[\"P\"],[\"P\"]]} : ()->()\n"
        "}) {profile=#protocol.profile<protocol>} : ()->() }";
    mlir::DialectRegistry registry;
    auto run = zkc::compileRun(source, "installed-services.mlir", {}, registry);
    if (!run) {
      llvm::errs() << llvm::toString(run.takeError());
      return 2;
    }
    auto artifact = zkc::protocol::exportModule(run->compilation.module());
    if (!artifact) {
      llvm::errs() << llvm::toString(artifact.takeError());
      return 3;
    }
    auto program = zkc::program::decode(*artifact);
    if (!program) {
      llvm::errs() << llvm::toString(program.takeError());
      return 4;
    }
    if (auto error = zkc::protocol::admit(*program)) {
      llvm::errs() << llvm::toString(std::move(error));
      return 5;
    }
    if (program->participants.size() != 1)
      return 6;
    const auto &participant = program->participants.front();
    if (participant.services.size() != 1 ||
        participant.services.front().contract != contract ||
        participant.body.size() != 3)
      return 7;
    for (unsigned i = 0; i < 2; ++i) {
      const auto *query = participant.body[i].get<zkc::program::ServiceQuery>();
      if (!query || query->method != "draw" ||
          query->port != participant.services.front().name ||
          query->outputs.size() != 1)
        return 8;
    }
    auto wrong = source;
    auto method = wrong.find("method=\"draw\"");
    wrong.replace(method, std::string("method=\"draw\"").size(),
                  "method=\"unregistered\"");
    auto rejected = zkc::compileRun(wrong, "wrong-service.mlir", {}, registry);
    if (rejected)
      return 9;
    llvm::consumeError(rejected.takeError());
    auto invalid = *program;
    invalid.participants.front().services.front().contract = "custom.service/1";
    auto refused = zkc::protocol::admit(invalid);
    if (!refused)
      return 10;
    llvm::consumeError(std::move(refused));
  }
}
