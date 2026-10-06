#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

static llvm::Expected<zkc::Compilation> compile() {
  auto analysis = zkc::frontend::analyzeProtocol(R"(
    fn Identity(x: bool) -> bool { x }
    protocol Send {
      roles(P, V); inputs(P x: bool); outputs(V bool);
      local P: let a = Identity(x);
      message value: P(a) -> V(y);
      return y;
    }
    instance run: Send { roles(P = prover, V = verifier); }
    entry main = run;
  )",
                                                 "consumer.pir");
  auto source = zkc::lowerSource(analysis);
  if (!source)
    return source.takeError();
  // The returned result owns everything needed after these locals die.
  mlir::DialectRegistry registry;
  return zkc::compileProtocol(std::move(*source), {}, registry);
}
int main(int argc, char **argv) {
  if (argc > 2)
    return 15;
  auto result = compile();
  if (!result) {
    llvm::consumeError(result.takeError());
    return 1;
  }
  if (mlir::failed(mlir::verify(result->module())) ||
      result->source()->filename() != "consumer.pir")
    return 2;
  auto source = zkc::protocol::exportSource(result->module());
  if (!source) {
    llvm::consumeError(source.takeError());
    return 3;
  }
  mlir::DialectRegistry registry;
  auto failure =
      zkc::compileProtocol(zkc::source::Document(*source), {}, registry);
  if (failure)
    return 4;
  bool structured = false;
  llvm::handleAllErrors(
      failure.takeError(), [&](const zkc::CompilationError &e) {
        for (const auto &refusal : e.refusals)
          structured |= refusal.code == "interactive-projection-stage";
      });
  if (!structured)
    return 5;
  auto native = zkc::compileRun(R"(module { "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%value: i1):
      "protocol.return"(%value) : (i1) -> ()
    }) {sym_name="main", function_type=(i1) -> i1, roles=["Solo"],
        input_roles=[["Solo"]], output_roles=[["Solo"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })",
                                "native-consumer.mlir", {}, registry);
  if (!native) {
    llvm::consumeError(native.takeError());
    return 6;
  }
  if (native->compilation.source() ||
      mlir::failed(mlir::verify(native->compilation.module())))
    return 7;
  auto bundle = llvm::json::parse(native->bundle);
  if (!bundle) {
    llvm::consumeError(bundle.takeError());
    return 8;
  }
  if (bundle->getAsObject()->getString("format") != "zkc.run/1")
    return 9;
  // Installed CompilerCore exports both view APIs, retaining ordinary source
  // admission even when a caller presents a compiled physical module.
  auto view = zkc::analyzePublicCoin(native->compilation.module(), "{}");
  if (view)
    return 10;
  llvm::consumeError(view.takeError());
  auto checked = zkc::checkPublicCoin(native->compilation.module(), "{}", "{}");
  if (!checked)
    return 11;
  llvm::consumeError(std::move(checked));
  zkc::NativeProofOptions proofOptions;
  proofOptions.policy =
      R"(["zkc.native-proof-policy/4","main","P","V","0","","",[],[]])";
  auto proof =
      zkc::compileNativeProof(R"(module { "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%value: i1):
      %received = protocol.exchange %value {site="message", sender="P", receiver="V"} : i1
      "protocol.return"(%received) : (i1) -> ()
    }) {sym_name="main", function_type=(i1) -> i1, roles=["P","V"],
        input_roles=[["P"]], output_roles=[["V"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })",
                              "proof-consumer.mlir", proofOptions, registry);
  if (!proof) {
    llvm::consumeError(proof.takeError());
    return 12;
  }
  auto deployment = llvm::json::parse(proof->deployment);
  if (!deployment) {
    llvm::consumeError(deployment.takeError());
    return 13;
  }
  if ((*deployment->getAsArray())[0].getAsString() != "zkc.native-proof/4" ||
      mlir::failed(mlir::verify(proof->compilation.module())))
    return 14;
  if (argc == 2) {
    auto write = [&](llvm::StringRef name, llvm::StringRef bytes) {
      llvm::SmallString<256> path(argv[1]);
      llvm::sys::path::append(path, name);
      std::error_code error;
      llvm::raw_fd_ostream stream(path, error, llvm::sys::fs::OF_None);
      if (error)
        return false;
      stream << bytes;
      stream.flush();
      return !stream.has_error();
    };
    if (!write("run.bundle", native->bundle) ||
        !write("proof.deployment", proof->deployment))
      return 16;
  }
  return 0;
}
