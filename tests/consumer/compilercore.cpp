#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Translation/Protocol.h"

static llvm::Expected<zkc::Compilation> compile() {
  auto analysis = zkc::frontend::analyzeProtocol(R"(module {
    fn Identity(x: bool) -> bool { x }
    protocol Send {
      roles(P, V); inputs(P x: bool); outputs(V bool);
      local P: let a = Identity(x);
      message value: P(a) -> V(y);
      return y;
    }
    instance run: Send { roles(P = prover, V = verifier); }
    entry main = run;
  })",
                                                 "consumer.pir");
  auto source = zkc::lowerSource(analysis);
  if (!source)
    return source.takeError();
  // The returned result owns everything needed after these locals die.
  mlir::DialectRegistry registry;
  return zkc::compileProtocol(std::move(*source), {}, registry);
}
int main() {
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
  return structured ? 0 : 5;
}
