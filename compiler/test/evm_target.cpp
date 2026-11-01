#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Evm.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Target/Evm/Target.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;

// An ordinary source consumer, also used by deployed integration checks. Keep
// the exact emitted original bytes; a parse/print cycle changes proof binding.
int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  if (argc != 5 && argc != 6) {
    errs() << "usage: evm_target ORIGINAL.mlir POLICY.json OUTPUT.json "
              "TARGET.mlir [TRANSITIONS]\n";
    return 2;
  }
  auto source = MemoryBuffer::getFile(argv[1]);
  auto policyBytes = MemoryBuffer::getFile(argv[2]);
  if (!source || !policyBytes) {
    errs() << "cannot read source or policy\n";
    return 2;
  }
  auto policy = parseNativeProofPolicy((*policyBytes)->getBuffer());
  if (!policy) {
    errs() << toString(policy.takeError()) << '\n';
    return 1;
  }
  EvmOptions options;
  options.policy = std::move(*policy);
  if (argc == 6 &&
      StringRef(argv[5]).getAsInteger(10, options.limits.transcriptTransitions))
    return 2;
  auto result = compileEvmProof((*source)->getBuffer(), argv[1], options,
                                DialectRegistry());
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    return 1;
  }
  auto target = result->targetSnapshot();
  if (failed(evm::checkTarget(*target)))
    return 1;
  std::error_code ec;
  raw_fd_ostream json(argv[3], ec);
  if (ec)
    return 2;
  json << formatv("{0:2}\n", encodeEvmCompilation(*result));
  raw_fd_ostream mlir(argv[4], ec);
  if (ec)
    return 2;
  target->print(mlir);
  mlir << '\n';
  return 0;
}
