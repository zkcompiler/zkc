#include "mlir/IR/DialectRegistry.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Driver/Compiler.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/TimeProfiler.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
int main(int argc, char **argv) {
  if (argc == 2 && llvm::StringRef(argv[1]) == "--version") {
    llvm::outs() << "zkc-compile " << ZKC_VERSION << " (LLVM "
                 << LLVM_VERSION_STRING << ")\n";
    return 0;
  }
  if (argc == 2 && llvm::StringRef(argv[1]) == "--capabilities") {
    llvm::outs()
        << llvm::json::Value(llvm::json::Object{
               {"format", "zkc.compiler-capabilities/0"},
               {"version", ZKC_VERSION},
               {"llvm", LLVM_VERSION_STRING},
               {"installation", zkc::language::compilerToolchainIdentity()},
               {"time_trace", true},
               {"observations", true},
               {"structured_diagnostics", true},
               {"phases", llvm::json::Array{"protocol", "participant", "exec",
                                            "physical"}},
               {"settings",
                llvm::json::Array{"simplify", "release-storage", "finite-bulk",
                                  "fuse-vector-reductions", "fuse-collect-fold",
                                  "calculation-batching"}}})
        << '\n';
    return 0;
  }
  std::vector<char *> arguments;
  std::string timeTrace;
  for (int i = 0; i < argc; ++i) {
    llvm::StringRef arg(argv[i]);
    if (arg.consume_front("--time-trace=")) {
      if (!timeTrace.empty() || arg.empty()) {
        llvm::errs() << "source.time-trace-options\n";
        return 2;
      }
      timeTrace = arg.str();
    } else
      arguments.push_back(argv[i]);
  }
  if (!timeTrace.empty())
    llvm::timeTraceProfilerInitialize(100, "zkc-compile");
  mlir::DialectRegistry registry;
  int result = zkc::runCompiler(arguments.size(), arguments.data(), registry);
  if (!timeTrace.empty()) {
    if (auto error = llvm::timeTraceProfilerWrite(timeTrace, "")) {
      llvm::errs() << llvm::toString(std::move(error)) << '\n';
      result = 1;
    }
    llvm::timeTraceProfilerCleanup();
  }
  return result;
}
