#include "mlir/IR/DialectRegistry.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Driver/Compiler.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FileSystem.h"
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
    llvm::json::Array phases;
    for (auto phase : zkc::compilationObservationPhases())
      phases.push_back(phase);
    llvm::outs()
        << llvm::json::Value(llvm::json::Object{
               {"format", "zkc.compiler-capabilities/0"},
               {"version", ZKC_VERSION},
               {"llvm", LLVM_VERSION_STRING},
               {"installation", zkc::language::compilerToolchainIdentity()},
               {"time_trace", true},
               {"observations", true},
               {"structured_diagnostics", true},
               {"phases", std::move(phases)},
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
      if (!timeTrace.empty() || arg.empty() || arg == "-") {
        llvm::errs() << "source.time-trace-options\n";
        return 2;
      }
      timeTrace = arg.str();
    } else
      arguments.push_back(argv[i]);
  }
  std::unique_ptr<llvm::raw_fd_ostream> trace;
  if (!timeTrace.empty()) {
    std::error_code ec;
    trace = std::make_unique<llvm::raw_fd_ostream>(
        timeTrace, ec, llvm::sys::fs::CD_CreateNew, llvm::sys::fs::FA_Write,
        llvm::sys::fs::OF_Text);
    if (ec) {
      llvm::errs() << "source.time-trace-io: " << ec.message() << '\n';
      return 1;
    }
    llvm::timeTraceProfilerInitialize(100, "zkc-compile");
  }
  mlir::DialectRegistry registry;
  int result = zkc::runCompiler(arguments.size(), arguments.data(), registry);
  if (trace) {
    llvm::timeTraceProfilerWrite(*trace);
    trace->flush();
    if (trace->has_error()) {
      llvm::errs() << "source.time-trace-io: " << trace->error().message()
                   << '\n';
      trace->clear_error();
      result = 1;
    }
    llvm::timeTraceProfilerCleanup();
  }
  return result;
}
