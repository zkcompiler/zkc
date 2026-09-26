#include "Service.h"
#include "zkc/Driver/Compiler.h"
int main(int argc, char **argv) {
  bool ambiguous = argc > 1 && llvm::StringRef(argv[1]) == "--ambiguous-family";
  if (ambiguous) {
    --argc;
    ++argv;
  }
  mlir::DialectRegistry registry;
  zkc::service::registerService(registry, ambiguous);
  return zkc::runCompiler(argc, argv, registry);
}
