#include "mlir/IR/DialectRegistry.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Driver/Compiler.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/raw_ostream.h"
int main(int argc, char **argv) {
  if (argc == 2 && llvm::StringRef(argv[1]) == "--version") {
    llvm::outs() << "zkc-compile " << ZKC_VERSION << " (LLVM "
                 << LLVM_VERSION_STRING << ")\n";
    return 0;
  }
  mlir::DialectRegistry registry;
  zkc::registerTableLibrary(registry);
  return zkc::runCompiler(argc, argv, registry);
}
