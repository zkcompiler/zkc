#include "zkc/Driver/Compiler.h"

int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  return zkc::runCompiler(argc, argv, registry);
}
