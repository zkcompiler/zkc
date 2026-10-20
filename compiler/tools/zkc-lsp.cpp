#include "mlir/IR/DialectRegistry.h"
#include "mlir/Tools/mlir-lsp-server/MlirLspServerMain.h"
#include "zkc/Dialect/Registry.h"
int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  return mlir::failed(mlir::MlirLspServerMain(argc, argv, registry));
}
