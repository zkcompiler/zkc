#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"

using namespace mlir;
#include "zkc/Dialect/Kernel/IR/kernelDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Kernel/IR/kernelOps.cpp.inc"

void zkc::kernel::KernelDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Kernel/IR/kernelOps.cpp.inc"
      >();
}
