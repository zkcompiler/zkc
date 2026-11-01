#include "zkc/Target/Cpu/Passes.h"
#include "mlir/Pass/PassRegistry.h"
namespace zkc {
void registerCpuPasses() {
  mlir::registerPass([] { return protocol::createSelectPhysicalPass(); });
}
} // namespace zkc
