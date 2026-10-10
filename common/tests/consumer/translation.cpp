#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
!B = !plan.data<i1, "native.bool/0">
module { "protocol.module"() ({
 "protocol.participant"() ({ ^entry(%x:!B): "protocol.finish"(%x) : (!B)->() })
 {sym_name="p",function_type=(!B)->!B,instance="main",role="P"} : ()->()
 "protocol.entry"() {sym_name="main",targets=[["P",@p]]} : ()->()
}) {profile=#protocol.profile<physical>} : ()->() })",
                                                        &context);
  if (!module)
    return 1;
  auto encoded = zkc::protocol::exportModule(*module);
  if (!encoded) {
    llvm::consumeError(encoded.takeError());
    return 2;
  }
  auto decoded = zkc::program::decode(*encoded);
  if (!decoded) {
    llvm::consumeError(decoded.takeError());
    return 3;
  }
  if (zkc::program::encode(*decoded) != *encoded)
    return 4;
  auto verified =
      zkc::protocol::verifyProgramArtifact(*module, zkc::printJson(*encoded));
  if (!verified) {
    llvm::consumeError(verified.takeError());
    return 5;
  }
  return zkc::program::encode(*verified) != *encoded;
}
