#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolAttrs.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;
#include "zkc/Dialect/Protocol/IR/protocolEnums.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolAttrs.cpp.inc"

namespace zkc::protocol_ir {
void ProtocolDialect::initializeAttributes() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Protocol/IR/protocolAttrs.cpp.inc"
      >();
}

LogicalResult ProfileAttr::verify(function_ref<InFlightDiagnostic()> emitError,
                                  Profile value) {
  if (!symbolizeProfile(static_cast<uint32_t>(value)))
    return emitError() << "unknown protocol profile";
  return success();
}
LogicalResult
ExecutionContractAttr::verify(function_ref<InFlightDiagnostic()> emitError,
                              ExecutionContract value) {
  if (!symbolizeExecutionContract(static_cast<uint32_t>(value)))
    return emitError() << "unknown participant execution contract";
  return success();
}
bool isMathematicalProfile(Profile profile) {
  return profile == Profile::Protocol || profile == Profile::Participant;
}
bool isExecutableProfile(Profile profile) {
  return profile == Profile::Exec || profile == Profile::Physical;
}
bool isProgram(ExecutionContract contract) {
  return contract == ExecutionContract::Program;
}
LogicalResult ProtocolModuleOp::verify() {
  if (!symbolizeProfile(static_cast<uint32_t>(getProfile())))
    return diagnostics::emit(emitOpError(), "protocol-profile");
  auto contract = getExecutionContract();
  if (bool(contract) != isExecutableProfile(getProfile()) ||
      (contract &&
       !symbolizeExecutionContract(static_cast<uint32_t>(*contract))))
    return diagnostics::emit(
        emitOpError(), "protocol-execution-contract",
        "exec and physical profiles require one execution contract; "
        "protocol, participant and protocol_exec require none");
  return success();
}
} // namespace zkc::protocol_ir
