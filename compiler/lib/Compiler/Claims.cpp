#include "zkc/Compiler/Claims.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
using namespace llvm;
namespace zkc::claims {
namespace {
Expected<protocol::ConstructionResult>
checkedConstruction(const source::Module &module, const Contract &contract,
                    const Certificate &certificate,
                    const source::Construction &descriptor,
                    const json::Value &candidate, mlir::MLIRContext &ctx) {
  if (descriptor.entry != contract.entry ||
      descriptor.validator != contract.validator)
    return error("claim-construction-binding");
  if (auto e = check(module, contract, certificate))
    return e;
  auto expected = protocol::construct(module, descriptor, ctx);
  if (!expected)
    return expected.takeError();
  if (expected->certificate != candidate)
    return error("construction-candidate-mismatch");
  return expected;
}
} // namespace
Error checkConstruction(const source::Module &module, const Contract &contract,
                        const Certificate &certificate,
                        const source::Construction &descriptor,
                        const json::Value &candidate, mlir::MLIRContext &ctx) {
  auto expected = checkedConstruction(module, contract, certificate, descriptor,
                                      candidate, ctx);
  return expected ? Error::success() : expected.takeError();
}
Error checkLowering(const source::Module &module, const Contract &contract,
                    const Certificate &certificate,
                    const source::Construction &descriptor,
                    const json::Value &construction,
                    const json::Value &physical, mlir::MLIRContext &ctx,
                    const protocol::PhysicalOptions &options) {
  auto expected = checkedConstruction(module, contract, certificate, descriptor,
                                      construction, ctx);
  if (!expected)
    return expected.takeError();
  // This common source comes from independently recomputed construction, not
  // from the supplied physical candidate or its implementation selections.
  auto common = source::decode((*expected->certificate.getAsArray())[2]);
  if (!common)
    return common.takeError();
  if (auto e = protocol::checkImplementationSelection(options.implementations,
                                                      *common))
    return e;
  auto participants = protocol::project(*expected->module);
  if (!participants)
    return participants.takeError();
  if (mlir::failed(protocol::lowerPhysical(
          **participants, options.implementations.choices,
          options.linearContractions, nullptr, options.releaseStorage)))
    return error("claim-lowering");
  auto encoded = protocol::exportModule(**participants);
  if (!encoded)
    return encoded.takeError();
  if (*encoded != physical)
    return error("claim-lowering-mismatch");
  return Error::success();
}
} // namespace zkc::claims
