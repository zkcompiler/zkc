#include "NativeRequest.h"
#include "mlir/IR/OperationSupport.h"

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace pir = protocol_ir;
Value resolveNativeRequestValue(NativeRequestValue input,
                                const NativeRequestValues &ordinary,
                                const NativeRequestValues &replica) {
  return input.ordinary ? ordinary.lookup(input.source)
                        : replica.lookup(input.source);
}
bool readNativeRequestLoopInputs(const NativeRequestLoop &loop,
                                 pir::ProtocolLoopOp actual,
                                 unsigned stateSlots,
                                 const NativeRequestValues &ordinary,
                                 const NativeRequestValues &replica) {
  unsigned split = 1 + pir::ProtocolLoopOp(loop.producer).getCarried();
  if (actual.getNumOperands() <
      pir::ProtocolLoopOp(loop.producer).getNumOperands() +
          loop.initial.size() + loop.captured.size() + stateSlots)
    return false;
  for (auto [i, input] : enumerate(loop.initial)) {
    Value expected = resolveNativeRequestValue(input, ordinary, replica);
    if (!expected || actual.getInputs()[split + i] != expected)
      return false;
  }
  unsigned captureStart = pir::ProtocolLoopOp(loop.producer).getNumOperands() +
                          loop.initial.size() + stateSlots;
  for (auto [i, input] : enumerate(loop.captured)) {
    Value expected = resolveNativeRequestValue(input, ordinary, replica);
    if (!expected || actual.getInputs()[captureStart + i] != expected)
      return false;
  }
  return true;
}
bool bindNativeRequestLoop(const NativeRequestLoop &loop,
                           pir::ProtocolLoopOp actual, unsigned stateSlots,
                           NativeRequestValues &replica) {
  unsigned split = 1 + pir::ProtocolLoopOp(loop.producer).getCarried();
  auto &body = actual.getBody().front();
  auto &source = *loop.body->validator;
  if (body.getNumArguments() < pir::ProtocolLoopOp(loop.producer)
                                       .getBody()
                                       .front()
                                       .getNumArguments() +
                                   loop.carried.size() + loop.captures.size() +
                                   stateSlots ||
      actual.getNumResults() !=
          pir::ProtocolLoopOp(loop.producer).getNumResults() +
              loop.carried.size() + stateSlots)
    return false;
  for (auto [i, index] : enumerate(loop.carried)) {
    Value argument = body.getArgument(split + i);
    Value result = actual.getResult(
        pir::ProtocolLoopOp(loop.producer).getNumResults() + i);
    if (argument.getType() != source.getArgument(1 + index).getType() ||
        result.getType() !=
            pir::ProtocolLoopOp(loop.validator).getResult(index).getType() ||
        !replica.try_emplace(source.getArgument(1 + index), argument).second ||
        !replica
             .try_emplace(pir::ProtocolLoopOp(loop.validator).getResult(index),
                          result)
             .second)
      return false;
  }
  unsigned captureStart =
      pir::ProtocolLoopOp(loop.producer).getBody().front().getNumArguments() +
      loop.carried.size() + stateSlots;
  for (auto [i, index] : enumerate(loop.captures)) {
    Value argument = source.getArgument(
        1 + pir::ProtocolLoopOp(loop.validator).getCarried() + index);
    Value actualArg = body.getArgument(captureStart + i);
    if (argument.getType() != actualArg.getType() ||
        !replica.try_emplace(argument, actualArg).second)
      return false;
  }
  return true;
}
bool readNativeRequestYield(const NativeRequestLoop &loop, ValueRange actual,
                            const NativeRequestValues &ordinary,
                            const NativeRequestValues &replica) {
  if (actual.size() != loop.yielded.size())
    return false;
  for (auto [input, output] : zip(loop.yielded, actual)) {
    Value expected = resolveNativeRequestValue(input, ordinary, replica);
    if (!expected || output != expected)
      return false;
  }
  return true;
}
} // namespace zkc::detail
