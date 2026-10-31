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
bool readNativeRequestSteps(const NativeRequestFrame &frame, Operation *anchor,
                            Operation *&cursor,
                            const NativeRequestValues &ordinary,
                            NativeRequestValues &replica) {
  auto found = frame.before.find(anchor);
  if (found == frame.before.end())
    return true;
  for (const auto &step : found->second) {
    auto *source = step.source;
    if (!cursor || source->getName() != cursor->getName() ||
        source->getNumRegions() || cursor->getNumRegions() ||
        source->getNumOperands() != cursor->getNumOperands() ||
        source->getResultTypes() != cursor->getResultTypes())
      return false;
    NamedAttrList expected(source->getAttrs()), actual(cursor->getAttrs());
    if (isa<pir::LocalCallOp>(source)) {
      auto call = cast<pir::LocalCallOp>(cursor);
      auto participant = call->getParentOfType<pir::ParticipantOp>();
      if (!participant || call.getRole() != participant.getRole() ||
          !call.getSiteAttr() || call.getSite().empty())
        return false;
      expected.erase("site");
      expected.erase("role");
      actual.erase("site");
      actual.erase("role");
    }
    if (expected != actual)
      return false;
    for (auto [input, operand] : zip(step.inputs, cursor->getOperands())) {
      Value related = resolveNativeRequestValue(input, ordinary, replica);
      if (!related || related != operand)
        return false;
    }
    for (auto [from, to] : zip(source->getResults(), cursor->getResults()))
      if (!replica.try_emplace(from, to).second)
        return false;
    cursor = cursor->getNextNode();
  }
  return true;
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
