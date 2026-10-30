#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using llvm::StringRef;
namespace zkc::runtime {
namespace {
bool validName(StringRef value) {
  return !value.empty() && value.size() <= 128 &&
         llvm::all_of(value,
                      [](unsigned char c) { return c >= 33 && c <= 126; });
}
LogicalResult names(llvm::function_ref<InFlightDiagnostic()> emit,
                    std::initializer_list<StringRef> values) {
  return llvm::all_of(values, validName)
             ? success()
             : LogicalResult(
                   diagnostics::emit(emit(), "interactive-native-origin"));
}
size_t stringBytes(StringRef value) { return 9 + value.size(); }
unsigned decimalDigits(uint64_t value) {
  unsigned count = 1;
  while (value >= 10) {
    value /= 10;
    ++count;
  }
  return count;
}
} // namespace
LogicalResult
AssetReferenceAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                           StringRef format, DenseI8ArrayAttr digest) {
  if (!validName(format) || !digest || digest.size() != 32)
    return diagnostics::emit(
        emit(), "asset-reference",
        "a format identity and 32 digest bytes are required");
  return success();
}
LogicalResult
OriginStepAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                       OriginStepKind kind, StringRef protocol,
                       StringRef site) {
  if (!symbolizeOriginStepKind(static_cast<uint32_t>(kind)))
    return diagnostics::emit(emit(), "interactive-native-origin");
  return names(emit, {protocol, site});
}
LogicalResult
QueryOriginAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                        StringRef protocol, StringRef site, uint64_t,
                        StringRef service, StringRef method, StringRef owner) {
  return names(emit, {protocol, site, service, method, owner});
}
LogicalResult
MessageOriginAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                          StringRef protocol, StringRef site, StringRef schema,
                          StringRef sender, StringRef receiver) {
  return names(emit, {protocol, site, schema, sender, receiver});
}
LogicalResult
StartOriginAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                        StringRef protocol, StringRef site) {
  return names(emit, {protocol, site});
}
LogicalResult
NativeOriginAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                         StringRef entry, llvm::ArrayRef<OriginStepAttr> path,
                         Attribute event) {
  auto refuse = [&] {
    return diagnostics::emit(emit(), "interactive-native-origin");
  };
  if (!validName(entry) || path.size() > 64)
    return refuse();
  // Canonical tree framing is nine bytes per string/array header. Account
  // directly, without serializing or reparsing a hexadecimal template.
  size_t bytes = 9 + stringBytes("zkc.native-origin-template/0") +
                 stringBytes(entry) + 9 + 9 + 9;
  for (auto step : path) {
    if (!step)
      return refuse();
    if (failed(OriginStepAttr::verify(emit, step.getKind(), step.getProtocol(),
                                      step.getSite())))
      return failure();
    bytes += 9 + stringBytes(stringifyOriginStepKind(step.getKind())) +
             stringBytes(step.getProtocol()) + stringBytes(step.getSite());
  }
  if (auto query = dyn_cast_or_null<QueryOriginAttr>(event)) {
    if (failed(QueryOriginAttr::verify(
            emit, query.getProtocol(), query.getSite(), query.getServiceInput(),
            query.getService(), query.getMethod(), query.getOwner())))
      return failure();
    bytes += stringBytes("query") + stringBytes(query.getProtocol()) +
             stringBytes(query.getSite()) + 9 + StringRef("input_").size() +
             decimalDigits(query.getServiceInput()) +
             stringBytes(query.getService()) + stringBytes(query.getMethod()) +
             stringBytes(query.getOwner());
  } else if (auto message = dyn_cast_or_null<MessageOriginAttr>(event)) {
    if (failed(MessageOriginAttr::verify(
            emit, message.getProtocol(), message.getSite(), message.getSchema(),
            message.getSender(), message.getReceiver())))
      return failure();
    for (StringRef value :
         {StringRef("message"), message.getProtocol(), message.getSite(),
          message.getSchema(), message.getSender(), message.getReceiver()})
      bytes += stringBytes(value);
  } else if (auto start = dyn_cast_or_null<StartOriginAttr>(event)) {
    if (failed(StartOriginAttr::verify(emit, start.getProtocol(),
                                       start.getSite())))
      return failure();
    bytes += stringBytes("start") + stringBytes(start.getProtocol()) +
             stringBytes(start.getSite());
  } else
    return refuse();
  if (bytes > 2048)
    return refuse();
  return success();
}
} // namespace zkc::runtime
