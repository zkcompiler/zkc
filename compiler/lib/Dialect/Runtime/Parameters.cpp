#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::runtime {
namespace {
InFlightDiagnostic silentDiagnostic(MLIRContext *context) {
  auto diagnostic = emitError(UnknownLoc::get(context));
  diagnostic.abandon();
  return diagnostic;
}
bool bounded(std::initializer_list<StringRef> fields) {
  return all_of(fields, [](StringRef name) { return name.size() <= 128; });
}
} // namespace
Expected<NativeOriginAttr>
importNativeOrigin(MLIRContext *context,
                   const protocol::NativeOriginTemplate &origin) {
  if (!context || !context->getLoadedDialect<RuntimeDialect>() ||
      origin.entry.size() > 128 || origin.path.size() > 64)
    return zkc::error("interactive-native-origin");
  SmallVector<OriginStepAttr> path;
  for (const auto &step : origin.path) {
    if (!bounded({step.protocol, step.site}) ||
        (step.kind != protocol::NativeOriginStep::Kind::Apply &&
         step.kind != protocol::NativeOriginStep::Kind::Repeat))
      return zkc::error("interactive-native-origin");
    path.push_back(
        OriginStepAttr::get(context,
                            step.kind == protocol::NativeOriginStep::Kind::Apply
                                ? OriginStepKind::Apply
                                : OriginStepKind::Repeat,
                            step.protocol, step.site));
  }
  Attribute event;
  if (auto *query = std::get_if<protocol::NativeQueryOrigin>(&origin.event)) {
    if (!bounded({query->protocol, query->site, query->service, query->method,
                  query->owner}))
      return zkc::error("interactive-native-origin");
    event = QueryOriginAttr::get(context, query->protocol, query->site,
                                 query->serviceInput, query->service,
                                 query->method, query->owner);
  } else if (auto *message =
                 std::get_if<protocol::NativeMessageOrigin>(&origin.event)) {
    if (!bounded({message->protocol, message->site, message->schema,
                  message->sender, message->receiver}))
      return zkc::error("interactive-native-origin");
    event = MessageOriginAttr::get(context, message->protocol, message->site,
                                   message->schema, message->sender,
                                   message->receiver);
  } else if (auto *start =
                 std::get_if<protocol::NativeStartOrigin>(&origin.event)) {
    if (!bounded({start->protocol, start->site}))
      return zkc::error("interactive-native-origin");
    event = StartOriginAttr::get(context, start->protocol, start->site);
  }
  auto attribute = NativeOriginAttr::getChecked(
      [&] { return silentDiagnostic(context); }, context,
      StringRef(origin.entry), ArrayRef<OriginStepAttr>(path), event);
  if (!attribute)
    return zkc::error("interactive-native-origin");
  return attribute;
}
Expected<protocol::NativeOriginTemplate>
exportNativeOrigin(NativeOriginAttr origin) {
  if (!origin || failed(NativeOriginAttr::verify(
                     [&] { return silentDiagnostic(origin.getContext()); },
                     origin.getEntry(), origin.getPath(), origin.getEvent())))
    return zkc::error("interactive-native-origin");
  protocol::NativeOriginTemplate result;
  result.entry = origin.getEntry().str();
  for (auto step : origin.getPath())
    result.path.push_back({step.getKind() == OriginStepKind::Apply
                               ? protocol::NativeOriginStep::Kind::Apply
                               : protocol::NativeOriginStep::Kind::Repeat,
                           step.getProtocol().str(), step.getSite().str()});
  auto event = origin.getEvent();
  if (auto query = dyn_cast<QueryOriginAttr>(event))
    result.event = protocol::NativeQueryOrigin{
        query.getProtocol().str(), query.getSite().str(),
        query.getServiceInput(),   query.getService().str(),
        query.getMethod().str(),   query.getOwner().str()};
  else if (auto message = dyn_cast<MessageOriginAttr>(event))
    result.event = protocol::NativeMessageOrigin{
        message.getProtocol().str(), message.getSite().str(),
        message.getSchema().str(), message.getSender().str(),
        message.getReceiver().str()};
  else {
    auto start = cast<StartOriginAttr>(event);
    result.event = protocol::NativeStartOrigin{start.getProtocol().str(),
                                               start.getSite().str()};
  }
  return result;
}
Expected<AssetReferenceAttr>
decodeAssetReference(MLIRContext *context, StringRef format, StringRef digest) {
  if (!context || !context->getLoadedDialect<RuntimeDialect>() ||
      format.size() > 128 || digest.size() != 64 || !all_of(digest, [](char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
      }))
    return zkc::error("asset-reference");
  auto digit = [](char c) { return c <= '9' ? c - '0' : c - 'a' + 10; };
  SmallVector<int8_t> bytes;
  for (size_t i = 0; i < digest.size(); i += 2)
    bytes.push_back(
        static_cast<int8_t>((digit(digest[i]) << 4) | digit(digest[i + 1])));
  auto attribute = AssetReferenceAttr::getChecked(
      [&] { return silentDiagnostic(context); }, context, format,
      DenseI8ArrayAttr::get(context, bytes));
  if (!attribute)
    return zkc::error("asset-reference");
  return attribute;
}
Expected<std::string> encodeAssetDigest(AssetReferenceAttr asset) {
  if (!asset || failed(AssetReferenceAttr::verify(
                    [&] { return silentDiagnostic(asset.getContext()); },
                    asset.getFormat(), asset.getDigest())))
    return zkc::error("asset-reference");
  constexpr char digits[] = "0123456789abcdef";
  std::string result;
  result.reserve(64);
  for (uint8_t byte : asset.getDigest().asArrayRef()) {
    result.push_back(digits[byte >> 4]);
    result.push_back(digits[byte & 15]);
  }
  return result;
}
} // namespace zkc::runtime
