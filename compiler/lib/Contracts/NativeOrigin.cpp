#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <cstdint>
#include <optional>
using namespace llvm;
namespace zkc::protocol {
namespace {
bool identifier(StringRef value) {
  return !value.empty() && value.size() <= 128 &&
         all_of(value, [](unsigned char c) { return c >= 33 && c <= 126; });
}
struct Reader {
  StringRef bytes;
  bool header(unsigned tag, uint64_t &size) {
    if (bytes.size() < 9 || static_cast<unsigned char>(bytes.front()) != tag)
      return false;
    size = 0;
    for (unsigned i = 0; i < 8; ++i)
      size |= uint64_t(static_cast<unsigned char>(bytes[i + 1])) << (8 * i);
    bytes = bytes.drop_front(9);
    return true;
  }
  bool array(uint64_t count) {
    uint64_t size;
    return header(1, size) && size == count;
  }
  bool string(StringRef &result) {
    uint64_t size;
    if (!header(0, size) || size > bytes.size())
      return false;
    result = bytes.take_front(size);
    bytes = bytes.drop_front(size);
    return true;
  }
  bool name(std::string &out) {
    StringRef value;
    if (!string(value) || !identifier(value))
      return false;
    out = value.str();
    return true;
  }
};
void header(std::string &out, unsigned tag, uint64_t size) {
  out.push_back(tag);
  for (unsigned i = 0; i < 8; ++i)
    out.push_back(static_cast<char>((size >> (8 * i)) & 255));
}
void string(std::string &out, StringRef value) {
  header(out, 0, value.size());
  out.append(value.data(), value.size());
}
std::optional<uint64_t> inputPort(StringRef value) {
  uint64_t port;
  if (!value.consume_front("input_") || value.empty() ||
      (value.size() > 1 && value.front() == '0') ||
      !all_of(value, [](char c) { return c >= '0' && c <= '9'; }) ||
      value.getAsInteger(10, port))
    return std::nullopt;
  return port;
}
} // namespace
Expected<NativeOriginTemplate> decodeNativeOriginTemplate(StringRef hex) {
  auto invalid = [] { return error("interactive-native-origin"); };
  if (hex.empty() || hex.size() > 4096 || hex.size() % 2 ||
      !all_of(hex, [](char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
      }))
    return invalid();
  auto digit = [](char c) { return c <= '9' ? c - '0' : c - 'a' + 10; };
  std::string bytes;
  bytes.reserve(hex.size() / 2);
  for (size_t i = 0; i < hex.size(); i += 2)
    bytes.push_back((digit(hex[i]) << 4) | digit(hex[i + 1]));
  Reader reader{bytes};
  StringRef value;
  uint64_t count;
  NativeOriginTemplate result;
  if (!reader.array(5) || !reader.string(value) ||
      value != "zkc.native-origin-template/0" || !reader.name(result.entry) ||
      !reader.header(1, count) || count > 64)
    return invalid();
  for (uint64_t i = 0; i < count; ++i) {
    NativeOriginStep step;
    if (!reader.array(3) || !reader.string(value) ||
        (value != "apply" && value != "repeat") ||
        !reader.name(step.protocol) || !reader.name(step.site))
      return invalid();
    step.kind = value == "apply" ? NativeOriginStep::Kind::Apply
                                 : NativeOriginStep::Kind::Repeat;
    result.path.push_back(std::move(step));
  }
  if (!reader.array(0) || !reader.header(1, count) || !reader.string(value))
    return invalid();
  if (value == "query" && count == 7) {
    NativeQueryOrigin query;
    std::string port;
    if (!reader.name(query.protocol) || !reader.name(query.site) ||
        !reader.name(port) || !reader.name(query.service) ||
        !reader.name(query.method) || !reader.name(query.owner))
      return invalid();
    auto input = inputPort(port);
    if (!input)
      return invalid();
    query.serviceInput = *input;
    result.event = std::move(query);
  } else if (value == "message" && count == 6) {
    NativeMessageOrigin message;
    if (!reader.name(message.protocol) || !reader.name(message.site) ||
        !reader.name(message.schema) || !reader.name(message.sender) ||
        !reader.name(message.receiver))
      return invalid();
    result.event = std::move(message);
  } else if (value == "start" && count == 3) {
    NativeStartOrigin start;
    if (!reader.name(start.protocol) || !reader.name(start.site))
      return invalid();
    result.event = std::move(start);
  } else
    return invalid();
  if (!reader.bytes.empty())
    return invalid();
  return result;
}
Error checkNativeOrigin(StringRef hex, StringRef kind, StringRef method) {
  auto origin = decodeNativeOriginTemplate(hex);
  if (!origin)
    return origin.takeError();
  if (kind == "query") {
    auto *query = std::get_if<NativeQueryOrigin>(&origin->event);
    if (query && (method.empty() || query->method == method))
      return Error::success();
  } else if ((kind == "message" &&
              std::holds_alternative<NativeMessageOrigin>(origin->event)) ||
             (kind == "start" &&
              std::holds_alternative<NativeStartOrigin>(origin->event)))
    return Error::success();
  return error("interactive-native-origin");
}
Expected<std::string>
encodeNativeOriginTemplate(const NativeOriginTemplate &origin) {
  if (!identifier(origin.entry) || origin.path.size() > 64)
    return error("interactive-native-origin");
  std::vector<std::string> event;
  if (auto *query = std::get_if<NativeQueryOrigin>(&origin.event)) {
    if (!all_of(std::initializer_list<StringRef>{StringRef(query->protocol),
                                                 StringRef(query->site),
                                                 StringRef(query->service),
                                                 StringRef(query->method),
                                                 StringRef(query->owner)},
                identifier))
      return error("interactive-native-origin");
    event = {"query",        query->protocol,
             query->site,    "input_" + std::to_string(query->serviceInput),
             query->service, query->method,
             query->owner};
  } else if (auto *message = std::get_if<NativeMessageOrigin>(&origin.event)) {
    if (!all_of(std::initializer_list<StringRef>{StringRef(message->protocol),
                                                 StringRef(message->site),
                                                 StringRef(message->schema),
                                                 StringRef(message->sender),
                                                 StringRef(message->receiver)},
                identifier))
      return error("interactive-native-origin");
    event = {"message",       message->protocol, message->site,
             message->schema, message->sender,   message->receiver};
  } else if (auto *start = std::get_if<NativeStartOrigin>(&origin.event)) {
    if (!identifier(start->protocol) || !identifier(start->site))
      return error("interactive-native-origin");
    event = {"start", start->protocol, start->site};
  }
  if (event.empty() || !all_of(event, identifier))
    return error("interactive-native-origin");
  size_t size = 9 + 9 + StringRef("zkc.native-origin-template/0").size() + 9 +
                origin.entry.size() + 9 + 9 + 9;
  for (const auto &step : origin.path) {
    if ((step.kind != NativeOriginStep::Kind::Apply &&
         step.kind != NativeOriginStep::Kind::Repeat) ||
        !identifier(step.protocol) || !identifier(step.site))
      return error("interactive-native-origin");
    size += 9 + 9 + (step.kind == NativeOriginStep::Kind::Apply ? 5 : 6) + 9 +
            step.protocol.size() + 9 + step.site.size();
  }
  for (const auto &part : event)
    size += 9 + part.size();
  if (size > 2048)
    return error("interactive-native-origin");
  std::string bytes;
  bytes.reserve(size);
  header(bytes, 1, 5);
  string(bytes, "zkc.native-origin-template/0");
  string(bytes, origin.entry);
  header(bytes, 1, origin.path.size());
  for (const auto &step : origin.path) {
    header(bytes, 1, 3);
    string(bytes,
           step.kind == NativeOriginStep::Kind::Apply ? "apply" : "repeat");
    string(bytes, step.protocol);
    string(bytes, step.site);
  }
  header(bytes, 1, 0);
  header(bytes, 1, event.size());
  for (const auto &part : event)
    string(bytes, part);
  constexpr char digits[] = "0123456789abcdef";
  std::string hex;
  hex.reserve(bytes.size() * 2);
  for (unsigned char byte : bytes) {
    hex.push_back(digits[byte >> 4]);
    hex.push_back(digits[byte & 15]);
  }
  return hex;
}
Expected<std::string>
encodeNativeOriginTemplate(StringRef entry,
                           ArrayRef<std::array<std::string, 3>> path,
                           ArrayRef<std::string> event) {
  NativeOriginTemplate origin;
  if (!identifier(entry) || path.size() > 64 || event.empty() ||
      event.size() > 7 || !all_of(event, identifier))
    return error("interactive-native-origin");
  origin.entry = entry.str();
  for (const auto &step : path) {
    if ((step[0] != "apply" && step[0] != "repeat") ||
        !all_of(step, identifier))
      return error("interactive-native-origin");
    origin.path.push_back({step[0] == "apply" ? NativeOriginStep::Kind::Apply
                                              : NativeOriginStep::Kind::Repeat,
                           step[1], step[2]});
  }
  if (event[0] == "query" && event.size() == 7) {
    auto input = inputPort(event[3]);
    if (!input)
      return error("interactive-native-origin");
    origin.event = NativeQueryOrigin{event[1], event[2], *input,
                                     event[4], event[5], event[6]};
  } else if (event[0] == "message" && event.size() == 6)
    origin.event =
        NativeMessageOrigin{event[1], event[2], event[3], event[4], event[5]};
  else if (event[0] == "start" && event.size() == 3)
    origin.event = NativeStartOrigin{event[1], event[2]};
  else
    return error("interactive-native-origin");
  return encodeNativeOriginTemplate(origin);
}
} // namespace zkc::protocol
