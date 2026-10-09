#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <cstdint>
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
  bool name() {
    StringRef value;
    return string(value) && identifier(value);
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
} // namespace
Error checkNativeOrigin(StringRef hex, StringRef kind) {
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
  if (!reader.array(5) || !reader.string(value) ||
      value != "zkc.native-origin-template" || !reader.name() ||
      !reader.header(1, count) || count > 64)
    return invalid();
  for (uint64_t i = 0; i < count; ++i) {
    if (!reader.array(3) || !reader.string(value) ||
        (value != "apply" && value != "repeat") || !reader.name() ||
        !reader.name())
      return invalid();
  }
  unsigned fields = kind == "query" ? 7 : kind == "message" ? 6 : 0;
  if (!fields || !reader.array(0) || !reader.array(fields) ||
      !reader.string(value) || value != kind)
    return invalid();
  for (unsigned i = 1; i < fields; ++i) {
    if (!reader.string(value) || !identifier(value))
      return invalid();
    if (kind == "query" && i == 3) {
      uint64_t port;
      if (!value.consume_front("input_") || value.empty() ||
          (value.size() > 1 && value.front() == '0') ||
          !all_of(value, [](char c) { return c >= '0' && c <= '9'; }) ||
          value.getAsInteger(10, port))
        return invalid();
    }
  }
  return reader.bytes.empty() ? Error::success() : invalid();
}
Expected<std::string>
encodeNativeOriginTemplate(StringRef entry,
                           ArrayRef<std::array<std::string, 3>> path,
                           ArrayRef<std::string> event) {
  if (!identifier(entry) || path.size() > 64 || event.empty() ||
      event.size() > 7 || !all_of(event, identifier))
    return error("interactive-native-origin");
  size_t size = 9 + 9 + StringRef("zkc.native-origin-template").size() + 9 +
                entry.size() + 9 + 9 + 9;
  for (const auto &step : path) {
    if ((step[0] != "apply" && step[0] != "repeat") ||
        !all_of(step, identifier))
      return error("interactive-native-origin");
    size += 9;
    for (const auto &part : step)
      size += 9 + part.size();
  }
  for (const auto &part : event)
    size += 9 + part.size();
  if (size > 2048)
    return error("interactive-native-origin");
  std::string bytes;
  bytes.reserve(size);
  header(bytes, 1, 5);
  string(bytes, "zkc.native-origin-template");
  string(bytes, entry);
  header(bytes, 1, path.size());
  for (const auto &step : path) {
    header(bytes, 1, 3);
    for (const auto &part : step)
      string(bytes, part);
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
  if (auto e = checkNativeOrigin(hex, event.front()))
    return std::move(e);
  return hex;
}

} // namespace zkc::protocol
