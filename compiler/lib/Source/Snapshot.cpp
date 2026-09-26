#include "zkc/Source/Snapshot.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::source {
namespace {
std::string hashSnapshot(const json::Value &source) {
  SHA256 hash;
  hash.update("zkc.source-snapshot/1\n");
  hash.update(printJson(source));
  return toHex(hash.final(), true);
}
} // namespace
Expected<std::string> snapshot(const Module &module, RecordMap *records) {
  if (auto e = source::checkStructure(module))
    return e;
  return hashSnapshot(encode(module, records));
}
Expected<std::string> snapshot(const Content &content, RecordMap *records) {
  if (auto e = source::checkStructure(content))
    return e;
  return hashSnapshot(encode(content, records));
}
} // namespace zkc::source
