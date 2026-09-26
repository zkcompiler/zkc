#include "Internal.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::claims {
std::string digest(StringRef domain, const json::Value &value) {
  SHA256 hash;
  hash.update(domain);
  hash.update(printJson(value));
  return toHex(hash.final(), true);
}
Expected<Trace> trace(const source::Module &original, StringRef entry) {
  auto execution = source::inspectExecution(original, entry);
  if (!execution)
    return execution.takeError();
  Trace result;
  static_cast<source::Execution &>(result) = std::move(*execution);
  result.digest =
      digest("zkc.execution-claims.source/1\n", source::encode(original));
  return result;
}
Expected<json::Value> inspect(const source::Module &module, StringRef entry) {
  auto source = trace(module, entry);
  if (!source)
    return source.takeError();
  auto names = [](const source::Names &items) {
    json::Array out;
    for (const auto &s : items)
      out.push_back(s);
    return out;
  };
  json::Array values, invocations, guards, loops, operations;
  for (const auto &[id, v] : source->values)
    values.push_back(json::Object{
        {"id", id}, {"type", v.type}, {"origin", v.origin}, {"name", v.name}});
  for (const auto &[path, i] : source->invocations)
    invocations.push_back(json::Object{{"path", path},
                                       {"callee", i.callee},
                                       {"instance", i.instance},
                                       {"inputs", names(i.inputs)},
                                       {"outputs", names(i.outputs)}});
  for (const auto &[path, g] : source->guards)
    guards.push_back(
        json::Object{{"path", path}, {"value", g.value}, {"role", g.role}});
  for (const auto &[path, count] : source->loops)
    loops.push_back(json::Object{{"path", path}, {"count", count}});
  for (const auto &[path, op] : source->operations)
    operations.push_back(json::Object{{"path", path},
                                      {"callee", op.callee},
                                      {"inputs", names(op.inputs)},
                                      {"outputs", names(op.outputs)}});
  return json::Value(json::Object{{"format", "zkc.claim-inspection/1"},
                                  {"source_digest", source->digest},
                                  {"entry", entry},
                                  {"roles", names(source->roles)},
                                  {"values", std::move(values)},
                                  {"invocations", std::move(invocations)},
                                  {"guards", std::move(guards)},
                                  {"loops", std::move(loops)},
                                  {"operations", std::move(operations)}});
}
} // namespace zkc::claims
