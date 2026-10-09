#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <string>

using namespace llvm;
using namespace zkc::relation;

// Bounded test transport: [bundle, configuration, instance, witness].
static Expected<json::Value> evaluate(StringRef text) {
  auto parsed = readBundleDataJson(text);
  if (!parsed)
    return parsed.takeError();
  auto *rows = parsed->getAsArray();
  if (!rows || rows->size() != 4)
    return zkc::error("test-schema");
  auto bundle = readBundle((*rows)[0]);
  if (!bundle)
    return bundle.takeError();
  auto config = readBundleConfiguration(*bundle, (*rows)[1]);
  if (!config)
    return config.takeError();
  auto instance = readBundleInstance(*bundle, (*rows)[2]);
  if (!instance)
    return instance.takeError();
  auto witness = readBundleWitness(*bundle, (*rows)[3]);
  if (!witness)
    return witness.takeError();
  auto result = bundle->evaluate(*config, *instance, *witness);
  if (!result)
    return result.takeError();
  return json::Object{{"accepted", true},
                      {"identity", bundle->identity().str()},
                      {"bundle", bundle->encode()},
                      {"result", result->encode()}};
}

int main() {
  std::string line;
  char byte;
  while (std::cin.get(byte)) {
    if (byte != '\n') {
      if (line.size() >= 1024 * 1024)
        return 2;
      line.push_back(byte);
      continue;
    }
    auto result = evaluate(line);
    if (!result) {
      const auto message = toString(result.takeError());
      outs() << zkc::printJson(json::Object{
                    {"accepted", false},
                    {"error", StringRef(message).split(':').first.str()}})
             << '\n';
    } else
      outs() << zkc::printJson(*result) << '\n';
    line.clear();
  }
  return line.empty() ? 0 : 2;
}
