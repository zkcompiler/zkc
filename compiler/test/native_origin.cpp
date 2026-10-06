#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
using namespace zkc::protocol;
int main() {
  auto encoded = encodeNativeOrigin("main", {"subprotocol"},
                                    {"query", "Round", "draw", "input_2",
                                     "random.bls12-381.fr/1", "draw", "V"});
  if (!encoded) {
    errs() << toString(encoded.takeError());
    return 1;
  }
  if (auto e = checkParameters("transcript.native.challenge", {*encoded})) {
    errs() << toString(std::move(e));
    return 1;
  }
  auto refuses = [](Error e) {
    bool failed = bool(e);
    consumeError(std::move(e));
    return failed;
  };
  if (!refuses(checkParameters("transcript.native.observe.field", {*encoded})))
    return 1;
  for (size_t end = 0; end < encoded->size(); ++end)
    if (!refuses(
            checkNativeOrigin(StringRef(*encoded).take_front(end), "query")))
      return 1;
  for (auto value :
       {*encoded + "00", StringRef(*encoded).upper(), std::string(4098, '0')})
    if (!refuses(checkNativeOrigin(value, "query")))
      return 1;
  auto message = encodeNativeOrigin(
      "main", {}, {"message", "Round", "response", "response", "P", "V"});
  if (!message) {
    consumeError(message.takeError());
    return 1;
  }
  if (auto e = checkParameters("transcript.native.observe.field", {*message})) {
    consumeError(std::move(e));
    return 1;
  }
  for (auto entry : {"", "has space"}) {
    auto bad =
        encodeNativeOrigin(entry, {}, {"message", "Round", "r", "r", "P", "V"});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  for (StringRef port : {"service_2", "input_", "input_01", "input_+1",
                         "input_18446744073709551616"}) {
    auto bad = encodeNativeOrigin(
        "main", {},
        {"query", "Round", "draw", port.str(), "random", "draw", "V"});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  auto indexed = encodeNativeOriginTemplate(
      "main", {{"repeat", "main", "rounds"}, {"apply", "main", "step"}},
      {"query", "Round", "draw", "input_2", "random.bls12-381.fr/1", "draw",
       "V"});
  if (!indexed) {
    consumeError(indexed.takeError());
    return 1;
  }
  if (auto e =
          checkParameters("transcript.native.indexed.challenge", {*indexed})) {
    consumeError(std::move(e));
    return 1;
  }
  if (!refuses(checkParameters("transcript.native.challenge", {*indexed})) ||
      !refuses(
          checkParameters("transcript.native.indexed.challenge", {*encoded})) ||
      !refuses(checkParameters("transcript.native.indexed.observe.field",
                               {*indexed})))
    return 1;
  for (size_t end = 0; end < indexed->size(); ++end)
    if (!refuses(checkNativeOrigin(StringRef(*indexed).take_front(end), "query",
                                   true)))
      return 1;
  for (auto value :
       {*indexed + "00", StringRef(*indexed).upper(), std::string(4098, '0')})
    if (!refuses(checkNativeOrigin(value, "query", true)))
      return 1;
  outs() << *encoded << '\n';
}
