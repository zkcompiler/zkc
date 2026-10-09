#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
using namespace zkc::protocol;
int main() {
  auto refuses = [](Error e) {
    bool failed = bool(e);
    consumeError(std::move(e));
    return failed;
  };
  auto indexed = encodeNativeOriginTemplate(
      "main", {{"repeat", "main", "rounds"}, {"apply", "main", "step"}},
      {"query", "Round", "draw", "input_2", "random.bls12-381.fr/0", "draw",
       "V"});
  if (!indexed) {
    errs() << toString(indexed.takeError());
    return 1;
  }
  if (refuses(
          checkParameters("transcript.native.indexed.challenge", {*indexed})) ||
      !refuses(checkParameters("transcript.native.indexed.observe.data",
                               {*indexed})))
    return 1;
  for (size_t end = 0; end < indexed->size(); ++end)
    if (!refuses(
            checkNativeOrigin(StringRef(*indexed).take_front(end), "query")))
      return 1;
  for (auto value :
       {*indexed + "00", StringRef(*indexed).upper(), std::string(4098, '0')})
    if (!refuses(checkNativeOrigin(value, "query")))
      return 1;
  auto message = encodeNativeOriginTemplate(
      "main", {}, {"message", "Round", "response", "response", "P", "V"});
  if (!message) {
    consumeError(message.takeError());
    return 1;
  }
  if (refuses(checkParameters("transcript.native.indexed.observe.data",
                              {*message})))
    return 1;
  for (auto entry : {"", "has space"}) {
    auto bad = encodeNativeOriginTemplate(
        entry, {}, {"message", "Round", "r", "r", "P", "V"});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  for (StringRef port : {"service_2", "input_", "input_01", "input_+1",
                         "input_18446744073709551616"}) {
    auto bad = encodeNativeOriginTemplate(
        "main", {},
        {"query", "Round", "draw", port.str(), "random", "draw", "V"});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  for (auto step : {"call", "unknown"}) {
    auto bad =
        encodeNativeOriginTemplate("main", {{step, "main", "step"}},
                                   {"message", "Round", "r", "r", "P", "V"});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  // A plain origin header cannot be substituted for the indexed template.
  auto plain = *message;
  const std::string current =
      "7a6b632e6e61746976652d6f726967696e2d74656d706c6174652f30";
  auto start = plain.find(current);
  if (start == std::string::npos)
    return 1;
  plain.replace(start, current.size(),
                "7a6b632e6e61746976652d6f726967696e2f30");
  plain.replace(start - 16, 16, "1300000000000000");
  if (!refuses(checkNativeOrigin(plain, "message")))
    return 1;
}
