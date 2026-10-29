#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
int main() {
  for (StringRef text : {"0", "123456789012345678901234567890"}) {
    auto parsed = zkc::parseJson(text);
    if (!parsed) {
      errs() << toString(parsed.takeError());
      return 1;
    }
    if (zkc::printJson(*parsed) != text)
      return 1;
  }
  for (StringRef digits : {"", "01", "-1", "1e3", "1,2"}) {
    auto n = zkc::natural(zkc::naturalValue(digits));
    if (n) {
      errs() << "accepted noncanonical natural marker: " << digits;
      return 1;
    }
    consumeError(n.takeError());
  }
  auto extra = zkc::natural(json::Object{{"natural", "1"}, {"extra", true}});
  if (extra)
    return 1;
  consumeError(extra.takeError());
  // Public callers can construct arbitrary LLVM JSON objects. Printing one
  // must not dereference an absent marker or synthesize raw numeric syntax.
  if (zkc::printJson(json::Object{}) != "{}" ||
      zkc::printJson(zkc::naturalValue("1,2")) != "{\"natural\":\"1,2\"}")
    return 1;
  auto unsupported = zkc::parseJson("{}");
  if (unsupported)
    return 1;
  consumeError(unsupported.takeError());

  for (StringRef malformed :
       {R"("\uD800")", R"("\uDC00")", R"("\uD800x")", R"("\uD800\u0041")",
        "\"\xc0\xaf\"", "\"\xed\xa0\x80\""}) {
    auto parsed = zkc::parseJson(malformed);
    if (parsed) {
      errs() << "lossy Unicode accepted\n";
      return 1;
    }
    consumeError(parsed.takeError());
  }
  for (StringRef valid :
       {R"("\uD83D\uDE00")", R"("\u0041")", R"("\\uD800")", "\"한글\""}) {
    auto parsed = zkc::parseJson(valid);
    if (!parsed) {
      errs() << toString(parsed.takeError());
      return 1;
    }
    auto again = zkc::parseJson(zkc::printJson(*parsed));
    if (!again || *again != *parsed)
      return 1;
  }
  auto exact = [](StringRef text) {
    return zkc::parseNaturalJson(text, 4096, 16, "json-invalid", "json-limit");
  };
  // Compare every pair, including adjacent values above the signed range.
  // The independently authored decimal spellings define the expected result.
  for (StringRef left : {"0", "1", "9007199254740992", "9007199254740993",
                         "9223372036854775807", "9223372036854775808",
                         "18446744073709551614", "18446744073709551615"}) {
    for (StringRef right : {"0", "1", "9007199254740992", "9007199254740993",
                            "9223372036854775807", "9223372036854775808",
                            "18446744073709551614", "18446744073709551615"}) {
      auto a = exact(("{\"value\":[" + left + "],\"flag\":true}").str());
      auto b = exact(("{\"flag\":true,\"value\":[" + right + "]}").str());
      if (!a || !b) {
        if (!a)
          consumeError(a.takeError());
        if (!b)
          consumeError(b.takeError());
        errs() << "unsigned boundary failed parsing\n";
        return 1;
      }
      if (zkc::equalNaturalJson(*a, *b) != (left == right)) {
        errs() << "inexact unsigned equality: " << left << " vs " << right;
        return 1;
      }
    }
  }
  for (StringRef text :
       {"18446744073709551616", "9999999999999999999999", "1e0", "1.0", "-0",
        "+1", "01", R"({"x":1,"\u0078":1})"}) {
    auto parsed = exact(text);
    if (parsed) {
      errs() << "lossy/noncanonical natural JSON accepted: " << text;
      return 1;
    }
    consumeError(parsed.takeError());
  }
  if (!zkc::equalNaturalJson(json::Value(1), json::Value(uint64_t(1))) ||
      zkc::equalNaturalJson(json::Value(1.0), json::Value(1)) ||
      zkc::equalNaturalJson(json::Value(1.0), json::Value(1.0)) ||
      zkc::equalNaturalJson(json::Value(-1), json::Value(-1)) ||
      zkc::equalNaturalJson(json::Array{0, 1}, json::Array{1, 0}) ||
      zkc::equalNaturalJson(json::Array{0}, json::Array{0, 1}) ||
      zkc::equalNaturalJson(json::Object{{"x", 1}}, json::Object{{"y", 1}}) ||
      zkc::equalNaturalJson(json::Object{}, json::Object{{"x", 1}}) ||
      zkc::equalNaturalJson(json::Value(nullptr), json::Value(false)) ||
      !zkc::equalNaturalJson(json::Value(nullptr), json::Value(nullptr))) {
    errs() << "exact natural JSON shape controls failed\n";
    return 1;
  }
  outs()
      << "natural markers, exact unsigned JSON and carrier controls passed\n";
}
