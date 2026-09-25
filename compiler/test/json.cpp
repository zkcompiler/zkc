#include "zkc/Target/Json.h"
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
  outs() << "natural markers and public JSON carrier controls passed\n";
}
