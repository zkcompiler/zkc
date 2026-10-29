#include "zkc/Source/Names.h"
#include "zkc/Syntax/Syntax.h"

int main() {
  using namespace zkc::source;
  auto parsed =
      zkc::syntax::parse(Revision({"m", "module m\ndef f():\n    0\n", ""}));
  if (parsed.status() != zkc::syntax::Status::Complete ||
      !zkc::syntax::format(parsed).complete)
    return 1;
  return !(isSourceIdentifier(u8"β₂") && !isSourceIdentifier(u8"e\u0301") &&
           encodeSourceSymbol(u8"m::α", 11) == "s1h6d2hceb1" &&
           nativeRoleName(15) == "role0000000f" &&
           matchingSourceDelimiter(0x27ea) == 0x27eb);
}
