#include "zkc/Language/Names.h"

int main() {
  using namespace zkc::language;
  return !(isSourceIdentifier(u8"β₂") && !isSourceIdentifier(u8"e\u0301") &&
           encodeSourceSymbol(u8"m::α", 11) == "s1h6d2hceb1" &&
           nativeRoleName(15) == "role0000000f" &&
           matchingSourceDelimiter(0x27ea) == 0x27eb);
}
