#include "zkc/Language/Names.h"
#include "llvm/Support/raw_ostream.h"
#include <array>
#include <fstream>
#include <limits>
#include <sstream>
#include <utf8proc.h>
#include <vector>

using namespace llvm;
using namespace zkc::language;

namespace {
unsigned failures = 0;
uint64_t checks = 0;
void check(bool value, StringRef context) {
  ++checks;
  if (!value) {
    if (failures < 30)
      errs() << "FAIL: " << context << '\n';
    ++failures;
  }
}
std::string scalarText(uint32_t value) {
  utf8proc_uint8_t bytes[4];
  auto count = utf8proc_encode_char(value, bytes);
  return std::string(reinterpret_cast<const char *>(bytes), count);
}
std::string normalize(StringRef text) {
  utf8proc_uint8_t *result = nullptr;
  auto size =
      utf8proc_map(reinterpret_cast<const utf8proc_uint8_t *>(text.data()),
                   text.size(), &result, UTF8PROC_STABLE | UTF8PROC_COMPOSE);
  check(size >= 0, "normalization corpus input is valid");
  std::string output;
  if (size >= 0)
    output.assign(reinterpret_cast<const char *>(result), size);
  utf8proc_free(result);
  return output;
}
std::vector<std::string> rows(StringRef filename) {
  std::ifstream input(std::string(ZKC_UNICODE_DATA) + "/" + filename.str());
  check(input.is_open(), filename);
  std::vector<std::string> result;
  std::string line;
  while (std::getline(input, line)) {
    line = StringRef(line).split('#').first.trim().str();
    if (!line.empty() && line[0] != '@')
      result.push_back(line);
  }
  return result;
}
std::vector<std::string> fields(StringRef row) {
  std::vector<std::string> result;
  while (row.contains(';')) {
    auto pair = row.split(';');
    result.push_back(pair.first.trim().str());
    row = pair.second;
  }
  result.push_back(row.trim().str());
  return result;
}
unsigned fromHex(const std::string &text) {
  return std::stoul(text, nullptr, 16);
}
std::string fromScalars(const std::string &text) {
  std::istringstream input(text);
  std::string result, scalar;
  while (input >> scalar)
    result += scalarText(fromHex(scalar));
  return result;
}

void normalizationCorpus() {
  unsigned count = 0;
  for (const auto &row : rows("NormalizationTest.txt")) {
    auto columns = fields(row);
    check(columns.size() == 6, "normalization corpus row shape");
    if (columns.size() != 6)
      continue;
    std::array<std::string, 5> text;
    for (unsigned i = 0; i < 5; ++i)
      text[i] = fromScalars(columns[i]);
    for (unsigned i = 0; i < 5; ++i) {
      const auto &expected = text[i < 3 ? 1 : 3];
      check(normalize(text[i]) == expected, row);
      check(isSourceNFC(text[i]) == (text[i] == expected), row);
    }
    ++count;
  }
  check(count == 20034, "complete Unicode 17 normalization corpus");
  outs() << count << " normalization rows, five NFC equations each\n";
}

void profileCorpus() {
  // Independently read raw properties, without consuming generated ranges.
  constexpr unsigned count = 0x110000;
  std::vector<uint8_t> expected(count, 0);
  enum : uint8_t {
    Start = 1,
    Continue = 2,
    Excluded = 4,
    Math = 8,
    Open = 16,
    Close = 32
  };
  for (StringRef filename : {"DerivedCoreProperties.txt", "PropList.txt"}) {
    for (const auto &row : rows(filename)) {
      auto columns = fields(row);
      unsigned flag = columns[1] == "XID_Start"      ? Start
                      : columns[1] == "XID_Continue" ? Continue
                      : columns[1] == "Default_Ignorable_Code_Point" ||
                              columns[1] == "Bidi_Control"
                          ? Excluded
                          : 0;
      if (!flag)
        continue;
      auto range = StringRef(columns[0]).split("..");
      unsigned first = fromHex(range.first.str());
      unsigned last =
          range.second.empty() ? first : fromHex(range.second.str());
      for (unsigned value = first; value <= last; ++value)
        expected[value] |= flag;
    }
  }
  expected['_'] |= Start;
  for (unsigned value = 0x2080; value <= 0x2089; ++value)
    expected[value] |= Continue;
  for (const auto &row : rows("UnicodeData.txt")) {
    auto columns = fields(row);
    unsigned flag = columns[2] == "Sm"   ? Math
                    : columns[2] == "Ps" ? Open
                    : columns[2] == "Pe" ? Close
                                         : 0;
    if (flag) {
      check(columns[1].find(", First>") == std::string::npos &&
                columns[1].find(", Last>") == std::string::npos,
            "relevant categories use individual raw rows");
      expected[fromHex(columns[0])] |= flag;
    }
  }
  std::vector<uint32_t> partners(count, 0);
  std::vector<bool> closers(count, false);
  for (const auto &row : rows("BidiBrackets.txt")) {
    auto columns = fields(row);
    unsigned opener = fromHex(columns[0]), closer = fromHex(columns[1]);
    if (columns[2] == "o" && opener >= 128 && closer >= 128 &&
        (expected[opener] & Open) && (expected[closer] & Close) &&
        !(expected[opener] & (Start | Continue | Excluded)) &&
        !(expected[closer] & (Start | Continue | Excluded)) &&
        isSourceNFC(scalarText(opener)) && isSourceNFC(scalarText(closer))) {
      partners[opener] = closer;
      closers[closer] = true;
    }
  }
  for (unsigned value = 0; value < count; ++value) {
    auto flags = expected[value];
    check(sourceIdentifierStart(value) ==
              ((flags & Start) && !(flags & Excluded)),
          "XID_Start corpus");
    check(sourceIdentifierContinue(value) ==
              ((flags & Continue) && !(flags & Excluded)),
          "XID_Continue corpus");
    check(isMathematicalSymbol(value) ==
              ((flags & Math) && value >= 128 &&
               !(flags & (Start | Continue | Excluded)) &&
               isSourceNFC(scalarText(value))),
          "Sm corpus");
    check(matchingSourceDelimiter(value).value_or(0) == partners[value],
          "BidiBrackets opener corpus");
    check(isSourceDelimiterCloser(value) == closers[value],
          "BidiBrackets closer corpus");
    if (value >= 0xd800 && value <= 0xdfff)
      continue;
    auto bytes = scalarText(value);
    auto scalar = decodeSourceScalar(bytes, 0);
    check(scalar && scalar->value == value && scalar->bytes == bytes.size(),
          "all Unicode scalar encodings");
  }
  for (uint32_t value : {0x110000U, 0xffffffffU}) {
    check(!sourceIdentifierStart(value) && !sourceIdentifierContinue(value) &&
              !isMathematicalSymbol(value) && !matchingSourceDelimiter(value) &&
              !isSourceDelimiterCloser(value),
          "out-of-range scalar refusal");
  }
}

void examples() {
  check(StringRef(utf8proc_version()) == "2.12.0", "exact NFC implementation");
  check(
      sourceNameProfileIdentity() ==
          "zkc.source-names/"
          "0:8c5968e4c0b582e3f8130e123383df16dce1674f2ecb41cd62feed03d2fdd73a",
      "profile identity includes the pinned manifest");
  for (StringRef text : {"x", "_", "beta_2", u8"β₂", u8"α", u8"한글", u8"é",
                         u8"𝛂", u8"𐐀", u8"a\u0316\u0315"})
    check(isSourceIdentifier(text), text);
  for (StringRef text : {"", "2a", u8"₂β", u8"e\u0301", u8"a\u0315\u0316",
                         u8"\u2126", u8"x\u200c", u8"x\u200d", u8"x\u202e",
                         u8"x\ufe0f", u8"\u034f", "a-b", "a::b", u8"\u0558"})
    check(!isSourceIdentifier(text), text);
  check(isSourceIdentifier(u8"a") && isSourceIdentifier(u8"а") &&
            encodeSourceSymbol(u8"a", 100) != encodeSourceSymbol(u8"а", 100),
        "Latin and Cyrillic confusables remain distinct");
  check(isSourceNFC(u8"𝛂") && normalize(u8"𝛂") == u8"𝛂",
        "no compatibility or case folding");
  check(!sourceIdentifierStart(0x558) && !sourceIdentifierContinue(0x558),
        "Unicode 18-only letter remains outside the Unicode 17 profile");
  for (StringRef text :
       {"\x80", "\xc0\xaf", "\xc1\xbf", "\xc2", "\xe0\x80\x80", "\xed\xa0\x80",
        "\xed\xbf\xbf", "\xe2\x82", "\xe2(A", "\xf0\x80\x80\x80",
        "\xf4\x90\x80\x80", "\xf5\x80\x80\x80", "\xff", "\xf0\x90\x80"}) {
    check(!decodeSourceScalar(text, 0), "invalid UTF-8 scalar");
    check(!isSourceIdentifier(text) && !isSourceNFC(text),
          "invalid UTF-8 name/NFC");
    check(!decodeNominalIdentity(encodeNominalIdentity(text), 100),
          "invalid UTF-8 nominal preimage");
  }
  StringRef text = u8"aβ𐐀";
  for (size_t offset : {2U, 4U, 5U, 6U, 7U, 8U})
    check(!decodeSourceScalar(text, offset), "non-boundary UTF-8 offset");
  check(!decodeSourceScalar(text, std::numeric_limits<size_t>::max()),
        "oversized UTF-8 offset");
  check(decodeSourceScalar(text, 1)->bytes == 2 &&
            decodeSourceScalar(text, 3)->bytes == 4,
        "exact UTF-8 byte spans");
  check(isSourceNFC(StringRef("x\0y", 3)) &&
            !isSourceIdentifier(StringRef("x\0y", 3)),
        "embedded NUL is not a terminator");
  check(isMathematicalSymbol(0x2299) && isMathematicalSymbol(0x2211) &&
            isMathematicalSymbol(0x220f),
        "Sm tokens include declaration-reserved binders");
  for (uint32_t scalar : {0x2b, 0x207a, 0x1d40, 0x2118, 0x200b, 0x2260}) {
    // U+207A and U+2260 are NFC Sm; superscript letters and XID Sm are not
    // operators.
    check(isMathematicalSymbol(scalar) ==
              (scalar == 0x207a || scalar == 0x2260),
          "operator category, identifier exclusion and NFC");
  }
  check(matchingSourceDelimiter(0x27ea) == 0x27eb &&
            isSourceDelimiterCloser(0x27eb),
        "angle bracket pair");
  check(!matchingSourceDelimiter('(') && !matchingSourceDelimiter(0x2329) &&
            !isSourceDelimiterCloser(0x232a),
        "reserved ASCII and non-NFC brackets");

  check(nativeRoleName(0) == "role00000000" &&
            nativeRoleName(0x1a) == "role0000001a" &&
            nativeRoleName(0xffffffff) == "roleffffffff",
        "role label bounds");
  check(nativeSetupName(0x10) == "setup00000010" &&
            nativeSetupName(0xffffffff) == "setupffffffff",
        "setup labels");
  check(nativeAlternativeName(0) == "case00000000" &&
            nativeAlternativeName(0xffffffff) == "caseffffffff",
        "alternative labels");
  check(encodeSourceSymbol(u8"m::α", 11) == "s1h6d2hceb1",
        "framed Unicode symbol");
  check(encodeSourceSymbol("ab::c", 100) == "s2h61621h63" &&
            encodeSourceSymbol("a::bc", 100) == "s1h612h6263",
        "unambiguous ASCII frames");
  auto symbol = encodeSourceSymbol(u8"m::α", 100);
  check(symbol && encodeSourceSymbol(u8"m::α", symbol->size()) == symbol &&
            !encodeSourceSymbol(u8"m::α", symbol->size() - 1),
        "exact symbol ceiling");
  for (StringRef path :
       {"", "::x", "x::", "x::::y", "x:y", "x::2y", u8"m::e\u0301"})
    check(!encodeSourceSymbol(path, 100), "malformed qualified name");
  check(!encodeSourceSymbol("a", 0) && !encodeSourceSymbol("a", 4) &&
            encodeSourceSymbol("a", 5) == "s1h61",
        "small symbol budgets");
  std::string longName(4096, 'a');
  check(encodeSourceSymbol(longName, 8198).has_value() &&
            !encodeSourceSymbol(longName, 8197),
        "decimal length and expansion ceiling");
  for (StringRef preimage : {"", u8"m::Τ<α,2>", u8"a\u0315\u0316"}) {
    auto hex = encodeNominalIdentity(preimage);
    check(decodeNominalIdentity(hex, preimage.size()) == preimage.str(),
          "exact nominal preimage, including non-NFC ordering");
    if (!preimage.empty())
      check(!decodeNominalIdentity(hex, preimage.size() - 1),
            "nominal size ceiling");
  }
  check(encodeNominalIdentity(u8"α") == "ceb1", "lowercase nominal hex");
  for (StringRef hex : {"c", "CEB1", "ceB1", "0x61", "61 62", "gg", "c080",
                        "eda080", "f4908080"})
    check(!decodeNominalIdentity(hex, 100), "noncanonical/invalid nominal hex");
  check(decodeNominalIdentity("00", 1) == std::string(1, '\0'),
        "nominal decoding preserves exact UTF-8 NUL bytes");
}

void dumpProfile() {
  for (auto predicate : {sourceIdentifierStart, sourceIdentifierContinue,
                         isMathematicalSymbol}) {
    uint32_t first = 0;
    bool active = false;
    for (uint32_t scalar = 0; scalar <= 0x110000; ++scalar) {
      bool member = predicate(scalar);
      if (member && !active)
        first = scalar;
      if (!member && active)
        outs() << first << ".." << scalar - 1 << '\n';
      active = member;
    }
    outs() << ";\n";
  }
  for (uint32_t scalar = 0; scalar < 0x110000; ++scalar)
    if (auto closer = matchingSourceDelimiter(scalar))
      outs() << scalar << ':' << *closer << '\n';
}
} // namespace

int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--dump-profile") {
    dumpProfile();
    return 0;
  }
  examples();
  normalizationCorpus();
  profileCorpus();
  outs() << checks << " checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
