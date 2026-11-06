#include "OracleNativeCommon.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include <array>
#include <limits>
#include <list>

namespace zkc::protocol {
// Private wire reader. Unescaped strings borrow the input until the complete
// record check returns. Escaped strings own their decoded spelling. Lexing
// validates UTF-8 while finding tokens, then grammar construction checks
// decoded-key uniqueness at insertion. There is no whole-input UTF-8 pass,
// owned copy of every name, or duplicate-key recount of the completed tree.
class OracleRecordJson {
  struct Token {
    char kind;
    llvm::json::Value value;
    bool owned = false;
    size_t elements = 0;
  };
  llvm::StringRef text;
  OracleNativeWork &work;
  // Linked nodes keep owned strings stable without any token-buffer relocation.
  std::list<Token> tokens;
  std::list<Token>::iterator position;
  std::array<Token *, 64> containers;
  size_t inventoryDepth = 0;
  bool valid = true, depthExceeded = false;

  bool spend(uint64_t amount = 1) {
    if (!work.charge(amount))
      return valid = false;
    return true;
  }
  void token(char kind, llvm::json::Value value = nullptr, bool owned = false) {
    if (!spend())
      return;
    tokens.push_back({kind, std::move(value), owned});
    if (!valid)
      return;
    // Inventory each token during its charged insertion, before any grammar
    // allocation. Nested containers contribute one immediate parent element.
    auto &current = tokens.back();
    if (inventoryDepth && containers[inventoryDepth - 1]->kind == '[' &&
        (kind == 's' || kind == 'n' || kind == 'v' || kind == '[' ||
         kind == '{'))
      ++containers[inventoryDepth - 1]->elements;
    if (kind == '[' || kind == '{') {
      if (inventoryDepth == containers.size()) {
        valid = false;
        return;
      }
      containers[inventoryDepth++] = &current;
    } else if (kind == ']' || kind == '}') {
      if (!inventoryDepth ||
          containers[inventoryDepth - 1]->kind != (kind == ']' ? '[' : '{'))
        valid = false;
      else
        --inventoryDepth;
    }
  }
  bool unit(size_t &offset, uint32_t &value) {
    value = 0;
    if (text.size() - offset < 4)
      return false;
    for (unsigned i = 0; i < 4; ++i) {
      int digit = llvm::hexDigitValue(text[offset++]);
      if (digit < 0)
        return false;
      value = 16 * value + digit;
    }
    return true;
  }
  void string(size_t &offset) {
    size_t start = ++offset, span = start;
    bool escaped = false, good = true, closed = false;
    struct Piece {
      size_t start, end;
      uint32_t scalar;
    };
    llvm::SmallVector<Piece, 0> pieces;
    size_t decodedSize = 0;
    auto piece = [&](size_t begin, size_t end, uint32_t scalar = 0) {
      if (!spend() ||
          (pieces.size() == pieces.capacity() && !spend(pieces.size())))
        return false;
      pieces.push_back({begin, end, scalar});
      decodedSize += end > begin        ? end - begin
                     : scalar < 0x80    ? 1
                     : scalar < 0x800   ? 2
                     : scalar < 0x10000 ? 3
                                        : 4;
      return true;
    };
    auto spanPiece = [&](size_t end) {
      return end == span || piece(span, end);
    };
    while (offset < text.size() && !work.exhausted) {
      unsigned char ch = text[offset++];
      if (ch == '"') {
        closed = true;
        break;
      }
      if (ch < 0x20) {
        good = false;
        continue;
      }
      if (ch >= 0x80) {
        // Validate the complete Unicode scalar while consuming its bytes.
        unsigned count = ch >= 0xc2 && ch <= 0xdf   ? 1
                         : ch >= 0xe0 && ch <= 0xef ? 2
                         : ch >= 0xf0 && ch <= 0xf4 ? 3
                                                    : 0;
        if (!count || text.size() - offset < count) {
          good = false;
          continue;
        }
        auto next = static_cast<unsigned char>(text[offset]);
        if ((ch == 0xe0 && next < 0xa0) || (ch == 0xed && next >= 0xa0) ||
            (ch == 0xf0 && next < 0x90) || (ch == 0xf4 && next >= 0x90))
          good = false;
        for (unsigned i = 0; i < count; ++i) {
          next = static_cast<unsigned char>(text[offset]);
          if (next < 0x80 || next > 0xbf) {
            good = false;
            break;
          }
          ++offset;
        }
        continue;
      }
      if (ch != '\\')
        continue;
      escaped = true;
      if (!spanPiece(offset - 1))
        return;
      if (offset == text.size()) {
        good = false;
        break;
      }
      ch = text[offset++];
      char simple = 0;
      switch (ch) {
      case '"':
        simple = '"';
        break;
      case '\\':
        simple = '\\';
        break;
      case '/':
        simple = '/';
        break;
      case 'b':
        simple = '\b';
        break;
      case 'f':
        simple = '\f';
        break;
      case 'n':
        simple = '\n';
        break;
      case 'r':
        simple = '\r';
        break;
      case 't':
        simple = '\t';
        break;
      case 'u': {
        uint32_t scalar;
        if (!unit(offset, scalar)) {
          good = false;
          break;
        }
        if (scalar >= 0xdc00 && scalar <= 0xdfff) {
          good = false;
          break;
        }
        if (scalar >= 0xd800 && scalar <= 0xdbff) {
          uint32_t low;
          if (!text.substr(offset).starts_with("\\u")) {
            good = false;
            break;
          }
          offset += 2;
          if (!unit(offset, low) || low < 0xdc00 || low > 0xdfff) {
            good = false;
            break;
          }
          scalar = 0x10000 + ((scalar - 0xd800) << 10) + low - 0xdc00;
        }
        if (!piece(0, 0, scalar))
          return;
        span = offset;
        continue;
      }
      default:
        good = false;
        break;
      }
      if (ch != 'u' && good && !piece(0, 0, simple))
        return;
      span = offset;
    }
    if (!closed || !good) {
      valid = false;
      return;
    }
    if (escaped) {
      if (!spanPiece(offset - 1) || !spend(pieces.size()) ||
          !spend(decodedSize))
        return;
      // Reserve the empty buffer once. The charged pieces describe its exact
      // width, so append cannot relocate an already decoded prefix.
      std::string decoded;
      decoded.reserve(decodedSize);
      for (const auto &part : pieces) {
        if (part.end > part.start) {
          decoded.append(text.data() + part.start, part.end - part.start);
          continue;
        }
        uint32_t scalar = part.scalar;
        char bytes[4];
        unsigned size = scalar < 0x80      ? 1
                        : scalar < 0x800   ? 2
                        : scalar < 0x10000 ? 3
                                           : 4;
        for (unsigned i = size - 1; i; --i) {
          bytes[i] = 0x80 | (scalar & 0x3f);
          scalar >>= 6;
        }
        bytes[0] = size == 1 ? scalar
                             : (size == 2   ? 0xc0
                                : size == 3 ? 0xe0
                                            : 0xf0) |
                                   scalar;
        decoded.append(bytes, size);
      }
      // The owned Value constructor independently checks the decoded UTF-8.
      if (!spend(decodedSize))
        return;
      token('s', llvm::json::Value(std::move(decoded)), true);
    } else {
      auto value = text.slice(start, offset - 1);
      // json::Value's borrowed-string constructor independently checks UTF-8.
      if (spend(value.size()))
        token('s', llvm::json::Value(value));
    }
  }
  void lex() {
    unsigned depth = 0;
    for (size_t i = 0; i < text.size() && !work.exhausted;) {
      char ch = text[i];
      if (ch == '"') {
        string(i);
        continue;
      }
      // Retain the bounded reader's depth refusal precedence, including later
      // delimiters after a malformed number or comment.
      if (ch == '/' && i + 1 < text.size() && text[i + 1] == '/') {
        valid = false;
        while (i < text.size() && text[i] != '\n')
          ++i;
        continue;
      }
      bool comparison = (ch == '<' || ch == '>') &&
                        ((i + 1 < text.size() && text[i + 1] == '=') ||
                         (ch == '>' && i && text[i - 1] == '-'));
      if (!comparison && (ch == '(' || ch == '[' || ch == '{' || ch == '<')) {
        if (++depth > 64) {
          depthExceeded = true;
          return;
        }
      } else if (!comparison &&
                 (ch == ')' || ch == ']' || ch == '}' || ch == '>')) {
        if (depth)
          --depth;
      }
      if (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') {
        ++i;
        continue;
      }
      if (ch >= '0' && ch <= '9') {
        uint64_t value = 0;
        bool leadingZero = ch == '0';
        size_t start = i;
        while (i < text.size() && text[i] >= '0' && text[i] <= '9') {
          unsigned digit = text[i++] - '0';
          if (value > (std::numeric_limits<uint64_t>::max() - digit) / 10)
            valid = false;
          else
            value = 10 * value + digit;
        }
        if (leadingZero && i - start != 1)
          valid = false;
        token('n', value);
        continue;
      }
      bool literal = false;
      for (auto word : {llvm::StringRef("null"), llvm::StringRef("true"),
                        llvm::StringRef("false")}) {
        if (ch != word.front())
          continue;
        // Only one word can match its first byte. The word comparison is a
        // second visit, separate from the reserved lexical input width.
        if (!spend(word.size()))
          return;
        if (text.substr(i).starts_with(word)) {
          token('v', word == "null" ? llvm::json::Value(nullptr)
                                    : llvm::json::Value(word == "true"));
          i += word.size();
          literal = true;
        }
        break;
      }
      if (literal)
        continue;
      if (ch != '[' && ch != ']' && ch != '{' && ch != '}' && ch != ',' &&
          ch != ':')
        valid = false;
      token(ch);
      ++i;
    }
  }
  bool take(char kind) {
    if (position == tokens.end() || position->kind != kind)
      return false;
    ++position;
    return true;
  }
  // json::Object does not expose DenseMap::reserve. Reserve its opaque work
  // before try_emplace instead. These bounds follow the pinned DenseMap's
  // linear probing, 64-bucket initial allocation and 3/4 growth threshold.
  // No deletion occurs here. Length checks need no string-byte comparison;
  // only equal-length keys can cost a complete memcmp during a lookup.
  bool objectInsertion(const llvm::json::Object &object, llvm::StringRef key,
                       bool owned, unsigned &buckets, uint64_t &keyWidths,
                       uint64_t &ownedWidths) {
    uint64_t count = object.size(), comparisonWidths = 0;
    if (count) {
      // Inspect the existing lengths, including the iterator's occupancy scan.
      if (!spend(buckets / 32 + count))
        return false;
      for (const auto &field : object)
        if (llvm::StringRef(field.first).size() == key.size())
          comparisonWidths += key.size();
    }
    auto lookup = [&] {
      // One hash, at most count occupied buckets and a terminating bucket.
      return spend(key.size()) && spend(count + 1) && spend(comparisonWidths);
    };
    if (buckets && !lookup())
      return false;
    if ((count + 1) * 4 >= uint64_t(buckets) * 3) {
      unsigned nextBuckets = buckets ? 2 * buckets : 64;
      // Growth scans the old occupancy words, initializes the new ones and
      // moves each prior entry. Its ith reinsert probes at most i buckets;
      // moveFrom hashes every prior key, without comparing any key bytes.
      // ObjectKey's move constructor copies an owned spelling in this LLVM.
      if (!spend(buckets / 32 + nextBuckets / 32 + count) ||
          !spend(count * (count + 1) / 2) || !spend(keyWidths) ||
          !spend(ownedWidths))
        return false;
      buckets = nextBuckets;
      // findBucketForInsertion repeats the new key's lookup after growth.
      if (!lookup())
        return false;
    }
    keyWidths += key.size();
    if (owned)
      ownedWidths += key.size();
    return true;
  }
  bool value(llvm::json::Value &output) {
    if (!spend() || position == tokens.end())
      return false;
    auto kind = position->kind;
    if (kind == 's' || kind == 'n' || kind == 'v') {
      output = std::move((position++)->value);
      return true;
    }
    if (kind == '[') {
      size_t elements = (position++)->elements;
      if (!spend(elements))
        return false;
      llvm::json::Array array;
      // Value's move is not noexcept in the pinned LLVM. Reserving before any
      // append prevents vector growth from copying prior owned subtrees.
      array.reserve(elements);
      if (!take(']'))
        do {
          llvm::json::Value child(nullptr);
          if (!value(child))
            return false;
          array.push_back(std::move(child));
          if (take(']')) {
            output = std::move(array);
            return true;
          }
        } while (take(','));
      else {
        output = std::move(array);
        return true;
      }
      return false;
    }
    if (take('{')) {
      llvm::json::Object object;
      unsigned buckets = 0;
      uint64_t keyWidths = 0, ownedWidths = 0;
      if (!take('}'))
        do {
          if (position == tokens.end() || position->kind != 's')
            return false;
          auto &keyToken = *position++;
          auto key = *keyToken.value.getAsString();
          // One insertion slot and ObjectKey UTF-8 validation. An escaped
          // spelling also pays key.str() and the insertion's ObjectKey copy.
          if (!spend(1 + (keyToken.owned ? 3 : 1) * key.size()))
            return false;
          llvm::json::ObjectKey name = keyToken.owned
                                           ? llvm::json::ObjectKey(key.str())
                                           : llvm::json::ObjectKey(key);
          if (!take(':'))
            return false;
          llvm::json::Value child(nullptr);
          if (!value(child) ||
              !objectInsertion(object, key, keyToken.owned, buckets, keyWidths,
                               ownedWidths) ||
              !object.try_emplace(std::move(name), std::move(child)).second)
            return false;
          if (take('}')) {
            output = std::move(object);
            return true;
          }
        } while (take(','));
      else {
        output = std::move(object);
        return true;
      }
    }
    return false;
  }

public:
  OracleRecordJson(llvm::StringRef text, OracleNativeWork &work)
      : text(text), work(work) {}
  llvm::Expected<llvm::json::Value> read() {
    if (text.size() > 32 * 1024 * 1024)
      return error("oracle-realization-record-limit");
    if (!spend(text.size()))
      return error("oracle-common-limit");
    lex();
    if (work.exhausted)
      return error("oracle-common-limit");
    if (depthExceeded)
      return error("oracle-realization-record-limit");
    position = tokens.begin();
    llvm::json::Value result(nullptr);
    if (!valid || !value(result) || position != tokens.end())
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-realization-record");
    return result;
  }
};
llvm::Expected<llvm::json::Value>
parseOracleRecordWithWork(llvm::StringRef text, OracleNativeWork &work) {
  return OracleRecordJson(text, work).read();
}
} // namespace zkc::protocol
