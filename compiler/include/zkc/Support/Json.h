#ifndef ZKC_SUPPORT_JSON_H
#define ZKC_SUPPORT_JSON_H

#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace zkc {
// The array format admits natural tokens of arbitrary precision. LLVM's JSON
// numeric carrier is insufficient, so parsing retains those tokens explicitly.
// Natural markers are singleton {"natural": "<canonical decimal>"} objects.
// The textual input profile rejects ordinary objects. printJson preserves
// malformed/programmatically supplied objects as JSON instead of unwrapping
// their contents; subsequent parsing/admission therefore rejects them.
/// Reject invalid UTF-8 and unpaired surrogate escapes in a quoted JSON token.
/// The caller still checks JSON string syntax and escapes.
bool validStringEncoding(llvm::StringRef quotedSpelling);
/// invalidStringOffset, when supplied, identifies a rejected Unicode spelling
/// in the original text. It is cleared before parsing; other failures leave it
/// empty.
llvm::Expected<llvm::json::Value>
parseJson(llvm::StringRef text,
          std::optional<size_t> *invalidStringOffset = nullptr);
std::string printJson(const llvm::json::Value &value);
llvm::Expected<std::string> natural(const llvm::json::Value &value);
llvm::json::Value naturalValue(llvm::StringRef digits);
/// A refusal carries its stable identifier as a field. Consumers that re-home
/// a refusal read `code`; the rendered text is `code` or `code: detail`, and
/// nothing recovers an identifier by splitting it.
class Refusal : public llvm::ErrorInfo<Refusal> {
public:
  static char ID;
  std::string code, detail;
  Refusal(std::string code, std::string detail)
      : code(std::move(code)), detail(std::move(detail)) {}
  void log(llvm::raw_ostream &out) const override;
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};
llvm::Error error(llvm::StringRef code, const llvm::Twine &detail = {});
} // namespace zkc
#endif
