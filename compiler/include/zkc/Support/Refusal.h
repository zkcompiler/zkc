#ifndef ZKC_SUPPORT_REFUSAL_H
#define ZKC_SUPPORT_REFUSAL_H

#include "llvm/Support/Error.h"

namespace zkc {
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
