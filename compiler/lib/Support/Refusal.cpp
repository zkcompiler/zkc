#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"

namespace zkc {
char Refusal::ID = 0;
void Refusal::log(llvm::raw_ostream &out) const {
  out << code;
  if (!detail.empty())
    out << ": " << detail;
}
llvm::Error error(llvm::StringRef code, const llvm::Twine &detail) {
  return llvm::make_error<Refusal>(code.str(), detail.str());
}
} // namespace zkc
