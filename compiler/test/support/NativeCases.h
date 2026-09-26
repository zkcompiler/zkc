#ifndef ZKC_TEST_SUPPORT_NATIVE_CASES_H
#define ZKC_TEST_SUPPORT_NATIVE_CASES_H

#include "../Names.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <stdexcept>

namespace zkc::test {
inline void require(bool condition, const llvm::Twine &message) {
  if (!condition)
    throw std::runtime_error(message.str());
}
template <typename T> T take(llvm::Expected<T> result) {
  if (!result)
    throw std::runtime_error(llvm::toString(result.takeError()));
  return std::move(*result);
}
template <typename T>
void refuses(llvm::Expected<T> result, llvm::StringRef code) {
  if (result)
    throw std::runtime_error("expected refusal: " + code.str());
  auto message = llvm::toString(result.takeError());
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
/// A failed prerequisite ends its own case; independent cases still execute.
class Cases {
  unsigned count = 0, failures = 0;

public:
  void run(const llvm::Twine &name, llvm::function_ref<void()> body) {
    ++count;
    try {
      body();
    } catch (const std::exception &failure) {
      ++failures;
      llvm::errs() << name << ": " << failure.what() << '\n';
    }
  }
  int result() const {
    llvm::outs() << count << " cases, " << failures << " failures\n";
    return failures ? 1 : 0;
  }
};
} // namespace zkc::test
#endif
