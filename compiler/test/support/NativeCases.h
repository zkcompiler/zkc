#ifndef ZKC_TEST_SUPPORT_NATIVE_CASES_H
#define ZKC_TEST_SUPPORT_NATIVE_CASES_H

#include "../Names.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <stdexcept>

namespace zkc::test {
// Compiler builtins preserve the assertion's caller location under C++17.
inline void require(bool condition, const llvm::Twine &message,
                    const char *file = __builtin_FILE(),
                    unsigned line = __builtin_LINE()) {
  if (!condition)
    throw std::runtime_error(
        (llvm::Twine(file) + ":" + llvm::Twine(line) + ": " + message).str());
}
template <typename T>
T take(llvm::Expected<T> result, const char *file = __builtin_FILE(),
       unsigned line = __builtin_LINE()) {
  if (!result)
    require(false, llvm::toString(result.takeError()), file, line);
  return std::move(*result);
}
template <typename T>
void refuses(llvm::Expected<T> result, llvm::StringRef code,
             const char *file = __builtin_FILE(),
             unsigned line = __builtin_LINE()) {
  if (result)
    require(false, llvm::Twine("expected refusal: ") + code, file, line);
  auto message = llvm::toString(result.takeError());
  require(namesIdentifier(message, code), "unexpected refusal: " + message,
          file, line);
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
