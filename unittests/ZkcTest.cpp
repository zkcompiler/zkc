//===- ZkcTest.cpp - The harness's registry and runner --------------------===//

#include "ZkcTest.h"

#include "llvm/Support/raw_ostream.h"

#include <vector>

namespace {

struct Case {
  const char *suite;
  const char *name;
  void (*body)();
};

/// Function-local so registration during static initialization cannot
/// race the container's own construction.
std::vector<Case> &cases() {
  static std::vector<Case> registry;
  return registry;
}

unsigned &failuresInCase() {
  static unsigned count = 0;
  return count;
}

} // namespace

zkctest::Failure::Failure(const char *file, int line, const char *what)
    : file(file), line(line), what(what) {}

zkctest::Failure::~Failure() {
  ++failuresInCase();
  llvm::errs() << "  " << file << ":" << line << ": " << what;
  if (!context.empty())
    llvm::errs() << " — " << context;
  llvm::errs() << "\n";
}

void zkctest::registerCase(const char *suite, const char *name,
                           void (*body)()) {
  cases().push_back({suite, name, body});
}

int zkctest::runAll() {
  unsigned failed = 0;
  for (const Case &item : cases()) {
    failuresInCase() = 0;
    item.body();
    if (failuresInCase() == 0)
      continue;
    ++failed;
    llvm::errs() << "FAILED: " << item.suite << "." << item.name << "\n";
  }
  llvm::outs() << cases().size() << " cases, " << failed << " failed\n";
  return failed == 0 ? 0 : 1;
}

int main() { return zkctest::runAll(); }
