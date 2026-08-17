//===- ZkcTest.cpp - The harness's registry and runner --------------------===//

#include "ZkcTest.h"

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
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

std::vector<std::string> &contexts() {
  static std::vector<std::string> stack;
  return stack;
}

} // namespace

zkctest::Failure::Failure(const char *file, int line, const char *what)
    : file(file), line(line), what(what) {}

zkctest::Failure::~Failure() {
  ++failuresInCase();
  llvm::errs() << "  " << file << ":" << line << ": " << what;
  for (const std::string &label : contexts())
    llvm::errs() << " [" << label << "]";
  if (!context.empty())
    llvm::errs() << " — " << context;
  llvm::errs() << "\n";
}

void zkctest::pushContext(std::string label) {
  contexts().push_back(std::move(label));
}

void zkctest::popContext() {
  if (!contexts().empty())
    contexts().pop_back();
}

zkctest::Outcome zkctest::outcomeOf(llvm::Error error) {
  if (!error)
    return {true, {}};
  return {false, llvm::toString(std::move(error))};
}

void zkctest::registerCase(const char *suite, const char *name,
                           void (*body)()) {
  cases().push_back({suite, name, body});
}

int zkctest::runAll(int argc, char **argv) {
  // A filter is what lets one case be run under a debugger; without it
  // the only way to isolate a failure is to edit the file.
  std::vector<llvm::StringRef> filters;
  for (int index = 1; index < argc; ++index)
    filters.push_back(argv[index]);

  unsigned failed = 0;
  unsigned ran = 0;
  for (const Case &item : cases()) {
    std::string label = std::string(item.suite) + "." + item.name;
    if (!filters.empty() &&
        llvm::none_of(filters, [&](llvm::StringRef filter) {
          return llvm::StringRef(label).contains(filter);
        }))
      continue;

    // Names the case in the crash report, so a case that does not reach
    // its own failure report still says which one it was.
    llvm::PrettyStackTraceString frame(label.c_str());
    contexts().clear();
    failuresInCase() = 0;
    ++ran;
    item.body();
    if (failuresInCase() == 0)
      continue;
    ++failed;
    llvm::errs() << "FAILED: " << label << "\n";
  }
  llvm::outs() << ran << " cases, " << failed << " failed\n";
  return failed == 0 ? 0 : 1;
}

int main(int argc, char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram program(argc, argv);
  return zkctest::runAll(argc, argv);
}
