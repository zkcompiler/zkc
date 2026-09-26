#ifndef ZKC_FRONTEND_INTERNAL_WORK_H
#define ZKC_FRONTEND_INTERNAL_WORK_H

#include "zkc/Frontend/Work.h"
#include "zkc/Support/Refusal.h"

namespace zkc::frontend::work {
inline llvm::StringRef name(WorkAccount account) {
  switch (account) {
  case WorkAccount::AuthoredStatic:
    return "authored-static";
  case WorkAccount::LibraryFormation:
    return "library-formation";
  case WorkAccount::GeneratedSource:
    return "generated-source";
  case WorkAccount::Output:
    return "output";
  }
  llvm_unreachable("unknown compiler work account");
}
inline llvm::Error exhausted(WorkAccount account) {
  return zkc::error(account == WorkAccount::AuthoredStatic ||
                            account == WorkAccount::Output
                        ? "source-staging-limit"
                        : "library-source-limit",
                    "compiler work budget exhausted: " + name(account));
}
inline llvm::Error charge(WorkBudget &budget, WorkAccount account,
                          uint64_t amount = 1) {
  return budget.charge(account, amount) ? llvm::Error::success()
                                        : exhausted(account);
}
} // namespace zkc::frontend::work
#endif
