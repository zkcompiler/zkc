#include "CompilationState.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
using namespace mlir;
namespace zkc {
char CompilationError::ID;
Compilation::Compilation(std::unique_ptr<Storage> value)
    : storage(std::move(value)) {}
Compilation::Compilation(Compilation &&) noexcept = default;
Compilation &Compilation::operator=(Compilation &&) noexcept = default;
Compilation::~Compilation() = default;
ModuleOp Compilation::module() const { return *storage->module; }
const LinearContractionStats &Compilation::statistics() const {
  return storage->statistics;
}
namespace detail {
void collectError(const Error &error,
                  std::vector<diagnostics::RefusalInfo> &refusals,
                  std::vector<DiagnosticLocation> &locations,
                  std::vector<InvocationPrecondition> &preconditions) {
  visitErrors(error, [&](const ErrorInfoBase &info) {
    if (info.isA<Refusal>()) {
      const auto &refusal = static_cast<const Refusal &>(info);
      refusals.push_back({refusal.code, refusal.detail});
    } else if (info.isA<CompilationError>()) {
      const auto &compilation = static_cast<const CompilationError &>(info);
      llvm::append_range(refusals, compilation.refusals);
      llvm::append_range(locations, compilation.locations);
      llvm::append_range(preconditions, compilation.invocationPreconditions);
    } else if (info.isA<DialectRegistrationError>()) {
      preconditions.push_back(
          static_cast<const DialectRegistrationError &>(info).precondition);
    }
  });
}
Error compilationError(Error error) {
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::vector<InvocationPrecondition> preconditions;
  collectError(error, refusals, locations, preconditions);
  return make_error<CompilationError>(toString(std::move(error)),
                                      std::move(refusals), std::move(locations),
                                      std::move(preconditions));
}
} // namespace detail
} // namespace zkc
