#include "CompilationState.h"
using namespace llvm;
using namespace mlir;
namespace zkc {
Compilation::Compilation(std::unique_ptr<Storage> value)
    : storage(std::move(value)) {}
Compilation::Compilation(Compilation &&) noexcept = default;
Compilation &Compilation::operator=(Compilation &&) noexcept = default;
Compilation::~Compilation() = default;
ModuleOp Compilation::module() const { return *storage->module; }
std::optional<OracleRealizationSnapshot>
Compilation::oracleRealizationSnapshot() const {
  if (!storage || !storage->realization)
    return std::nullopt;
  const auto &edge = *storage->realization;
  return OracleRealizationSnapshot{edge.preparedSnapshot(),
                                   edge.candidateSnapshot(),
                                   edge.realizationRecord().str()};
}
const LinearContractionStats &Compilation::statistics() const {
  return storage->statistics;
}
} // namespace zkc
