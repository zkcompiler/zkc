#ifndef ZKC_MATHEMATICAL_DIAGNOSTIC_H
#define ZKC_MATHEMATICAL_DIAGNOSTIC_H
#include "zkc/Support/Refusal.h"
#include <cstdint>
#include <vector>

namespace zkc::mathematical {
/// Coordinates in the actual raw term. They carry diagnostic provenance only.
struct AdmissionCoordinate {
  enum Kind { Definition, Step, Node, Terminal } kind;
  uint32_t index;
};
class AdmissionRefusal : public llvm::ErrorInfo<AdmissionRefusal, Refusal> {
public:
  static char ID;
  std::vector<AdmissionCoordinate> path;
  AdmissionRefusal(const Refusal &refusal, AdmissionCoordinate outer)
      : llvm::ErrorInfo<AdmissionRefusal, Refusal>(refusal.code,
                                                   refusal.detail) {
    path.push_back(outer);
    if (refusal.isA(AdmissionRefusal::classID())) {
      const auto &inner = static_cast<const AdmissionRefusal &>(refusal).path;
      path.insert(path.end(), inner.begin(), inner.end());
    }
  }
};
inline llvm::Error atCoordinate(llvm::Error failure,
                                AdmissionCoordinate coordinate) {
  return llvm::handleErrors(
      std::move(failure), [coordinate](const Refusal &refusal) -> llvm::Error {
        return llvm::make_error<AdmissionRefusal>(refusal, coordinate);
      });
}
} // namespace zkc::mathematical
#endif
