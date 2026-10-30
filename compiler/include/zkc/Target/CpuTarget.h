#ifndef ZKC_TARGET_CPU_TARGET_H
#define ZKC_TARGET_CPU_TARGET_H

#include "zkc/Contracts/Bindings.h"
#include <cstddef>

namespace mlir {
class Type;
}
namespace zkc {
struct NativeBinding;
struct NativeBindingApplication;
} // namespace zkc
namespace zkc::target {
/// Immutable subtractive view of the compiled CPU installation. Descriptors
/// select known contributions; they never supply contracts, signatures or laws.
/// The default preserves the complete compiled installation.
class CpuTarget {
  unsigned providers = 31;
  explicit CpuTarget(unsigned providers) : providers(providers) {}
  llvm::Error
  checkImplementation(llvm::StringRef contract, llvm::StringRef implementation,
                      llvm::ArrayRef<llvm::StringRef> identities) const;
  llvm::Error checkCodec(llvm::StringRef identity) const;

public:
  bool operator==(const CpuTarget &other) const {
    return providers == other.providers;
  }
  CpuTarget() = default;
  static constexpr size_t descriptorByteLimit = 4096;
  static llvm::Expected<CpuTarget> parse(llvm::StringRef);
  /// Canonical descriptor for textual pipeline reproduction of typed intent.
  std::string descriptor() const;
  bool includes(llvm::StringRef provider) const;
  /// These checks follow independent Contracts resolution. The type check
  /// visits every physical child, including inactive variant alternatives.
  llvm::Error checkType(const protocol::BoundType &) const;
  /// Native formation is checked independently before inspecting installed
  /// storage owners. Every represented child is visited, including dormant
  /// arms.
  llvm::Error checkType(mlir::Type) const;
  llvm::Error checkBinding(const zkc::NativeBinding &) const;
  llvm::Error
  checkNativeApplication(const zkc::NativeBindingApplication &) const;
  llvm::Error
  checkNativeImplementation(const zkc::NativeBindingApplication &) const;
  llvm::Error checkBinding(const protocol::BindingApplication &,
                           const protocol::BoundOperation &) const;
  /// Family selection can precede physical specialization. Check its owner
  /// now; exact physical ports must be checked again after specialization.
  llvm::Error checkImplementation(const protocol::BindingApplication &) const;
  /// A declared field service always requires its draw reply layout, even if
  /// unused or used only for index sampling.
  llvm::Error checkService(llvm::StringRef contract) const;
};
} // namespace zkc::target
#endif
