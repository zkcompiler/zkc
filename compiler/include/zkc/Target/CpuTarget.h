#ifndef ZKC_TARGET_CPU_TARGET_H
#define ZKC_TARGET_CPU_TARGET_H

#include "zkc/Contracts/Bindings.h"
#include <cstddef>

namespace zkc::target {
/// Immutable subtractive view of the compiled CPU installation. Descriptors
/// select known contributions; they never supply contracts, signatures or laws.
/// The default preserves the complete compiled installation.
class CpuTarget {
  unsigned providers = 31;
  explicit CpuTarget(unsigned providers) : providers(providers) {}

public:
  CpuTarget() = default;
  static constexpr size_t descriptorByteLimit = 4096;
  static llvm::Expected<CpuTarget> parse(llvm::StringRef);
  bool includes(llvm::StringRef provider) const;
  /// These checks follow independent Contracts resolution. The type check
  /// visits every physical child, including inactive variant alternatives.
  llvm::Error checkType(const protocol::BoundType &) const;
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
