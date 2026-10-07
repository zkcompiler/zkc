#ifndef ZKC_CONTRACTS_NATIVEPOLICY_H
#define ZKC_CONTRACTS_NATIVEPOLICY_H
#include "zkc/Contracts/Bindings.h"
namespace zkc::protocol {
struct NativeTypePolicy {
  bool total, shared, affine, protocolPort, wire;
};
/// Head classification only. Formation, custody, element permissions and
/// concrete wire admission must still be checked on the complete type.
struct NativeTypeConstructorPolicy {
  bool total, shared;
};
std::optional<NativeTypeConstructorPolicy>
    nativeTypeConstructorPolicy(llvm::StringRef);
/// Closed native-local/1 vocabulary. The caller supplies a shared node budget;
/// exhaustion or depth above 64 sets limited and returns no policy.
std::optional<NativeTypePolicy>
nativeTypePolicy(const BoundType &, unsigned &remaining, bool &limited);
std::optional<NativeTypePolicy> nativeTypePolicy(const BoundType &);
} // namespace zkc::protocol
#endif
