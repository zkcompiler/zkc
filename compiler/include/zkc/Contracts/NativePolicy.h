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
/// Immutable logical relation inputs. The caller supplies an admitted type;
/// this rule excludes physical representations, keys, services and custody.
/// Recursive work shares the supplied native type budget.
enum class RelationData { Supported, Unsupported, Limit };
RelationData logicalRelationData(const BoundType &, TypeParseBudget &,
                                 unsigned depth = 0);
} // namespace zkc::protocol
#endif
