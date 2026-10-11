#ifndef ZKC_CONTRACTS_MATHEMATICAL_H
#define ZKC_CONTRACTS_MATHEMATICAL_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
/// Logical identities shared by source checking and admitted IR interfaces.
/// This vocabulary does not select an operation implementation or a backend.
#define ZKC_MATHEMATICAL_IDENTITIES
#include "zkc/Contracts/Mathematical.inc"
#undef ZKC_MATHEMATICAL_IDENTITIES
llvm::StringRef mathematicalIdentityName(MathematicalIdentity);
/// Library authoring hooks for total mathematics. Field operations have a
/// field root followed by naturals; Boolean operations have no static roots.
/// Domain points are canonical field literals, independently checked by IR.
struct MathematicalIntrinsic {
  enum class Domain { Boolean, Index, Collection, Field, Group };
  llvm::StringRef name;
  MathematicalIdentity identity;
  Domain domain;
  unsigned naturals = 0;
  bool domainPoints = false;
  /// Scalar primitives also admit direct ordered evaluation of this identity.
  bool scalar = false;
};
llvm::ArrayRef<MathematicalIntrinsic> mathematicalIntrinsics();
const MathematicalIntrinsic *mathematicalIntrinsic(llvm::StringRef);
} // namespace zkc

#endif
