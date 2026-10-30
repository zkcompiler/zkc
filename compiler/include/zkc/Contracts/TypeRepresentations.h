#ifndef ZKC_CONTRACTS_TYPE_REPRESENTATIONS_H
#define ZKC_CONTRACTS_TYPE_REPRESENTATIONS_H

#include "zkc/Contracts/Bindings.h"

namespace zkc::protocol {
/// A closed realization pattern with typed exact domain/type arguments.
/// Natural ranges describe storage support, not type equality; their argument
/// is the zero natural. No internal type schema is stored as a string.
struct TypeArgumentPattern {
  TypeArgument argument;
  uint64_t maximum = 0;
  uint64_t minimum = 0;
};
struct AppliedTypeRepresentation {
  llvm::StringRef constructor;
  llvm::ArrayRef<TypeArgumentPattern> arguments;
  llvm::StringRef representation;
  bool isDefault;
  /// Exact physical type of the single dense child, including its layout.
  BoundType childType;
};
/// Validate closed patterns and exact child types against the logical schemas,
/// and reject overlapping defaults or named matches.
/// This does not assign implementations or provider ownership to an ABI.
llvm::Error validateAppliedTypeRepresentations(
    llvm::ArrayRef<AppliedTypeRepresentation> representations);
llvm::ArrayRef<AppliedTypeRepresentation> appliedTypeRepresentations();
/// Refuses missing and ambiguous matches. An empty name requests the default.
const AppliedTypeRepresentation *
appliedTypeRepresentation(const BoundType &, llvm::StringRef name = {});
} // namespace zkc::protocol
#endif
