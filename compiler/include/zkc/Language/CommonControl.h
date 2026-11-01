#ifndef ZKC_LANGUAGE_COMMONCONTROL_H
#define ZKC_LANGUAGE_COMMONCONTROL_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Language/Project.h"

namespace zkc::language {
/// Coordinates in the source schema, independent of flattened native ports.
/// Alternative/Payload steps always occur as a pair, in declaration order.
struct CommonControlStep {
  enum class Kind { Field, Alternative, Payload } kind;
  unsigned index;
  bool operator==(const CommonControlStep &other) const {
    return kind == other.kind && index == other.index;
  }
};
struct CommonControlComponent {
  unsigned input, role;
  std::vector<CommonControlStep> path;
  bool operator==(const CommonControlComponent &other) const {
    return input == other.input && role == other.role && path == other.path;
  }
};
/// An obligation on actual input admission, never trusted agreement evidence.
/// Components retain immutable root/path associations through helper calls.
struct CommonControlRequirement {
  std::vector<CommonControlComponent> components;
  Type type;
  bool tagOnly = false;
  Span control;
  /// Observe only this collection axis; type remains the container type.
  /// This facet is never combined with tagOnly.
  std::optional<unsigned> extentAxis = {};
};
/// Recompute from the immutable checked body and its complete call closure.
/// Public markings and availability never establish common provenance. Unknown
/// Local/received/service provenance refuses with source.common-provenance.
/// Every derivation, including dormant arms and zero-trip state, debits Limits.
/// Demanded loop observations check both initial and yielded components under
/// grounded induction for that exact invocation, slot, role and observation.
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const CheckedProject &, DeclarationId,
                                const Limits & = {});
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const ClosedEntry &, const Limits & = {});
/// Derive for one retained concrete declaration using this closed call closure.
/// Explicit Limits preserves existing (entry, {}) root calls.
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const ClosedEntry &, DeclarationId,
                                const Limits &);
/// Share a cumulative allowance when deriving several retained declarations.
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const ClosedEntry &, DeclarationId,
                                const Limits &, uint64_t &remaining);
/// Exact handoff to the native original and flat participant data ABI. Native
/// variant paths retain (alternative, payload) pairs. Source association
/// remains available for diagnostics and SDK interface checks.
struct NativeCommonControlComponent {
  unsigned originalInput, participantInput, role;
  std::vector<unsigned> path;
  CommonControlComponent source;
};
struct NativeCommonControlRequirement {
  std::vector<NativeCommonControlComponent> components;
  protocol::BoundType type;
  bool tagOnly;
  Span control;
  /// Observe only this collection axis; type remains the container type.
  /// This facet is never combined with tagOnly.
  std::optional<unsigned> extentAxis = {};
};
/// Derive and flatten the actual source requirements; no caller-provided
/// annotations or requirement manifest is accepted as authority.
llvm::Expected<std::vector<NativeCommonControlRequirement>>
deriveNativeCommonControlRequirements(const ClosedEntry &, const Limits & = {});
/// The same independent source derivation and exact layout handoff for one
/// concrete retained Protocol in this closed declaration environment. This is
/// used to validate helper inventories, not just the selected root's inventory.
/// Explicit Limits keeps existing (entry, {}) calls unambiguous.
llvm::Expected<std::vector<NativeCommonControlRequirement>>
deriveNativeCommonControlRequirements(const ClosedEntry &, DeclarationId,
                                      const Limits &);
} // namespace zkc::language
#endif
