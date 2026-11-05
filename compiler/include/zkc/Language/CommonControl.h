#ifndef ZKC_LANGUAGE_COMMONCONTROL_H
#define ZKC_LANGUAGE_COMMONCONTROL_H

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
/// A closed concrete Protocol: a Protocol with a body and no open static,
/// scoped or domain parameters, which is not abstract. Closed derivation, the
/// interface writer and the interface comparison select by this one predicate.
bool isClosedConcreteProtocol(const Declaration &);
/// Recompute from the immutable checked body and its complete call closure.
/// Public markings and availability never establish common provenance. Actual
/// completed sends forward the sender's immutable subject on normal paths;
/// distinct opaque Local/service subjects refuse with source.common-provenance.
/// Every derivation, including dormant arms and zero-trip state, debits Limits.
/// Demanded loop observations check both initial and yielded components under
/// grounded induction for that exact invocation, slot, role and observation.
llvm::Expected<std::vector<CommonControlRequirement>>
deriveCommonControlRequirements(const CheckedProject &, DeclarationId,
                                const Limits & = {});
} // namespace zkc::language
#endif
