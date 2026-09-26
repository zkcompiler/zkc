#ifndef ZKC_TARGET_SELECTION_H
#define ZKC_TARGET_SELECTION_H
#include "zkc/Contracts/Bindings.h"
#include <optional>
namespace zkc::target {
struct ImplementationChoice {
  protocol::BindingApplication application;
  bool fixed;
};
/// Honor explicit choices, otherwise use the installed canonical fallback.
/// Contracts establishes legality; policy cannot change source admission.
llvm::Expected<ImplementationChoice>
selectImplementation(protocol::BindingApplication,
                     std::optional<llvm::StringRef> requested = {});
} // namespace zkc::target
#endif
