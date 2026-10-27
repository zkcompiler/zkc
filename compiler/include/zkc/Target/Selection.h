#ifndef ZKC_TARGET_SELECTION_H
#define ZKC_TARGET_SELECTION_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Target/CpuTarget.h"
#include <optional>
namespace zkc::target {
/// Explicit executable ABI choice, scoped to an actual retained function port.
/// It never inserts an entry conversion or specializes source helper calls.
struct FunctionPortSelection {
  std::string function;
  bool output = false;
  unsigned port = 0;
  /// Complete canonical physical type, including every aggregate child.
  std::string physicalType = {};
};
/// Select a semantic instruction result in the retained executable subject.
/// The function and site identify its actual outlined owner and qualified site;
/// administrative CFG/scope operations carrying that site are not data results.
struct ValueLayoutSelection {
  std::string function, site;
  unsigned result = 0;
  std::string physicalType;
};
struct ImplementationChoice {
  protocol::BindingApplication application;
  bool fixed;
};
/// Honor explicit choices, otherwise use the installed canonical fallback.
/// Contracts establishes legality; policy cannot change source admission.
llvm::Expected<ImplementationChoice>
selectImplementation(protocol::BindingApplication,
                     std::optional<llvm::StringRef> requested = {},
                     const CpuTarget &cpuTarget = {});
} // namespace zkc::target
#endif
