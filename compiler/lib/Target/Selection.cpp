#include "zkc/Target/Selection.h"
#include "zkc/Support/Json.h"
namespace zkc::target {
llvm::Expected<ImplementationChoice>
selectImplementation(protocol::BindingApplication application,
                     std::optional<llvm::StringRef> requested) {
  const bool fixed =
      requested.has_value() || !application.implementation.empty();
  if (requested) {
    if (!application.implementation.empty() &&
        application.implementation != *requested)
      return error("binding-selection-conflict");
    application.implementation = requested->str();
  } else if (application.implementation.empty()) {
    auto selected = protocol::defaultImplementation(application);
    if (!selected)
      return selected.takeError();
    application.implementation = std::move(*selected);
  }
  auto installed = protocol::resolveBinding(application, true);
  if (!installed)
    return installed.takeError();
  return ImplementationChoice{std::move(application), fixed};
}
} // namespace zkc::target
