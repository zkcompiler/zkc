#include "zkc/Dialect/Protocol/Services.h"
#include "zkc/Dialect/TypeFormation.h"
using namespace mlir;
namespace zkc::protocol_ir {
namespace {
bool matches(Type type, const protocol::BoundType &expected) {
  // Installed service ports are logical atoms. A future structured service
  // signature must define its associations explicitly, not accept a spelling.
  if (!type || !expected.representation.empty() || expected.physicalChildren ||
      !expected.arguments.empty())
    return false;
  if (failed(verifyLogicalType(
          [&] {
            auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
            diagnostic.abandon();
            return diagnostic;
          },
          type)))
    return false;
  auto interface = dyn_cast<CatalogTypeInterface>(type);
  auto application =
      interface ? interface.getCatalogApplication() : std::nullopt;
  if (!application || application->constructor != expected.kind)
    return false;
  if (expected.identity.empty())
    return application->arguments.empty();
  return application->arguments.size() == 1 &&
         application->arguments.front() ==
             StringAttr::get(type.getContext(), expected.identity);
}
} // namespace
bool matchesServiceSignature(TypeRange inputs, TypeRange outputs,
                             const protocol::ServiceMethod &method) {
  return inputs.size() == method.inputs.size() && outputs.size() == 1 &&
         matches(outputs.front(), method.output) &&
         llvm::all_of(llvm::zip(inputs, method.inputs), [](const auto &pair) {
           return matches(std::get<0>(pair), std::get<1>(pair));
         });
}
} // namespace zkc::protocol_ir
