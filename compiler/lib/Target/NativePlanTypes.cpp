#include "NativePlanTypes.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::target {
namespace {
auto diagnostic(MLIRContext *context) {
  return [context] {
    auto value = emitError(UnknownLoc::get(context));
    value.abandon();
    return value;
  };
}

} // namespace
Error checkPhysicalType(Type type) {
  if (!type || !isa<runtime::RepresentedType>(type))
    return error("binding-logical-type-at-physical-stage");
  if (failed(verifyValueType(diagnostic(type.getContext()), type)))
    return error("binding-representation");
  return Error::success();
}
Expected<Type> formPhysicalType(Type logical, StringRef representation,
                                ArrayRef<Type> children) {
  if (!logical ||
      !logical.getContext()->getLoadedDialect<runtime::RuntimeDialect>())
    return error("binding-representation");
  auto type = runtime::RepresentedType::getChecked(
      diagnostic(logical.getContext()), logical.getContext(), logical,
      representation, children);
  if (!type)
    return error("binding-representation");
  return Type(type);
}
Expected<Type> defaultPlanType(Type logical) {
  if (!logical)
    return error("binding-type");
  // Missing defaults are ordinary speculative query failures: exact aggregate
  // equations can still select a complete layout. Keep their diagnostics in
  // the returned error so a successful later selection emits no false error.
  std::string detail;
  zkc::diagnostics::ScopedThreadDiagnosticHandler capture(
      logical.getContext(), [&](Diagnostic &value) {
        detail += value.str();
        return success();
      });
  auto emit = [&] { return emitError(UnknownLoc::get(logical.getContext())); };
  auto type = defaultPhysicalType(emit, logical);
  if (!type)
    return error("binding-representation", detail);
  return type;
}
StringRef planTypeConstructor(Type type) {
  auto logical = logicalValueType(type);
  if (isa_and_nonnull<data::VariantType>(logical))
    return "variant";
  auto interface = dyn_cast_or_null<CatalogTypeInterface>(logical);
  auto app = interface ? interface.getCatalogApplication() : std::nullopt;
  return app ? app->constructor : StringRef{};
}
Expected<SmallVector<Type>> planLogicalChildren(Type type) {
  if (!type || failed(verifyValueType(diagnostic(type.getContext()), type)))
    return error("binding-type");
  auto logical = logicalValueType(type);
  SmallVector<Type> children;
  if (auto variant = dyn_cast_or_null<data::VariantType>(logical)) {
    for (auto arm : variant.getAlternatives())
      append_range(children, arm.getPayload());
  } else {
    auto interface = dyn_cast_or_null<CatalogTypeInterface>(logical);
    auto app = interface ? interface.getCatalogApplication() : std::nullopt;
    if (!app)
      return error("binding-type");
    if (app->constructor == "sequence" || app->constructor == "fixed_vector")
      children.push_back(cast<TypeAttr>(app->arguments[0]).getValue());
    else if (app->constructor == "field_array") {
      auto field = constructLogicalType(diagnostic(logical.getContext()),
                                        logical.getContext(),
                                        {"field", {app->arguments[0]}});
      if (!field)
        return error("binding-type");
      children.push_back(field);
    }
  }
  return children;
}
} // namespace zkc::target
