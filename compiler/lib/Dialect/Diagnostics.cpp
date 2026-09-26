#include "zkc/Dialect/Diagnostics.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "zkc/Support/Refusal.h"

namespace zkc::diagnostics {
namespace {
constexpr llvm::StringLiteral metadataKey = "zkc.refusal";

void attach(mlir::InFlightDiagnostic &diagnostic, llvm::StringRef code,
            llvm::StringRef detail) {
  auto *value = diagnostic.getUnderlyingDiagnostic();
  if (!value)
    return;
  auto *context = value->getLocation().getContext();
  // MLIR's string diagnostic arguments borrow memory. Attributes instead own
  // their strings in the diagnostic's context, including after source teardown.
  auto data =
      mlir::ArrayAttr::get(context, {mlir::StringAttr::get(context, code),
                                     mlir::StringAttr::get(context, detail)});
  value->getMetadata().emplace_back(mlir::DictionaryAttr::get(
      context, {mlir::NamedAttribute(metadataKey, data)}));
}
} // namespace

mlir::InFlightDiagnostic emit(mlir::InFlightDiagnostic diagnostic,
                              llvm::StringRef code, const llvm::Twine &detail) {
  return emit(std::move(diagnostic), zkc::error(code, detail));
}

mlir::InFlightDiagnostic emit(mlir::InFlightDiagnostic diagnostic,
                              llvm::Error error) {
  llvm::visitErrors(error, [&](const llvm::ErrorInfoBase &info) {
    if (info.isA<zkc::Refusal>()) {
      const auto &refusal = static_cast<const zkc::Refusal &>(info);
      attach(diagnostic, refusal.code, refusal.detail);
    }
  });
  // Consume errors even when the caller has disabled the diagnostic.
  auto text = llvm::toString(std::move(error));
  if (diagnostic.getUnderlyingDiagnostic())
    diagnostic << text;
  return diagnostic;
}

std::vector<RefusalInfo> refusals(mlir::Diagnostic &diagnostic) {
  std::vector<RefusalInfo> result;
  for (const auto &item : diagnostic.getMetadata()) {
    if (item.getKind() !=
        mlir::DiagnosticArgument::DiagnosticArgumentKind::Attribute)
      continue;
    auto dictionary =
        llvm::dyn_cast<mlir::DictionaryAttr>(item.getAsAttribute());
    if (!dictionary)
      continue;
    auto data = dictionary.getAs<mlir::ArrayAttr>(metadataKey);
    if (!data || data.size() != 2)
      continue;
    auto code = llvm::dyn_cast<mlir::StringAttr>(data[0]);
    auto detail = llvm::dyn_cast<mlir::StringAttr>(data[1]);
    if (code && detail)
      result.push_back({code.getValue().str(), detail.getValue().str()});
  }
  return result;
}
} // namespace zkc::diagnostics
