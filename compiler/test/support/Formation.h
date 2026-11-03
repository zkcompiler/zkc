#ifndef ZKC_TEST_SUPPORT_FORMATION_H
#define ZKC_TEST_SUPPORT_FORMATION_H

#include "NativeCases.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include <utility>

namespace zkc::test {
/// Test the actual storage formation boundary without constructing a rejected
/// type or attribute. Downstream readers need separately formed candidates.
/// Pass the generated builder's exact parameter types: implicit conversions can
/// select MLIR's generic getChecked template instead of the generated overload.
template <typename Storage, typename... Args>
void refusesFormation(mlir::MLIRContext *context, llvm::StringRef code,
                      Args &&...args) {
  llvm::SmallVector<std::string> codes;
  mlir::ScopedDiagnosticHandler handler(context, [&](mlir::Diagnostic &value) {
    for (const auto &refusal : diagnostics::refusals(value))
      codes.push_back(refusal.code);
    return mlir::success();
  });
  auto emit = [&] { return mlir::emitError(mlir::UnknownLoc::get(context)); };
  require(!Storage::getChecked(emit, context, std::forward<Args>(args)...),
          "malformed storage acquired a native value: " + code);
  require(llvm::is_contained(codes, code),
          "storage formation lost its refusal identity: " + code);
}
} // namespace zkc::test
#endif
