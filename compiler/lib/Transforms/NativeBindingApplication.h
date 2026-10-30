#ifndef ZKC_TRANSFORMS_NATIVEBINDINGAPPLICATION_H
#define ZKC_TRANSFORMS_NATIVEBINDINGAPPLICATION_H

#include "zkc/Dialect/Bindings.h"
#include "llvm/ADT/STLExtras.h"
#include <string>

namespace zkc {
/// Compare independently derived expectations with the actual declaration,
/// including its checked ABI and executable installation. No producer is used.
inline bool matchesNativeBinding(runtime::BindingOp binding,
                                 const NativeBindingApplication &expected) {
  if (!binding || binding.getContract() != expected.contract ||
      binding.getImplementation() != expected.implementation ||
      !llvm::equal(binding.getArguments(), expected.arguments))
    return false;
  auto silent = [&] {
    auto diagnostic = binding.emitOpError();
    diagnostic.abandon();
    return diagnostic;
  };
  return mlir::succeeded(readNativeBinding(silent, binding, false));
}
} // namespace zkc
#endif
