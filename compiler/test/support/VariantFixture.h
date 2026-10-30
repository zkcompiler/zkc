#ifndef ZKC_TEST_SUPPORT_VARIANT_FIXTURE_H
#define ZKC_TEST_SUPPORT_VARIANT_FIXTURE_H
#include "NativeCases.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Registry.h"
namespace zkc::test {
/// Import a program-format fixture at the neutral boundary, then exercise the
/// production structural type. No legacy MLIR parser is retained.
inline data::VariantType variantType(mlir::MLIRContext *context,
                                     llvm::StringRef spelling) {
  auto descriptor = protocol::decodeVariant(spelling);
  require(bool(descriptor), "invalid variant fixture descriptor");
  auto type = data::importVariantType(context, *descriptor);
  require(bool(type), "invalid structured variant fixture");
  return type;
}
inline std::string variantAssembly(llvm::StringRef spelling) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string result;
  llvm::raw_string_ostream stream(result);
  mlir::Type(variantType(&context, spelling)).print(stream);
  return result;
}
} // namespace zkc::test
#endif
