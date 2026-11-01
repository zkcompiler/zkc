#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
std::optional<llvm::SmallVector<Attribute>> booleanArguments(Type type,
                                                             llvm::StringRef) {
  if (!type.isSignlessInteger(1))
    return std::nullopt;
  return llvm::SmallVector<Attribute>{};
}
std::optional<llvm::SmallVector<Attribute>> indexArguments(Type type,
                                                           llvm::StringRef) {
  if (!type.isUnsignedInteger(64))
    return std::nullopt;
  return llvm::SmallVector<Attribute>{};
}
Type constructBoolean(llvm::function_ref<InFlightDiagnostic()>,
                      MLIRContext *context, llvm::StringRef,
                      llvm::ArrayRef<Attribute>) {
  return IntegerType::get(context, 1);
}
Type constructIndex(llvm::function_ref<InFlightDiagnostic()>,
                    MLIRContext *context, llvm::StringRef,
                    llvm::ArrayRef<Attribute>) {
  return IntegerType::get(context, 64, IntegerType::Unsigned);
}
using Shake128Adapter = NullaryAdapter<zkc::crypto::Shake128StateType>;
Type decodeBoolean(MLIRContext *context, const BoundType &) {
  return IntegerType::get(context, 1);
}
std::optional<BoundType> encodeBoolean(Type type, llvm::StringRef constructor) {
  if (type.isSignlessInteger(1))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
Type decodeIndex(MLIRContext *context, const BoundType &) {
  return IntegerType::get(context, 64, IntegerType::Unsigned);
}
std::optional<BoundType> encodeIndex(Type type, llvm::StringRef constructor) {
  if (type.isUnsignedInteger(64))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Core.inc"
