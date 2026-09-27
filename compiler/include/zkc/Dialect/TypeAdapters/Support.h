#ifndef ZKC_DIALECT_TYPE_ADAPTERS_SUPPORT_H
#define ZKC_DIALECT_TYPE_ADAPTERS_SUPPORT_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/TypeSupport.h"
#include "zkc/Dialect/TypeAdapters.h"
#include <utility>

namespace zkc::protocol::type_adapters {
// Translation never initializes the caller's context. A loaded namespace is
// insufficient if it has not registered the expected native type.
template <typename T, typename... Args>
mlir::Type loadedType(mlir::MLIRContext *context, Args &&...args) {
  if (!context || !context->getLoadedDialect(T::dialectName))
    return {};
  auto registered = mlir::AbstractType::lookup(T::name, context);
  if (!registered || registered->get().getTypeID() != T::getTypeID())
    return {};
  return T::get(context, std::forward<Args>(args)...);
}

template <typename T>
mlir::Type decodeDomainType(mlir::MLIRContext *context, const BoundType &type) {
  return loadedType<T>(context, type.identity);
}

template <typename T>
std::optional<BoundType> encodeDomainType(mlir::Type type,
                                          llvm::StringRef constructor) {
  if (auto native = mlir::dyn_cast<T>(type))
    return BoundType{constructor.str(), native.getDomain().str(), {}};
  return std::nullopt;
}

inline mlir::Type vectorType(mlir::Type element) {
  return element ? mlir::RankedTensorType::get({mlir::ShapedType::kDynamic},
                                               element)
                 : mlir::Type{};
}

inline mlir::Type vectorElement(mlir::Type type) {
  auto tensor = mlir::dyn_cast<mlir::RankedTensorType>(type);
  if (!tensor || tensor.getRank() != 1 || !tensor.isDynamicDim(0) ||
      tensor.getEncoding())
    return {};
  return tensor.getElementType();
}

template <typename T>
mlir::Type decodeDomainVector(mlir::MLIRContext *context,
                              const BoundType &type) {
  return vectorType(decodeDomainType<T>(context, type));
}

template <typename T>
std::optional<BoundType> encodeDomainVector(mlir::Type type,
                                            llvm::StringRef constructor) {
  auto element = vectorElement(type);
  return element ? encodeDomainType<T>(element, constructor) : std::nullopt;
}
// Compact single-domain constructors retain their identity slot. Decoding
// ignores the admitted outer representation, which decodeBoundType wraps later.
template <typename T> struct DomainAdapter {
  using Native = T;
  using Parameters = ParameterKinds<ParameterKind::Domain>;
  static mlir::Type decode(mlir::MLIRContext *context, const BoundType &type) {
    if (!type.arguments.empty())
      return {};
    return decodeDomainType<T>(context, type);
  }
  static std::optional<BoundType> encode(mlir::Type type,
                                         llvm::StringRef constructor) {
    return encodeDomainType<T>(type, constructor);
  }
};

// A deliberately small applied helper, with explicit typed getters. Nested
// decode operates on an already admitted subtree; nested encode retains unique
// matching. Only the public boundary parses/admit-checks the complete value.
template <typename T, mlir::Type (T::*Element)() const,
          uint64_t (T::*Length)() const>
struct TypeNatAdapter {
  using Native = T;
  using Parameters = ParameterKinds<ParameterKind::Type, ParameterKind::Nat>;
  static mlir::Type decode(mlir::MLIRContext *context, const BoundType &type) {
    if (!type.identity.empty() || type.arguments.size() != 2 ||
        type.arguments[0].kind != TypeArgument::Kind::Type ||
        !type.arguments[0].type ||
        type.arguments[1].kind != TypeArgument::Kind::Nat)
      return {};
    const auto &element = *type.arguments[0].type;
    auto *adapter = findAdapter(element.kind);
    auto native = adapter ? adapter->decode(context, element) : mlir::Type{};
    return native ? loadedType<T>(context, native, type.arguments[1].natural)
                  : mlir::Type{};
  }
  static std::optional<BoundType> encode(mlir::Type type,
                                         llvm::StringRef constructor) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    auto element = encodeLogicalType((native.*Element)());
    if (!element) {
      llvm::consumeError(element.takeError());
      return std::nullopt;
    }
    return BoundType{constructor.str(),
                     {},
                     {},
                     {TypeArgument::typeArgument(std::move(*element)),
                      TypeArgument::naturalArgument((native.*Length)())}};
  }
};
} // namespace zkc::protocol::type_adapters

#endif
