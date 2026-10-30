#ifndef ZKC_DIALECT_TYPE_ADAPTERS_SUPPORT_H
#define ZKC_DIALECT_TYPE_ADAPTERS_SUPPORT_H

#include "mlir/IR/Builders.h"
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

template <typename T, typename... Args>
using NativeVerification = decltype(T::verify(
    std::declval<llvm::function_ref<mlir::InFlightDiagnostic()>>(),
    std::declval<Args>()...));

template <typename T, typename... Args>
mlir::Type
loadedCheckedType(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                  mlir::MLIRContext *context, Args &&...args) {
  if (!context || !context->getLoadedDialect(T::dialectName))
    return {};
  auto registered = mlir::AbstractType::lookup(T::name, context);
  if (!registered || registered->get().getTypeID() != T::getTypeID())
    return {};
  // TypeDefs without a custom verifier have no generated getChecked overload;
  // instantiating their inherited template would require private storage here.
  // Call the generated public verifier when present, then the ordinary builder.
  if constexpr (llvm::is_detected<NativeVerification, T, Args...>::value)
    if (mlir::failed(T::verify(emit, args...)))
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

// Compact single-domain constructors retain their identity slot. Decoding
// ignores the admitted outer representation, which decodeBoundType wraps later.
template <typename T> struct DomainAdapter {
  // Called only after complete kind/arity/formation checking.
  static mlir::Type
  construct(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
            mlir::MLIRContext *context, llvm::StringRef,
            llvm::ArrayRef<mlir::Attribute> arguments) {
    return loadedCheckedType<T>(
        emit, context, mlir::cast<mlir::StringAttr>(arguments[0]).getValue());
  }

  static std::optional<llvm::SmallVector<mlir::Attribute>>
  arguments(mlir::Type type, llvm::StringRef) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    return llvm::SmallVector<mlir::Attribute>{
        mlir::StringAttr::get(type.getContext(), native.getDomain())};
  }

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
  // Called only after complete kind/arity/formation checking.
  static mlir::Type
  construct(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
            mlir::MLIRContext *context, llvm::StringRef,
            llvm::ArrayRef<mlir::Attribute> arguments) {
    return loadedCheckedType<T>(
        emit, context, mlir::cast<mlir::TypeAttr>(arguments[0]).getValue(),
        mlir::cast<mlir::IntegerAttr>(arguments[1]).getValue().getZExtValue());
  }

  static std::optional<llvm::SmallVector<mlir::Attribute>>
  arguments(mlir::Type type, llvm::StringRef) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    mlir::Builder builder(type.getContext());
    return llvm::SmallVector<mlir::Attribute>{
        mlir::TypeAttr::get((native.*Element)()),
        builder.getIntegerAttr(
            mlir::IntegerType::get(type.getContext(), 64,
                                   mlir::IntegerType::Unsigned),
            (native.*Length)())};
  }

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

template <typename T> struct NullaryAdapter {
  // Called only after complete kind/arity/formation checking.
  static mlir::Type
  construct(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
            mlir::MLIRContext *context, llvm::StringRef,
            llvm::ArrayRef<mlir::Attribute> arguments) {
    (void)arguments;
    return loadedCheckedType<T>(emit, context);
  }

  static std::optional<llvm::SmallVector<mlir::Attribute>>
  arguments(mlir::Type type, llvm::StringRef) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    return llvm::SmallVector<mlir::Attribute>{};
  }

  using Native = T;
  using Parameters = ParameterKinds<>;
  static mlir::Type decode(mlir::MLIRContext *context, const BoundType &type) {
    if (!type.identity.empty() || !type.arguments.empty())
      return {};
    return loadedType<T>(context);
  }
  static std::optional<BoundType> encode(mlir::Type type,
                                         llvm::StringRef constructor) {
    if (!mlir::isa<T>(type))
      return std::nullopt;
    return BoundType{constructor.str(), {}, {}};
  }
};

template <typename T, llvm::StringRef (T::*Domain)() const,
          uint64_t (T::*Length)() const>
struct DomainNatAdapter {
  // Called only after complete kind/arity/formation checking.
  static mlir::Type
  construct(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
            mlir::MLIRContext *context, llvm::StringRef,
            llvm::ArrayRef<mlir::Attribute> arguments) {
    return loadedCheckedType<T>(
        emit, context, mlir::cast<mlir::StringAttr>(arguments[0]).getValue(),
        mlir::cast<mlir::IntegerAttr>(arguments[1]).getValue().getZExtValue());
  }

  static std::optional<llvm::SmallVector<mlir::Attribute>>
  arguments(mlir::Type type, llvm::StringRef) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    mlir::Builder builder(type.getContext());
    return llvm::SmallVector<mlir::Attribute>{
        builder.getStringAttr((native.*Domain)()),
        builder.getIntegerAttr(
            mlir::IntegerType::get(type.getContext(), 64,
                                   mlir::IntegerType::Unsigned),
            (native.*Length)())};
  }

  using Native = T;
  using Parameters = ParameterKinds<ParameterKind::Domain, ParameterKind::Nat>;
  static mlir::Type decode(mlir::MLIRContext *context, const BoundType &type) {
    if (!type.identity.empty() || type.arguments.size() != 2 ||
        type.arguments[0].kind != TypeArgument::Kind::Domain ||
        type.arguments[1].kind != TypeArgument::Kind::Nat)
      return {};
    return loadedType<T>(context, type.arguments[0].domain,
                         type.arguments[1].natural);
  }
  static std::optional<BoundType> encode(mlir::Type type,
                                         llvm::StringRef constructor) {
    auto native = mlir::dyn_cast<T>(type);
    if (!native)
      return std::nullopt;
    return BoundType{constructor.str(),
                     {},
                     {},
                     {TypeArgument::domainArgument((native.*Domain)().str()),
                      TypeArgument::naturalArgument((native.*Length)())}};
  }
};
} // namespace zkc::protocol::type_adapters

#endif
