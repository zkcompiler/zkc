#include "zkc/Dialect/TypeFormation.h"
#include "Data/IR/Structure.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Interfaces/CatalogType.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
namespace zkc {
namespace {
// Installation patterns are immutable typed data. Match them against native
// catalog observations without serializing the caller or reconstructing its
// carrier. The installed dense patterns use catalog applications; nominal
// variants retain their separate structural layout rule below.
bool matchesLogicalPattern(Type type, const protocol::BoundType &pattern,
                           unsigned depth = 0) {
  if (!type || depth >= 64)
    return false;
  auto interface = dyn_cast<CatalogTypeInterface>(type);
  auto application =
      interface ? interface.getCatalogApplication() : std::nullopt;
  if (!application || application->constructor != pattern.kind)
    return false;
  if (pattern.arguments.empty()) {
    if (pattern.identity.empty())
      return application->arguments.empty();
    return application->arguments.size() == 1 &&
           application->arguments[0] ==
               StringAttr::get(type.getContext(), pattern.identity);
  }
  if (!pattern.identity.empty() ||
      application->arguments.size() != pattern.arguments.size())
    return false;
  for (const auto &[native, expected] :
       llvm::zip(application->arguments, pattern.arguments)) {
    switch (expected.kind) {
    case protocol::TypeArgument::Kind::Domain: {
      auto identity = dyn_cast<StringAttr>(native);
      if (!identity || identity.getValue() != expected.domain)
        return false;
      break;
    }
    case protocol::TypeArgument::Kind::Type: {
      auto nested = dyn_cast<TypeAttr>(native);
      if (!nested || !expected.type ||
          !matchesLogicalPattern(nested.getValue(), *expected.type, depth + 1))
        return false;
      break;
    }
    case protocol::TypeArgument::Kind::Nat: {
      auto number = dyn_cast<IntegerAttr>(native);
      if (!number || !number.getType().isUnsignedInteger(64) ||
          number.getValue().getZExtValue() != expected.natural)
        return false;
      break;
    }
    }
  }
  return true;
}
bool matchesPhysicalPattern(Type type, const protocol::BoundType &pattern,
                            unsigned depth = 0) {
  auto represented = dyn_cast<runtime::RepresentedType>(type);
  if (!represented || depth >= 64 ||
      represented.getRepresentation() != pattern.representation ||
      !matchesLogicalPattern(represented.getLogical(), pattern))
    return false;
  auto children = represented.getChildren();
  if (!pattern.physicalChildren)
    return children.empty();
  if (children.size() != pattern.physicalChildren->size())
    return false;
  return llvm::all_of(llvm::zip(children, *pattern.physicalChildren),
                      [&](const auto &pair) {
                        return matchesPhysicalPattern(
                            std::get<0>(pair), std::get<1>(pair), depth + 1);
                      });
}
const protocol::AppliedTypeRepresentation *
representationFor(const CatalogTypeApplication &application, StringRef name) {
  const protocol::AppliedTypeRepresentation *selected = nullptr;
  for (const auto &entry : protocol::appliedTypeRepresentations()) {
    if (entry.constructor != application.constructor ||
        entry.representation != name ||
        entry.arguments.size() != application.arguments.size())
      continue;
    bool matches = llvm::all_of(
        llvm::zip(application.arguments, entry.arguments),
        [](const auto &pair) {
          auto [value, pattern] = pair;
          switch (pattern.argument.kind) {
          case protocol::TypeArgument::Kind::Domain: {
            auto identity = dyn_cast<StringAttr>(value);
            return identity && identity.getValue() == pattern.argument.domain;
          }
          case protocol::TypeArgument::Kind::Type: {
            auto type = dyn_cast<TypeAttr>(value);
            return type && pattern.argument.type &&
                   matchesLogicalPattern(type.getValue(),
                                         *pattern.argument.type);
          }
          case protocol::TypeArgument::Kind::Nat: {
            auto natural = dyn_cast<IntegerAttr>(value);
            return natural && natural.getType().isUnsignedInteger(64) &&
                   pattern.minimum <= natural.getValue().getZExtValue() &&
                   natural.getValue().getZExtValue() <= pattern.maximum;
          }
          }
          return false;
        });
    if (!matches)
      continue;
    if (selected)
      return nullptr;
    selected = &entry;
  }
  return selected;
}
struct Formation {
  llvm::function_ref<InFlightDiagnostic()> emit;
  unsigned remaining = 200000;

  LogicalResult refuse(StringRef reason) { return emit() << reason; }
  LogicalResult inspect(Type type, unsigned depth,
                        LogicalTypePermissions &permissions) {
    if (!type || depth >= 64 || !remaining--)
      return refuse("missing type or excessive expanded logical structure");
    auto child = [&](Type type) {
      LogicalTypePermissions nested;
      if (failed(inspect(type, depth + 1, nested)))
        return failure();
      permissions.copy &= nested.copy;
      permissions.drop &= nested.drop;
      return success();
    };
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      auto identity = variant.getIdentity();
      if (!identity ||
          failed(data::IdentityAttr::verify(emit, identity.getTerm())))
        return refuse("invalid nominal variant identity");
      auto alternatives = variant.getAlternatives();
      if (alternatives.empty() || alternatives.size() > 512)
        return refuse("invalid variant alternative count");
      llvm::SmallDenseSet<StringAttr, 8> labels;
      for (auto arm : alternatives) {
        if (!arm ||
            failed(data::AlternativeAttr::verify(emit, arm.getLabel(),
                                                 arm.getPayload())) ||
            !labels.insert(arm.getLabel()).second)
          return refuse("invalid or duplicate variant alternative");
        for (auto payload : arm.getPayload())
          if (failed(child(payload)))
            return failure();
      }
      return success();
    }
    auto interface = dyn_cast<CatalogTypeInterface>(type);
    auto application =
        interface ? interface.getCatalogApplication() : std::nullopt;
    if (!application)
      return refuse("type has no unique catalog application");
    return inspectApplication(*application, type.getContext(), depth,
                              permissions);
  }
  LogicalResult represented(Type logical, StringRef representation,
                            ArrayRef<Type> children, unsigned depth) {
    LogicalTypePermissions permissions;
    if (failed(inspect(logical, depth, permissions)))
      return failure();
    SmallVector<Type> expected;
    std::optional<CatalogTypeApplication> application;
    StringRef constructor;
    if (auto variant = dyn_cast<data::VariantType>(logical)) {
      constructor = "variant";
      for (auto arm : variant.getAlternatives())
        llvm::append_range(expected, arm.getPayload());
    } else {
      application = cast<CatalogTypeInterface>(logical).getCatalogApplication();
      constructor = application->constructor;
      if (constructor == "sequence" || constructor == "fixed_vector")
        expected.push_back(
            cast<TypeAttr>(application->arguments[0]).getValue());
      else if (constructor == "field_array")
        expected.push_back(algebra::FieldType::get(
            logical.getContext(),
            cast<StringAttr>(application->arguments[0]).getValue()));
    }
    if (children.size() != expected.size())
      return refuse(
          "representation child count differs from its logical structure");
    for (auto [child, schema] : llvm::zip(children, expected)) {
      auto physical = dyn_cast<runtime::RepresentedType>(child);
      if (!physical || physical.getLogical() != schema)
        return refuse("representation child has a different logical type");
      if (failed(represented(physical.getLogical(),
                             physical.getRepresentation(),
                             physical.getChildren(), depth + 1)))
        return failure();
    }
    if (constructor == "sequence" || constructor == "variant" ||
        constructor == "resource_unit") {
      auto required = constructor == "sequence"  ? "logical.sequence/0"
                      : constructor == "variant" ? "logical.variant/0"
                                                 : "logical.resource_unit/0";
      return representation == required
                 ? success()
                 : refuse("unknown structural representation");
    }
    if (constructor == "field_array" || constructor == "fixed_vector") {
      auto *descriptor = representationFor(*application, representation);
      return descriptor && matchesPhysicalPattern(children.front(),
                                                  descriptor->childType)
                 ? success()
                 : refuse("dense representation or exact child layout differs");
    }
    StringRef identity;
    if (!application->arguments.empty())
      identity = cast<StringAttr>(application->arguments.front()).getValue();
    return protocol::installedDomains().representation(constructor, identity,
                                                       representation)
               ? success()
               : refuse("representation is not declared for this logical "
                        "instance");
  }
  LogicalResult inspectApplication(const CatalogTypeApplication &application,
                                   MLIRContext *context, unsigned depth,
                                   LogicalTypePermissions &permissions) {
    auto child = [&](Type type) {
      LogicalTypePermissions nested;
      if (failed(inspect(type, depth + 1, nested)))
        return failure();
      permissions.copy &= nested.copy;
      permissions.drop &= nested.drop;
      return success();
    };
    auto *declaration = protocol::typeDeclaration(application.constructor);
    auto *rules = protocol::typePermissions(application.constructor);
    if (!declaration || !rules ||
        application.arguments.size() != declaration->parameters.size())
      return refuse(
          "catalog application has an unknown constructor or wrong arity");
    permissions = {rules->copy, rules->drop};
    for (auto [argument, parameter] :
         llvm::zip(application.arguments, declaration->parameters)) {
      if (!argument || argument.getContext() != context)
        return refuse("missing or foreign-context static argument");
      switch (parameter.kind) {
      case protocol::StaticKind::Domain: {
        auto identity = dyn_cast<StringAttr>(argument);
        if (!identity ||
            (parameter.sort == "Slot"
                 ? !protocol::resourceUnitDomain(identity.getValue())
                 : protocol::installedDomains().identitySort(
                       identity.getValue()) != parameter.sort))
          return refuse("static identity has the wrong catalog sort");
        break;
      }
      case protocol::StaticKind::Type: {
        auto nested = dyn_cast<TypeAttr>(argument);
        if (!nested || failed(child(nested.getValue())))
          return refuse("static argument is not a formed logical type");
        break;
      }
      case protocol::StaticKind::Nat: {
        auto value = dyn_cast<IntegerAttr>(argument);
        if (!value || !value.getType().isUnsignedInteger(64) ||
            value.getValue().getZExtValue() > 1048576)
          return refuse(
              "static natural has the wrong type or exceeds its limit");
        break;
      }
      }
    }
    // Atomic nominal instances have an explicit installation-independent
    // logical admission table. A known domain sort alone is insufficient.
    if (application.constructor != "resource_unit" &&
        (declaration->parameters.empty() ||
         (declaration->parameters.size() == 1 &&
          declaration->parameters.front().kind ==
              protocol::StaticKind::Domain))) {
      StringRef identity;
      if (!application.arguments.empty())
        identity = cast<StringAttr>(application.arguments.front()).getValue();
      if (!protocol::installedDomains().admitsLogicalType(
              application.constructor, identity))
        return refuse("logical instance is not declared");
    }
    if (application.constructor == "sequence" &&
        (!permissions.copy || !permissions.drop))
      return refuse("sequence elements must be copyable and discardable");
    return success();
  }
};
} // namespace
LogicalResult verifyLogicalType(llvm::function_ref<InFlightDiagnostic()> emit,
                                Type type,
                                LogicalTypePermissions *permissions) {
  return verifyLogicalTypes(emit, TypeRange{type}, permissions);
}
LogicalResult verifyLogicalTypes(llvm::function_ref<InFlightDiagnostic()> emit,
                                 TypeRange types,
                                 LogicalTypePermissions *permissions) {
  // Standard MLIR subelement traversal includes inactive alternatives and
  // repeated uniqued children. This is a structural allowance, not a byte cap.
  auto diagnostic = [&] {
    return diagnostics::emit(emit(), "logical-type-formation");
  };
  SmallVector<Type> roots(types);
  if (failed(data::detail::verifyStructure(diagnostic, {}, roots)))
    return failure();
  LogicalTypePermissions result;
  Formation formation{diagnostic};
  for (Type type : types) {
    LogicalTypePermissions value;
    if (failed(formation.inspect(type, 0, value)))
      return failure();
    result.copy &= value.copy;
    result.drop &= value.drop;
  }
  if (permissions)
    *permissions = result;
  return success();
}
LogicalResult
verifyRepresentedType(llvm::function_ref<InFlightDiagnostic()> emit,
                      Type logical, StringRef representation,
                      ArrayRef<Type> children) {
  auto diagnostic = [&] {
    return diagnostics::emit(emit(), "represented-type-formation");
  };
  SmallVector<Type> roots{logical};
  llvm::append_range(roots, children);
  if (failed(data::detail::verifyStructure(diagnostic, {}, roots)))
    return failure();
  return Formation{diagnostic}.represented(logical, representation, children,
                                           0);
}
LogicalResult verifyValueType(llvm::function_ref<InFlightDiagnostic()> emit,
                              Type type) {
  if (auto represented = dyn_cast_or_null<runtime::RepresentedType>(type)) {
    if (!represented.getLogical() ||
        represented.getLogical().getContext() != type.getContext())
      return diagnostics::emit(emit(), "represented-type-formation",
                               "logical child crosses MLIR contexts");
    return verifyRepresentedType(emit, represented.getLogical(),
                                 represented.getRepresentation(),
                                 represented.getChildren());
  }
  return verifyLogicalType(emit, type);
}
Type logicalValueType(Type type) {
  if (auto represented = dyn_cast_or_null<runtime::RepresentedType>(type))
    return represented.getLogical();
  return type;
}
LogicalResult
verifyLogicalTypeApplication(llvm::function_ref<InFlightDiagnostic()> emit,
                             MLIRContext *context,
                             const CatalogTypeApplication &application) {
  auto diagnostic = [&] {
    return diagnostics::emit(emit(), "logical-type-formation");
  };
  if (!context)
    return diagnostic() << "missing logical type context";
  if (failed(data::detail::verifyStructure(diagnostic, application.arguments)))
    return failure();
  LogicalTypePermissions permissions;
  return Formation{diagnostic}.inspectApplication(application, context, 0,
                                                  permissions);
}
Type constructLogicalType(llvm::function_ref<InFlightDiagnostic()> emit,
                          MLIRContext *context,
                          const CatalogTypeApplication &application) {
  if (failed(verifyLogicalTypeApplication(emit, context, application)))
    return {};
  const auto *adapter =
      protocol::type_adapters::findAdapter(application.constructor);
  if (!adapter || !adapter->construct) {
    diagnostics::emit(emit(), "logical-type-construction",
                      "no unique native constructor");
    return {};
  }
  auto type = adapter->construct(emit, context, application.constructor,
                                 application.arguments);
  auto interface = dyn_cast_or_null<CatalogTypeInterface>(type);
  auto observed = interface ? interface.getCatalogApplication() : std::nullopt;
  if (!observed || type.getContext() != context ||
      observed->constructor != application.constructor ||
      observed->arguments != application.arguments) {
    diagnostics::emit(
        emit(), "logical-type-construction",
        "native type is unavailable or has a different application");
    return {};
  }
  return type;
}
} // namespace zkc
