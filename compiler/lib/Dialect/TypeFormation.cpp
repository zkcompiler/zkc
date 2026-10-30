#include "zkc/Dialect/TypeFormation.h"
#include "Data/IR/Structure.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Interfaces/CatalogType.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
namespace zkc {
namespace {
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
  // Standard MLIR subelement traversal includes inactive alternatives and
  // repeated uniqued children. This is a structural allowance, not a byte cap.
  auto diagnostic = [&] {
    return diagnostics::emit(emit(), "logical-type-formation");
  };
  if (failed(data::detail::verifyStructure(diagnostic, {}, {type})))
    return failure();
  LogicalTypePermissions result;
  if (failed(Formation{diagnostic}.inspect(type, 0, result)))
    return failure();
  if (permissions)
    *permissions = result;
  return success();
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
} // namespace zkc
