#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Mathematical/Registry.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::mathematical {
Error checkInstalledDomainType(StringRef nominalIdentity,
                               const TypeShape &shape) {
  const auto &catalog = protocol::installedDomains();
  const auto *domain = catalog.domain(nominalIdentity);
  if (!domain || !shape.domain || !shape.elements.empty())
    return error("math-installed-domain");
  if (shape.kind == TypeShape::Kind::Polynomial ||
      shape.kind == TypeShape::Kind::Residual) {
    if (!shape.constructor.empty() || shape.statics.size() != 2 ||
        domain->sort != "Field" ||
        !catalog.hasFact("Field", {nominalIdentity.str()}))
      return error("math-installed-field-family");
    if ((shape.kind == TypeShape::Kind::Residual &&
         shape.degree != raw::PolynomialType::Degree::Individual) ||
        (shape.degree != raw::PolynomialType::Degree::Individual &&
         shape.degree != raw::PolynomialType::Degree::Total))
      return error("math-installed-field-family");
    return Error::success();
  }
  if (shape.kind != TypeShape::Kind::Nominal || !shape.statics.empty() ||
      shape.degree != raw::PolynomialType::Degree::Individual)
    return error("math-installed-nominal-shape");
  const auto *declaration = protocol::typeDeclaration(shape.constructor);
  if (!declaration || declaration->parameters.size() != 1 ||
      declaration->parameters[0].kind != protocol::StaticKind::Domain ||
      declaration->parameters[0].sort != domain->sort)
    return error("math-installed-nominal-constructor");
  const auto *permissions = protocol::typePermissions(shape.constructor);
  if (!permissions || !permissions->copy || !permissions->drop ||
      (permissions->custody != protocol::Custody::PublicValue &&
       permissions->custody != protocol::Custody::PrivateImmutable))
    return error("math-installed-nominal-resource");
  if (!catalog.admitsLogicalType(shape.constructor, nominalIdentity))
    return error("math-installed-nominal-instance");
  // Use the existing closed formation path as well as its declaration/catalog
  // facts. The temporary BoundType stays inside this adapter.
  auto formed = protocol::parseBoundType(
      shape.constructor + ":" + nominalIdentity.str(), false);
  if (!formed) {
    consumeError(formed.takeError());
    return error("math-installed-nominal-instance");
  }
  return Error::success();
}
} // namespace zkc::mathematical
