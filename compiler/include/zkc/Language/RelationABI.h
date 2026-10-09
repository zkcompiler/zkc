#ifndef ZKC_LANGUAGE_RELATIONABI_H
#define ZKC_LANGUAGE_RELATIONABI_H
#include "zkc/Language/Project.h"
#include <string>
#include <vector>
namespace zkc::relation {
class Bundle;
}
namespace zkc::language {
/// One formal of the signature a captured relation bundle denotes. The label
/// names the bundle object it stands for; it is diagnostic text, not identity.
struct DerivedFormal {
  RelationPurpose purpose = RelationPurpose::Statement;
  Type type;
  std::string label;
};
/// The exact ordered formals of a `bundle(asset ...)` relation, derived from
/// the admitted bundle alone: one Statement field formal per public slot in
/// slot order, then per table in table order a Statement `bool` presence
/// formal when the table is optional, a height `index` formal whose purpose
/// follows the height authority (Parameter for config, Statement for
/// instance, none for fixed), then one `builtin("vector", field)` formal per
/// group in group order whose purpose follows the group authority (witness
/// to Witness, config to Parameter, public to Statement). Channels contribute
/// nothing. The result size is bounded by the bundle formation limits; callers
/// charge it against their own work budgets. See
/// docs/spec/language/protocols.md for the denotation of these formals.
std::vector<DerivedFormal> bundleRelationFormals(const relation::Bundle &);
} // namespace zkc::language
#endif
