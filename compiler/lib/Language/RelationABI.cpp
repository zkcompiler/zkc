#include "zkc/Language/RelationABI.h"
#include "zkc/Relation/Bundle.h"
namespace zkc::language {
namespace {
Type vectorOf(llvm::StringRef field) {
  Type result(Type::Kind::Builtin, "vector");
  result.arguments = {Type(Type::Kind::Field, field.str())};
  return result;
}
RelationPurpose purposeOf(relation::BundleAuthority authority) {
  switch (authority) {
  case relation::BundleAuthority::Witness:
    return RelationPurpose::Witness;
  case relation::BundleAuthority::Config:
    return RelationPurpose::Parameter;
  case relation::BundleAuthority::Public:
    return RelationPurpose::Statement;
  }
  return RelationPurpose::Statement;
}
} // namespace
std::vector<DerivedFormal>
bundleRelationFormals(const relation::Bundle &bundle) {
  std::vector<DerivedFormal> result;
  for (const auto &slot : bundle.publics())
    result.push_back({RelationPurpose::Statement,
                      Type(Type::Kind::Field, slot.field),
                      "public " + slot.name});
  for (const auto &table : bundle.tables()) {
    if (table.optional)
      result.push_back({RelationPurpose::Statement, Type(Type::Kind::Boolean),
                        "table " + table.name + " presence"});
    switch (table.height.authority) {
    case relation::BundleHeightAuthority::Fixed:
      break;
    case relation::BundleHeightAuthority::Config:
      result.push_back({RelationPurpose::Parameter, Type(Type::Kind::Index),
                        "table " + table.name + " height"});
      break;
    case relation::BundleHeightAuthority::Instance:
      result.push_back({RelationPurpose::Statement, Type(Type::Kind::Index),
                        "table " + table.name + " height"});
      break;
    }
    for (const auto &group : table.groups)
      result.push_back({purposeOf(group.authority), vectorOf(group.field),
                        "table " + table.name + " group " + group.name});
  }
  return result;
}
} // namespace zkc::language
