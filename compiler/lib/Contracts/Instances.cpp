#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include <set>

namespace zkc::protocol {
#define ZKC_INSTALLED_INSTANCE_TABLES
#include "zkc/Contracts/Instances.inc"

namespace instances {
const Domain *domain(llvm::StringRef identity) {
  for (const auto &row : domains())
    if (row.identity == identity)
      return &row;
  return nullptr;
}
const FrameTag *frameTag(unsigned tag) {
  for (const auto &row : frameTags())
    if (row.tag == tag)
      return &row;
  return nullptr;
}
const Codec *codec(llvm::StringRef identity) {
  for (const auto &row : codecs())
    if (row.identity == identity)
      return &row;
  return nullptr;
}
std::optional<BinomialExtension> binomialExtension(llvm::StringRef field) {
  const auto *row = domain(field);
  if (!row || !row->field || !row->field->extension)
    return std::nullopt;
  const auto &extension = *row->field->extension;
  if (extension.over != ExtensionBase::BaseField ||
      extension.reduction.size() != 1 ||
      extension.reduction.front().exponent != 0)
    return std::nullopt;
  for (const auto &member : row->members)
    if (member.member == "BaseField")
      return BinomialExtension{member.identity, extension.degree,
                               extension.reduction.front().coefficient};
  return std::nullopt;
}
const Limit *limit(llvm::StringRef name) {
  for (const auto &row : limits())
    if (row.name == name)
      return &row;
  return nullptr;
}
} // namespace instances

namespace installation {
const Provider *provider(llvm::StringRef domain) {
  for (const auto &row : providers())
    if (row.domain == domain)
      return &row;
  return nullptr;
}
llvm::StringRef providerUnit(llvm::StringRef provider) {
  for (const auto &row : providerUnits())
    if (row.provider == provider)
      return row.unit;
  return {};
}
const FieldForm *fieldForm(llvm::StringRef field) {
  for (const auto &row : fieldForms())
    if (row.field == field)
      return &row;
  return nullptr;
}
} // namespace installation

bool nativeMessageAtom(llvm::StringRef kind, llvm::StringRef identity) {
  static const std::set<std::pair<std::string, std::string>> atoms = [] {
    std::set<std::pair<std::string, std::string>> result;
    for (const auto &codec : instances::codecs()) {
      const auto *type = typeDeclaration(codec.kind);
      if (type && type->message && codec.frame)
        result.emplace(codec.kind, codec.domain);
    }
    return result;
  }();
  return atoms.count({kind.str(), identity.str()});
}
bool canonicalRepresentation(llvm::StringRef kind, llvm::StringRef identity,
                             llvm::StringRef representation) {
  return llvm::any_of(installation::representations(), [&](const auto &row) {
    return row.kind == kind && row.domain == identity &&
           row.identity == representation &&
           row.frame == installation::ValueFrame::Canonical;
  });
}
llvm::StringRef residentRepresentation(llvm::StringRef kind,
                                       llvm::StringRef identity) {
  llvm::StringRef resident;
  for (const auto &row : installation::representations())
    if (row.kind == kind && row.domain == identity && !row.isDefault &&
        row.frame == installation::ValueFrame::Canonical) {
      if (!resident.empty())
        return {};
      resident = row.identity;
    }
  return resident;
}
bool setupCommitment(llvm::StringRef identity) {
  const auto *row = instances::domain(identity);
  return row && row->commitment &&
         row->commitment->scheme == instances::CommitmentScheme::MultilinearKzg;
}
bool nativeFieldArrayFrame(llvm::StringRef field) {
  return llvm::any_of(instances::aggregateFrames(), [&](const auto &row) {
    return row.constructor == "field_array" && row.domain == field;
  });
}
bool nativeFieldArrayRepresentation(llvm::StringRef field, uint64_t size,
                                    llvm::StringRef representation) {
  using Kind = installation::ArgumentPattern::Kind;
  return llvm::any_of(
      installation::appliedRepresentations(), [&](const auto &row) {
        return row.constructor == "field_array" &&
               row.identity == representation &&
               row.frame == installation::ValueFrame::Canonical &&
               row.arguments.size() == 2 &&
               row.arguments[0].kind == Kind::Domain &&
               row.arguments[0].identity == field &&
               row.arguments[1].kind == Kind::NatRange &&
               row.arguments[1].minimum <= size &&
               size <= row.arguments[1].maximum;
      });
}

llvm::ArrayRef<RandomService> randomServices() {
  static const std::vector<RandomService> services = [] {
    std::vector<RandomService> result;
    for (const auto &row : instances::randomServices())
      result.push_back({row.contract, row.field});
    return result;
  }();
  return services;
}
} // namespace zkc::protocol
