#include "zkc/Contracts/Instances.h"

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
} // namespace zkc::protocol
