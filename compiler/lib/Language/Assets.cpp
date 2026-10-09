#include "zkc/Language/Assets.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc::language {
RelationAsset::RelationAsset(std::string name, Definition definition)
    : name_(std::move(name)), definition(std::move(definition)) {
  identity_ = std::visit([](const auto &value) { return value->identity(); },
                         this->definition);
}
Expected<RelationAsset> RelationAsset::read(const AssetBuffer &buffer) {
  if (buffer.format == "air-json") {
    auto value = relation::readAIRText(buffer.bytes);
    if (!value)
      return value.takeError();
    return RelationAsset(
        buffer.name, std::make_shared<const relation::AIR>(std::move(*value)));
  }
  Expected<relation::R1CS> value = [&]() -> Expected<relation::R1CS> {
    if (buffer.format == "r1cs-binary")
      return relation::readR1CS(buffer.bytes);
    if (buffer.format != "r1cs-json")
      return error("source.asset", "unknown captured asset format");
    auto json = relation::parseR1CSText(buffer.bytes);
    if (!json)
      return json.takeError();
    return relation::decodeR1CS(*json);
  }();
  if (!value)
    return value.takeError();
  return RelationAsset(
      buffer.name, std::make_shared<const relation::R1CS>(std::move(*value)));
}
const relation::R1CS *RelationAsset::r1cs() const {
  auto *value = std::get_if<std::shared_ptr<const relation::R1CS>>(&definition);
  return value ? value->get() : nullptr;
}
const relation::AIR *RelationAsset::air() const {
  auto *value = std::get_if<std::shared_ptr<const relation::AIR>>(&definition);
  return value ? value->get() : nullptr;
}
json::Value RelationAsset::encode() const {
  return std::visit([](const auto &value) { return value->encode(); },
                    definition);
}
} // namespace zkc::language
