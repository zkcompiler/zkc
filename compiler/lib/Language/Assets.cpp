#include "zkc/Language/Assets.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc::language {
Asset::Asset(std::string name, Definition definition)
    : name_(std::move(name)), definition(std::move(definition)) {
  identity_ = std::visit(
      [](const auto &value) { return StringRef(value->identity()).str(); },
      this->definition);
}
Expected<Asset> Asset::read(const AssetBuffer &buffer) {
  if (buffer.format == "ring-json") {
    auto value = ring::readExpressionText(buffer.bytes);
    if (!value)
      return value.takeError();
    return Asset(buffer.name,
                 std::make_shared<const ring::Expression>(std::move(*value)));
  }
  if (buffer.format == "relation-bundle-json") {
    auto value = relation::readBundleText(buffer.bytes);
    if (!value)
      return value.takeError();
    return Asset(buffer.name,
                 std::make_shared<const relation::Bundle>(std::move(*value)));
  }
  if (buffer.format == "air-json") {
    auto value = relation::readAIRText(buffer.bytes);
    if (!value)
      return value.takeError();
    return Asset(buffer.name,
                 std::make_shared<const relation::AIR>(std::move(*value)));
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
  return Asset(buffer.name,
               std::make_shared<const relation::R1CS>(std::move(*value)));
}
const relation::R1CS *Asset::r1cs() const {
  auto *value = std::get_if<std::shared_ptr<const relation::R1CS>>(&definition);
  return value ? value->get() : nullptr;
}
const relation::AIR *Asset::air() const {
  auto *value = std::get_if<std::shared_ptr<const relation::AIR>>(&definition);
  return value ? value->get() : nullptr;
}
const ring::Expression *Asset::ring() const {
  auto *value =
      std::get_if<std::shared_ptr<const ring::Expression>>(&definition);
  return value ? value->get() : nullptr;
}
const relation::Bundle *Asset::bundle() const {
  auto *value =
      std::get_if<std::shared_ptr<const relation::Bundle>>(&definition);
  return value ? value->get() : nullptr;
}
json::Value Asset::encode() const {
  return std::visit([](const auto &value) { return value->encode(); },
                    definition);
}
} // namespace zkc::language
