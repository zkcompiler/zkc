#include "zkc/Contracts/Variant.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
#include <set>

using namespace llvm;
namespace zkc::protocol {
namespace {
constexpr size_t MaxNodes = 16384, MaxBytes = 8 * 1024 * 1024,
                 MaxExpandedNodes = 200000;
bool label(StringRef s) {
  return !s.empty() && s.size() <= 128 &&
         (isAlpha(s.front()) || s.front() == '_') && all_of(s, [](char c) {
           return isAlnum(c) || c == '_' || c == '-' || c == '.';
         });
}
// Each spelling owns its table. The table is only an encoding of exact content,
// never a registry whose ordinal or hash could stand in for type equality.
struct Table {
  json::Array nodes;
  std::map<std::string, size_t> ids;
  size_t visits = 0, encodedBytes = 0;
  std::optional<size_t> intern(const json::Value &value, unsigned depth = 0) {
    if (depth >= 64 || ++visits > MaxExpandedNodes)
      return std::nullopt;
    json::Value node = nullptr;
    if (auto text = value.getAsString()) {
      if (text->size() > VariantSpellingBytes ||
          !all_of(*text, [](unsigned char c) { return c >= 32 && c <= 126; }))
        return std::nullopt;
      node = text->str();
    } else if (auto *array = value.getAsArray()) {
      json::Array refs;
      for (const auto &child : *array) {
        auto id = intern(child, depth + 1);
        if (!id)
          return std::nullopt;
        refs.push_back(std::to_string(*id));
      }
      node = std::move(refs);
    } else
      return std::nullopt;
    auto key = printJson(node);
    if (auto it = ids.find(key); it != ids.end())
      return it->second;
    if (nodes.size() >= MaxNodes)
      return std::nullopt;
    encodedBytes += key.size() + 1;
    if (encodedBytes > (VariantSpellingBytes - 8) / 2)
      return std::nullopt;
    size_t id = nodes.size();
    ids.emplace(std::move(key), id);
    nodes.push_back(std::move(node));
    return id;
  }
};
std::optional<std::string> pack(const json::Value &tree) {
  Table table;
  if (!table.intern(tree))
    return std::nullopt;
  auto text = printJson(json::Array{"zkc.variant/0", std::move(table.nodes)});
  if (text.size() > (VariantSpellingBytes - 8) / 2)
    return std::nullopt;
  return "variant:" + toHex(text, true);
}
std::optional<json::Value> unpack(StringRef spelling) {
  auto type = spelling;
  if (type.size() > VariantSpellingBytes || !type.consume_front("variant:") ||
      type.empty() || type.size() % 2 || !all_of(type, [](char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
      }))
    return std::nullopt;
  auto value = parseJson(fromHex(type));
  if (!value) {
    consumeError(value.takeError());
    return std::nullopt;
  }
  auto *root = value->getAsArray();
  if (!root || root->size() != 2 || (*root)[0].getAsString() != "zkc.variant/0")
    return std::nullopt;
  auto *nodes = (*root)[1].getAsArray();
  if (!nodes || nodes->empty() || nodes->size() > MaxNodes)
    return std::nullopt;
  std::vector<json::Value> values;
  std::vector<size_t> sizes, counts, depths;
  size_t totalBytes = 0, totalNodes = 0;
  const size_t byteBudget = std::min(MaxBytes, size_t(512) * spelling.size());
  const size_t nodeBudget =
      std::min(MaxExpandedNodes, size_t(512) * spelling.size());
  for (const auto &node : *nodes) {
    size_t bytes = 2, count = 1, depth = 1;
    json::Value decoded = nullptr;
    if (auto s = node.getAsString()) {
      bytes = printJson(node).size();
      decoded = s->str();
    } else if (auto *refs = node.getAsArray()) {
      // Bound expansion before copying any referenced subtree.
      std::vector<size_t> indices;
      for (const auto &ref : *refs) {
        auto s = ref.getAsString();
        size_t index;
        if (!s || s->empty() || (s->size() > 1 && s->front() == '0') ||
            !all_of(*s, [](char c) { return isDigit(c); }) ||
            s->getAsInteger(10, index) || index >= values.size())
          return std::nullopt;
        bytes += sizes[index] + (indices.empty() ? 0 : 1);
        count += counts[index];
        depth = std::max(depth, depths[index] + 1);
        if (bytes > byteBudget || count > nodeBudget || depth > 64)
          return std::nullopt;
        indices.push_back(index);
      }
      if (totalBytes + bytes > byteBudget || totalNodes + count > nodeBudget)
        return std::nullopt;
      json::Array array;
      for (auto index : indices)
        array.push_back(values[index]);
      decoded = std::move(array);
    } else
      return std::nullopt;
    totalBytes += bytes;
    totalNodes += count;
    if (totalBytes > byteBudget || totalNodes > nodeBudget)
      return std::nullopt;
    sizes.push_back(bytes);
    counts.push_back(count);
    depths.push_back(depth);
    values.push_back(std::move(decoded));
  }
  auto canonical = pack(values.back());
  if (!canonical || *canonical != spelling)
    return std::nullopt;
  return std::move(values.back());
}
std::optional<VariantDescriptor>
descriptor(const json::Value &tree, unsigned depth, TypeParseBudget &budget) {
  auto *root = tree.getAsArray();
  if (depth >= 8 || !budget.consume() || !root || root->size() != 2)
    return std::nullopt;
  auto nominal = decodeVariantIdentity((*root)[0], budget);
  if (!nominal)
    return std::nullopt;
  auto *arms = (*root)[1].getAsArray();
  if (!arms || arms->empty() || arms->size() > VariantDescriptorAlternatives)
    return std::nullopt;
  VariantDescriptor result{std::move(*nominal), {}};
  std::set<std::string> labels;
  for (const auto &value : *arms) {
    auto *arm = value.getAsArray();
    if (!arm || arm->size() != 2)
      return std::nullopt;
    auto name = (*arm)[0].getAsString();
    auto *payload = (*arm)[1].getAsArray();
    if (!name || !label(*name) || !labels.insert(name->str()).second ||
        !payload || payload->size() > 128)
      return std::nullopt;
    VariantAlternative alternative{name->str(), {}};
    for (const auto &entry : *payload) {
      if (auto leaf = entry.getAsString()) {
        if (leaf->contains('@') || leaf->starts_with("variant:"))
          return std::nullopt;
        auto parsed = parseBoundType(*leaf, false, depth + 1, &budget);
        if (!parsed) {
          consumeError(parsed.takeError());
          return std::nullopt;
        }
        alternative.payload.push_back(std::move(*parsed));
      } else {
        auto nested = descriptor(entry, depth + 1, budget);
        if (!nested)
          return std::nullopt;
        auto encoded = pack(entry);
        if (!encoded || !unpack(*encoded))
          return std::nullopt;
        BoundType type{"variant", {}, {}};
        type.variant =
            std::make_shared<const VariantDescriptor>(std::move(*nested));
        alternative.payload.push_back(std::move(type));
      }
    }
    result.alternatives.push_back(std::move(alternative));
  }
  return result;
}
std::optional<json::Value> descriptorTree(const VariantDescriptor &descriptor,
                                          unsigned depth) {
  if (depth >= 8 || descriptor.alternatives.empty() ||
      descriptor.alternatives.size() > VariantDescriptorAlternatives)
    return std::nullopt;
  json::Array arms;
  for (const auto &arm : descriptor.alternatives) {
    if (arm.payload.size() > 128)
      return std::nullopt;
    json::Array payload;
    for (const auto &type : arm.payload) {
      if (type.kind == "variant") {
        if (!type.variant)
          return std::nullopt;
        auto tree = descriptorTree(*type.variant, depth + 1);
        auto encoded = tree ? pack(*tree) : std::nullopt;
        if (!encoded || !unpack(*encoded))
          return std::nullopt;
        payload.push_back(std::move(*tree));
      } else {
        auto spelling = type.spelling();
        if (spelling.empty())
          return std::nullopt;
        payload.push_back(std::move(spelling));
      }
    }
    arms.push_back(json::Array{arm.label, std::move(payload)});
  }
  return json::Value(
      json::Array{encodeVariantIdentity(descriptor.nominal), std::move(arms)});
}
} // namespace
std::optional<VariantIdentity> decodeVariantIdentity(const json::Value &value,
                                                     TypeParseBudget &budget,
                                                     unsigned depth) {
  if (depth >= 64 || !budget.consume())
    return std::nullopt;
  if (auto atom = value.getAsString()) {
    if (atom->empty() || !budget.charge(atom->size()) || !json::isUTF8(*atom))
      return std::nullopt;
    return VariantIdentity(atom->str());
  }
  auto *array = value.getAsArray();
  if (!array || array->size() > budget.remaining)
    return std::nullopt;
  VariantIdentity::Tuple children;
  for (const auto &item : *array) {
    auto child = decodeVariantIdentity(item, budget, depth + 1);
    if (!child)
      return std::nullopt;
    children.push_back(std::move(*child));
  }
  return VariantIdentity(std::move(children));
}
json::Value encodeVariantIdentity(const VariantIdentity &identity) {
  if (auto *atom = identity.atom())
    return *atom;
  json::Array tuple;
  for (const auto &child : *identity.tuple())
    tuple.push_back(encodeVariantIdentity(child));
  return tuple;
}
std::optional<VariantDescriptor>
decodeVariant(std::string_view type, unsigned depth, TypeParseBudget *budget) {
  TypeParseBudget localBudget;
  if (!budget)
    budget = &localBudget;
  if (depth >= 8)
    return std::nullopt;
  auto tree = unpack(StringRef(type.data(), type.size()));
  return tree ? descriptor(*tree, depth, *budget) : std::nullopt;
}
std::optional<std::string> encodeVariant(const VariantDescriptor &d) {
  BoundType type{"variant", {}, {}};
  type.variant = std::make_shared<const VariantDescriptor>(d);
  if (auto e = checkBoundType(type, false)) {
    consumeError(std::move(e));
    return std::nullopt;
  }
  auto tree = descriptorTree(d, 0);
  auto encoded = tree ? pack(*tree) : std::nullopt;
  return encoded && decodeVariant(*encoded) ? encoded : std::nullopt;
}
} // namespace zkc::protocol
