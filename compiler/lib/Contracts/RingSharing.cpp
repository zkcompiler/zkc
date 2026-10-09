#include "zkc/Contracts/RingSharing.h"
#include "zkc/Support/Refusal.h"
#include <map>
#include <tuple>

using namespace llvm;
namespace zkc::ring {
namespace {
/// Everything admission leaves meaningful on a node, with children already
/// replaced by their shared images. Admission canonicalizes the unused fields
/// of each kind, so comparing the whole tuple compares exactly the label. The
/// strings are borrowed from the original arena, which outlives the walk.
using Key =
    std::tuple<Kind, StringRef, StringRef, uint32_t, uint32_t, uint32_t>;

bool hasLeft(Kind kind) {
  return kind == Kind::Add || kind == Kind::Mul || kind == Kind::Neg ||
         kind == Kind::Embed;
}
bool hasRight(Kind kind) { return kind == Kind::Add || kind == Kind::Mul; }
} // namespace

Expected<Sharing> shareExpression(const Expression &original) {
  std::vector<Node> nodes;
  std::vector<uint32_t> nodeMap;
  nodeMap.reserve(original.nodes().size());
  std::map<Key, uint32_t> images;
  bool changed = false;
  for (const auto &node : original.nodes()) {
    uint32_t left = hasLeft(node.kind) ? nodeMap[node.left] : 0;
    uint32_t right = hasRight(node.kind) ? nodeMap[node.right] : 0;
    auto [it, inserted] = images.try_emplace(
        Key{node.kind, node.field, node.constant, node.input, left, right},
        uint32_t(nodes.size()));
    if (inserted) {
      nodes.push_back(node);
      nodes.back().left = left;
      nodes.back().right = right;
    } else
      changed = true;
    nodeMap.push_back(it->second);
  }
  std::vector<uint32_t> outputs;
  outputs.reserve(original.outputs().size());
  for (uint32_t output : original.outputs())
    outputs.push_back(nodeMap[output]);
  auto expression = Expression::create(
      std::vector<Input>(original.inputs().begin(), original.inputs().end()),
      std::move(nodes), std::move(outputs));
  if (!expression)
    return expression.takeError();
  return Sharing{std::move(*expression), std::move(nodeMap), changed};
}

Error checkSharing(const Expression &original, const Expression &shared,
                   ArrayRef<uint32_t> nodeMap) {
  if (nodeMap.size() != original.nodes().size())
    return zkc::error("ring-sharing-map");
  for (uint32_t image : nodeMap)
    if (image >= shared.nodes().size())
      return zkc::error("ring-sharing-map");
  if (original.inputs().size() != shared.inputs().size())
    return zkc::error("ring-sharing-inputs");
  for (size_t i = 0; i < original.inputs().size(); ++i)
    if (original.inputs()[i].field != shared.inputs()[i].field)
      return zkc::error("ring-sharing-inputs");
  for (uint32_t i = 0; i < original.nodes().size(); ++i) {
    const auto &node = original.nodes()[i];
    const auto &image = shared.nodes()[nodeMap[i]];
    if (image.kind != node.kind || image.field != node.field ||
        image.constant != node.constant || image.input != node.input)
      return zkc::error("ring-sharing-node");
    if (hasLeft(node.kind) && image.left != nodeMap[node.left])
      return zkc::error("ring-sharing-node");
    if (hasRight(node.kind) && image.right != nodeMap[node.right])
      return zkc::error("ring-sharing-node");
  }
  if (original.outputs().size() != shared.outputs().size())
    return zkc::error("ring-sharing-outputs");
  for (size_t p = 0; p < original.outputs().size(); ++p)
    if (shared.outputs()[p] != nodeMap[original.outputs()[p]])
      return zkc::error("ring-sharing-outputs");
  return Error::success();
}
} // namespace zkc::ring
