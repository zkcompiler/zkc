#include "zkc/Contracts/RingExpression.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>
#include <numeric>

using namespace llvm;
namespace zkc::ring {
namespace {
bool fieldExists(StringRef field) {
  return protocol::installedDomains().hasFact("Field", {field.str()});
}
bool literalFits(StringRef field, StringRef value) {
  auto modulus = protocol::fieldModulus(field);
  return !modulus.empty() && !value.empty() && value.size() <= 256 &&
         (value.size() == 1 || value.front() != '0') &&
         llvm::all_of(value, [](char c) { return c >= '0' && c <= '9'; }) &&
         (value.size() < modulus.size() ||
          (value.size() == modulus.size() && value < modulus));
}
bool embeddingExists(StringRef source, StringRef target) {
  const auto &catalog = protocol::installedDomains();
  return catalog.hasFact("ExtensionField", {target.str()}) &&
         catalog.associatedIdentity(target, "BaseField") == source;
}
std::optional<uint32_t> index(const json::Value &value) {
  auto number = value.getAsUINT64();
  if (!number || *number > UINT32_MAX)
    return std::nullopt;
  return uint32_t(*number);
}
} // namespace

Node Node::literal(std::string field, std::string value) {
  Node node;
  node.field = std::move(field);
  node.constant = std::move(value);
  return node;
}
Node Node::slot(uint32_t index) {
  Node node;
  node.kind = Kind::Input;
  node.input = index;
  return node;
}
Node Node::add(uint32_t left, uint32_t right) {
  Node node;
  node.kind = Kind::Add;
  node.left = left;
  node.right = right;
  return node;
}
Node Node::mul(uint32_t left, uint32_t right) {
  auto node = add(left, right);
  node.kind = Kind::Mul;
  return node;
}
Node Node::neg(uint32_t operand) {
  Node node;
  node.kind = Kind::Neg;
  node.left = operand;
  return node;
}
Node Node::embed(std::string field, uint32_t operand) {
  auto node = neg(operand);
  node.kind = Kind::Embed;
  node.field = std::move(field);
  return node;
}

Expression::Expression(std::vector<Input> inputs, std::vector<Node> nodes,
                       std::vector<uint32_t> outputs, std::vector<Fact> facts)
    : inputs_(std::move(inputs)), nodes_(std::move(nodes)),
      outputs_(std::move(outputs)), facts_(std::move(facts)) {}

Expected<Expression> Expression::create(std::vector<Input> inputs,
                                        std::vector<Node> nodes,
                                        std::vector<uint32_t> outputs) {
  if (inputs.size() > Limits::inputs || nodes.size() > Limits::nodes ||
      outputs.size() > Limits::outputs)
    return zkc::error("ring-limit");
  for (const auto &input : inputs) {
    if (!fieldExists(input.field))
      return zkc::error("ring-field");
  }
  std::vector<Fact> facts;
  facts.reserve(nodes.size());
  for (uint32_t i = 0; i < nodes.size(); ++i) {
    const auto &node = nodes[i];
    Fact fact{"", 0, 1};
    if ((node.kind != Kind::Constant && node.constant != "0") ||
        (node.kind != Kind::Input && node.input != 0) ||
        (node.kind != Kind::Constant && node.kind != Kind::Embed &&
         !node.field.empty()))
      return zkc::error("ring-node-shape");
    switch (node.kind) {
    case Kind::Constant:
      if (node.left || node.right)
        return zkc::error("ring-node-shape");
      if (!fieldExists(node.field))
        return zkc::error("ring-field");
      if (!literalFits(node.field, node.constant))
        return zkc::error("ring-literal");
      fact.field = node.field;
      break;
    case Kind::Input:
      if (node.left || node.right)
        return zkc::error("ring-node-shape");
      if (node.input >= inputs.size())
        return zkc::error("ring-input");
      fact.field = inputs[node.input].field;
      fact.degree = 1;
      break;
    case Kind::Add:
    case Kind::Mul:
      if (node.left >= i || node.right >= i)
        return zkc::error("ring-edge");
      if (facts[node.left].field != facts[node.right].field)
        return zkc::error("ring-field-mismatch");
      fact.field = facts[node.left].field;
      fact.depth =
          1 + std::max(facts[node.left].depth, facts[node.right].depth);
      fact.degree =
          node.kind == Kind::Add
              ? std::max(facts[node.left].degree, facts[node.right].degree)
              : std::min(Limits::degree + 1,
                         facts[node.left].degree + facts[node.right].degree);
      break;
    case Kind::Neg:
    case Kind::Embed:
      if (node.right)
        return zkc::error("ring-node-shape");
      if (node.left >= i)
        return zkc::error("ring-edge");
      fact = facts[node.left];
      ++fact.depth;
      if (node.kind == Kind::Embed) {
        if (!embeddingExists(fact.field, node.field))
          return zkc::error("ring-embedding");
        fact.field = node.field;
      }
      break;
    default:
      return zkc::error("ring-node-shape");
    }
    if (fact.depth > Limits::depth)
      return zkc::error("ring-depth");
    facts.push_back(std::move(fact));
  }
  Expression result(std::move(inputs), std::move(nodes), std::move(outputs),
                    std::move(facts));
  std::vector<uint32_t> positions(result.outputs_.size());
  std::iota(positions.begin(), positions.end(), 0);
  auto needed = result.dependencies(positions);
  if (!needed)
    return needed.takeError();
  if (!llvm::all_of(*needed, [](bool used) { return used; }))
    return zkc::error("ring-unreachable-node");
  if (zkc::printJson(result.encode()).size() > Limits::bytes)
    return zkc::error("ring-limit");
  return result;
}

Expected<std::vector<bool>>
Expression::dependencies(ArrayRef<uint32_t> positions) const {
  if (positions.size() > Limits::outputs)
    return zkc::error("ring-limit");
  std::vector<bool> needed(nodes_.size(), false);
  for (uint32_t position : positions) {
    if (position >= outputs_.size() || outputs_[position] >= nodes_.size())
      return zkc::error("ring-output");
    needed[outputs_[position]] = true;
  }
  for (size_t i = nodes_.size(); i-- > 0;) {
    if (!needed[i])
      continue;
    const auto &node = nodes_[i];
    if (node.kind == Kind::Add || node.kind == Kind::Mul) {
      needed[node.left] = true;
      needed[node.right] = true;
    } else if (node.kind == Kind::Neg || node.kind == Kind::Embed)
      needed[node.left] = true;
  }
  return needed;
}

Expected<std::vector<uint32_t>>
Expression::degrees(ArrayRef<uint32_t> weights) const {
  if (weights.size() != inputs_.size())
    return zkc::error("ring-input");
  for (auto weight : weights)
    if (weight > Limits::degree)
      return zkc::error("ring-degree");
  std::vector<uint32_t> result;
  result.reserve(nodes_.size());
  for (const auto &node : nodes_) {
    uint64_t degree = 0;
    switch (node.kind) {
    case Kind::Constant:
      break;
    case Kind::Input:
      degree = weights[node.input];
      break;
    case Kind::Add:
      degree = std::max(result[node.left], result[node.right]);
      break;
    case Kind::Mul:
      degree = uint64_t(result[node.left]) + result[node.right];
      break;
    case Kind::Neg:
    case Kind::Embed:
      degree = result[node.left];
      break;
    }
    if (degree > Limits::degree)
      return zkc::error("ring-degree");
    result.push_back(degree);
  }
  return result;
}

Expected<std::vector<uint32_t>>
Expression::usedInputs(ArrayRef<uint32_t> positions) const {
  auto needed = dependencies(positions);
  if (!needed)
    return needed.takeError();
  std::vector<bool> used(inputs_.size(), false);
  for (uint32_t i = 0; i < nodes_.size(); ++i)
    if ((*needed)[i] && nodes_[i].kind == Kind::Input)
      used[nodes_[i].input] = true;
  std::vector<uint32_t> result;
  for (uint32_t i = 0; i < used.size(); ++i)
    if (used[i])
      result.push_back(i);
  return result;
}

json::Value Expression::encode() const {
  json::Array inputs, nodes, outputs;
  for (const auto &input : inputs_)
    inputs.push_back(input.field);
  for (const auto &node : nodes_) {
    switch (node.kind) {
    case Kind::Constant:
      nodes.push_back(json::Array{"constant", node.field, node.constant});
      break;
    case Kind::Input:
      nodes.push_back(json::Array{"input", node.input});
      break;
    case Kind::Add:
    case Kind::Mul:
      nodes.push_back(json::Array{node.kind == Kind::Add ? "add" : "mul",
                                  node.left, node.right});
      break;
    case Kind::Neg:
      nodes.push_back(json::Array{"neg", node.left});
      break;
    case Kind::Embed:
      nodes.push_back(json::Array{"embed", node.field, node.left});
      break;
    }
  }
  for (auto output : outputs_)
    outputs.push_back(output);
  return json::Array{"zkc.ring/0", std::move(inputs), std::move(nodes),
                     std::move(outputs)};
}

std::string Expression::identity() const {
  auto bytes = zkc::printJson(encode());
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}

Expected<Expression> readExpression(const json::Value &value) {
  auto *row = value.getAsArray();
  if (!row || row->size() != 4 || (*row)[0].getAsString() != "zkc.ring/0")
    return zkc::error("ring-schema");
  auto *inputRows = (*row)[1].getAsArray();
  auto *nodeRows = (*row)[2].getAsArray();
  auto *outputRows = (*row)[3].getAsArray();
  if (!inputRows || !nodeRows || !outputRows)
    return zkc::error("ring-schema");
  if (inputRows->size() > Limits::inputs || nodeRows->size() > Limits::nodes ||
      outputRows->size() > Limits::outputs)
    return zkc::error("ring-limit");
  std::vector<Input> inputs;
  std::vector<Node> nodes;
  std::vector<uint32_t> outputs;
  for (const auto &item : *inputRows) {
    auto input = item.getAsString();
    if (!input)
      return zkc::error("ring-schema");
    inputs.push_back({input->str()});
  }
  for (const auto &item : *nodeRows) {
    auto *node = item.getAsArray();
    if (!node || node->empty() || !(*node)[0].getAsString())
      return zkc::error("ring-schema");
    auto kind = *(*node)[0].getAsString();
    if (kind == "constant" && node->size() == 3 && (*node)[1].getAsString() &&
        (*node)[2].getAsString())
      nodes.push_back(Node::literal((*node)[1].getAsString()->str(),
                                    (*node)[2].getAsString()->str()));
    else if (kind == "input" && node->size() == 2 && index((*node)[1]))
      nodes.push_back(Node::slot(*index((*node)[1])));
    else if ((kind == "add" || kind == "mul") && node->size() == 3 &&
             index((*node)[1]) && index((*node)[2]))
      nodes.push_back(kind == "add"
                          ? Node::add(*index((*node)[1]), *index((*node)[2]))
                          : Node::mul(*index((*node)[1]), *index((*node)[2])));
    else if (kind == "neg" && node->size() == 2 && index((*node)[1]))
      nodes.push_back(Node::neg(*index((*node)[1])));
    else if (kind == "embed" && node->size() == 3 && (*node)[1].getAsString() &&
             index((*node)[2]))
      nodes.push_back(
          Node::embed((*node)[1].getAsString()->str(), *index((*node)[2])));
    else
      return zkc::error("ring-schema");
  }
  for (const auto &item : *outputRows) {
    auto output = index(item);
    if (!output)
      return zkc::error("ring-schema");
    outputs.push_back(*output);
  }
  return Expression::create(std::move(inputs), std::move(nodes),
                            std::move(outputs));
}

Expected<Expression> readExpressionText(StringRef text) {
  auto json = zkc::parseNaturalJson(text, Limits::bytes, 16, "ring-schema",
                                    "ring-limit");
  if (!json)
    return json.takeError();
  return readExpression(*json);
}
} // namespace zkc::ring
