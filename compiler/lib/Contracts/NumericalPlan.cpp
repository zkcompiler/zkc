#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include <limits>

using namespace llvm;
namespace zkc::protocol {
namespace {
SmallVector<unsigned, 2> operands(const ring::Node &node) {
  switch (node.kind) {
  case ring::Kind::Add:
  case ring::Kind::Mul:
    return {node.left, node.right};
  case ring::Kind::Neg:
    return {node.left};
  default:
    return {};
  }
}
} // namespace
json::Value NumericalPlan::encode() const {
  json::Array locations;
  for (unsigned slot : this->locations)
    locations.push_back(slot);
  return json::Array{"zkc.numerical-plan/0", expression.encode(), lanes, slots,
                     std::move(locations)};
}
Error checkNumericalPlan(const NumericalPlan &plan, StringRef field,
                         StringRef mask) {
  if (mask.size() > NumericalLimits::slots ||
      !all_of(mask, [](char bit) { return bit == '0' || bit == '1'; }))
    return error("numerical-mask");
  const auto &expression = plan.expression;
  if (installedDomains().identitySort(field) != "Field" ||
      expression.inputs().size() != mask.size() ||
      expression.outputs().size() != 1)
    return error("numerical-body-signature");
  for (const auto &input : expression.inputs())
    if (input.field != field)
      return error("numerical-body-field");
  for (auto [node, fact] : zip(expression.nodes(), expression.facts()))
    if (node.kind == ring::Kind::Embed || fact.field != field)
      return error("numerical-body-field");
  const size_t nodes = expression.nodes().size();
  if (!plan.lanes || plan.lanes > NumericalLimits::lanes || !plan.slots ||
      plan.slots > nodes || plan.locations.size() != nodes)
    return error("numerical-plan-shape");
  if (nodes > NumericalLimits::bodyBytes ||
      printJson(expression.encode()).size() > NumericalLimits::bodyBytes ||
      printJson(plan.encode()).size() > NumericalLimits::planBytes)
    return error("numerical-plan-bytes");
  std::vector<bool> used(plan.slots, false), varying(nodes, false),
      persistent(nodes, false);
  for (auto [id, node] : enumerate(expression.nodes())) {
    if (plan.locations[id] >= plan.slots)
      return error("numerical-plan-shape");
    used[plan.locations[id]] = true;
    varying[id] = node.kind == ring::Kind::Input && mask[node.input] == '1';
    for (unsigned dependency : operands(node))
      varying[id] = varying[id] || varying[dependency];
  }
  if (is_contained(used, false))
    return error("numerical-plan-shape");
  unsigned root = expression.outputs()[0];
  persistent[root] = !varying[root];
  for (auto [id, node] : enumerate(expression.nodes()))
    if (varying[id])
      for (unsigned dependency : operands(node))
        if (!varying[dependency])
          persistent[dependency] = true;

  constexpr unsigned empty = std::numeric_limits<unsigned>::max();
  std::vector<unsigned> contents(plan.slots, empty);
  for (bool phase : {false, true})
    for (auto [id, node] : enumerate(expression.nodes())) {
      if (varying[id] != phase)
        continue;
      for (unsigned dependency : operands(node))
        if (contents[plan.locations[dependency]] != dependency)
          return error("numerical-plan-schedule");
      unsigned &owner = contents[plan.locations[id]];
      if (owner != empty && persistent[owner])
        return error("numerical-plan-schedule");
      owner = id;
    }
  if (contents[plan.locations[root]] != root)
    return error("numerical-plan-schedule");
  return Error::success();
}
Expected<NumericalPlan> readNumericalPlan(StringRef body, StringRef field,
                                          StringRef mask) {
  if (body.size() > NumericalLimits::planBytes)
    return error("numerical-plan-bytes");
  auto json = parseNaturalJson(body, NumericalLimits::planBytes, 16,
                               "numerical-plan", "numerical-plan-bytes");
  if (!json)
    return json.takeError();
  auto *record = json->getAsArray();
  if (!record || record->size() != 5 ||
      (*record)[0].getAsString() != "zkc.numerical-plan/0")
    return error("numerical-plan");
  auto lanes = (*record)[2].getAsInteger(), slots = (*record)[3].getAsInteger();
  auto *locations = (*record)[4].getAsArray();
  if (!lanes || *lanes < 1 || *lanes > NumericalLimits::lanes || !slots ||
      *slots < 1 || *slots > ring::Limits::nodes || !locations)
    return error("numerical-plan-shape");
  auto expression = ring::readExpression((*record)[1]);
  if (!expression)
    return expression.takeError();
  if (locations->size() != expression->nodes().size())
    return error("numerical-plan-shape");
  NumericalPlan plan{
      std::move(*expression), unsigned(*lanes), unsigned(*slots), {}};
  for (const auto &location : *locations) {
    auto slot = location.getAsInteger();
    if (!slot || *slot < 0 || *slot >= plan.slots)
      return error("numerical-plan-shape");
    plan.locations.push_back(*slot);
  }
  if (auto e = checkNumericalPlan(plan, field, mask))
    return std::move(e);
  if (printJson(plan.encode()) != body)
    return error("numerical-plan-canonical");
  return plan;
}
} // namespace zkc::protocol
