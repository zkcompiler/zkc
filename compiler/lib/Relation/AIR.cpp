#include "zkc/Relation/AIR.h"
#include "Field.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <map>
#include <set>
#include <utility>

using namespace llvm;
namespace zkc::relation {

AIRNode AIRNode::constant(std::string value) {
  AIRNode n;
  n.value = std::move(value);
  return n;
}
AIRNode AIRNode::publicInput(uint32_t index) {
  AIRNode n;
  n.kind = AIRKind::Public;
  n.index = index;
  return n;
}
AIRNode AIRNode::read(uint32_t offset, uint32_t column) {
  AIRNode n;
  n.kind = AIRKind::Read;
  n.offset = offset;
  n.column = column;
  return n;
}
AIRNode AIRNode::add(uint32_t lhs, uint32_t rhs) {
  AIRNode n;
  n.kind = AIRKind::Add;
  n.lhs = lhs;
  n.rhs = rhs;
  return n;
}
AIRNode AIRNode::mul(uint32_t lhs, uint32_t rhs) {
  auto n = add(lhs, rhs);
  n.kind = AIRKind::Mul;
  return n;
}
AIRNode AIRNode::neg(uint32_t operand) {
  auto n = add(operand, 0);
  n.kind = AIRKind::Neg;
  return n;
}

namespace {
bool binary(AIRKind kind) {
  return kind == AIRKind::Add || kind == AIRKind::Mul;
}
Expected<AIRConstraintAnalysis> analyze(const AIRConstraint &c,
                                        const Field &field, uint32_t columns,
                                        uint32_t publics) {
  if (c.expression.empty())
    return zkc::error("air-expression");
  if (c.expression.size() > AIRLimits::nodes)
    return zkc::error("air-node-limit");
  switch (c.scope.kind) {
  case AIRScopeKind::Every:
  case AIRScopeKind::First:
  case AIRScopeKind::Last:
    if (c.scope.lookahead)
      return zkc::error("air-scope");
    break;
  case AIRScopeKind::Transition:
    if (c.scope.lookahead > AIRLimits::offset)
      return zkc::error("air-offset-limit");
    break;
  default:
    return zkc::error("air-scope");
  }
  std::vector<uint32_t> degrees, depths;
  degrees.reserve(c.expression.size());
  depths.reserve(c.expression.size());
  AIRConstraintAnalysis facts;
  std::set<AIRCell> reads;
  for (const auto &n : c.expression) {
    uint64_t degree = 0;
    uint32_t depth = 1;
    if ((!binary(n.kind) && n.kind != AIRKind::Neg && n.lhs) ||
        (!binary(n.kind) && n.rhs) ||
        (n.kind != AIRKind::Constant && n.value != "0") ||
        (n.kind != AIRKind::Read && (n.offset || n.column)) ||
        (n.kind != AIRKind::Public && n.index))
      return zkc::error("air-node-shape");
    if (binary(n.kind) || n.kind == AIRKind::Neg) {
      if (n.lhs >= degrees.size() ||
          (binary(n.kind) && n.rhs >= degrees.size()))
        return zkc::error("air-node-reference");
      degree = degrees[n.lhs];
      depth = depths[n.lhs] + 1;
      if (binary(n.kind)) {
        degree = n.kind == AIRKind::Mul
                     ? degree + degrees[n.rhs]
                     : std::max(degree, uint64_t(degrees[n.rhs]));
        depth = std::max(depth, depths[n.rhs] + 1);
      }
    }
    switch (n.kind) {
    case AIRKind::Constant: {
      auto value = field.parse(n.value);
      if (!value)
        return value.takeError();
      break;
    }
    case AIRKind::Public:
      if (n.index >= publics)
        return zkc::error("air-public-index");
      break;
    case AIRKind::Read:
      if (n.column >= columns)
        return zkc::error("air-column");
      if (n.offset > AIRLimits::offset)
        return zkc::error("air-offset-limit");
      reads.insert({n.offset, n.column});
      facts.maxOffset = std::max(facts.maxOffset, n.offset);
      ++facts.readNodes;
      degree = 1;
      break;
    case AIRKind::Add:
    case AIRKind::Mul:
    case AIRKind::Neg:
      break;
    default:
      return zkc::error("air-unsupported-operation");
    }
    if (degree > AIRLimits::degree)
      return zkc::error("air-degree-limit");
    if (depth > AIRLimits::depth)
      return zkc::error("air-depth-limit");
    degrees.push_back(degree);
    depths.push_back(depth);
  }
  // Keep one representation of the actual expression: dead arena nodes cannot
  // contribute spurious reads or hide unsupported syntax from admission.
  std::vector<bool> live(c.expression.size());
  live.back() = true;
  for (size_t i = c.expression.size(); i-- > 0;) {
    if (!live[i])
      return zkc::error("air-dead-node");
    const auto &n = c.expression[i];
    if (binary(n.kind) || n.kind == AIRKind::Neg)
      live[n.lhs] = true;
    if (binary(n.kind))
      live[n.rhs] = true;
  }
  facts.degree = degrees.back();
  facts.depth = depths.back();
  facts.reads.assign(reads.begin(), reads.end());
  if ((c.declaredMaxOffset && *c.declaredMaxOffset > AIRLimits::offset) ||
      (c.declaredDegree && *c.declaredDegree > AIRLimits::degree))
    return zkc::error("air-declaration-limit");
  if ((c.declaredMaxOffset && *c.declaredMaxOffset < facts.maxOffset) ||
      (c.scope.kind == AIRScopeKind::Transition &&
       c.scope.lookahead < facts.maxOffset))
    return zkc::error("air-window-declaration");
  if (c.declaredDegree && *c.declaredDegree < facts.degree)
    return zkc::error("air-degree-declaration");
  return facts;
}
json::Value cellJSON(AIRCell c) { return json::Array{c.row, c.column}; }
json::Value scopeJSON(AIRScope scope) {
  switch (scope.kind) {
  case AIRScopeKind::Every:
    return json::Object{{"kind", "every"}};
  case AIRScopeKind::First:
    return json::Object{{"kind", "first"}};
  case AIRScopeKind::Last:
    return json::Object{{"kind", "last"}};
  case AIRScopeKind::Transition:
    return json::Object{{"kind", "transition"}, {"lookahead", scope.lookahead}};
  }
  llvm_unreachable("admitted AIR scope");
}
json::Value nodeJSON(const AIRNode &n) {
  switch (n.kind) {
  case AIRKind::Constant:
    return json::Object{{"op", "constant"}, {"value", n.value}};
  case AIRKind::Public:
    return json::Object{{"op", "public"}, {"index", n.index}};
  case AIRKind::Read:
    return json::Object{
        {"op", "read"}, {"offset", n.offset}, {"column", n.column}};
  case AIRKind::Add:
  case AIRKind::Mul:
    return json::Object{{"op", n.kind == AIRKind::Add ? "add" : "mul"},
                        {"lhs", n.lhs},
                        {"rhs", n.rhs}};
  case AIRKind::Neg:
    return json::Object{{"op", "neg"}, {"operand", n.lhs}};
  }
  llvm_unreachable("admitted AIR node");
}
std::pair<uint32_t, uint32_t> activeRows(AIRScope scope, uint32_t height) {
  switch (scope.kind) {
  case AIRScopeKind::Every:
    return {0, height};
  case AIRScopeKind::First:
    return {0, 1};
  case AIRScopeKind::Last:
    return {height - 1, height};
  case AIRScopeKind::Transition:
    return {0, height > scope.lookahead ? height - scope.lookahead : 0};
  }
  llvm_unreachable("admitted AIR scope");
}
Error layoutCheck(const AIR &air, uint32_t height,
                  const AIRTraceLayout &layout) {
  if (layout.field != air.field())
    return zkc::error("air-trace-field");
  if (layout.height != height || layout.columns != air.columns())
    return zkc::error("air-trace-layout");
  return Error::success();
}
} // namespace

AIR::AIR(std::string field, uint32_t columns, uint32_t publicInputs,
         std::vector<AIRConstraint> constraints,
         std::vector<AIRConstraintAnalysis> facts)
    : fieldName(std::move(field)), columnCount(columns),
      publicCount(publicInputs), constraints_(std::move(constraints)),
      facts_(std::move(facts)) {}
Expected<AIR> AIR::create(std::string field, uint32_t columns,
                          uint32_t publicInputs,
                          std::vector<AIRConstraint> constraints) {
  StringRef modulus = Field::primeModulus(field);
  if (modulus.empty())
    return zkc::error("air-field");
  if (columns > AIRLimits::columns || publicInputs > AIRLimits::publicInputs)
    return zkc::error("air-dimension-limit");
  if (constraints.size() > AIRLimits::constraints)
    return zkc::error("air-constraint-limit");
  size_t count = 0;
  for (const auto &c : constraints) {
    if (c.expression.size() > AIRLimits::nodes - count)
      return zkc::error("air-node-limit");
    count += c.expression.size();
  }
  Field arithmetic(modulus);
  std::vector<AIRConstraintAnalysis> facts;
  facts.reserve(constraints.size());
  for (const auto &c : constraints) {
    auto fact = analyze(c, arithmetic, columns, publicInputs);
    if (!fact)
      return fact.takeError();
    facts.push_back(std::move(*fact));
  }
  return AIR(std::move(field), columns, publicInputs, std::move(constraints),
             std::move(facts));
}
json::Value AIR::encode() const {
  json::Array constraints;
  for (const auto &c : constraints_) {
    json::Array nodes;
    for (const auto &n : c.expression)
      nodes.push_back(nodeJSON(n));
    json::Object entry{{"scope", scopeJSON(c.scope)},
                       {"nodes", std::move(nodes)}};
    if (c.declaredMaxOffset)
      entry["declared_max_offset"] = *c.declaredMaxOffset;
    if (c.declaredDegree)
      entry["declared_degree"] = *c.declaredDegree;
    constraints.push_back(std::move(entry));
  }
  return json::Object{{"schema", "zkc.air.v1"},
                      {"field", fieldName},
                      {"columns", columnCount},
                      {"public_inputs", publicCount},
                      {"constraints", std::move(constraints)}};
}
json::Value AIR::analysis() const {
  json::Array constraints;
  uint32_t maxDegree = 0, maxOffset = 0;
  for (size_t i = 0; i < facts_.size(); ++i) {
    const auto &fact = facts_[i];
    json::Array reads;
    for (auto cell : fact.reads)
      reads.push_back(cellJSON(cell));
    constraints.push_back(
        json::Object{{"constraint", uint64_t(i)},
                     {"scope", scopeJSON(constraints_[i].scope)},
                     {"max_offset", fact.maxOffset},
                     {"expression_degree", fact.degree},
                     {"depth", fact.depth},
                     {"read_nodes", fact.readNodes},
                     {"nodes", uint64_t(constraints_[i].expression.size())},
                     {"read_set", std::move(reads)}});
    maxDegree = std::max(maxDegree, fact.degree);
    maxOffset = std::max(maxOffset, fact.maxOffset);
  }
  return json::Object{{"schema", "zkc.air.analysis.v1"},
                      {"field", fieldName},
                      {"columns", columnCount},
                      {"public_inputs", publicCount},
                      {"max_offset", maxOffset},
                      {"expression_degree", maxDegree},
                      {"degree_variables", "trace-cells"},
                      {"selector_degree", nullptr},
                      {"domain_degree", nullptr},
                      {"constraints", std::move(constraints)}};
}
AIRPlan::AIRPlan(AIR relation, uint32_t height)
    : relation(std::move(relation)), height(height) {}
Expected<AIRPlan> AIR::compile(uint32_t height) const {
  if (!height || height > AIRLimits::height)
    return zkc::error("air-height");
  uint64_t work = 0, naive = 0;
  std::map<uint32_t, std::vector<std::pair<uint32_t, uint32_t>>> intervals;
  // Preflight all rows arithmetically before any schedule allocation.
  for (size_t i = 0; i < constraints_.size(); ++i) {
    auto range = activeRows(constraints_[i].scope, height);
    uint64_t count = range.second - range.first;
    if (count && uint64_t(range.second - 1) + facts_[i].maxOffset >= height)
      return zkc::error("air-window-out-of-range");
    work += count * constraints_[i].expression.size();
    naive += count * facts_[i].readNodes;
    if (work > AIRLimits::work)
      return zkc::error("air-work-limit");
    if (count)
      for (auto read : facts_[i].reads)
        intervals[read.column].push_back(
            {range.first + read.row, range.second + read.row});
  }
  // Count the union of absolute read intervals per column. This rejects an
  // oversized cache before expanding rows or allocating any cache/schedule.
  uint64_t uniqueCells = 0;
  for (auto &entry : intervals) {
    auto &ranges = entry.second;
    llvm::sort(ranges);
    uint32_t end = 0;
    for (auto range : ranges) {
      if (range.second > end) {
        uniqueCells += range.second - std::max(end, range.first);
        end = range.second;
      }
    }
    if (uniqueCells > AIRLimits::cells)
      return zkc::error("air-cell-limit");
  }
  AIRPlan plan(*this, height);
  plan.cells_.reserve(uniqueCells);
  plan.instructionWork = work;
  plan.naiveReads = naive;
  std::map<AIRCell, uint32_t> slots;
  for (uint32_t i = 0; i < constraints_.size(); ++i) {
    auto range = activeRows(constraints_[i].scope, height);
    for (uint32_t row = range.first; row < range.second; ++row) {
      AIRPlan::Invocation invocation{row, i, {}};
      invocation.slots.reserve(facts_[i].readNodes);
      for (const auto &node : constraints_[i].expression) {
        if (node.kind != AIRKind::Read)
          continue;
        AIRCell cell{row + node.offset, node.column};
        auto found = slots.find(cell);
        if (found == slots.end()) {
          if (plan.cells_.size() == AIRLimits::cells)
            return zkc::error("air-cell-limit");
          auto index = uint32_t(plan.cells_.size());
          found = slots.emplace(cell, index).first;
          plan.cells_.push_back(cell);
        }
        invocation.slots.push_back(found->second);
      }
      plan.invocations_.push_back(std::move(invocation));
    }
  }
  return plan;
}
json::Value AIRPlan::encode() const {
  json::Array cells, invocations;
  for (auto cell : cells_)
    cells.push_back(cellJSON(cell));
  for (const auto &call : invocations_) {
    json::Array slots;
    for (auto slot : call.slots)
      slots.push_back(slot);
    invocations.push_back(json::Object{{"row", call.row},
                                       {"constraint", call.constraint},
                                       {"read_slots", std::move(slots)}});
  }
  return json::Object{
      {"schema", "zkc.air.plan.v1"},
      {"height", height},
      {"analysis", relation.analysis()},
      {"dense_trace_cells", uint64_t(height) * relation.columns()},
      {"read_node_fetches", naiveReads},
      {"scheduled_reads", uint64_t(cells_.size())},
      {"instruction_work", instructionWork},
      {"cells", std::move(cells)},
      {"invocations", std::move(invocations)}};
}
Expected<AIREvaluation>
AIRPlan::evaluate(const AIRTraceLayout &layout, ArrayRef<std::string> statement,
                  function_ref<Expected<std::string>(AIRCell)> read) const {
  if (auto error = layoutCheck(relation, height, layout))
    return error;
  if (statement.size() != relation.publicInputs())
    return zkc::error("air-public-shape");
  Field arithmetic(Field::primeModulus(relation.field()));
  std::vector<APInt> publics, cells;
  publics.reserve(statement.size());
  for (const auto &text : statement) {
    auto scalar = arithmetic.parse(text);
    if (!scalar)
      return scalar.takeError();
    publics.push_back(std::move(*scalar));
  }
  cells.reserve(cells_.size());
  for (auto cell : cells_) {
    auto text = read(cell);
    if (!text)
      return text.takeError();
    auto scalar = arithmetic.parse(*text);
    if (!scalar)
      return scalar.takeError();
    cells.push_back(std::move(*scalar));
  }
  // Constants are parsed once per expression, not once per active row.
  std::vector<std::vector<APInt>> constants;
  for (const auto &c : relation.constraints()) {
    std::vector<APInt> values;
    for (const auto &n : c.expression) {
      if (n.kind != AIRKind::Constant)
        continue;
      auto scalar = arithmetic.parse(n.value);
      if (!scalar)
        return scalar.takeError();
      values.push_back(std::move(*scalar));
    }
    constants.push_back(std::move(values));
  }
  APInt modulus(arithmetic.zero().getBitWidth(),
                Field::primeModulus(relation.field()), 10);
  AIREvaluation result;
  result.scheduledReads = cells_.size();
  result.residuals.reserve(invocations_.size());
  std::vector<APInt> values;
  for (const auto &call : invocations_) {
    values.clear();
    const auto &nodes = relation.constraints()[call.constraint].expression;
    values.reserve(nodes.size());
    uint32_t readIndex = 0, constantIndex = 0;
    for (const auto &n : nodes) {
      switch (n.kind) {
      case AIRKind::Constant:
        values.push_back(constants[call.constraint][constantIndex++]);
        break;
      case AIRKind::Public:
        values.push_back(publics[n.index]);
        break;
      case AIRKind::Read:
        values.push_back(cells[call.slots[readIndex++]]);
        break;
      case AIRKind::Add:
        values.push_back(arithmetic.add(values[n.lhs], values[n.rhs]));
        break;
      case AIRKind::Mul:
        values.push_back(arithmetic.mul(values[n.lhs], values[n.rhs]));
        break;
      case AIRKind::Neg:
        values.push_back(values[n.lhs].isZero() ? arithmetic.zero()
                                                : modulus - values[n.lhs]);
        break;
      }
    }
    result.satisfied &= values.back().isZero();
    result.residuals.push_back(
        {call.row, call.constraint, Field::print(values.back())});
  }
  return result;
}
Expected<AIREvaluation>
AIRPlan::evaluate(const AIRTrace &trace,
                  ArrayRef<std::string> statement) const {
  if (auto error = layoutCheck(relation, height, trace.layout))
    return error;
  uint64_t count = uint64_t(height) * relation.columns();
  if (count > AIRLimits::cells)
    return zkc::error("air-cell-limit");
  if (trace.cells.size() != count)
    return zkc::error("air-trace-layout");
  Field arithmetic(Field::primeModulus(relation.field()));
  for (const auto &text : trace.cells) {
    auto scalar = arithmetic.parse(text);
    if (!scalar)
      return scalar.takeError();
  }
  return evaluate(
      trace.layout, statement, [&](AIRCell cell) -> Expected<std::string> {
        return trace.cells[size_t(cell.row) * relation.columns() + cell.column];
      });
}
Expected<AIREvaluation> AIR::evaluate(const AIRTrace &trace,
                                      ArrayRef<std::string> statement) const {
  auto plan = compile(trace.layout.height);
  if (!plan)
    return plan.takeError();
  return plan->evaluate(trace, statement);
}
json::Value AIREvaluation::encode() const {
  json::Array values;
  for (const auto &r : residuals)
    values.push_back(json::Object{
        {"row", r.row}, {"constraint", r.constraint}, {"value", r.value}});
  return json::Object{{"satisfied", satisfied},
                      {"scheduled_reads", scheduledReads},
                      {"residuals", std::move(values)}};
}

namespace {
bool keys(const json::Object &object, ArrayRef<StringRef> required,
          ArrayRef<StringRef> optional = {}) {
  for (auto key : required)
    if (!object.get(key))
      return false;
  for (const auto &entry : object)
    if (!llvm::is_contained(required, entry.first.str()) &&
        !llvm::is_contained(optional, entry.first.str()))
      return false;
  return true;
}
Expected<uint32_t> number(const json::Object &object, StringRef key,
                          uint32_t limit, StringRef code = "air-json-shape") {
  auto n = object.getInteger(key);
  if (!n || *n < 0)
    return zkc::error("air-json-shape");
  if (uint64_t(*n) > limit)
    return zkc::error(code);
  return uint32_t(*n);
}
Expected<AIRNode> readNode(const json::Value &value) {
  const auto *o = value.getAsObject();
  auto op = o ? o->getString("op") : std::nullopt;
  if (!op)
    return zkc::error("air-json-shape");
  if (*op == "constant") {
    auto text = o->getString("value");
    if (!keys(*o, {"op", "value"}) || !text)
      return zkc::error("air-json-shape");
    if (text->size() > 256)
      return zkc::error("relation-coefficient");
    return AIRNode::constant(text->str());
  }
  if (*op == "public") {
    if (!keys(*o, {"op", "index"}))
      return zkc::error("air-json-shape");
    auto index =
        number(*o, "index", AIRLimits::publicInputs, "air-public-index");
    if (!index)
      return index.takeError();
    return AIRNode::publicInput(*index);
  }
  if (*op == "read") {
    if (!keys(*o, {"op", "offset", "column"}))
      return zkc::error("air-json-shape");
    auto offset = number(*o, "offset", AIRLimits::offset, "air-offset-limit");
    if (!offset)
      return offset.takeError();
    auto column = number(*o, "column", AIRLimits::columns, "air-column");
    if (!column)
      return column.takeError();
    return AIRNode::read(*offset, *column);
  }
  if (*op == "neg") {
    if (!keys(*o, {"op", "operand"}))
      return zkc::error("air-json-shape");
    auto operand =
        number(*o, "operand", AIRLimits::nodes, "air-node-reference");
    if (!operand)
      return operand.takeError();
    return AIRNode::neg(*operand);
  }
  if (*op == "add" || *op == "mul") {
    if (!keys(*o, {"op", "lhs", "rhs"}))
      return zkc::error("air-json-shape");
    auto lhs = number(*o, "lhs", AIRLimits::nodes, "air-node-reference");
    if (!lhs)
      return lhs.takeError();
    auto rhs = number(*o, "rhs", AIRLimits::nodes, "air-node-reference");
    if (!rhs)
      return rhs.takeError();
    return *op == "add" ? AIRNode::add(*lhs, *rhs) : AIRNode::mul(*lhs, *rhs);
  }
  return zkc::error("air-unsupported-operation");
}
Expected<AIRScope> readScope(const json::Object *o) {
  auto kind = o ? o->getString("kind") : std::nullopt;
  if (!kind)
    return zkc::error("air-scope");
  if (*kind == "transition") {
    if (!keys(*o, {"kind", "lookahead"}))
      return zkc::error("air-scope");
    auto lookahead =
        number(*o, "lookahead", AIRLimits::offset, "air-offset-limit");
    if (!lookahead)
      return lookahead.takeError();
    return AIRScope{AIRScopeKind::Transition, *lookahead};
  }
  if (!keys(*o, {"kind"}))
    return zkc::error("air-scope");
  if (*kind == "every")
    return AIRScope{AIRScopeKind::Every, 0};
  if (*kind == "first")
    return AIRScope{AIRScopeKind::First, 0};
  if (*kind == "last")
    return AIRScope{AIRScopeKind::Last, 0};
  return zkc::error("air-scope");
}
} // namespace

Expected<AIR> readAIR(const json::Value &value) {
  auto *o = value.getAsObject();
  if (!o ||
      !keys(*o,
            {"schema", "field", "columns", "public_inputs", "constraints"}) ||
      o->getString("schema") != "zkc.air.v1")
    return zkc::error("air-json-shape");
  auto field = o->getString("field");
  if (!field || Field::primeModulus(*field).empty())
    return zkc::error("air-field");
  auto columns =
      number(*o, "columns", AIRLimits::columns, "air-dimension-limit");
  if (!columns)
    return columns.takeError();
  auto publics = number(*o, "public_inputs", AIRLimits::publicInputs,
                        "air-dimension-limit");
  if (!publics)
    return publics.takeError();
  auto *array = o->getArray("constraints");
  if (!array)
    return zkc::error("air-json-shape");
  if (array->size() > AIRLimits::constraints)
    return zkc::error("air-constraint-limit");
  // Counts across every expression are checked before allocating native nodes.
  size_t count = 0;
  for (const auto &entry : *array) {
    auto *c = entry.getAsObject();
    auto *nodes = c ? c->getArray("nodes") : nullptr;
    if (!c ||
        !keys(*c, {"scope", "nodes"},
              {"declared_max_offset", "declared_degree"}) ||
        !nodes)
      return zkc::error("air-json-shape");
    if (nodes->size() > AIRLimits::nodes - count)
      return zkc::error("air-node-limit");
    count += nodes->size();
  }
  std::vector<AIRConstraint> constraints;
  constraints.reserve(array->size());
  for (const auto &entry : *array) {
    auto *c = entry.getAsObject();
    auto scope = readScope(c->getObject("scope"));
    if (!scope)
      return scope.takeError();
    AIRConstraint constraint{*scope, {}, std::nullopt, std::nullopt};
    for (auto key : {"declared_max_offset", "declared_degree"}) {
      if (!c->get(key))
        continue;
      auto bound =
          number(*c, key,
                 StringRef(key) == "declared_degree" ? AIRLimits::degree
                                                     : AIRLimits::offset,
                 "air-declaration-limit");
      if (!bound)
        return bound.takeError();
      (StringRef(key) == "declared_degree" ? constraint.declaredDegree
                                           : constraint.declaredMaxOffset) =
          *bound;
    }
    auto *nodes = c->getArray("nodes");
    constraint.expression.reserve(nodes->size());
    for (const auto &node : *nodes) {
      auto n = readNode(node);
      if (!n)
        return n.takeError();
      constraint.expression.push_back(std::move(*n));
    }
    constraints.push_back(std::move(constraint));
  }
  return AIR::create(field->str(), *columns, *publics, std::move(constraints));
}
Expected<json::Value> readAIRJson(StringRef text) {
  if (text.size() > AIRLimits::bytes)
    return zkc::error("air-byte-limit");
  // The arena codec has shallow JSON even for deep arithmetic. This preflight
  // avoids recursive-parser exhaustion and duplicate-key last-writer behavior.
  struct Level {
    char opener;
    std::set<std::string> keys;
  };
  std::vector<Level> stack;
  auto space = [](char c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
  };
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (c == '"') {
      size_t start = i++;
      while (i < text.size() && text[i] != '"') {
        if (text[i] == '\\')
          ++i;
        ++i;
      }
      if (i >= text.size())
        return zkc::error("air-invalid-json");
      StringRef spelling = text.slice(start, i + 1);
      if (spelling.size() > 258)
        return zkc::error("air-string-limit");
      if (!zkc::validStringEncoding(spelling))
        return zkc::error("air-invalid-json");
      size_t next = i + 1;
      while (next < text.size() && space(text[next]))
        ++next;
      if (next < text.size() && text[next] == ':' && !stack.empty() &&
          stack.back().opener == '{') {
        auto key = json::parse(spelling);
        if (!key) {
          consumeError(key.takeError());
          return zkc::error("air-invalid-json");
        }
        if (!stack.back().keys.insert(key->getAsString()->str()).second)
          return zkc::error("air-duplicate-key");
      }
    } else if (c == '[' || c == '{') {
      if (stack.size() == 16)
        return zkc::error("air-json-depth-limit");
      stack.push_back({c, {}});
    } else if (c == ']' || c == '}') {
      if (stack.empty() || stack.back().opener != (c == ']' ? '[' : '{'))
        return zkc::error("air-invalid-json");
      stack.pop_back();
    } else if (c >= '0' && c <= '9') {
      size_t start = i;
      while (i + 1 < text.size() && text[i + 1] >= '0' && text[i + 1] <= '9')
        ++i;
      if (i - start >= 10 || (i > start && c == '0') ||
          (i + 1 < text.size() &&
           (text[i + 1] == '.' || text[i + 1] == 'e' || text[i + 1] == 'E')))
        return zkc::error("air-invalid-json");
    } else if (c == '-' || c == '.' || c == '+') {
      return zkc::error("air-invalid-json");
    }
  }
  auto parsed = json::parse(text);
  if (!parsed) {
    consumeError(parsed.takeError());
    return zkc::error("air-invalid-json");
  }
  return std::move(*parsed);
}
Expected<AIR> readAIRText(StringRef text) {
  auto json = readAIRJson(text);
  if (!json)
    return json.takeError();
  return readAIR(*json);
}
Expected<AIRTrace> readAIRTrace(const json::Value &value) {
  auto *o = value.getAsObject();
  if (!o || !keys(*o, {"field", "height", "columns", "cells"}))
    return zkc::error("air-json-shape");
  auto field = o->getString("field");
  if (!field || Field::primeModulus(*field).empty())
    return zkc::error("air-field");
  auto height = number(*o, "height", AIRLimits::height, "air-height");
  if (!height)
    return height.takeError();
  if (!*height)
    return zkc::error("air-height");
  auto columns =
      number(*o, "columns", AIRLimits::columns, "air-dimension-limit");
  if (!columns)
    return columns.takeError();
  uint64_t count = uint64_t(*height) * *columns;
  if (count > AIRLimits::cells)
    return zkc::error("air-cell-limit");
  auto *cells = o->getArray("cells");
  if (!cells || cells->size() != count)
    return zkc::error("air-trace-layout");
  Field arithmetic(Field::primeModulus(*field));
  AIRTrace trace{{field->str(), *height, *columns}, {}};
  trace.cells.reserve(count);
  for (const auto &cell : *cells) {
    auto text = cell.getAsString();
    if (!text)
      return zkc::error("air-json-shape");
    auto scalar = arithmetic.parse(*text);
    if (!scalar)
      return scalar.takeError();
    trace.cells.push_back(text->str());
  }
  return trace;
}
} // namespace zkc::relation
