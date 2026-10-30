#include "OracleQueryBlocks.h"
#include "OracleLayout.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
Error charge(unsigned &remaining) {
  if (!remaining)
    return error("oracle-query-block-limit");
  --remaining;
  return Error::success();
}
Expected<Value> origin(Value value, unsigned &remaining) {
  while (value) {
    if (auto e = charge(remaining))
      return std::move(e);
    if (auto view = value.getDefiningOp<pir::RestrictRolesOp>())
      value = view.getInput();
    else if (auto view = value.getDefiningOp<pir::OracleForgetShapeOp>())
      value = view.getInput();
    else if (auto arg = dyn_cast<BlockArgument>(value)) {
      auto loop = dyn_cast<pir::RepeatOp>(arg.getOwner()->getParentOp());
      if (!loop || arg.getArgNumber() <= uint64_t(loop.getCarried()))
        break;
      value = loop.getInputs()[arg.getArgNumber()];
    } else
      break;
  }
  return value;
}
Expected<std::optional<uint64_t>> literal(Value value, unsigned &remaining) {
  auto source = origin(value, remaining);
  if (!source)
    return source.takeError();
  if (auto constant = source->getDefiningOp<data::IndexOp>())
    return std::optional<uint64_t>(constant.getValue());
  return std::optional<uint64_t>();
}
Expected<std::vector<unsigned>> path(Operation *operation,
                                     unsigned &remaining) {
  std::vector<unsigned> result;
  while (operation && !isa<pir::MathematicalOp>(operation)) {
    if (result.size() >= 64)
      return error("oracle-query-block-limit");
    unsigned position = 0;
    for (auto &sibling : *operation->getBlock()) {
      if (auto e = charge(remaining))
        return std::move(e);
      if (&sibling == operation)
        break;
      ++position;
    }
    result.push_back(position);
    operation = operation->getParentOp();
  }
  if (!operation)
    return error("oracle-query-block-source");
  std::reverse(result.begin(), result.end());
  return result;
}
} // namespace
Expected<std::optional<OracleDirectQuery>>
admitOracleDirectQuery(pir::OracleQueryOp query,
                       const OracleAnchorStorage &storage,
                       unsigned &remaining) {
  auto anchor = origin(query.getHandle(), remaining);
  auto position = origin(query.getPosition(), remaining);
  if (!anchor)
    return anchor.takeError();
  if (!position)
    return position.takeError();
  auto *definition = anchor->getDefiningOp();
  if (!definition || !isa<pir::OracleSendOp, pir::OracleInputOp>(definition))
    return std::optional<OracleDirectQuery>();
  auto location = path(definition, remaining);
  if (!location)
    return location.takeError();
  unsigned ordinal = 0;
  for (; ordinal < storage.constructors.size(); ++ordinal) {
    if (auto e = charge(remaining))
      return std::move(e);
    if (storage.constructors[ordinal].path == *location)
      break;
  }
  if (ordinal == storage.constructors.size())
    return std::optional<OracleDirectQuery>(); // component rebinding
  const auto &constructor = storage.constructors[ordinal];
  if (constructor.kind.getIdentity() != "table" || constructor.scheme.empty() ||
      constructor.holder == *query.getOwner())
    return std::optional<OracleDirectQuery>();
  auto dimensions = constructor.kind.getShapeDimensions();
  if (dimensions.size() != 1 || dimensions.front().name != "rows")
    return std::optional<OracleDirectQuery>();
  std::optional<uint64_t> rows = dimensions.front().extent;
  if (!rows)
    if (auto send = dyn_cast<pir::OracleSendOp>(definition)) {
      auto value = literal(send.getShapeOperand("rows"), remaining);
      if (!value)
        return value.takeError();
      rows = *value;
    }
  if (!rows || !*rows)
    return std::optional<OracleDirectQuery>();
  auto constant = literal(*position, remaining);
  if (!constant)
    return constant.takeError();
  bool valid = *constant && **constant < *rows;
  if (!valid)
    if (auto draw = position->getDefiningOp<pir::QueryOp>()) {
      if (draw.getMethod() == "index" && draw.getOwner() == *query.getOwner() &&
          draw.getInputs().size() == 1) {
        auto bound = literal(draw.getInputs().front(), remaining);
        if (!bound)
          return bound.takeError();
        valid = *bound && **bound > 0 && **bound <= *rows;
      }
    }
  if (!valid)
    return std::optional<OracleDirectQuery>();
  return std::optional<OracleDirectQuery>(
      {query, ordinal, *anchor, *position, *rows, *constant});
}
Expected<bool> shareOracleOpening(const OracleDirectQuery &left,
                                  const OracleDirectQuery &right,
                                  ArrayRef<OracleTableRealization> choices) {
  if (left.anchor != right.anchor || left.constructor != right.constructor ||
      left.rows != right.rows)
    return false;
  if (left.position == right.position)
    return true;
  if (!left.literal || !right.literal)
    return false;
  const auto &choice = choices[left.constructor];
  auto layout =
      OracleTableLayout::create(left.rows, choice.grouping, choice.order);
  if (!layout)
    return layout.takeError();
  auto a = layout->locate(*left.literal), b = layout->locate(*right.literal);
  if (!a)
    return a.takeError();
  if (!b)
    return b.takeError();
  return a->leaf == b->leaf;
}
} // namespace zkc::protocol
