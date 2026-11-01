#include "NumericalPlan.h"
#include "mlir/Analysis/Liveness.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ResidueArithmetic.h"
#include "zkc/Analysis/ResidueTile.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Residue.h"
#include "llvm/ADT/SmallString.h"
#include <functional>

using namespace mlir;
using namespace llvm;
namespace zkc::target {
namespace {
std::string maskText(DenseBoolArrayAttr mask) {
  std::string result;
  for (bool row : mask.asArrayRef())
    result.push_back(row ? '1' : '0');
  return result;
}
// Deterministic conservative size units, not an estimate of processor time.
// Formation bounds precede serialization and allocation. Width and lane factors
// bound the expanded scalar/tile problem; every transaction keeps its debit.
Expected<uint64_t> workUnits(algebra::FieldType field,
                             algebra::RingExpressionAttr expression,
                             unsigned lanes) {
  if (!field || !expression || !lanes ||
      lanes > protocol::NumericalLimits::lanes)
    return error("numerical-plan-shape");
  if (expression.getInputs().size() > protocol::NumericalLimits::slots ||
      expression.getNodes().size() > protocol::NumericalLimits::bodyBytes)
    return error("numerical-plan-bytes");
  const auto *domain = protocol::installedDomains().domain(field.getDomain());
  APInt modulus;
  unsigned bytes = 1;
  if (domain && !StringRef(domain->modulus).getAsInteger(10, modulus))
    bytes += llvm::divideCeil(modulus.getActiveBits(), 8u);
  return uint64_t(1 + expression.getInputs().size() +
                  expression.getNodes().size()) *
         (lanes + 1) * bytes;
}
bool debit(uint64_t &remaining, uint64_t amount) {
  if (amount > remaining)
    return false;
  remaining -= amount;
  return true;
}
residue::ValueType residueType(algebra::FieldType field) {
  const auto &catalog = protocol::installedDomains();
  StringRef name = field.getDomain();
  if (!catalog.hasFact("PrimeField", {name.str()}))
    return {};
  const auto *domain = catalog.domain(name);
  APInt modulus;
  if (!domain || StringRef(domain->modulus).getAsInteger(10, modulus) ||
      modulus.ult(2))
    return {};
  unsigned bits = llvm::alignTo(modulus.getActiveBits(), 8);
  if (bits > residue::MaximumWordWidth)
    return {};
  auto word = IntegerType::get(field.getContext(), bits, IntegerType::Unsigned);
  field.getContext()->getOrLoadDialect<residue::ResidueDialect>();
  return residue::ValueType::get(
      field.getContext(), IntegerAttr::get(word, modulus.zextOrTrunc(bits)));
}
/// Mathematical domain transport, not optimization. The installed PrimeField
/// fact supplies the exact canonical representative relation; no codec or
/// resident storage layout is inferred from the characteristic.
OwningOpRef<ModuleOp> residueSubject(const ring::Expression &expression,
                                     residue::ValueType type) {
  auto location = UnknownLoc::get(type.getContext());
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  OpBuilder builder(module->getBodyRegion());
  auto signature = builder.getFunctionType(
      SmallVector<Type>(expression.inputs().size(), type), {type});
  auto function =
      func::FuncOp::create(builder, location, "pointwise", signature);
  auto *block = function.addEntryBlock();
  builder.setInsertionPointToEnd(block);
  auto literal = [&](StringRef text) -> Value {
    APInt value(type.getWidth(), text, 10);
    auto attr = residue::LiteralAttr::get(
        type.getContext(), type,
        IntegerAttr::get(type.getModulus().getType(), value));
    return residue::ResidueConstantOp::create(builder, location, type, attr);
  };
  SmallVector<Value> values;
  for (const auto &node : expression.nodes()) {
    Value value;
    switch (node.kind) {
    case ring::Kind::Input:
      value = block->getArgument(node.input);
      break;
    case ring::Kind::Constant:
      value = literal(node.constant);
      break;
    case ring::Kind::Add:
      value = residue::ResidueAddOp::create(
          builder, location, type, values[node.left], values[node.right]);
      break;
    case ring::Kind::Mul:
      value = residue::ResidueMultiplyOp::create(
          builder, location, type, values[node.left], values[node.right]);
      break;
    case ring::Kind::Neg:
      value = residue::ResidueSubtractOp::create(
          builder, location, type, literal("0"), values[node.left]);
      break;
    case ring::Kind::Embed:
      return {};
    }
    values.push_back(value);
  }
  func::ReturnOp::create(builder, location, values[expression.outputs()[0]]);
  return module;
}
Expected<ring::Expression> readResidue(ModuleOp module, StringRef field) {
  auto function = *module.getOps<func::FuncOp>().begin();
  auto returned = cast<func::ReturnOp>(function.front().getTerminator());
  std::vector<ring::Node> nodes;
  llvm::DenseMap<Value, unsigned> indices;
  std::function<Expected<unsigned>(Value, unsigned)> visit =
      [&](Value value, unsigned depth) -> Expected<unsigned> {
    if (depth > ring::Limits::depth)
      return error("represented-arithmetic");
    if (auto found = indices.find(value); found != indices.end())
      return found->second;
    ring::Node node;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      node = ring::Node::slot(argument.getArgNumber());
    } else if (auto constant =
                   value.getDefiningOp<residue::ResidueConstantOp>()) {
      SmallString<32> text;
      constant.getValue().getValue().getValue().toString(text, 10, false);
      node = ring::Node::literal(field.str(), text.str().str());
    } else {
      auto *op = value.getDefiningOp();
      if (!op || op->getNumOperands() != 2)
        return error("represented-arithmetic");
      if (isa<residue::ResidueSubtractOp>(op)) {
        auto zero =
            op->getOperand(0).getDefiningOp<residue::ResidueConstantOp>();
        if (!zero || !zero.getValue().getValue().getValue().isZero())
          return error("represented-arithmetic");
        auto operand = visit(op->getOperand(1), depth + 1);
        if (!operand)
          return operand.takeError();
        node = ring::Node::neg(*operand);
      } else {
        auto left = visit(op->getOperand(0), depth + 1);
        if (!left)
          return left.takeError();
        auto right = visit(op->getOperand(1), depth + 1);
        if (!right)
          return right.takeError();
        if (isa<residue::ResidueAddOp>(op))
          node = ring::Node::add(*left, *right);
        else if (isa<residue::ResidueMultiplyOp>(op))
          node = ring::Node::mul(*left, *right);
        else
          return error("represented-arithmetic");
      }
    }
    unsigned id = nodes.size();
    nodes.push_back(std::move(node));
    indices.try_emplace(value, id);
    return id;
  };
  auto root = visit(returned.getOperand(0), 0);
  if (!root)
    return root.takeError();
  return ring::Expression::create(
      std::vector<ring::Input>(function.getNumArguments(), {field.str()}),
      std::move(nodes), {*root});
}

/// Build the actual two-phase evaluation order in SSA, then use standard MLIR
/// liveness to propose storage reuse. Independent admission uses symbolic slot
/// owners instead. Nothing in this scheduling module is executable authority.
Expected<protocol::NumericalPlan> schedule(ring::Expression expression,
                                           algebra::FieldType field,
                                           DenseBoolArrayAttr mask,
                                           unsigned lanes) {
  const size_t count = expression.nodes().size();
  SmallVector<bool> varying(count), persistent(count);
  for (auto [id, node] : enumerate(expression.nodes())) {
    switch (node.kind) {
    case ring::Kind::Input:
      varying[id] = mask[node.input];
      break;
    case ring::Kind::Add:
    case ring::Kind::Mul:
      varying[id] = varying[node.left] || varying[node.right];
      break;
    case ring::Kind::Neg:
      varying[id] = varying[node.left];
      break;
    default:
      break;
    }
  }
  unsigned root = expression.outputs()[0];
  persistent[root] = !varying[root];
  for (auto [id, node] : enumerate(expression.nodes()))
    if (varying[id]) {
      if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul)
        persistent[node.right] = persistent[node.right] || !varying[node.right];
      if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul ||
          node.kind == ring::Kind::Neg)
        persistent[node.left] = persistent[node.left] || !varying[node.left];
    }
  auto location = UnknownLoc::get(field.getContext());
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  OpBuilder builder(module->getBodyRegion());
  auto function = func::FuncOp::create(
      builder, location, "schedule",
      builder.getFunctionType(SmallVector<Type>(mask.size(), field), {field}));
  auto *block = function.addEntryBlock();
  builder.setInsertionPointToEnd(block);
  auto literal = [&](StringRef value) -> Expected<Value> {
    auto attr = algebra::decodeFieldLiteral(field, value);
    if (!attr)
      return attr.takeError();
    return Value(
        algebra::ConstantFieldOp::create(builder, location, field, *attr));
  };
  auto zero = literal("0");
  if (!zero)
    return zero.takeError();
  SmallVector<Value> values(count);
  SmallVector<unsigned> order;
  for (bool phase : {false, true})
    for (auto [id, node] : enumerate(expression.nodes())) {
      if (varying[id] != phase)
        continue;
      Value value;
      switch (node.kind) {
      case ring::Kind::Input:
        // Distinct loads of the same operand remain distinct plan nodes.
        value = algebra::FieldAddOp::create(
            builder, location, field, block->getArgument(node.input), *zero);
        break;
      case ring::Kind::Constant: {
        auto constant = literal(node.constant);
        if (!constant)
          return constant.takeError();
        value = *constant;
        break;
      }
      case ring::Kind::Add:
        value = algebra::FieldAddOp::create(
            builder, location, field, values[node.left], values[node.right]);
        break;
      case ring::Kind::Mul:
        value = algebra::FieldMultiplyOp::create(
            builder, location, field, values[node.left], values[node.right]);
        break;
      case ring::Kind::Neg:
        value = algebra::SubtractFieldOp::create(builder, location, field,
                                                 *zero, values[node.left]);
        break;
      case ring::Kind::Embed:
        return error("numerical-body-field");
      }
      values[id] = value;
      order.push_back(id);
    }
  func::ReturnOp::create(builder, location, values[root]);
  if (failed(verify(*module)))
    return error("numerical-plan-schedule");
  Liveness liveness(function);
  std::vector<unsigned> locations(count);
  std::vector<std::optional<unsigned>> owners;
  for (unsigned id : order) {
    auto *current = values[id].getDefiningOp();
    for (auto &owner : owners)
      if (owner && !persistent[*owner] &&
          liveness.isDeadAfter(values[*owner], current))
        owner.reset();
    auto vacant = llvm::find(owners, std::nullopt);
    unsigned slot = std::distance(owners.begin(), vacant);
    if (vacant == owners.end())
      owners.push_back(id);
    else
      *vacant = id;
    locations[id] = slot;
  }
  protocol::NumericalPlan plan{std::move(expression), lanes,
                               unsigned(owners.size()), std::move(locations)};
  if (auto e =
          protocol::checkNumericalPlan(plan, field.getDomain(), maskText(mask)))
    return std::move(e);
  return plan;
}
} // namespace
Expected<runtime::NumericalPlanAttr>
NumericalPlanProposals::propose(algebra::FieldType field,
                                algebra::RingExpressionAttr expression,
                                DenseBoolArrayAttr mask, unsigned lanes) {
  auto units = workUnits(field, expression, lanes);
  if (!units)
    return units.takeError();
  if (!mask)
    return error("numerical-plan-shape");
  if (!debit(remaining, 1))
    return error("represented-construction-limit");
  auto *context = field.getContext();
  auto key = ArrayAttr::get(
      context, {TypeAttr::get(field), expression, mask,
                IntegerAttr::get(IntegerType::get(context, 32), lanes)});
  if (auto found = proposals.find(key); found != proposals.end())
    return found->second;
  if (!debit(remaining, *units))
    return error("represented-construction-limit");
  auto candidate = proposeNumericalPlan(field, expression, mask, lanes);
  if (!candidate)
    return candidate.takeError();
  proposals.try_emplace(key, *candidate);
  return *candidate;
}
Expected<runtime::NumericalPlanAttr>
proposeNumericalPlan(algebra::FieldType field,
                     algebra::RingExpressionAttr subject,
                     DenseBoolArrayAttr mask, unsigned lanes) {
  if (!field || !subject || !mask || !lanes ||
      lanes > protocol::NumericalLimits::lanes)
    return error("numerical-plan-shape");
  field.getContext()->getOrLoadDialect<runtime::RuntimeDialect>();
  auto source = algebra::exportRingExpression(subject);
  if (!source)
    return source.takeError();
  // A fresh-slot plan supplies bounded formation checking before any MLIR work.
  protocol::NumericalPlan admission{
      *source, lanes, unsigned(source->nodes().size()), {}};
  for (unsigned i = 0; i < source->nodes().size(); ++i)
    admission.locations.push_back(i);
  if (auto e = protocol::checkNumericalPlan(admission, field.getDomain(),
                                            maskText(mask)))
    return std::move(e);
  auto actual = *source;
  auto type = residueType(field);
  // Selection by the declared profile, before attempting a candidate. Refusal
  // within the chosen profile is terminal; there is no error-driven fallback.
  if (type && source->inputs().size() <= 256) {
    auto *context = field.getContext();
    context->getOrLoadDialect<residue::ResidueDialect>();
    auto scalar = residueSubject(*source, type);
    auto tile = residue::proposeTile(*scalar, mask.asArrayRef(), lanes);
    auto read = tile ? residue::readTile(*scalar, mask.asArrayRef(), *tile)
                     : std::nullopt;
    if (!read)
      return error("represented-tile");
    auto expression = readResidue(*read->scalar, field.getDomain());
    if (!expression)
      return expression.takeError();
    actual = std::move(*expression);
    lanes = read->lanes;
  }
  auto plan = schedule(std::move(actual), field, mask, lanes);
  if (!plan)
    return plan.takeError();
  return runtime::importNumericalPlan(field.getContext(), *plan);
}
Error NumericalPlanChecks::check(algebra::FieldType field,
                                 algebra::RingExpressionAttr source,
                                 DenseBoolArrayAttr mask,
                                 runtime::NumericalPlanAttr candidate) {
  if (!field || !source || !mask || !candidate)
    return error("numerical-plan-shape");
  if (!debit(remaining, 1))
    return error("represented-checking-limit");
  auto key = ArrayAttr::get(field.getContext(),
                            {TypeAttr::get(field), source, mask, candidate});
  if (accepted.contains(key))
    return Error::success();
  if (auto e = verifyNumericalPlan(field, source, mask, candidate, &remaining))
    return e;
  accepted.insert(key);
  return Error::success();
}
Error verifyNumericalPlan(algebra::FieldType field,
                          algebra::RingExpressionAttr subject,
                          DenseBoolArrayAttr mask,
                          runtime::NumericalPlanAttr candidate,
                          uint64_t *remaining) {
  if (!field || !subject || !mask || !candidate)
    return error("numerical-plan-shape");
  uint64_t local = NumericalCheckingWork;
  auto sourceUnits = workUnits(field, subject, 1);
  auto candidateUnits = workUnits(field, candidate.getExpression(), 1);
  if (!sourceUnits)
    return sourceUnits.takeError();
  if (!candidateUnits)
    return candidateUnits.takeError();
  if (!debit(remaining ? *remaining : local, *sourceUnits + *candidateUnits))
    return error("represented-checking-limit");
  auto plan = runtime::exportNumericalPlan(candidate);
  if (!plan)
    return plan.takeError();
  if (auto e = protocol::checkNumericalPlan(*plan, field.getDomain(),
                                            maskText(mask)))
    return e;
  if (candidate.getExpression() == subject)
    return Error::success();
  auto source = algebra::exportRingExpression(subject);
  if (!source)
    return source.takeError();
  protocol::NumericalPlan formation{
      *source, 1, unsigned(source->nodes().size()), {}};
  for (unsigned i = 0; i < source->nodes().size(); ++i)
    formation.locations.push_back(i);
  if (auto e = protocol::checkNumericalPlan(formation, field.getDomain(),
                                            maskText(mask)))
    return e;
  auto type = residueType(field);
  if (!type || source->inputs().size() > 256)
    return error("represented-arithmetic");
  // Both mathematical subjects are read, not lowered or optimized to obtain an
  // expected producer output. This also accepts safe alternative plans.
  auto left = residueSubject(*source, type);
  auto right = residueSubject(plan->expression, type);
  if (failed(residue::verifyResidue(*left, *right)))
    return error("represented-arithmetic");
  return Error::success();
}
} // namespace zkc::target
