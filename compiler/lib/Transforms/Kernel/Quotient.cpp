#ifdef ZKC_ENABLE_HEIR
#include "Quotient.h"
#include "lib/Dialect/ModArith/IR/ModArithDialect.h"
#include "lib/Dialect/ModArith/IR/ModArithOps.h"
#include "lib/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "lib/Dialect/Polynomial/IR/PolynomialOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace poly = mlir::heir::polynomial;
namespace modular = mlir::heir::mod_arith;
namespace zkc::kernel {
namespace {
Value create(OpBuilder &builder, Location loc, StringRef name, Type result,
             ValueRange operands) {
  OperationState state(loc, name);
  state.addTypes(result);
  state.addOperands(operands);
  return builder.create(state)->getResult(0);
}
OwningOpRef<mlir::ModuleOp>
importQuotient(func::FuncOp source, const heir::ArithmeticMeaning &meaning) {
  auto *context = source.getContext();
  context->getOrLoadDialect<poly::PolynomialDialect>();
  context->getOrLoadDialect<modular::ModArithDialect>();
  OpBuilder builder(context);
  auto loc = source.getLoc();
  OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(loc));
  auto scalar = modular::ModArithType::get(
      context, builder.getI32IntegerAttr(meaning.modulus));
  poly::IntPolynomial modulus(
      {poly::IntMonomial(1, 0), poly::IntMonomial(1, meaning.degree)});
  auto ring = poly::RingAttr::get(
      scalar, poly::IntPolynomialAttr::get(context, modulus));
  auto polynomial = poly::PolynomialType::get(context, ring);
  auto raw =
      RankedTensorType::get({int64_t(meaning.degree)}, builder.getI32Type());
  auto coefficients = RankedTensorType::get({int64_t(meaning.degree)}, scalar);
  SmallVector<Type> inputs(meaning.inputs, raw),
      outputs(meaning.outputs.size(), raw);
  builder.setInsertionPointToEnd(module->getBody());
  auto function = func::FuncOp::create(
      builder, loc, "compute", builder.getFunctionType(inputs, outputs));
  auto *body = function.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  llvm::DenseMap<Value, Value> values;
  for (auto [input, argument] :
       zip(source.getArguments(), body->getArguments())) {
    auto wrapped =
        create(builder, loc, modular::EncapsulateOp::getOperationName(),
               coefficients, {argument});
    values[input] = create(builder, loc, poly::FromTensorOp::getOperationName(),
                           polynomial, {wrapped});
  }
  for (auto &op : source.front().without_terminator()) {
    auto left = values.lookup(op.getOperand(0));
    Value value;
    if (isa<algebra::ProjectQuotientOp, algebra::ObserveQuotientOp>(op))
      value = left;
    else {
      auto name = isa<algebra::AddQuotientOp>(op)
                      ? poly::AddOp::getOperationName()
                  : isa<algebra::SubtractQuotientOp>(op)
                      ? poly::SubOp::getOperationName()
                      : poly::MulOp::getOperationName();
      value = create(builder, op.getLoc(), name, polynomial,
                     {left, values.lookup(op.getOperand(1))});
    }
    values[op.getResult(0)] = value;
  }
  SmallVector<Value> returned;
  for (Value result : source.front().back().getOperands()) {
    auto tensor = create(builder, loc, poly::ToTensorOp::getOperationName(),
                         coefficients, {values.lookup(result)});
    auto lift = modular::LiftOp::create(builder, loc, raw, tensor,
                                        modular::LiftType::STANDARD);
    returned.push_back(lift.getResult());
  }
  func::ReturnOp::create(builder, loc, returned);
  return module;
}

// Construct a private executable recipe. All outputs and binding declarations
// are owned by this module until the independent source/native reader succeeds.
OwningOpRef<mlir::ModuleOp> lowerPlaced(func::FuncOp source,
                                        mlir::ModuleOp placed,
                                        const heir::ArithmeticMeaning &meaning,
                                        StringRef rootSite) {
  auto function = cast<func::FuncOp>(placed.getBody()->front());
  auto *context = source.getContext();
  auto loc = source.getLoc();
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(loc));
  OpBuilder builder(result->getBody(), result->getBody()->end());
  auto target =
      func::FuncOp::create(builder, loc, "compute", source.getFunctionType());
  auto *body = target.addEntryBlock();
  builder.setInsertionPointToEnd(body);
  auto indices = algebra::IndicesType::get(context);
  auto index = builder.getIntegerType(64, false);
  unsigned ordinal = 0;
  std::map<std::string, FlatSymbolRefAttr> bindings;
  auto emit = [&](StringRef contract, Type output, ValueRange args,
                  ArrayRef<std::string> parameters = {}) {
    auto &binding = bindings[contract.str()];
    if (!binding) {
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPoint(target);
      auto name = "binding_" + std::to_string(bindings.size());
      local::OperationBindingOp::create(builder, loc, name, contract,
                                        builder.getArrayAttr({}), "");
      binding = FlatSymbolRefAttr::get(context, name);
    }
    OperationState state(loc, protocol::boundOperationName(contract));
    state.addOperands(args);
    state.addTypes(output);
    state.addAttribute("binding", binding);
    SmallVector<Attribute> attrs;
    for (const auto &parameter : parameters)
      attrs.push_back(builder.getStringAttr(parameter));
    state.addAttribute("parameters", builder.getArrayAttr(attrs));
    auto suffix = ordinal ? "value_" + std::to_string(ordinal) : "begin";
    ++ordinal;
    state.addAttribute(
        "site", builder.getStringAttr(rootSite + "_recipe_quotient_" + suffix));
    return builder.create(state)->getResult(0);
  };
  std::map<uint64_t, Value> constants;
  auto constant = [&](uint64_t value) {
    auto &stored = constants[value];
    if (!stored)
      stored = emit("index.constant", index, {}, {std::to_string(value)});
    return stored;
  };
  auto q = constant(meaning.modulus);
  auto n = constant(meaning.degree);
  llvm::DenseMap<Value, Value> values;
  for (auto [input, argument] :
       zip(function.getArguments(), target.getArguments()))
    values[input] = emit("quotient.project", indices, {argument, q, n});
  for (auto &op : function.front().without_terminator()) {
    auto left = values.lookup(op.getOperand(0));
    Value value;
    if (isa<modular::EncapsulateOp, modular::LiftOp, poly::FromTensorOp,
            poly::ToTensorOp>(op)) {
      value = left;
    } else if (isa<poly::NTTOp, poly::INTTOp>(op)) {
      auto root = op.getAttrOfType<poly::PrimitiveRootAttr>("root");
      auto rootValue = cast<modular::ModArithAttr>(root.getValue())
                           .getValue()
                           .getValue()
                           .getZExtValue();
      value = emit(isa<poly::NTTOp>(op) ? "quotient.ntt" : "quotient.intt",
                   indices, {left, q, constant(rootValue)});
    } else {
      auto output = cast<poly::PolynomialType>(op.getResult(0).getType());
      StringRef contract = isa<poly::AddOp>(op)   ? "quotient.add"
                           : isa<poly::SubOp>(op) ? "quotient.subtract"
                           : output.getForm() == poly::Form::EVAL
                               ? "quotient.pointwise"
                               : "quotient.multiply";
      value =
          emit(contract, indices, {left, values.lookup(op.getOperand(1)), q});
    }
    values[op.getResult(0)] = value;
  }
  SmallVector<Value> outputs;
  llvm::DenseMap<Value, std::string> labels;
  for (auto [position, operand] :
       enumerate(function.front().back().getOperands())) {
    auto value = values.lookup(operand);
    outputs.push_back(value);
    auto &label = labels[value];
    label += "_" + std::to_string(position);
  }
  for (auto [value, label] : labels)
    value.getDefiningOp()->setAttr(
        "site",
        builder.getStringAttr(rootSite + "_recipe_quotient_outputs" + label));
  func::ReturnOp::create(builder, loc, outputs);
  return result;
}
} // namespace

FailureOr<OwningOpRef<mlir::ModuleOp>>
proposeQuotientExecution(func::FuncOp source,
                         mathematical::RealizationWork &work) {
  auto unavailable = [] { return OwningOpRef<mlir::ModuleOp>{}; };
  if (!work.quotientPlacements || !work.quotientInspection)
    return unavailable();
  if (!source || !source.getBody().hasOneBlock() ||
      !llvm::any_of(source.front(), [](Operation &op) {
        return isa<algebra::MultiplyQuotientOp>(op);
      }))
    return unavailable();
  auto meaning = readQuotientSource(source, work.quotientInspection);
  if (failed(meaning))
    return unavailable();
  auto site = source.front().front().getAttrOfType<StringAttr>("site");
  if (!site)
    return failure();
  for (StringRef contract :
       {"index.constant", "quotient.project", "quotient.add",
        "quotient.subtract", "quotient.multiply", "quotient.ntt",
        "quotient.intt", "quotient.pointwise"})
    if (protocol::boundOperationName(contract).empty())
      return unavailable();
  // Source admission caps entries at 512 operations and 128 ports. Reserve a
  // conservative whole-scratch envelope before cloning or invoking the solver.
  uint64_t instructions =
      8 * (source.front().getOperations().size() + source.getNumArguments() +
           source.getNumResults());
  uint64_t construction = 8 * instructions;
  uint64_t bytesPerSite =
      site.getValue().size() + 64 + 4 * source.getNumResults();
  if (construction > work.quotientConstruction ||
      bytesPerSite > work.quotientSiteBytes / instructions)
    return unavailable();
  work.quotientConstruction -= construction;
  uint64_t siteBytes = instructions * bytesPerSite;
  work.quotientSiteBytes -= siteBytes;
  --work.quotientPlacements;
  // Optional capacity refusal must not publish an error diagnostic. A genuine
  // mismatch returns failure and the caller emits its preservation diagnostic.
  ScopedDiagnosticHandler quiet(source.getContext(),
                                [](Diagnostic &) { return success(); });
  auto imported = importQuotient(source, *meaning);
  bool exhausted = false;
  auto read =
      heir::readArithmetic(*imported, work.quotientInspection, &exhausted);
  if (failed(read))
    return exhausted ? FailureOr<OwningOpRef<mlir::ModuleOp>>(unavailable())
                     : FailureOr<OwningOpRef<mlir::ModuleOp>>(failure());
  if (read->modulus != meaning->modulus || read->degree != meaning->degree ||
      read->inputs != meaning->inputs || read->outputs != meaning->outputs)
    return failure();
  heir::PlacementStatus status;
  auto placed =
      heir::placeTransforms(*imported, &status, &work.quotientInspection);
  if (failed(placed))
    return status == heir::PlacementStatus::Unavailable
               ? FailureOr<OwningOpRef<mlir::ModuleOp>>(unavailable())
               : FailureOr<OwningOpRef<mlir::ModuleOp>>(failure());
  auto arithmetic = cast<func::FuncOp>((*placed)->getBody()->front());
  if (arithmetic.front().getOperations().size() > instructions / 2)
    return unavailable();
  auto candidate = lowerPlaced(source, **placed, *meaning, site.getValue());
  auto function = *candidate->getOps<func::FuncOp>().begin();
  auto *cursor = &function.front().front();
  auto checked = readQuotientExecution(
      source, *candidate, site.getValue(), function.getArguments(), cursor,
      work.quotientInspection, &exhausted, &siteBytes);
  if (failed(checked))
    return exhausted ? FailureOr<OwningOpRef<mlir::ModuleOp>>(unavailable())
                     : FailureOr<OwningOpRef<mlir::ModuleOp>>(failure());
  auto returned = dyn_cast_or_null<func::ReturnOp>(cursor);
  if (!returned || returned->getNextNode() ||
      returned.getOperands() != ValueRange(*checked) ||
      failed(verify(*candidate)))
    return failure();
  return candidate;
}
} // namespace zkc::kernel

#endif
