#include "zkc/Transforms/NestedContractions.h"
#include "AlgorithmSupport.h"
#include "CheckedCandidate.h"
#include "ComputationSelection.h"
#include "NestedContractionVerification.h"
#include "RealizationEmission.h"
#include "RealizationTrace.h"
#include "RecipeRealizations.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/detail/Builders.h"
#include "llvm/ADT/DenseSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::nested {
namespace {
using Record = protocol::detail::AlgorithmExpansionRecord;
using Occurrence = protocol::detail::AlgorithmOccurrence;
using StateAccess = protocol::detail::AlgorithmStateAccess;

// Naming only: source/candidate admission readers separately count the inner
// finite recipe's primitive sites. Keep its leaf identity and prior call path
// in the existing expansion record, rather than treating an encoded call site
// as a new authored leaf.
Occurrence innerOrigin(local::ApplyOp call, Operation *inner,
                       const Record &record) {
  auto function = call->getParentOfType<local::FuncOp>();
  auto saved = protocol::detail::occurrence(record, function.getSymName(),
                                            protocol::attr(call, "site"));
  Occurrence result;
  if (saved) {
    result.path = saved->path;
    result.depth = saved->depth;
  }
  result.definition = SymbolTable::getSymbolName(inner).str();
  result.declaration = result.definition;
  result.path.emplace_back(saved ? saved->originalSite
                                 : protocol::attr(call, "site").str(),
                           result.definition);
  ++result.depth;
  return result;
}

// Common trust points are type admission, installed scalar-law facets and the
// finite ABI. Selection below is never called by the source/candidate reader.
using Selection = mathematical::NestedContraction;
mathematical::NestedContractionSelection
select(Operation *declaration, finite::ComputationWork &work,
       const mathematical::MathematicalRecipes &recipes) {
  finite::Computation computation;
  if (failed(finite::describe(declaration, computation)))
    return {};
  finite::ComputationDiagnostic diagnostic;
  auto view = finite::analyzeComputation(computation, work, &diagnostic);
  if (view)
    return mathematical::selectNestedContraction(*view, work, recipes);
  mathematical::NestedContractionSelection result;
  result.diagnostic = diagnostic;
  return result;
}

class Emitter {
  OpBuilder builder;
  Location location;
  mathematical::RealizationEmitter emitter;
  unsigned occurrence = 0;
  Record &record;
  std::string functionName;
  std::optional<Occurrence> admissionOrigin;
  unsigned admissionOccurrence = 0;
  bool valid = true;
  std::string site() { return "nested_" + std::to_string(occurrence++); }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> args = {},
             ArrayRef<std::string> params = {}) {
    std::string emittedSite = site();
    if (admissionOrigin) {
      admissionOrigin->originalSite =
          "finite_" + std::to_string(admissionOccurrence++);
      if (contract == "control.require") {
        auto encoded = protocol::algorithmSite(admissionOrigin->path,
                                               admissionOrigin->originalSite,
                                               record.originBytes);
        if (!encoded) {
          diagnostics::emit(mlir::emitError(location), encoded.takeError());
          valid = false;
        } else {
          emittedSite = std::move(*encoded);
          valid &= record.occurrences
                       .emplace(protocol::detail::OccurrenceKey{functionName,
                                                                emittedSite},
                                *admissionOrigin)
                       .second;
        }
      }
    }
    SmallVector<Type> outputs;
    if (output)
      outputs.push_back(output);
    auto *op = emitter.emit(builder, location, emittedSite,
                            {contract.str(), {args.begin(), args.end()}, ""},
                            inputs, outputs, params);
    return output ? op->getResult(0) : Value();
  }

public:
  Emitter(protocol_ir::ProtocolModuleOp unit, Record &record)
      : builder(unit.getContext()), location(unit.getLoc()),
        emitter(unit, "_nested_binding_"), record(record) {}
  LogicalResult run(const Selection &selection,
                    const mathematical::MatrixContractionRecipe &recipe) {
    auto c = selection.outer;
    location = c.operation->getLoc();
    occurrence = 0;
    auto name = SymbolTable::getSymbolName(c.operation);
    functionName = name.str();
    auto origin = innerOrigin(cast<local::ApplyOp>(selection.call),
                              selection.inner.operation, record);
    if (origin.path.size() > 64 || origin.depth > 64)
      return diagnostics::emit(selection.call->emitOpError(),
                               "interactive-call-depth");
    // Insert at the old declaration, then erase it before any symbol lookup.
    // Finite declarations have no SSA results, so callers retain the same name.
    builder.setInsertionPoint(c.operation);
    auto function =
        local::FuncOp::create(builder, location, name.getValue(), c.signature);
    if (auto visibility = c.operation->getAttr("sym_visibility"))
      function->setAttr("sym_visibility", visibility);
    function->setAttr("logical_origin",
                      builder.getArrayAttr({name, builder.getArrayAttr({})}));
    auto *entry = function.addEntryBlock();
    builder.setInsertionPointToEnd(entry);
    Type index =
        IntegerType::get(builder.getContext(), 64, IntegerType::Unsigned);
    Type boolean = builder.getI1Type();
    Type output = c.signature.getResult(0);
    Type field = cast<algebra::FieldVectorType>(output).getElementType();
    SmallVector<std::string> fieldArgs{
        cast<algebra::FieldType>(field).getDomain().str()};
    Value matrix = entry->getArgument(selection.matrix);
    Value size = emit("matrix.dimension", matrix, index, fieldArgs,
                      {std::to_string(selection.axis)});
    Value zero = emit("index.constant", {}, index, {}, {"0"});
    Value nonempty = emit("index.less", {zero, size}, boolean);
    SmallVector<Value> captures(entry->getArguments());
    captures.push_back(size);
    captures.push_back(zero);
    SmallVector<Value> operands{nonempty};
    append_range(operands, captures);
    OperationState branchState(location, "local.if");
    branchState.addOperands(operands);
    branchState.addTypes(output);
    branchState.addAttribute("site", builder.getStringAttr(site()));
    branchState.addRegion();
    branchState.addRegion();
    auto *branch = builder.create(branchState);
    for (unsigned branchIndex = 0; branchIndex < 2; ++branchIndex) {
      auto *block = new Block();
      branch->getRegion(branchIndex).push_back(block);
      for (Value capture : captures)
        block->addArgument(capture.getType(), location);
      builder.setInsertionPointToEnd(block);
      if (branchIndex) {
        Value empty = emit("vector.empty", {}, output, fieldArgs);
        local::LocalYieldOp::create(builder, location, empty);
        continue;
      }
      auto &domain = selection.inner.domain->getRegion(0).front();
      Value selected = block->getArgument(c.signature.getNumInputs() + 1);
      auto mapped = [&](Value formal) {
        unsigned input = cast<BlockArgument>(formal).getArgNumber();
        auto actual = cast<BlockArgument>(selection.call->getOperand(input));
        return actual.getArgNumber() == 0
                   ? selected
                   : block->getArgument(actual.getArgNumber() - 1);
      };
      // Read every constructor in source order. All index checks are for the
      // first entered row/column; identical later checks are guaranteed by the
      // outer indices domain. Native shape rejection is interpreted through
      // these explicit require guards, before calling the bulk primitive.
      llvm::DenseMap<Value, Value> sizes;
      admissionOrigin = origin;
      admissionOccurrence = 0;
      location = selection.inner.operation->getLoc();
      for (auto &op : domain.without_terminator()) {
        Value extent;
        if (isa<data::DomainElementsOp>(op))
          extent =
              emit("vector.length", mapped(op.getOperand(0)), index, fieldArgs);
        else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
          Value m = mapped(op.getOperand(0));
          Value limit = emit("matrix.dimension", m, index, fieldArgs,
                             {std::to_string(selection.axis)});
          Value valid =
              emit("index.less", {mapped(op.getOperand(1)), limit}, boolean);
          emit("control.require", valid, {});
          extent = emit("matrix.dimension", m, index, fieldArgs,
                        {std::to_string(1 - selection.axis)});
        } else {
          extent = sizes.lookup(op.getOperand(0));
          for (Value child : op.getOperands().drop_front()) {
            Value equal =
                emit("index.equal", {extent, sizes.lookup(child)}, boolean);
            emit("control.require", equal, {});
          }
        }
        sizes[op.getResult(0)] = extent;
      }
      admissionOrigin.reset();
      location = c.operation->getLoc();
      Value seed = selection.seed.input
                       ? block->getArgument(*selection.seed.input)
                       : emit("field.constant", {}, field, fieldArgs,
                              {selection.seed.constant});
      SmallVector<Value> roles{block->getArgument(selection.matrix),
                               block->getArgument(selection.vector)};
      SmallVector<Value> inputs;
      for (unsigned i = 0; i < recipe.arity; ++i)
        inputs.push_back(roles[recipe.operands[i]]);
      Value result = emit(recipe.target, inputs, output, fieldArgs);
      Value initial = emit(
          "vector.fill", {seed, block->getArgument(c.signature.getNumInputs())},
          output, fieldArgs);
      result = emit(recipe.seedCombiner, {initial, result}, output, fieldArgs);
      local::LocalYieldOp::create(builder, location, result);
    }
    builder.setInsertionPointAfter(branch);
    local::ReturnOp::create(builder, location, branch->getResults());
    c.operation->erase();
    return success(valid);
  }
};

LogicalResult rewriteFiniteCollectionsImpl(
    ModuleOp module, protocol::AlgorithmExpansionState &state,
    MathematicalSelectionPolicy policy, mathematical::RealizationWork &work,
    const mathematical::MathematicalRecipes &recipes,
    mathematical::RealizationTrace *trace) {
  mathematical::RealizationScope scope(trace, "nested-contractions", module,
                                       policy, &work);
  if (failed(mlir::verify(module)))
    return failure();
  if (!policy.finiteBulk) {
    scope.selection(
        module, mathematical::DecisionFamily::NestedContraction,
        mathematical::RealizationChoice::Ordered,
        {OptimizationStatus::PolicyDisabled, OptimizationReason::Policy});
    scope.complete(mathematical::CompletionKind::Unchanged);
    return success();
  }
  if (!hasSingleElement(*module.getBody()))
    return failure();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!unit)
    return failure();
  mathematical::CheckedCandidate candidate(module);
  auto candidateUnit =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  const auto &input = StateAccess::get(state);
  auto output = input;
  Emitter emitter(candidateUnit, output);
  // Selections borrow only the still-live candidate helper closure. Each outer
  // declaration is replaced immediately; no selection outlives publication.
  SmallVector<Operation *> declarations;
  for (auto &operation : candidateUnit.getBody().front())
    if (isa<local::FiniteCollectOp>(operation))
      declarations.push_back(&operation);
  bool changed = false;
  for (Operation *declaration : declarations) {
    auto selection = select(declaration, work.matching, recipes);
    scope.selectionDiagnostic(
        declaration, mathematical::DecisionFamily::NestedContraction,
        selection.recipe ? mathematical::RealizationChoice::NestedContraction
                         : mathematical::RealizationChoice::Ordered,
        selection.diagnostic);
    if (selection.recipe) {
      if (!changed)
        scope.propose(policy);
      if (failed(emitter.run(*selection.equation, *selection.recipe)))
        return failure();
      changed = true;
    }
  }
  if (!changed) {
    scope.complete(mathematical::CompletionKind::Unchanged);
    return success();
  }
  auto expected = input;
  scope.failure(mathematical::VerificationDecision{
      mathematical::VerificationObservation::Unclassified,
      "nested contraction correspondence",
      {},
      {}});
  if (failed(candidate.publish([&](ModuleOp before, ModuleOp after) {
        return checkFiniteCollections(before, after, input, expected, &output);
      })))
    return failure();
  StateAccess::set(state, std::move(output));
  scope.publish();
  return success();
}
} // namespace

LogicalResult rewriteFiniteCollections(ModuleOp module,
                                       protocol::AlgorithmExpansionState &state,
                                       MathematicalSelectionPolicy policy,
                                       mathematical::RealizationWork *work,
                                       mathematical::RealizationTrace *trace) {
  const auto &input = StateAccess::get(state);
  if (!input.retained || input.finished)
    return diagnostics::emit(module.emitError(),
                             "nested-contraction-correspondence",
                             "expected retained, unfinished preparation");
  mathematical::RealizationWork standalone;
  return rewriteFiniteCollectionsImpl(
      module, state, policy, work ? *work : standalone,
      mathematical::mathematicalRecipes(), trace);
}

LogicalResult rewriteFiniteCollections(ModuleOp module,
                                       MathematicalSelectionPolicy policy,
                                       mathematical::RealizationWork *work,
                                       mathematical::RealizationTrace *trace) {
  protocol::AlgorithmExpansionState state;
  mathematical::RealizationWork standalone;
  return rewriteFiniteCollectionsImpl(
      module, state, policy, work ? *work : standalone,
      mathematical::mathematicalRecipes(), trace);
}
LogicalResult
rewriteFiniteCollections(ModuleOp module, MathematicalSelectionPolicy policy,
                         const mathematical::MathematicalRecipes &recipes,
                         mathematical::RealizationTrace *trace) {
  protocol::AlgorithmExpansionState state;
  mathematical::RealizationWork work;
  return rewriteFiniteCollectionsImpl(module, state, policy, work, recipes,
                                      trace);
}
} // namespace zkc::nested
