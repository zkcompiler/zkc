#include "CheckedCandidate.h"
#include "CollectionRealization.h"
#include "ComputationSelection.h"
#include "FiniteVerification.h"
#include "LaneRealization.h"
#include "MathematicalSupport.h"
#include "RealizationEmission.h"
#include "RecipeRealizations.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Finite.h"
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
class Realizer {
  protocol_ir::ProtocolModuleOp unit;
  RewriterBase &builder;
  SymbolTableCollection symbols;
  Location loc;
  Type index, boolean;
  mathematical::RealizationEmitter emitter;
  unsigned occurrence = 0;
  llvm::DenseMap<Value, Value> values, sizes, lowers;
  Computation computation;
  mathematical::RealizationWork &work;
  const mathematical::MathematicalRecipes &recipes;
  bool failedHelper = false;
  std::string sitePrefix = "finite_";
  std::string site() { return sitePrefix + std::to_string(occurrence++); }
  Value emit(const protocol::BindingApplication &application, ValueRange inputs,
             Type output, ArrayRef<std::string> params = {}) {
    SmallVector<Type> outputs;
    if (output)
      outputs.push_back(output);
    auto *op = emitter.emit(builder, loc, site(), application, inputs, outputs,
                            params);
    return output ? op->getResult(0) : Value();
  }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> args = {},
             ArrayRef<std::string> params = {}) {
    return emit({contract.str(), {args.begin(), args.end()}, ""}, inputs,
                output, params);
  }
  Value number(uint64_t n) {
    return emit("index.constant", {}, index, {}, {std::to_string(n)});
  }
  Value length(Value input, unsigned axis = 0) {
    auto col = mathematical::collectionRealization(input.getType());
    assert(col && axis < col->rank && "admitted collection axis required");
    if (col->staticExtent)
      return number(*col->staticExtent);
    return emit(*col->length, input, index,
                col->rank == 2 ? ArrayRef<std::string>{std::to_string(axis)}
                               : ArrayRef<std::string>{});
  }
  void require(Value condition) { emit("control.require", condition, {}, {}); }
  Operation *control(StringRef name, ValueRange inputs, TypeRange outputs,
                     unsigned regions) {
    OperationState state(loc, name);
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttribute("site", builder.getStringAttr(site()));
    for (unsigned i = 0; i < regions; ++i)
      state.addRegion();
    return builder.create(state);
  }
  Block *region(Operation *op, unsigned i, TypeRange types) {
    auto *block =
        builder.createBlock(&op->getRegion(i), op->getRegion(i).end(), types,
                            SmallVector<Location>(types.size(), loc));
    return block;
  }
  void yield(ValueRange values) {
    local::LocalYieldOp::create(builder, loc, values);
  }
  // A zero-trip loop applies the existing executable bound admission without
  // inventing a second limit contract or evaluating a helper.
  void validateBound(Value bound) {
    auto *loop = control("local.for", {bound, bound}, {}, 1);
    region(loop, 0, {index});
    yield({});
    builder.setInsertionPointAfter(loop);
  }
  Value reversedRange(Value lower, Value upper) {
    Value less = emit("index.less", {lower, upper}, boolean);
    SmallVector<Value> inputs{less, lower};
    if (upper != lower)
      inputs.push_back(upper);
    SmallVector<Type> types(inputs.size() - 1, index);
    auto *branch = control("local.if", inputs, {index}, 2);
    auto *yes = region(branch, 0, types);
    yield(emit("index.sub",
               {yes->getArgument(upper == lower ? 0 : 1), yes->getArgument(0)},
               index));
    region(branch, 1, types);
    yield(number(0));
    builder.setInsertionPointAfter(branch);
    return branch->getResult(0);
  }
  Value cardinalityProduct(Value left, Value right) {
    validateBound(left);
    validateBound(right);
    Value result = emit("index.mul", {left, right}, index);
    validateBound(result);
    return result;
  }
  void admit(ArrayRef<Operation *> admission) {
    // Visit all constructors in descriptor order, including dead intermediates.
    for (Operation *constructor : admission) {
      auto &op = *constructor;
      Value size;
      if (isa<data::DomainElementsOp, data::DomainIndicesOp>(op)) {
        unsigned axis =
            isa<data::DomainIndicesOp>(op)
                ? unsigned(cast<data::DomainIndicesOp>(op).getAxis())
                : 0;
        size = length(values.lookup(op.getOperand(0)), axis);
      } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
        bool row = isa<data::DomainMatrixRowOp>(op);
        Value matrix = values.lookup(op.getOperand(0));
        Value selected = values.lookup(op.getOperand(1));
        Value bound = length(matrix, row ? 0 : 1);
        require(emit("index.less", {selected, bound}, boolean));
        size = length(matrix, row ? 1 : 0);
      } else if (isa<data::DomainRangeOp>(op)) {
        Value lower = values.lookup(op.getOperand(0)),
              upper = values.lookup(op.getOperand(1));
        validateBound(lower);
        validateBound(upper);
        lowers[op.getResult(0)] = lower;
        size = reversedRange(lower, upper);
      } else if (isa<data::DomainZipOp>(op)) {
        size = sizes.lookup(op.getOperand(0));
        for (Value child : op.getOperands().drop_front())
          require(emit("index.equal", {size, sizes.lookup(child)}, boolean));
      } else if (isa<data::DomainProductOp>(op)) {
        size = sizes.lookup(op.getOperand(0));
        for (Value child : op.getOperands().drop_front())
          size = cardinalityProduct(size, sizes.lookup(child));
      } else if (isa<data::DomainMatrixCoordinatesOp>(op)) {
        Value matrix = values.lookup(op.getOperand(0));
        Value rows = length(matrix, 0), columns = length(matrix, 1);
        // The second radix is retained as an ordinary SSA capture.
        lowers[op.getResult(0)] =
            cast<data::DomainMatrixCoordinatesOp>(op).getOrder() == "row_major"
                ? columns
                : rows;
        size = cardinalityProduct(rows, columns);
      }
      sizes[op.getResult(0)] = size;
    }
  }
  SmallVector<Value> items(Value descriptor, Value position,
                           IRMapping &mapping) {
    auto *op = descriptor.getDefiningOp();
    auto actual = [&](Value v) { return mapping.lookup(values.lookup(v)); };
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Value> result;
      for (Value child : op->getOperands())
        append_range(result, items(child, position, mapping));
      return result;
    }
    if (isa<data::DomainProductOp>(op)) {
      SmallVector<SmallVector<Value>> factors;
      Value quotient = position;
      for (Value child : reverse(op->getOperands())) {
        Value divisor = mapping.lookup(sizes.lookup(child));
        Value remainder = emit("index.mod", {quotient, divisor}, index);
        factors.push_back(items(child, remainder, mapping));
        quotient = emit("index.div", {quotient, divisor}, index);
      }
      SmallVector<Value> result;
      for (auto &factor : reverse(factors))
        append_range(result, factor);
      return result;
    }
    if (isa<data::DomainIndicesOp>(op))
      return {position};
    if (isa<data::DomainRangeOp>(op))
      return {emit("index.add",
                   {mapping.lookup(lowers.lookup(descriptor)), position},
                   index)};
    if (isa<data::DomainMatrixCoordinatesOp>(op)) {
      Value radix = mapping.lookup(lowers.lookup(descriptor));
      Value major = emit("index.div", {position, radix}, index),
            minor = emit("index.mod", {position, radix}, index);
      return cast<data::DomainMatrixCoordinatesOp>(op).getOrder() == "row_major"
                 ? SmallVector<Value>{major, minor}
                 : SmallVector<Value>{minor, major};
    }
    Value container = actual(op->getOperand(0));
    auto col = mathematical::collectionRealization(container.getType());
    assert(col && col->get && "admitted collection read required");
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      Value selected = actual(op->getOperand(1));
      bool row = isa<data::DomainMatrixRowOp>(op);
      return {emit(
          *col->get,
          {container, row ? selected : position, row ? position : selected},
          col->element)};
    }
    return {emit(*col->get, {container, position}, col->element)};
  }
  Expected<mathematical::LaneRealizationResult>
  elementwise(const ComputationView &view,
              const mathematical::Elementwise &equation, ValueRange entry) {
    auto &body = computation.helper->getRegion(0).front();
    Value root = view.iteration[view.root].descriptor;
    llvm::DenseMap<Value, mathematical::LaneInput> inputs;
    for (const auto &access : view.accesses)
      if (access.kind == AccessKind::Element)
        inputs[access.value] = {entry[access.input], true};
    for (const auto &capture : view.captures)
      inputs[capture.formal] = {entry[capture.input], false};
    for (auto [lookup, container] : equation.lookups)
      inputs[lookup] = {inputs.lookup(container).value, true};
    auto vector = computation.signature.getResult(0);
    SmallVector<std::string> args{
        cast<algebra::FieldType>(elementType(vector)).getDomain().str()};
    return mathematical::realizeLanes(
        body, inputs, vector, sizes.lookup(root), &work.lanes, recipes,
        [&](StringRef contract, ValueRange operands, Type output,
            ArrayRef<std::string> parameters) {
          return emit(contract, operands, output, args, parameters);
        });
  }
  SmallVector<Value> apply(CallbackRole role, CallbackValues actuals) {
    auto callback = readCallback(computation, role);
    if (failed(callback)) {
      failedHelper = true;
      return {};
    }
    auto environment = bindCallback(*callback, actuals);
    if (failed(environment)) {
      failedHelper = true;
      return {};
    }
    auto *helper = callback->symbol;
    auto type = callback->signature;
    ValueRange arguments = environment->actuals;
    if (computation.total) {
      auto math = cast<func::FuncOp>(helper);
      if (failed(mathematical::chargeHelperOperations(
              math, work.helperOperations, work.helperSlots))) {
        failedHelper = true;
        return {};
      }
      // Detached normalization subject, separate from body emission. Expansion
      // and polynomial elimination remain fallible and consume shared work.
      OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(math->clone()));
      SymbolTableCollection tables;
      if (failed(mathematical::inlineHelpers(*scratch, work.helperOperations,
                                             work.helperSlots, tables, unit)) ||
          failed(
              poly::eliminatePolynomials(scratch->front(), work.polynomial))) {
        failedHelper = true;
        return {};
      }
      IRMapping mapping;
      for (auto [a, b] : zip(scratch->getArguments(), arguments))
        mapping.map(a, b);
      for (auto &op : scratch->front().without_terminator()) {
        auto *copy = builder.clone(op, mapping);
        builder.modifyOpInPlace(copy, [&] {
          copy->setAttr("site", builder.getStringAttr(site()));
        });
      }
      SmallVector<Value> results;
      for (Value v : scratch->front().back().getOperands())
        results.push_back(mapping.lookup(v));
      return results;
    }
    auto call = local::ApplyOp::create(
        builder, loc, type.getResults(), arguments,
        SymbolTable::getSymbolName(helper).getValue(), site());
    return SmallVector<Value>(call.getResults());
  }
  SmallVector<Value> transition(ValueRange state, ValueRange item,
                                ValueRange environment) {
    auto result =
        apply(computation.collect ? CallbackRole::Body : CallbackRole::Step,
              {computation.collect ? ValueRange{} : state, item,
               environment.take_front(computation.arguments),
               environment.drop_front(computation.arguments)});
    if (failedHelper)
      return {};
    if (!computation.collect)
      return result;
    auto col = mathematical::collectionRealization(state[0].getType());
    assert(col && col->append && "admitted collection append required");
    return {emit(*col->append, {state[0], result[0]}, state[0].getType())};
  }

public:
  Realizer(protocol_ir::ProtocolModuleOp unit, RewriterBase &builder,
           mathematical::RealizationWork &work,
           const mathematical::MathematicalRecipes &recipes =
               mathematical::mathematicalRecipes())
      : unit(unit), builder(builder), loc(unit.getLoc()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()), emitter(unit, "_finite_binding_"),
        work(work), recipes(recipes) {}
  FailureOr<SmallVector<Value>> emitBody(Operation *source, ValueRange entry,
                                         bool optimize) {
    if (failed(describe(source, computation, unit, &symbols)))
      return failure();
    auto partitions = partitionEntry(computation, entry);
    if (failed(partitions))
      return failure();
    // Ordered emission reads the domain directly. It needs no optional
    // structural/equation work, including when retrying a discarded proposal.
    mathematical::ComputationSelection selection;
    if (optimize)
      selection = mathematical::selectComputation(computation, {true, false},
                                                  work.matching, recipes);
    const ComputationView *view = selection.view ? &*selection.view : nullptr;
    SmallVector<Operation *> admission;
    for (auto &op : computation.domain.getBody().front().without_terminator())
      admission.push_back(&op);
    values.clear();
    sizes.clear();
    lowers.clear();
    occurrence = 0;
    failedHelper = false;
    loc = source->getLoc();
    if (computation.total)
      sitePrefix = source->getAttrOfType<StringAttr>("site").getValue().str() +
                   "_finite_";
    else
      sitePrefix = "finite_";
    for (auto [formal, actual] :
         zip(computation.domain.getBody().front().getArguments(),
             partitions->domain))
      values[formal] = actual;
    admit(admission);
    SmallVector<Value> initial(partitions->initialState), environment;
    append_range(environment, partitions->domain);
    append_range(environment, partitions->captures);
    if (selection.kind == mathematical::RealizationKind::Bilinear) {
      const auto &plan = selection.equations.bilinear;
      auto type = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(
          values.lookup(plan->matrix).getType());
      const auto &recipe = *selection.matrix;
      SmallVector<Value> roles{values.lookup(plan->matrix),
                               values.lookup(plan->left),
                               values.lookup(plan->right)};
      SmallVector<Value> inputs;
      for (unsigned i = 0; i < recipe.arity; ++i)
        inputs.push_back(roles[recipe.operands[i]]);
      Value result = emit(recipe.target, inputs, type, col->get->arguments);
      result = emit(recipe.seedCombiner, {initial.front(), result}, type,
                    col->get->arguments);
      return SmallVector<Value>{result};
    }
    if (selection.kind == mathematical::RealizationKind::Reduction) {
      const auto &reduction = selection.reduction;
      SmallVector<Value> inputs;
      for (unsigned position : reduction->inputs)
        inputs.push_back(entry[position]);
      if (reduction->selectedIndex)
        inputs.push_back(entry[*reduction->selectedIndex]);
      auto resultType = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(
          entry[reduction->staticSourceInput].getType());
      Value reduced = emit(reduction->recipe->target, inputs, resultType,
                           col->get->arguments);
      Value result =
          emit(reduction->recipe->combiner, {initial.front(), reduced},
               resultType, col->get->arguments);
      return SmallVector<Value>{result};
    }
    if (selection.kind == mathematical::RealizationKind::Elementwise) {
      auto result = elementwise(*view, *selection.equations.elementwise, entry);
      if (!result) {
        diagnostics::emit(source->emitOpError(), result.takeError());
        return failure();
      }
      if (result->status == mathematical::LaneRealizationStatus::Realized) {
        return SmallVector<Value>{result->value};
      }
      // A declined optional formula has emitted no payload or bindings. Keep
      // the complete admission above and continue with the ordinary loop.
    }
    if (computation.collect) {
      auto result = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(result);
      assert(col && col->empty && "admitted collection construction required");
      initial.push_back(emit(*col->empty, {}, col->storage));
    }
    Value root = computation.domain.getBody().front().back().getOperand(0);
    Value zero = number(0), upper = sizes.lookup(root);
    // Capture only Copy/Drop values; each affine state is in the carried
    // prefix.
    SmallVector<Value> captures(environment);
    for (Operation *op : admission) {
      captures.push_back(sizes.lookup(op->getResult(0)));
      if (auto v = lowers.lookup(op->getResult(0)))
        captures.push_back(v);
    }
    SmallVector<Value> unique;
    for (Value value : captures)
      if (!is_contained(unique, value))
        unique.push_back(value);
    captures = std::move(unique);
    SmallVector<Value> loopInputs{zero, upper};
    append_range(loopInputs, initial);
    append_range(loopInputs, captures);
    SmallVector<Type> stateTypes;
    for (Value v : initial)
      stateTypes.push_back(v.getType());
    auto *loop = control("local.for", loopInputs, stateTypes, 1);
    SmallVector<Type> arguments{index};
    append_range(arguments, stateTypes);
    for (Value v : captures)
      arguments.push_back(v.getType());
    auto *body = region(loop, 0, arguments);
    IRMapping mapping;
    auto state = body->getArguments().slice(1, initial.size());
    auto captured = body->getArguments().drop_front(1 + initial.size());
    for (auto [a, b] : zip(captures, captured))
      mapping.map(a, b);
    auto item = items(root, body->getArgument(0), mapping);
    SmallVector<Value> env;
    for (Value v : environment)
      env.push_back(mapping.lookup(v));
    SmallVector<Value> next;
    if (computation.predicate) {
      auto predicate =
          apply(CallbackRole::Predicate,
                {{},
                 item,
                 ValueRange(env).take_front(computation.arguments),
                 ValueRange(env).drop_front(computation.arguments)});
      if (failedHelper)
        return failure();
      Value condition = predicate[0];
      SmallVector<Value> branchCaptures;
      auto capture = [&](ValueRange operands) {
        for (Value value : operands)
          if (!is_contained(branchCaptures, value))
            branchCaptures.push_back(value);
      };
      capture(state);
      capture(item);
      capture(env);
      SmallVector<Value> branchInputs{condition};
      append_range(branchInputs, branchCaptures);
      auto *branch = control("local.if", branchInputs, stateTypes, 2);
      SmallVector<Type> branchTypes;
      for (Value v : branchCaptures)
        branchTypes.push_back(v.getType());
      auto *yes = region(branch, 0, branchTypes);
      IRMapping branchMapping;
      for (auto [a, b] : zip(branchCaptures, yes->getArguments()))
        branchMapping.map(a, b);
      auto remap = [&](ValueRange operands) {
        SmallVector<Value> result;
        for (Value value : operands)
          result.push_back(branchMapping.lookup(value));
        return result;
      };
      auto transitionResults =
          transition(remap(state), remap(item), remap(env));
      if (failedHelper)
        return failure();
      yield(transitionResults);
      auto *no = region(branch, 1, branchTypes);
      for (auto [a, b] : zip(branchCaptures, no->getArguments()))
        branchMapping.map(a, b);
      yield(remap(state));
      builder.setInsertionPointAfter(branch);
      append_range(next, branch->getResults());
    } else
      next = transition(state, item, env);
    if (failedHelper)
      return failure();
    append_range(next, captured);
    yield(next);
    builder.setInsertionPointAfter(loop);
    SmallVector<Value> results(loop->getResults());
    if (computation.collect &&
        computation.signature.getResult(0) != results[0].getType()) {
      auto col = mathematical::collectionRealization(
          computation.signature.getResult(0));
      assert(col && col->wrap && "admitted collection wrapper required");
      results[0] =
          emit(*col->wrap, results, computation.signature.getResult(0));
    }
    return results;
  }
  LogicalResult run(Operation *declaration, bool optimize) {
    Computation source;
    if (failed(describe(declaration, source, unit, &symbols)))
      return failure();
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto name = SymbolTable::getSymbolName(declaration);
    auto function = local::FuncOp::create(builder, declaration->getLoc(),
                                          name.getValue(), source.signature);
    builder.modifyOpInPlace(function, [&] {
      function->setAttr("logical_origin",
                        builder.getArrayAttr({name, builder.getArrayAttr({})}));
    });
    auto *entry = builder.createBlock(
        &function.getBody(), function.getBody().end(),
        source.signature.getInputs(),
        SmallVector<Location>(source.signature.getNumInputs(),
                              declaration->getLoc()));
    auto results = emitBody(declaration, entry->getArguments(), optimize);
    if (failed(results))
      return failure();
    local::ReturnOp::create(builder, declaration->getLoc(), *results);
    builder.eraseOp(declaration);
    symbols.invalidateSymbolTable(unit);
    return success();
  }
};
// RewriterBase's builder-copy constructor retains the caller's listener and
// insertion point. All new operations, blocks and bindings use this rewriter.
class BodyRewriter : public RewriterBase {
public:
  explicit BodyRewriter(const OpBuilder &builder) : RewriterBase(builder) {}
};
} // namespace
FailureOr<SmallVector<Value>>
realizeExpression(Operation *op, ValueRange inputs, OpBuilder &builder,
                  MathematicalSelectionPolicy policy,
                  mathematical::RealizationWork *work) {
  auto unit = op->getParentOfType<protocol_ir::ProtocolModuleOp>();
  auto site = op->getAttrOfType<StringAttr>("site");
  if (!unit || !site || site.getValue().empty())
    return failure();
  mathematical::RealizationWork standalone;
  BodyRewriter rewriter(builder);
  Realizer realizer(unit, rewriter, work ? *work : standalone);
  auto results = realizer.emitBody(op, inputs, policy.finiteBulk);
  builder.restoreInsertionPoint(rewriter.saveInsertionPoint());
  return results;
}

LogicalResult realizeLocals(ModuleOp module, MathematicalSelectionPolicy policy,
                            mathematical::RealizationWork *work) {
  return realizeLocals(module, policy, work,
                       mathematical::mathematicalRecipes());
}

LogicalResult realizeLocals(ModuleOp module, MathematicalSelectionPolicy policy,
                            mathematical::RealizationWork *work,
                            const mathematical::MathematicalRecipes &recipes) {
  return realizeLocalsWithLimits(module, policy, work, recipes, {});
}

LogicalResult
realizeLocalsWithLimits(ModuleOp module, MathematicalSelectionPolicy policy,
                        mathematical::RealizationWork *work,
                        const mathematical::MathematicalRecipes &recipes,
                        VerificationLimits limits) {
  if (failed(mlir::verify(module)) || !hasSingleElement(*module.getBody()))
    return failure();
  mathematical::RealizationWork standalone;
  auto &available = work ? *work : standalone;
  bool optimize = policy.finiteBulk;
  for (;;) {
    // Reserve required ordered work independently of a speculative proposal.
    // A retry always starts from the admitted source, never from bulk output.
    auto attemptWork = available;
    mathematical::CheckedCandidate candidate(module);
    auto unit =
        dyn_cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    if (!unit)
      return failure();
    IRRewriter rewriter(module.getContext());
    Realizer realizer(unit, rewriter, attemptWork, recipes);
    auto retainOptionalWork = [&] {
      available.matching = attemptWork.matching;
      available.lanes = attemptWork.lanes;
    };
    for (auto &op : make_early_inc_range(unit.getBody().front()))
      if (isDeclaration(&op) && failed(realizer.run(&op, optimize))) {
        retainOptionalWork();
        return failure();
      }
    // Matching/lane allowances remain cumulative even when the candidate is
    // discarded. Only required construction work has an ordered reserve.
    retainOptionalWork();
    VerificationResult checked{VerificationStatus::Mismatch, {}};
    auto published = candidate.publish([&](ModuleOp source, ModuleOp proposal) {
      checked = checkRealizations(source, proposal, limits);
      if (checked.status == VerificationStatus::OptionalCapacity && optimize)
        return failure();
      return checked.diagnose(proposal);
    });
    if (succeeded(published)) {
      available = attemptWork;
      return success();
    }
    if (!optimize || checked.status != VerificationStatus::OptionalCapacity)
      return failure();
    optimize = false;
  }
}
} // namespace zkc::finite
