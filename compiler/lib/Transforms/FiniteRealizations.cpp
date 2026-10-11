#include "AlgorithmSupport.h"
#include "ComputationSelection.h"
#include "LaneRealization.h"
#include "MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/StringSet.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
class Realizer {
  protocol_ir::ProtocolModuleOp unit;
  OpBuilder builder;
  Location loc;
  Type index, boolean;
  llvm::StringSet<> names;
  unsigned next = 0, occurrence = 0;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
  llvm::DenseMap<Value, Value> values, sizes, lowers;
  Computation computation;
  mathematical::RealizationWork &work;
  bool failedHelper = false;
  std::string sitePrefix = "finite_";
  std::string site() { return sitePrefix + std::to_string(occurrence++); }
  FlatSymbolRefAttr binding(StringRef contract, ArrayRef<std::string> args) {
    auto key = std::make_pair(
        contract.str(), std::vector<std::string>(args.begin(), args.end()));
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      std::string name;
      do {
        name = "_finite_binding_" + std::to_string(next++);
      } while (!names.insert(name).second);
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Attribute> attrs;
      for (auto &arg : args)
        attrs.push_back(builder.getStringAttr(arg));
      local::OperationBindingOp::create(builder, loc, name, contract,
                                        builder.getArrayAttr(attrs), "");
      found = bindings.emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> args = {},
             ArrayRef<std::string> params = {}) {
    OperationState state(loc, protocol::boundOperationName(contract));
    state.addOperands(inputs);
    if (output)
      state.addTypes(output);
    state.addAttribute("binding", binding(contract, args));
    state.addAttribute("site", builder.getStringAttr(site()));
    SmallVector<Attribute> attrs;
    for (auto &p : params)
      attrs.push_back(builder.getStringAttr(p));
    state.addAttribute("parameters", builder.getArrayAttr(attrs));
    auto *op = builder.create(state);
    return output ? op->getResult(0) : Value();
  }
  Value number(uint64_t n) {
    return emit("index.constant", {}, index, {}, {std::to_string(n)});
  }
  Value length(Value input, unsigned axis = 0) {
    auto col = collection(input.getType());
    if (col.family == "field_array")
      return number(cast<RankedTensorType>(input.getType()).getDimSize(0));
    return emit(
        col.family == "matrix" ? "matrix.dimension" : col.family + ".length",
        input, index, col.arguments,
        col.family == "matrix" ? ArrayRef<std::string>{std::to_string(axis)}
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
    auto *block = new Block();
    op->getRegion(i).push_back(block);
    for (Type type : types)
      block->addArgument(type, loc);
    builder.setInsertionPointToEnd(block);
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
    auto *branch = control("local.if", {less, lower, upper}, {index}, 2);
    auto *yes = region(branch, 0, {index, index});
    yield(emit("index.sub", {yes->getArgument(1), yes->getArgument(0)}, index));
    region(branch, 1, {index, index});
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
    auto col = collection(container.getType());
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      Value selected = actual(op->getOperand(1));
      bool row = isa<data::DomainMatrixRowOp>(op);
      return {emit(
          "matrix.get",
          {container, row ? selected : position, row ? position : selected},
          col.element, col.arguments)};
    }
    StringRef suffix =
        col.family == "indices" || col.family == "sequence" ? ".at" : ".get";
    return {emit(col.family + suffix.str(), {container, position}, col.element,
                 col.arguments)};
  }
  Expected<mathematical::LaneRealizationResult>
  elementwise(const ComputationView &view, ValueRange entry) {
    auto &body = computation.helper->getRegion(0).front();
    Value root = view.iteration[view.root].descriptor;
    llvm::DenseMap<Value, mathematical::LaneInput> inputs;
    for (const auto &access : view.accesses)
      if (access.kind == AccessKind::Element)
        inputs[access.value] = {entry[access.input], true};
    for (const auto &capture : view.captures)
      inputs[capture.formal] = {entry[capture.input], false};
    for (auto [lookup, container] : view.elementwise->lookups)
      inputs[lookup] = {inputs.lookup(container).value, true};
    auto vector = computation.signature.getResult(0);
    SmallVector<std::string> args{
        cast<algebra::FieldType>(elementType(vector)).getDomain().str()};
    return mathematical::realizeLanes(
        body, inputs, vector, sizes.lookup(root), &work.lanes,
        [&](StringRef contract, ValueRange operands, Type output,
            ArrayRef<std::string> parameters) {
          return emit(contract, operands, output, args, parameters);
        });
  }
  SmallVector<Value> apply(Operation *helper, ValueRange arguments) {
    auto type = cast<FunctionType>(
        helper->getAttrOfType<TypeAttr>("function_type").getValue());
    if (computation.total) {
      auto math = cast<func::FuncOp>(helper);
      if (failed(mathematical::chargeHelperOperations(
              math, work.helperOperations, work.helperSlots))) {
        failedHelper = true;
        return {};
      }
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
        copy->setAttr("site", builder.getStringAttr(site()));
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
    SmallVector<Value> args;
    if (!computation.collect)
      append_range(args, state);
    append_range(args, item);
    append_range(args, environment);
    auto result = apply(computation.helper, args);
    if (failedHelper)
      return {};
    if (!computation.collect)
      return result;
    auto col = collection(state[0].getType());
    return {emit(col.family + ".append", {state[0], result[0]},
                 state[0].getType(), col.arguments)};
  }

public:
  Realizer(protocol_ir::ProtocolModuleOp unit,
           mathematical::RealizationWork &work)
      : unit(unit), builder(unit.getContext()), loc(unit.getLoc()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()), work(work) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  LogicalResult run(Operation *declaration, bool optimize,
                    StringRef expressionName = {}) {
    if (failed(describe(declaration, computation)))
      return failure();
    auto selection =
        mathematical::selectComputation(computation, {optimize, false});
    const ComputationView *view = selection.view ? &*selection.view : nullptr;
    SmallVector<Operation *> fallbackAdmission;
    if (!view)
      for (auto &op : computation.domain.getBody().front().without_terminator())
        fallbackAdmission.push_back(&op);
    ArrayRef<Operation *> admission =
        view ? ArrayRef<Operation *>(view->admission)
             : ArrayRef<Operation *>(fallbackAdmission);
    values.clear();
    sizes.clear();
    lowers.clear();
    occurrence = 0;
    failedHelper = false;
    loc = declaration->getLoc();
    if (computation.total)
      sitePrefix =
          declaration->getAttrOfType<StringAttr>("site").getValue().str() +
          "_finite_";
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto name = computation.total ? builder.getStringAttr(expressionName)
                                  : SymbolTable::getSymbolName(declaration);
    auto function = local::FuncOp::create(builder, loc, name.getValue(),
                                          computation.signature);
    function->setAttr("logical_origin",
                      builder.getArrayAttr({name, builder.getArrayAttr({})}));
    auto *entry = function.addEntryBlock();
    builder.setInsertionPointToEnd(entry);
    for (auto [formal, actual] :
         zip(computation.domain.getBody().front().getArguments(),
             entry->getArguments()))
      values[formal] = actual;
    admit(admission);
    SmallVector<Value> initial, environment;
    if (view) {
      for (const auto &seed : view->seeds)
        initial.push_back(entry->getArgument(seed.input));
      for (const auto &capture : view->captures)
        environment.push_back(entry->getArgument(capture.input));
    } else {
      append_range(initial, entry->getArguments().slice(computation.arguments,
                                                        computation.states));
      append_range(environment,
                   entry->getArguments().take_front(computation.arguments));
      append_range(environment,
                   entry->getArguments().drop_front(computation.arguments +
                                                    computation.states));
    }
    if (selection.kind == mathematical::RealizationKind::Bilinear) {
      const auto &plan = view->bilinear;
      auto type = computation.signature.getResult(0);
      auto col = collection(values.lookup(plan->matrix).getType());
      Value result =
          emit("matrix.bilinear",
               {values.lookup(plan->matrix), values.lookup(plan->left),
                values.lookup(plan->right)},
               type, col.arguments);
      result =
          emit("field.add", {initial.front(), result}, type, col.arguments);
      local::ReturnOp::create(builder, loc, result);
      if (!computation.total)
        declaration->erase();
      return success();
    }
    if (selection.kind == mathematical::RealizationKind::Reduction) {
      const auto &reduction = selection.view->reduction;
      SmallVector<Value> inputs;
      for (unsigned position : reduction->inputs)
        inputs.push_back(entry->getArgument(position));
      if (reduction->selectedIndex)
        inputs.push_back(entry->getArgument(*reduction->selectedIndex));
      auto resultType = computation.signature.getResult(0);
      auto col = collection(
          inputs[reduction->kernel == "curve.msm" ? 1 : 0].getType());
      Value reduced =
          emit(reduction->kernel, inputs, resultType, col.arguments);
      Value result = emit(reduction->combine, {initial.front(), reduced},
                          resultType, col.arguments);
      local::ReturnOp::create(builder, loc, result);
      if (!computation.total)
        declaration->erase();
      return success();
    }
    if (selection.kind == mathematical::RealizationKind::Elementwise) {
      auto result = elementwise(*view, entry->getArguments());
      if (!result)
        return diagnostics::emit(declaration->emitOpError(),
                                 result.takeError());
      if (result->status == mathematical::LaneRealizationStatus::Realized) {
        local::ReturnOp::create(builder, loc, result->value);
        if (!computation.total)
          declaration->erase();
        return success();
      }
      // A declined optional formula has emitted no payload or bindings. Keep
      // the complete admission above and continue with the ordinary loop.
    }
    if (computation.collect) {
      auto result = computation.signature.getResult(0);
      auto col = collection(result);
      // Fixed arrays are collected in their corresponding dynamic field vector.
      Type storage =
          col.family == "field_array"
              ? Type(RankedTensorType::get({ShapedType::kDynamic}, col.element))
              : result;
      col = collection(storage);
      initial.push_back(
          emit(col.family + ".empty", {}, storage, col.arguments));
    }
    Value root =
        view ? view->iteration[view->root].descriptor
             : computation.domain.getBody().front().back().getOperand(0);
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
      SmallVector<Value> args(item);
      append_range(args, env);
      auto predicate = apply(computation.predicate, args);
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
      yield(transition(remap(state), remap(item), remap(env)));
      auto *no = region(branch, 1, branchTypes);
      for (auto [a, b] : zip(branchCaptures, no->getArguments()))
        branchMapping.map(a, b);
      yield(remap(state));
      builder.setInsertionPointAfter(branch);
      append_range(next, branch->getResults());
    } else
      next = transition(state, item, env);
    append_range(next, captured);
    yield(next);
    builder.setInsertionPointAfter(loop);
    SmallVector<Value> results(loop->getResults());
    if (computation.collect &&
        computation.signature.getResult(0) != results[0].getType()) {
      auto col = collection(computation.signature.getResult(0));
      results[0] = emit("field_array.from_vector", results,
                        computation.signature.getResult(0), col.arguments);
    }
    local::ReturnOp::create(builder, loc, results);
    if (!computation.total)
      declaration->erase();
    return failure(failedHelper);
  }
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
  SymbolTable symbols(unit);
  unsigned next = 0;
  std::string name;
  do {
    name = "_finite_expression_" + std::to_string(next++);
  } while (symbols.lookup(name));
  mathematical::RealizationWork standalone;
  Realizer realizer(unit, work ? *work : standalone);
  if (failed(realizer.run(op, policy.finiteBulk, name)))
    return failure();
  auto function = cast<local::FuncOp>(SymbolTable::lookupSymbolIn(unit, name));
  IRMapping mapping;
  for (auto [a, b] : zip(function.getArguments(), inputs))
    mapping.map(a, b);
  for (auto &instruction : function.getBody().front().without_terminator()) {
    auto *copy = builder.clone(instruction, mapping);
    if (failed(protocol::detail::canonicalizeCaptures(copy)))
      return failure();
  }
  SmallVector<Value> outputs;
  for (Value v : function.getBody().front().back().getOperands())
    outputs.push_back(mapping.lookup(v));
  function.erase();
  return outputs;
}

LogicalResult realizeLocals(ModuleOp module, MathematicalSelectionPolicy policy,
                            mathematical::RealizationWork *work) {
  if (failed(mlir::verify(module)) || !hasSingleElement(*module.getBody()))
    return failure();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  if (!unit)
    return failure();
  mathematical::RealizationWork standalone;
  Realizer realizer(unit, work ? *work : standalone);
  for (auto &op : make_early_inc_range(unit.getBody().front()))
    if (isDeclaration(&op) && failed(realizer.run(&op, policy.finiteBulk)))
      return failure();
  if (failed(verifyRealizations(module, *candidate)))
    return failure();
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::finite
