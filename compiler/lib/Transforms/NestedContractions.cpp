#include "zkc/Transforms/NestedContractions.h"
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
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::nested {
namespace {
// Common trust points are type admission, installed scalar-law facets and the
// finite ABI. Selection below is never called by the source/candidate reader.
std::optional<unsigned> argument(Value value, Block &block) {
  auto arg = dyn_cast<BlockArgument>(value);
  if (!arg || arg.getOwner() != &block)
    return std::nullopt;
  return arg.getArgNumber();
}
bool nativeVector(Type type, Type field) {
  auto tensor = dyn_cast<RankedTensorType>(type);
  return tensor && tensor.getRank() == 1 && tensor.isDynamicDim(0) &&
         tensor.getElementType() == field;
}
bool nativeMatrix(Type type, Type field) {
  auto tensor = dyn_cast<RankedTensorType>(type);
  return tensor && tensor.getRank() == 2 && tensor.isDynamicDim(0) &&
         tensor.isDynamicDim(1) && tensor.getElementType() == field;
}
struct Seed {
  std::optional<unsigned> input;
  std::string constant;
};
struct Selection {
  finite::Computation outer, inner;
  local::ApplyOp call;
  unsigned matrix = 0, vector = 0, axis = 0;
  Seed seed;
};
std::optional<Selection> select(Operation *declaration) {
  if (!isa<local::FiniteCollectOp>(declaration))
    return std::nullopt;
  Selection selected;
  if (failed(finite::describe(declaration, selected.outer)) ||
      selected.outer.predicate || !isa<local::FuncOp>(selected.outer.helper))
    return std::nullopt;
  auto view = finite::analyzeComputation(selected.outer);
  if (!view || view->nested.size() != 1 || view->iteration.size() != 1 ||
      view->iteration[0].kind != finite::IterationKind::Indices)
    return std::nullopt;
  auto indices = dyn_cast<data::DomainIndicesOp>(view->iteration[0].operation);
  auto matrix =
      argument(indices.getInput(), selected.outer.domain.getBody().front());
  auto &body = selected.outer.helper->getRegion(0).front();
  auto &child = view->nested.front();
  auto call = dyn_cast_or_null<local::ApplyOp>(child.occurrence);
  if (!matrix || !call || child.computation.collect ||
      child.computation.predicate || child.computation.states != 1 ||
      !isa<local::FiniteFoldOp>(child.computation.operation) ||
      !isa<local::FuncOp>(child.computation.helper) || !child.reduction ||
      child.reduction->inputs.size() != 2 || !child.reduction->selectedIndex ||
      view->result != call->getResult(0))
    return std::nullopt;
  unsigned axis = indices.getAxis();
  if (axis > 1 ||
      child.reduction->demand != (axis ? finite::DemandKind::MatrixColumn
                                       : finite::DemandKind::MatrixRow))
    return std::nullopt;
  Type field = child.computation.signature.getResult(0);
  if (!isa<algebra::FieldType>(field) ||
      !nativeMatrix(selected.outer.signature.getInput(*matrix), field) ||
      !nativeVector(selected.outer.signature.getResult(0), field))
    return std::nullopt;
  auto mapInput = [&](unsigned input) -> std::optional<unsigned> {
    auto mapped = argument(call->getOperand(input), body);
    if (!mapped || !*mapped)
      return std::nullopt;
    return *mapped - 1;
  };
  auto innerMatrix = mapInput(child.reduction->inputs[0]);
  auto vector = mapInput(child.reduction->inputs[1]);
  if (!innerMatrix || *innerMatrix != *matrix || !vector ||
      !nativeVector(selected.outer.signature.getInput(*vector), field) ||
      call->getOperand(*child.reduction->selectedIndex) != body.getArgument(0))
    return std::nullopt;
  // Even unused descriptor inputs must have a direct environment mapping in
  // this first strategy. More general uniform expressions keep the fallback.
  for (Value operand :
       call->getOperands().take_front(child.computation.arguments))
    if (!argument(operand, body))
      return std::nullopt;
  Value seed = call->getOperand(child.computation.arguments);
  if (auto input = argument(seed, body)) {
    if (!*input)
      return std::nullopt;
    selected.seed.input = *input - 1;
  } else {
    auto constant = finite::fieldConstant(seed.getDefiningOp());
    if (!constant || seed.getType() != field)
      return std::nullopt;
    selected.seed.constant = *constant;
  }
  for (Operation *op : view->payload)
    if (op != call.getOperation() &&
        (op != seed.getDefiningOp() || !finite::fieldConstant(op)))
      return std::nullopt;
  auto &step = child.computation.helper->getRegion(0).front();
  if (std::distance(step.begin(), step.end()) != 3)
    return std::nullopt;
  // This initial strategy supports strict zip, including ignored lanes and
  // unused zip constructors. Every constructor still contributes admission.
  auto &domain = child.computation.domain->getRegion(0).front();
  for (auto &op : domain.without_terminator()) {
    if (isa<data::DomainZipOp>(op))
      continue;
    auto formal = argument(op.getOperand(0), domain);
    if (!formal)
      return std::nullopt;
    auto mapped = mapInput(*formal);
    if (!mapped)
      return std::nullopt;
    if (isa<data::DomainElementsOp>(op)) {
      if (!nativeVector(selected.outer.signature.getInput(*mapped), field))
        return std::nullopt;
    } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      auto index = argument(op.getOperand(1), domain);
      if (*mapped != *matrix || !index ||
          call->getOperand(*index) != body.getArgument(0) ||
          isa<data::DomainMatrixColumnOp>(op) != bool(axis))
        return std::nullopt;
    } else
      return std::nullopt;
  }
  selected.inner = child.computation;
  selected.call = call;
  selected.matrix = *matrix;
  selected.vector = *vector;
  selected.axis = axis;
  return selected;
}

class Emitter {
  protocol_ir::ProtocolModuleOp unit;
  OpBuilder builder;
  Location location;
  llvm::StringSet<> names;
  unsigned serial = 0, occurrence = 0;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
  std::string site() { return "nested_" + std::to_string(occurrence++); }
  FlatSymbolRefAttr binding(StringRef contract, ArrayRef<std::string> args) {
    auto key = std::make_pair(
        contract.str(), std::vector<std::string>(args.begin(), args.end()));
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      std::string name;
      do {
        name = "_nested_binding_" + std::to_string(serial++);
      } while (!names.insert(name).second);
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Attribute> attributes;
      for (const auto &arg : args)
        attributes.push_back(builder.getStringAttr(arg));
      local::OperationBindingOp::create(builder, location, name, contract,
                                        builder.getArrayAttr(attributes), "");
      found = bindings.emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> args = {},
             ArrayRef<std::string> params = {}) {
    OperationState state(location, protocol::boundOperationName(contract));
    state.addOperands(inputs);
    if (output)
      state.addTypes(output);
    state.addAttribute("binding", binding(contract, args));
    state.addAttribute("site", builder.getStringAttr(site()));
    SmallVector<Attribute> parameters;
    for (const auto &param : params)
      parameters.push_back(builder.getStringAttr(param));
    state.addAttribute("parameters", builder.getArrayAttr(parameters));
    auto *op = builder.create(state);
    return output ? op->getResult(0) : Value();
  }

public:
  explicit Emitter(protocol_ir::ProtocolModuleOp unit)
      : unit(unit), builder(unit.getContext()), location(unit.getLoc()) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  void run(const Selection &selection) {
    auto c = selection.outer;
    location = c.operation->getLoc();
    occurrence = 0;
    auto name = SymbolTable::getSymbolName(c.operation);
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
    Type field = cast<RankedTensorType>(output).getElementType();
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
      Value seed = selection.seed.input
                       ? block->getArgument(*selection.seed.input)
                       : emit("field.constant", {}, field, fieldArgs,
                              {selection.seed.constant});
      Value result = emit(selection.axis ? "matrix.transpose_mul_vector"
                                         : "matrix.mul_vector",
                          {block->getArgument(selection.matrix),
                           block->getArgument(selection.vector)},
                          output, fieldArgs);
      Value initial = emit(
          "vector.fill", {seed, block->getArgument(c.signature.getNumInputs())},
          output, fieldArgs);
      result = emit("vector.add", {initial, result}, output, fieldArgs);
      local::LocalYieldOp::create(builder, location, result);
    }
    builder.setInsertionPointAfter(branch);
    local::ReturnOp::create(builder, location, branch->getResults());
    c.operation->erase();
  }
};

// Independent source reader. It reconstructs the returned scalar term and its
// input map from the actual callback SSA and actual descriptor constructors.
// It deliberately does not use analyzeComputation/recognizeReduction/select.
struct Source {
  finite::Computation outer, inner;
  local::ApplyOp call;
  unsigned matrix = 0, vector = 0, axis = 0;
  Seed seed;
  SmallVector<unsigned> inputMap;
};
std::optional<Source> readSource(Operation *declaration) {
  Source source;
  if (!isa<local::FiniteCollectOp>(declaration) ||
      failed(finite::describe(declaration, source.outer)) ||
      source.outer.predicate || !isa<local::FuncOp>(source.outer.helper))
    return std::nullopt;
  auto &outerDomain = source.outer.domain.getBody().front();
  if (std::distance(outerDomain.begin(), outerDomain.end()) != 2)
    return std::nullopt;
  auto indices = dyn_cast<data::DomainIndicesOp>(outerDomain.front());
  if (!indices || outerDomain.back().getOperand(0) != indices.getOutput())
    return std::nullopt;
  auto m = argument(indices.getInput(), outerDomain);
  if (!m || indices.getAxis() > 1)
    return std::nullopt;
  source.matrix = *m;
  source.axis = indices.getAxis();
  auto &body = source.outer.helper->getRegion(0).front();
  if (!isa<local::ReturnOp>(body.back()) || body.back().getNumOperands() != 1)
    return std::nullopt;
  source.call = body.back().getOperand(0).getDefiningOp<local::ApplyOp>();
  if (!source.call || source.call->getBlock() != &body)
    return std::nullopt;
  auto ref = source.call->getAttrOfType<FlatSymbolRefAttr>("callee");
  Operation *fold =
      ref ? SymbolTable::lookupNearestSymbolFrom(source.call, ref) : nullptr;
  if (!isa_and_nonnull<local::FiniteFoldOp>(fold) ||
      failed(finite::describe(fold, source.inner)) || source.inner.predicate ||
      source.inner.states != 1 || !isa<local::FuncOp>(source.inner.helper))
    return std::nullopt;
  Type field = source.inner.signature.getResult(0);
  if (!isa<algebra::FieldType>(field) ||
      !nativeVector(source.outer.signature.getResult(0), field) ||
      !nativeMatrix(source.outer.signature.getInput(source.matrix), field))
    return std::nullopt;
  Value seed = source.call->getOperand(source.inner.arguments);
  if (auto formal = argument(seed, body)) {
    if (!*formal || seed.getType() != field)
      return std::nullopt;
    source.seed.input = *formal - 1;
  } else {
    auto constant = finite::fieldConstant(seed.getDefiningOp());
    if (!constant || seed.getType() != field)
      return std::nullopt;
    source.seed.constant = *constant;
  }
  for (auto &op : body.without_terminator())
    if (&op != source.call.getOperation() &&
        (&op != seed.getDefiningOp() || !finite::fieldConstant(&op)))
      return std::nullopt;
  // Domain inputs are mapped through the nested call to the actual outer
  // helper environment. Zero denotes the enumerated index, i+1 input i.
  for (Value operand :
       source.call->getOperands().take_front(source.inner.arguments)) {
    auto input = argument(operand, body);
    if (!input)
      return std::nullopt;
    source.inputMap.push_back(*input);
  }
  auto &domain = source.inner.domain.getBody().front();
  llvm::DenseMap<Value, SmallVector<Operation *>> items;
  auto actual = [&](Value value) -> std::optional<unsigned> {
    auto formal = argument(value, domain);
    if (!formal || *formal >= source.inputMap.size())
      return std::nullopt;
    return source.inputMap[*formal];
  };
  for (auto &op : domain.without_terminator()) {
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Operation *> lanes;
      for (Value operand : op.getOperands()) {
        auto found = items.find(operand);
        if (found == items.end())
          return std::nullopt;
        append_range(lanes, found->second);
      }
      items[op.getResult(0)] = std::move(lanes);
      continue;
    }
    if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
             data::DomainMatrixColumnOp>(op))
      return std::nullopt;
    auto input = actual(op.getOperand(0));
    if (!input || !*input)
      return std::nullopt;
    Type type = source.outer.signature.getInput(*input - 1);
    if (isa<data::DomainElementsOp>(op)) {
      if (!nativeVector(type, field))
        return std::nullopt;
    } else {
      auto selected = actual(op.getOperand(1));
      if (*input - 1 != source.matrix || !selected || *selected != 0 ||
          isa<data::DomainMatrixColumnOp>(op) != bool(source.axis))
        return std::nullopt;
    }
    items[op.getResult(0)] = {&op};
  }
  auto root = items.find(domain.back().getOperand(0));
  if (root == items.end())
    return std::nullopt;
  auto &step = source.inner.helper->getRegion(0).front();
  if (std::distance(step.begin(), step.end()) != 3 ||
      !isa<local::ReturnOp>(step.back()) || step.back().getNumOperands() != 1)
    return std::nullopt;
  Operation *add = step.back().getOperand(0).getDefiningOp();
  auto *sumLaw = finite::semantics(add);
  if (!sumLaw || sumLaw->identity != MathematicalIdentity::FieldAdd ||
      !sumLaw->law.total || !sumLaw->law.associative ||
      !sumLaw->law.commutative || add->getBlock() != &step)
    return std::nullopt;
  Value state = step.getArgument(0), term;
  if (add->getOperand(0) == state)
    term = add->getOperand(1);
  else if (add->getOperand(1) == state)
    term = add->getOperand(0);
  else
    return std::nullopt;
  Operation *mul = term.getDefiningOp();
  auto *productLaw = finite::semantics(mul);
  if (!productLaw ||
      productLaw->identity != MathematicalIdentity::FieldMultiply ||
      !productLaw->law.total || !productLaw->law.commutative ||
      mul->getBlock() != &step || mul == add ||
      add->getResult(0).getType() != field ||
      mul->getResult(0).getType() != field)
    return std::nullopt;
  bool matrixLane = false, vectorLane = false;
  for (Value operand : mul->getOperands()) {
    auto item = argument(operand, step);
    if (!item || !*item || *item > root->second.size())
      return std::nullopt;
    auto *access = root->second[*item - 1];
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(access)) {
      if (matrixLane)
        return std::nullopt;
      matrixLane = true;
    } else {
      if (vectorLane)
        return std::nullopt;
      vectorLane = true;
      source.vector = *actual(access->getOperand(0)) - 1;
    }
  }
  if (!matrixLane || !vectorLane)
    return std::nullopt;
  return source;
}

class CandidateReader {
  SymbolTable &symbols;
  llvm::DenseSet<Operation *> &bindings;
  Operation *cursor = nullptr;
  bool valid = true;
  uint64_t remaining = 100000;
  Type index, boolean;
  Value kernel(StringRef contract, ValueRange inputs, Type output,
               ArrayRef<std::string> arguments = {},
               ArrayRef<std::string> parameters = {}) {
    if (!valid || !cursor || !remaining ||
        cursor->getName().getStringRef() !=
            protocol::boundOperationName(contract)) {
      valid = false;
      return {};
    }
    --remaining;
    auto *operation = cursor;
    cursor = cursor->getNextNode();
    auto reference = operation->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        reference
            ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
            : local::OperationBindingOp();
    auto params = operation->getAttrOfType<ArrayAttr>("parameters");
    if (!binding || !params || operation->getAttrs().size() != 3 ||
        !operation->getAttrOfType<StringAttr>("site") ||
        operation->getNumRegions() || operation->getOperands() != inputs ||
        operation->getNumResults() != unsigned(bool(output)) ||
        (output && operation->getResult(0).getType() != output) ||
        binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != arguments.size() ||
        params.size() != parameters.size()) {
      valid = false;
      return {};
    }
    for (auto [attr, value] : zip(binding.getArguments(), arguments))
      if (attr != StringAttr::get(operation->getContext(), value))
        valid = false;
    for (auto [attr, value] : zip(params, parameters))
      if (attr != StringAttr::get(operation->getContext(), value))
        valid = false;
    bindings.insert(binding);
    return valid && output ? operation->getResult(0) : Value();
  }
  void end(StringRef name, Value value) {
    if (!valid || !value || !cursor ||
        cursor->getName().getStringRef() != name ||
        cursor->getOperands() != ValueRange{value} || cursor->getNumResults() ||
        cursor->getNumRegions() || !cursor->getAttrs().empty() ||
        cursor->getNextNode())
      valid = false;
    cursor = nullptr;
  }

public:
  CandidateReader(SymbolTable &symbols, llvm::DenseSet<Operation *> &bindings,
                  MLIRContext *context)
      : symbols(symbols), bindings(bindings),
        index(IntegerType::get(context, 64, IntegerType::Unsigned)),
        boolean(IntegerType::get(context, 1)) {}
  bool check(Operation *original, local::FuncOp candidate) {
    auto source = readSource(original);
    if (!source || !candidate || !candidate.getBody().hasOneBlock() ||
        candidate.getFunctionType() != source->outer.signature)
      return false;
    Builder builder(candidate.getContext());
    auto name = SymbolTable::getSymbolName(original);
    NamedAttrList expected;
    expected.set("sym_name", name);
    expected.set("function_type", TypeAttr::get(source->outer.signature));
    if (auto visibility = original->getAttr("sym_visibility"))
      expected.set("sym_visibility", visibility);
    expected.set("logical_origin",
                 builder.getArrayAttr({name, builder.getArrayAttr({})}));
    if (candidate->getAttrDictionary() !=
        expected.getDictionary(builder.getContext()))
      return false;
    auto &entry = candidate.getBody().front();
    if (entry.empty())
      return false;
    cursor = &entry.front();
    Type output = source->outer.signature.getResult(0);
    Type field = cast<RankedTensorType>(output).getElementType();
    SmallVector<std::string> fieldArgs{
        cast<algebra::FieldType>(field).getDomain().str()};
    Value size = kernel("matrix.dimension", entry.getArgument(source->matrix),
                        index, fieldArgs, {std::to_string(source->axis)});
    Value zero = kernel("index.constant", {}, index, {}, {"0"});
    Value nonempty = kernel("index.less", {zero, size}, boolean);
    if (!valid || !cursor || !isa<local::LocalIfOp>(cursor))
      return false;
    SmallVector<Value> captures(entry.getArguments());
    captures.push_back(size);
    captures.push_back(zero);
    SmallVector<Value> inputs{nonempty};
    append_range(inputs, captures);
    Operation *branch = cursor, *after = cursor->getNextNode();
    if (branch->getOperands() != ValueRange(inputs) ||
        branch->getResultTypes() != TypeRange{output} ||
        branch->getNumRegions() != 2 || branch->getAttrs().size() != 1 ||
        !branch->getAttrOfType<StringAttr>("site"))
      return false;
    for (unsigned region = 0; region < 2; ++region) {
      if (!branch->getRegion(region).hasOneBlock())
        return false;
      auto &block = branch->getRegion(region).front();
      if (block.empty() ||
          block.getArgumentTypes() != ValueRange(captures).getTypes())
        return false;
      cursor = &block.front();
      if (region == 1) {
        Value empty = kernel("vector.empty", {}, output, fieldArgs);
        end("local.yield", empty);
        continue;
      }
      auto &domain = source->inner.domain.getBody().front();
      auto mapped = [&](Value value) {
        auto formal = cast<BlockArgument>(value).getArgNumber();
        unsigned input = source->inputMap[formal];
        return input ? block.getArgument(input - 1)
                     : block.getArgument(entry.getNumArguments() + 1);
      };
      llvm::DenseMap<Value, Value> extents;
      // Ordered domain admission is a separate obligation from the field law.
      // It stays inside the nonempty branch, even when the inner extent is
      // zero.
      for (auto &operation : domain.without_terminator()) {
        if (!valid)
          return false;
        Value extent;
        if (isa<data::DomainElementsOp>(operation))
          extent = kernel("vector.length", mapped(operation.getOperand(0)),
                          index, fieldArgs);
        else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
                     operation)) {
          Value matrix = mapped(operation.getOperand(0));
          Value bound = kernel("matrix.dimension", matrix, index, fieldArgs,
                               {std::to_string(source->axis)});
          Value inRange = kernel(
              "index.less", {mapped(operation.getOperand(1)), bound}, boolean);
          kernel("control.require", inRange, {});
          extent = kernel("matrix.dimension", matrix, index, fieldArgs,
                          {std::to_string(1 - source->axis)});
        } else {
          extent = extents.lookup(operation.getOperand(0));
          for (Value child : operation.getOperands().drop_front()) {
            Value equal =
                kernel("index.equal", {extent, extents.lookup(child)}, boolean);
            kernel("control.require", equal, {});
          }
        }
        extents[operation.getResult(0)] = extent;
      }
      if (!valid)
        return false;
      Value seed = source->seed.input
                       ? block.getArgument(*source->seed.input)
                       : kernel("field.constant", {}, field, fieldArgs,
                                {source->seed.constant});
      Value contracted = kernel(source->axis ? "matrix.transpose_mul_vector"
                                             : "matrix.mul_vector",
                                {block.getArgument(source->matrix),
                                 block.getArgument(source->vector)},
                                output, fieldArgs);
      Value initial = kernel("vector.fill",
                             {seed, block.getArgument(entry.getNumArguments())},
                             output, fieldArgs);
      Value result =
          kernel("vector.add", {initial, contracted}, output, fieldArgs);
      end("local.yield", result);
    }
    cursor = after;
    end("local.return", branch->getResult(0));
    return valid;
  }
};
} // namespace

LogicalResult verifyFiniteCollections(ModuleOp source, ModuleOp candidate) {
  auto refuse = [&](StringRef detail) {
    return diagnostics::emit(candidate.emitError(),
                             "nested-contraction-correspondence", detail);
  };
  if (failed(mlir::verify(source)) || failed(mlir::verify(candidate)))
    return refuse("source or candidate is not admitted");
  if (!hasSingleElement(*source.getBody()) ||
      !hasSingleElement(*candidate.getBody()) ||
      source->getAttrDictionary() != candidate->getAttrDictionary())
    return refuse("module interface changed");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse("unit interface changed");
  SymbolTable symbols(after);
  llvm::DenseSet<Operation *> retained, bindings;
  SmallVector<Operation *> sourceOrder;
  for (auto &operation : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&operation);
    auto *replacement = name ? symbols.lookup(name) : nullptr;
    if (!replacement)
      return refuse("missing surrounding definition");
    retained.insert(replacement);
    sourceOrder.push_back(replacement);
    if (OperationEquivalence::isEquivalentTo(
            &operation, replacement, OperationEquivalence::IgnoreLocations))
      continue;
    if (!isa<local::FiniteCollectOp>(operation) ||
        !CandidateReader(symbols, bindings, candidate.getContext())
             .check(&operation, dyn_cast<local::FuncOp>(replacement)))
      return refuse("collection or unchanged context differs");
  }
  unsigned position = 0;
  for (auto &operation : after.getBody().front()) {
    if (retained.contains(&operation)) {
      if (position >= sourceOrder.size() ||
          sourceOrder[position++] != &operation)
        return refuse("surrounding definition order changed");
    } else if (!bindings.contains(&operation))
      return refuse("unexpected definition or unused binding");
  }
  return success();
}

LogicalResult rewriteFiniteCollections(ModuleOp module,
                                       MathematicalSelectionPolicy policy) {
  if (failed(mlir::verify(module)))
    return failure();
  if (!policy.finiteBulk)
    return success();
  if (!hasSingleElement(*module.getBody()))
    return failure();
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  if (!unit)
    return failure();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  auto candidateUnit =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  Emitter emitter(candidateUnit);
  // Selections borrow only the still-live candidate helper closure. Each outer
  // declaration is replaced immediately; no selection outlives publication.
  SmallVector<Operation *> declarations;
  for (auto &operation : candidateUnit.getBody().front())
    if (isa<local::FiniteCollectOp>(operation))
      declarations.push_back(&operation);
  bool changed = false;
  for (Operation *declaration : declarations)
    if (auto selection = select(declaration)) {
      emitter.run(*selection);
      changed = true;
    }
  if (!changed)
    return success();
  if (failed(verifyFiniteCollections(module, *candidate)))
    return failure();
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  return success();
}
} // namespace zkc::nested
