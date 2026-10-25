#include "AlgorithmSupport.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Transforms/NestedContractions.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include <map>

#include "NestedContractionVerification.h"
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

std::optional<unsigned> argument(Value value, Block &block) {
  auto arg = dyn_cast<BlockArgument>(value);
  if (!arg || arg.getOwner() != &block)
    return std::nullopt;
  return arg.getArgNumber();
}
bool nativeVector(Type type, Type field) {
  auto vector = dyn_cast<algebra::FieldVectorType>(type);
  return vector && vector.getElementType() == field;
}
bool nativeMatrix(Type type, Type field) {
  auto matrix = dyn_cast<algebra::FieldMatrixType>(type);
  return matrix && matrix.getElementType() == field;
}
struct Seed {
  std::optional<unsigned> input;
  std::string constant;
};
// Independent source reader. It reconstructs the returned scalar term and its
// input map from the actual callback SSA and actual descriptor constructors.
// It deliberately does not use the computation analysis or selector.
struct Source {
  finite::Computation outer, inner;
  local::ApplyOp call;
  unsigned matrix = 0, vector = 0, axis = 0;
  Seed seed;
  SmallVector<unsigned> inputMap;
};
// Reconstruct neutral scalar paths from source SSA. The complete body is
// inspected, including unused work and implementation pins. This reader owns
// its traversal and consumes no producer equations or structural witnesses.
class ScalarSource {
public:
  // The same helper SSA at two calls is two distinct occurrences. These pairs
  // only address actual source SSA; they do not contain an expression model.
  using Scalar = std::pair<Value, unsigned>;

private:
  struct Invocation {
    Block *body;
    llvm::DenseMap<Value, Scalar> values;
  };
  SmallVector<Invocation> invocations;
  SmallVector<Scalar> instructions;
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection symbols;
  Operation *nestedCall;
  uint64_t remaining = 100000;
  bool charge(Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining) {
      valid = false;
      return false;
    }
    remaining -= cost;
    return true;
  }
  Scalar actual(Value value, unsigned invocation) {
    if (!remaining || invocation >= invocations.size()) {
      valid = false;
      return {};
    }
    --remaining;
    auto found = invocations[invocation].values.find(value);
    if (found == invocations[invocation].values.end()) {
      valid = false;
      return {};
    }
    return found->second;
  }
  SmallVector<Scalar> read(Block &body, ArrayRef<Scalar> arguments,
                           bool numerical) {
    auto *owner = body.getParentOp();
    if (active.size() >= 64 || !active.insert(owner).second || body.empty() ||
        body.getNumArguments() != arguments.size() || !charge(owner)) {
      valid = false;
      return {};
    }
    auto leave = llvm::scope_exit([&] { active.erase(owner); });
    unsigned invocation = invocations.size();
    invocations.emplace_back();
    invocations.back().body = &body;
    for (auto [formal, input] : zip(body.getArguments(), arguments)) {
      if (!input.first || formal.getType() != input.first.getType()) {
        valid = false;
        return {};
      }
      invocations[invocation].values[formal] = input;
    }
    for (auto &op : body.without_terminator()) {
      if (!charge(&op) || op.getNumRegions()) {
        valid = false;
        return {};
      }
      SmallVector<Scalar> inputs;
      for (Value operand : op.getOperands())
        inputs.push_back(actual(operand, invocation));
      if (!valid)
        return {};
      func::FuncOp helper;
      if (auto call = dyn_cast<kernel::CallOp>(op)) {
        if (auto policy = call->getAttrOfType<ArrayAttr>("policy"))
          if (policy.size() != 3 || !isa<BoolAttr>(policy[0]) ||
              !isa<BoolAttr>(policy[1]) || !isa<BoolAttr>(policy[2]) ||
              !cast<BoolAttr>(policy[0]).getValue()) {
            valid = false;
            return {};
          }
        helper = kernel::resolve(call, symbols);
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        helper = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
      }
      if (isa<kernel::CallOp, func::CallOp>(op)) {
        if (!helper || !helper.getBody().hasOneBlock()) {
          valid = false;
          return {};
        }
        auto outputs = read(helper.front(), inputs, true);
        if (!valid || outputs.size() != op.getNumResults()) {
          valid = false;
          return {};
        }
        for (auto [result, output] : zip(op.getResults(), outputs)) {
          if (result.getType() != output.first.getType()) {
            valid = false;
            return {};
          }
          invocations[invocation].values[result] = output;
        }
        continue;
      }
      auto *meaning = finite::semantics(&op);
      if (op.getNumResults() != 1 ||
          (&op != nestedCall &&
           (!meaning || !meaning->law.total || meaning->access ||
            !finite::replaceable(&op)))) {
        valid = false;
        return {};
      }
      Scalar value{op.getResult(0), invocation};
      instructions.push_back(value);
      invocations[invocation].values[op.getResult(0)] = value;
    }
    auto &end = body.back();
    if (!charge(&end) ||
        (numerical ? !isa<func::ReturnOp>(end) : !isa<local::ReturnOp>(end))) {
      valid = false;
      return {};
    }
    SmallVector<Scalar> outputs;
    for (Value operand : end.getOperands())
      outputs.push_back(actual(operand, invocation));
    return outputs;
  }

public:
  bool valid = true;
  ScalarSource(Block &body, Operation *nestedCall = nullptr)
      : nestedCall(nestedCall) {
    SmallVector<Scalar> arguments;
    for (Value value : body.getArguments())
      arguments.emplace_back(value, 0);
    auto outputs = read(body, arguments, false);
    if (!valid)
      return;
    llvm::DenseSet<Scalar> live(outputs.begin(), outputs.end());
    for (auto value : llvm::reverse(instructions)) {
      auto *op = value.first.getDefiningOp();
      if (!charge(op) || !live.contains(value)) {
        valid = false;
        return;
      }
      for (Value input : op->getOperands())
        live.insert(actual(input, value.second));
    }
  }
  Scalar scalar(Value value) { return scalar(actual(value, 0)); }
  Scalar operand(Scalar value, unsigned index) {
    if (!value.first || !value.first.getDefiningOp() ||
        index >= value.first.getDefiningOp()->getNumOperands()) {
      valid = false;
      return {};
    }
    return scalar(
        actual(value.first.getDefiningOp()->getOperand(index), value.second));
  }
  std::optional<unsigned> input(Scalar value) {
    return valid && !invocations.empty() && value.second == 0
               ? argument(value.first, *invocations[0].body)
               : std::nullopt;
  }
  Scalar scalar(Scalar value) {
    for (unsigned depth = 0; valid && value.first && depth < 64; ++depth) {
      if (!remaining) {
        valid = false;
        return {};
      }
      --remaining;
      auto *op = value.first.getDefiningOp();
      const auto *meaning = finite::semantics(op);
      if (!meaning || op->getNumOperands() != 2 ||
          meaning->law.algebra != protocol::ComputationAlgebra::FieldRing)
        break;
      auto neutral = [&](Value operand, protocol::ScalarIdentity identity) {
        auto resolved = actual(operand, value.second);
        if (!resolved.first)
          return false;
        auto *constant = resolved.first.getDefiningOp();
        const auto *constantMeaning = finite::semantics(constant);
        if (!constantMeaning ||
            constantMeaning->identity != MathematicalIdentity::FieldConstant)
          return false;
        auto text = finite::fieldConstant(constant);
        return (identity == protocol::ScalarIdentity::Zero && text == "0") ||
               (identity == protocol::ScalarIdentity::One && text == "1");
      };
      if (neutral(op->getOperand(1), meaning->law.rightIdentity))
        value = actual(op->getOperand(0), value.second);
      else if (neutral(op->getOperand(0), meaning->law.leftIdentity))
        value = actual(op->getOperand(1), value.second);
      else
        break;
    }
    return valid ? value : Scalar();
  }
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
  for (Operation &op : body.without_terminator())
    if (auto call = dyn_cast<local::ApplyOp>(op)) {
      if (source.call)
        return std::nullopt;
      source.call = call;
    }
  ScalarSource outerScalar(body, source.call);
  if (!source.call || !outerScalar.valid ||
      outerScalar.scalar(body.back().getOperand(0)) !=
          outerScalar.scalar(source.call.getResult(0)))
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
  auto seed =
      outerScalar.scalar(source.call->getOperand(source.inner.arguments));
  if (!outerScalar.valid || !seed.first)
    return std::nullopt;
  if (auto formal = outerScalar.input(seed)) {
    if (!*formal || seed.first.getType() != field)
      return std::nullopt;
    source.seed.input = *formal - 1;
  } else {
    auto constant = finite::fieldConstant(seed.first.getDefiningOp());
    if (!constant || !finite::replaceable(seed.first.getDefiningOp()) ||
        seed.first.getType() != field)
      return std::nullopt;
    source.seed.constant = *constant;
  }
  // Domain inputs are mapped through the nested call to the actual outer
  // helper environment. Zero denotes the enumerated index, i+1 input i.
  for (Value operand :
       source.call->getOperands().take_front(source.inner.arguments)) {
    auto input = outerScalar.input(outerScalar.scalar(operand));
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
  if (!isa<local::ReturnOp>(step.back()) || step.back().getNumOperands() != 1)
    return std::nullopt;
  ScalarSource innerScalar(step);
  auto sum = innerScalar.scalar(step.back().getOperand(0));
  if (!innerScalar.valid || !sum.first)
    return std::nullopt;
  Operation *add = sum.first.getDefiningOp();
  auto *sumLaw = finite::replaceable(add) ? finite::semantics(add) : nullptr;
  if (!sumLaw || sumLaw->identity != MathematicalIdentity::FieldAdd ||
      !sumLaw->law.total || !sumLaw->law.associative ||
      !sumLaw->law.commutative)
    return std::nullopt;
  ScalarSource::Scalar state{step.getArgument(0), 0}, term;
  auto left = innerScalar.operand(sum, 0);
  auto right = innerScalar.operand(sum, 1);
  if (left == state)
    term = right;
  else if (right == state)
    term = left;
  else
    return std::nullopt;
  if (!innerScalar.valid || !term.first)
    return std::nullopt;
  Operation *mul = term.first.getDefiningOp();
  auto *productLaw =
      finite::replaceable(mul) ? finite::semantics(mul) : nullptr;
  if (!productLaw ||
      productLaw->identity != MathematicalIdentity::FieldMultiply ||
      !productLaw->law.total || !productLaw->law.commutative || mul == add ||
      add->getResult(0).getType() != field ||
      mul->getResult(0).getType() != field)
    return std::nullopt;
  bool matrixLane = false, vectorLane = false;
  for (unsigned index = 0; index < mul->getNumOperands(); ++index) {
    auto item = innerScalar.input(innerScalar.operand(term, index));
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
  if (!innerScalar.valid || !matrixLane || !vectorLane)
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
  const Record &input;
  Record &expected;
  std::string functionName;
  std::optional<Occurrence> admissionOrigin;
  std::optional<Location> admissionLocation;
  unsigned admissionOccurrence = 0;
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
        reference ? symbols.lookup<runtime::BindingOp>(reference.getValue())
                  : runtime::BindingOp();
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
    if (admissionOrigin) {
      admissionOrigin->originalSite =
          "finite_" + std::to_string(admissionOccurrence++);
      if (contract == "control.require") {
        auto encoded = protocol::algorithmSite(admissionOrigin->path,
                                               admissionOrigin->originalSite,
                                               expected.checkOriginBytes);
        auto measured = protocol::algorithmSite(admissionOrigin->path,
                                                admissionOrigin->originalSite,
                                                expected.originBytes);
        if (!encoded || !measured) {
          consumeError(encoded.takeError());
          consumeError(measured.takeError());
          valid = false;
        } else {
          valid &= protocol::attr(operation, "site") == *encoded &&
                   operation->getLoc() == *admissionLocation &&
                   expected.occurrences
                       .emplace(protocol::detail::OccurrenceKey{functionName,
                                                                *encoded},
                                *admissionOrigin)
                       .second;
        }
      }
    }
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
                  MLIRContext *context, const Record &input, Record &expected)
      : symbols(symbols), bindings(bindings),
        index(IntegerType::get(context, 64, IntegerType::Unsigned)),
        boolean(IntegerType::get(context, 1)), input(input),
        expected(expected) {}
  bool check(Operation *original, local::FuncOp candidate) {
    auto source = readSource(original);
    if (!source || !candidate || !candidate.getBody().hasOneBlock() ||
        candidate.getFunctionType() != source->outer.signature)
      return false;
    Builder builder(candidate.getContext());
    auto name = SymbolTable::getSymbolName(original);
    functionName = name.str();
    auto origin = innerOrigin(source->call, source->inner.operation, input);
    if (origin.path.size() > 64 || origin.depth > 64)
      return false;
    NamedAttrList attributes;
    attributes.set("sym_name", name);
    attributes.set("function_type", TypeAttr::get(source->outer.signature));
    if (auto visibility = original->getAttr("sym_visibility"))
      attributes.set("sym_visibility", visibility);
    attributes.set("logical_origin",
                   builder.getArrayAttr({name, builder.getArrayAttr({})}));
    if (candidate->getAttrDictionary() !=
        attributes.getDictionary(builder.getContext()))
      return false;
    auto &entry = candidate.getBody().front();
    if (entry.empty())
      return false;
    cursor = &entry.front();
    Type output = source->outer.signature.getResult(0);
    Type field = cast<algebra::FieldVectorType>(output).getElementType();
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
      admissionOrigin = origin;
      admissionLocation = source->inner.operation->getLoc();
      admissionOccurrence = 0;
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
      admissionOrigin.reset();
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

LogicalResult checkFiniteCollections(ModuleOp source, ModuleOp candidate,
                                     const Record &input, Record &expected,
                                     Record *output) {
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
        !CandidateReader(symbols, bindings, candidate.getContext(), input,
                         expected)
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
  if (output) {
    if (!expected.sameExpansion(*output))
      return refuse("occurrence records or cumulative limits differ");
    output->checkOriginBytes = expected.checkOriginBytes;
  }
  return success();
}

LogicalResult verifyFiniteCollections(ModuleOp source, ModuleOp candidate) {
  Record input, expected;
  return checkFiniteCollections(source, candidate, input, expected);
}

LogicalResult verifyFiniteCollections(
    ModuleOp source, ModuleOp candidate,
    const protocol::AlgorithmExpansionState &sourceState,
    const protocol::AlgorithmExpansionState &candidateState) {
  const auto &input = StateAccess::get(sourceState);
  const auto &candidateRecord = StateAccess::get(candidateState);
  if (!input.retained || input.finished || !candidateRecord.retained ||
      candidateRecord.finished)
    return diagnostics::emit(candidate.emitError(),
                             "nested-contraction-correspondence",
                             "expected retained, unfinished preparation");
  auto expected = input, output = candidateRecord;
  return checkFiniteCollections(source, candidate, input, expected, &output);
}

} // namespace zkc::nested
