#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Environment = llvm::DenseMap<Value, Value>;
struct Result {
  Values values;
  bool stopped = false;
};

// Source admission consumes the actual CFG and associates each ordered step
// with its logical SSA ports and closed bodies. Reconstruct only that checked
// control profile. No Local IR or native-program body is used for production.
class ScopedExpander {
  const SourceExecutionClosure &source;
  SymbolTable symbols;
  protocol_ir::ProtocolModuleOp target;
  OpBuilder builder;
  llvm::StringSet<> names;
  unsigned nextRegion = 0;
  unsigned definitions = 0;
  uint64_t remaining = 100000, remainingBytes = 16 * 1024 * 1024;
  bool valid = true;
  std::string root;

  bool charge(Operation *op, uint64_t work) {
    if (!valid)
      return false;
    if (work > remaining) {
      diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit");
      valid = false;
      return false;
    }
    remaining -= work;
    return true;
  }
  bool declaration(Operation *op) {
    if (++definitions <= 4096)
      return true;
    diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit",
                      "expanded definition limit");
    valid = false;
    return false;
  }
  Values values(ValueRange inputs, const Environment &env) {
    Values result;
    for (Value input : inputs)
      result.push_back(env.lookup(input));
    return result;
  }
  Types types(ValueRange values) { return Types(values.getTypes()); }
  std::string site(Operation *op, const Assignments &path) {
    auto original = op->getAttrOfType<StringAttr>("site");
    if (!original)
      return {};
    auto encoded = algorithmSite(path, original.getValue(), remainingBytes);
    if (!encoded) {
      diagnostics::emit(op->emitOpError(), encoded.takeError());
      valid = false;
      return {};
    }
    return *encoded;
  }
  // Inlining can identify distinct immutable capture bindings. Keep the first
  // actual value and substitute every old formal position at the same time.
  SmallVector<unsigned> captures(ValueRange inputs, Values &unique) {
    llvm::DenseMap<Value, unsigned> positions;
    SmallVector<unsigned> indices;
    for (Value input : inputs) {
      auto [found, inserted] = positions.try_emplace(input, unique.size());
      if (inserted)
        unique.push_back(input);
      indices.push_back(found->second);
    }
    return indices;
  }
  func::FuncOp region(func::FuncOp original, ArrayRef<unsigned> indices,
                      ValueRange captured, const Assignments &path,
                      unsigned depth) {
    OpBuilder::InsertionGuard guard(builder);
    std::string name;
    do {
      name = "_execution_region_" + std::to_string(nextRegion++);
    } while (!names.insert(name).second);
    unsigned prefix = original.getNumArguments() - 1 - indices.size();
    Types inputs(original.getArgumentTypes().take_front(1 + prefix));
    append_range(inputs, captured.getTypes());
    if (!declaration(original) || !charge(original, 1 + inputs.size()))
      return {};
    builder.setInsertionPointToEnd(&target.getBody().front());
    auto function = func::FuncOp::create(
        builder, original.getLoc(), name,
        builder.getFunctionType(inputs, original.getResultTypes()));
    NamedAttrList attributes(original->getAttrs());
    attributes.set("sym_name", function->getAttr("sym_name"));
    attributes.set("function_type", function->getAttr("function_type"));
    function->setAttrs(attributes.getDictionary(builder.getContext()));
    if (auto conditions =
            original->getAttrOfType<ArrayAttr>("data.preconditions")) {
      if (!charge(original, conditions.size()))
        return {};
      auto position = [&](unsigned argument) {
        return argument <= prefix ? argument
                                  : 1 + prefix + indices[argument - 1 - prefix];
      };
      SmallVector<Attribute> transported;
      for (Attribute condition : conditions) {
        if (auto bound = dyn_cast<data::IndexBoundAttr>(condition))
          transported.push_back(data::IndexBoundAttr::get(
              builder.getContext(), position(bound.getIndexArg()),
              position(bound.getContainerArg()), bound.getAxis()));
        else {
          auto equal = cast<data::EqualExtentAttr>(condition);
          transported.push_back(data::EqualExtentAttr::get(
              builder.getContext(), position(equal.getLeftArg()),
              equal.getLeftAxis(), position(equal.getRightArg()),
              equal.getRightAxis()));
        }
      }
      function->setAttr("data.preconditions",
                        builder.getArrayAttr(transported));
    }
    function.addEntryBlock();
    builder.setInsertionPointToEnd(&function.front());
    Environment env;
    for (unsigned i = 0; i < prefix; ++i)
      env[original.getArgument(1 + i)] = function.getArgument(1 + i);
    for (auto [i, index] : enumerate(indices))
      env[original.getArgument(1 + prefix + i)] =
          function.getArgument(1 + prefix + index);
    exec::ScopedExecutionBuilder control(builder, function);
    body(original, std::move(env), control, path, depth, false);
    return valid ? function : func::FuncOp();
  }
  Result body(func::FuncOp function, Environment env,
              exec::ScopedExecutionBuilder &control, const Assignments &path,
              unsigned depth, bool inlineReturn) {
    if (depth > 64) {
      diagnostics::emit(function.emitOpError(), "algorithm-expansion-limit");
      valid = false;
      return {};
    }
    const auto &steps = source.bodies.at(function.getSymName().str());
    for (const auto &step : steps) {
      auto *op = step.operation;
      if (!charge(op, 1 + step.inputs.size() + step.outputs.size()))
        return {};
      auto inputs = values(step.inputs, env);
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = symbols.lookup<func::FuncOp>(call.getCallee());
        Assignments nested(path);
        nested.emplace_back(
            call->getAttrOfType<StringAttr>("runtime.site").getValue().str(),
            call.getCallee().str());
        Environment arguments;
        for (auto [formal, actual] :
             zip(callee.getArguments().drop_front(), inputs))
          arguments[formal] = actual;
        auto returned = body(callee, std::move(arguments), control, nested,
                             depth + 1, true);
        if (!valid || returned.stopped)
          return returned;
        for (auto [before, after] : zip(step.outputs, returned.values))
          env[before] = after;
        continue;
      }
      if (isa<exec::ReturnOp>(op)) {
        if (!inlineReturn)
          control.returned(inputs);
        return {std::move(inputs), false};
      }
      if (isa<exec::CompleteOp>(op)) {
        control.complete(inputs);
        return {std::move(inputs), false};
      }
      if (isa<runtime::ReleaseBindingsOp>(op)) {
        control.release(inputs);
        continue;
      }
      auto occurrence = site(op, path);
      if (!valid)
        return {};
      if (auto reject = dyn_cast<exec::RejectOp>(op)) {
        control.reject(reject.getReason(), occurrence);
        return {{}, true};
      }
      Values outputs;
      auto outputTypes = types(step.outputs);
      if (!step.regions.empty()) {
        unsigned prefix = isa<exec::RangeOp>(op) ? 2 + step.outputs.size() : 1;
        Values unique;
        auto indices = captures(ArrayRef(inputs).drop_front(prefix), unique);
        auto outline = [&](unsigned index) {
          return region(step.regions[index], indices, unique, path, depth + 1);
        };
        if (isa<exec::TestOp>(op)) {
          outputs = control.conditional(inputs.front(), unique, outputTypes,
                                        occurrence, outline);
        } else if (auto match = dyn_cast<exec::MatchOp>(op)) {
          SmallVector<std::string> alternatives;
          for (Attribute value : match.getAlternatives())
            alternatives.push_back(cast<StringAttr>(value).str());
          outputs = control.match(inputs.front(), unique, outputTypes,
                                  alternatives, occurrence, outline);
        } else {
          outputs = control.loop(inputs[0], inputs[1],
                                 ArrayRef(inputs).slice(2, step.outputs.size()),
                                 unique, outputTypes, step.conditional,
                                 occurrence, outline);
        }
      } else {
        NamedAttrList attributes(op->getAttrs());
        attributes.set("site", builder.getStringAttr(occurrence));
        outputs = control.invoke(op->getName().getStringRef(), outputTypes,
                                 control.scoped(inputs), attributes.getAttrs());
      }
      if (!valid)
        return {};
      for (auto [before, after] : zip(step.outputs, outputs))
        env[before] = after;
    }
    valid = false;
    return {};
  }

public:
  ScopedExpander(const SourceExecutionClosure &source, Operation *original,
                 protocol_ir::ProtocolModuleOp target)
      : source(source), symbols(original), target(target),
        builder(target.getContext()) {
    for (Operation &op : original->getRegion(0).front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  LogicalResult run(Operation *original) {
    // The input is independently admitted before any cloning or substitution.
    // Its non-execution declarations remain exact and in their original order.
    for (Operation &op : original->getRegion(0).front()) {
      auto function = dyn_cast<func::FuncOp>(op);
      if (!function || !isScopedExecutionFunction(function)) {
        if (!declaration(&op))
          return failure();
        builder.setInsertionPointToEnd(&target.getBody().front());
        builder.clone(op);
        continue;
      }
      if (function->hasAttr("runtime.region"))
        continue;
      if (!declaration(function) ||
          !charge(function, function.getNumArguments()))
        return failure();
      root = function.getSymName().str();
      builder.setInsertionPointToEnd(&target.getBody().front());
      auto copied = func::FuncOp::create(builder, function.getLoc(), root,
                                         function.getFunctionType());
      copied->setAttrs(function->getAttrs());
      copied.addEntryBlock();
      builder.setInsertionPointToEnd(&copied.front());
      Environment env;
      for (auto [before, after] : zip(function.getArguments().drop_front(),
                                      copied.getArguments().drop_front()))
        env[before] = after;
      exec::ScopedExecutionBuilder control(builder, copied);
      body(function, std::move(env), control, {}, 0, false);
      if (!valid)
        return failure();
    }
    return success();
  }
};
} // namespace

OwningOpRef<ModuleOp>
expandScopedHelpers(ModuleOp source, std::vector<AlgorithmOrigin> *origins) {
  if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner)
    return {};
  auto closure = readSourceExecutionClosure(owner);
  if (!closure) {
    diagnostics::emit(owner.emitOpError(), closure.takeError());
    return {};
  }
  OwningOpRef<ModuleOp> candidate(ModuleOp::create(source.getLoc()));
  candidate->getOperation()->setAttrs(source->getAttrs());
  OpBuilder builder(candidate->getBodyRegion());
  auto target = protocol_ir::ProtocolModuleOp::create(builder, owner.getLoc(),
                                                      owner.getProfileAttr());
  target->setAttrs(owner->getAttrs());
  target.getBody().push_back(new Block);
  if (failed(ScopedExpander(*closure, owner, target).run(owner)) ||
      failed(verify(*candidate)) ||
      failed(verifyScopedHelperExpansionPreserved(source, *candidate, origins)))
    return {};
  return candidate;
}
} // namespace zkc::protocol
