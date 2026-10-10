#include "zkc/Transforms/VectorReductions.h"
#include "AlgorithmSupport.h"
#include "MathematicalSupport.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/detail/Builders.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
using Record = protocol::detail::AlgorithmExpansionRecord;
using Occurrence = protocol::detail::AlgorithmOccurrence;
using StateAccess = protocol::detail::AlgorithmStateAccess;
using Products = std::map<std::string, std::pair<unsigned, unsigned>>;

protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return {};
  auto root =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  return root && root.getProfile() == protocol_ir::Profile::Protocol
             ? root
             : protocol_ir::ProtocolModuleOp();
}
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "vector-reduction-correspondence",
                           reason);
}
bool fieldBound(StringRef contract) {
  return !contract.starts_with("index.") && contract != "control.require";
}
ArrayAttr arguments(MLIRContext *context, StringRef contract, StringRef field) {
  return ArrayAttr::get(
      context, fieldBound(contract)
                   ? ArrayRef<Attribute>{StringAttr::get(context, field)}
                   : ArrayRef<Attribute>{});
}
// Symbol allocation is a naming convention only, shared with the reader. It
// grants no operation or formula semantics and creates no candidate IR.
class BindingNames {
  llvm::StringSet<> names;
  std::map<std::pair<std::string, std::string>, std::string> assigned;
  unsigned next = 0;

public:
  explicit BindingNames(protocol_ir::ProtocolModuleOp root) {
    for (Operation &op : root.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  StringRef get(StringRef contract, StringRef field) {
    auto key =
        std::make_pair(contract.str(), fieldBound(contract) ? field.str() : "");
    auto found = assigned.find(key);
    if (found != assigned.end())
      return found->second;
    std::string name;
    do {
      name = "_vector_reduction_binding_" + std::to_string(next++);
    } while (!names.insert(name).second);
    return assigned.emplace(std::move(key), std::move(name)).first->second;
  }
};

// Exact native contract recognition, never a source reducer spelling. The
// typed operation and its resolved logical binding must both agree.
algebra::MapRealizeOp productMap(local::ApplyOp call, SymbolTable &symbols,
                                 const Products &products) {
  if (!call || call->getNumResults() != 1 || !call->getResult(0).hasOneUse() ||
      !products.count(call.getCallee().str()))
    return {};
  auto map = symbols.lookup<algebra::MapRealizeOp>(call.getCallee());
  auto sum = dyn_cast_if_present<algebra::VectorSumOp>(call->getNextNode());
  if (!map || !sum || sum->getNumOperands() != 1 ||
      sum->getOperand(0) != call->getResult(0))
    return {};
  auto reference = sum->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding =
      reference
          ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
          : local::OperationBindingOp();
  auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
  if (!binding || binding.getContract() != "vector.sum" ||
      !binding.getImplementation().empty() ||
      binding.getArguments() !=
          arguments(call.getContext(), "vector.sum", field.getDomain()) ||
      sum->getAttrOfType<ArrayAttr>("parameters") !=
          ArrayAttr::get(call.getContext(), {}))
    return {};
  return map;
}

class Rewriter {
  protocol_ir::ProtocolModuleOp root;
  SymbolTable symbols;
  BindingNames names;
  llvm::StringSet<> emitted;
  OpBuilder builder;
  Record &record;

public:
  Rewriter(protocol_ir::ProtocolModuleOp root, Record &record)
      : root(root), symbols(root), names(root), builder(root.getContext()),
        record(record) {}
  LogicalResult run(const Products &products) {
    SmallVector<local::ApplyOp> calls;
    root.walk([&](local::ApplyOp call) { calls.push_back(call); });
    for (auto call : calls) {
      auto map = productMap(call, symbols, products);
      if (!map)
        continue;
      auto function = call->getParentOfType<local::FuncOp>();
      auto saved = protocol::detail::occurrence(record, function.getSymName(),
                                                protocol::attr(call, "site"));
      if (!saved)
        return refuse(call, "missing retained occurrence");
      Occurrence origin = *saved;
      origin.path.emplace_back(origin.originalSite, map.getHelper().str());
      origin.definition = map.getHelper().str();
      origin.declaration = map.getSymName().str();
      ++origin.depth;
      if (origin.depth > 64 || origin.path.size() > 64)
        return diagnostics::emit(call.emitOpError(), "interactive-call-depth");
      record.occurrences.erase(
          {function.getSymName().str(), protocol::attr(call, "site").str()});
      Operation *sum = call->getNextNode();
      auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
      builder.setInsertionPoint(call);
      unsigned nextSite = 0;
      auto emit = [&](StringRef contract, ValueRange inputs, Type output,
                      bool guard) -> Operation * {
        if (!record.work) {
          diagnostics::emit(call.emitOpError(), "algorithm-expansion-limit");
          return nullptr;
        }
        --record.work;
        auto name = names.get(contract, field.getDomain());
        if (emitted.insert(name).second) {
          OpBuilder::InsertionGuard position(builder);
          builder.setInsertionPointToStart(&root.getBody().front());
          local::OperationBindingOp::create(
              builder, map.getLoc(), name, contract,
              arguments(root.getContext(), contract, field.getDomain()), "");
        }
        std::string site = protocol::attr(sum, "site").str();
        if (guard) {
          origin.originalSite = "map_" + std::to_string(nextSite++);
          auto encoded = protocol::algorithmSite(
              origin.path, origin.originalSite, record.originBytes);
          if (!encoded) {
            diagnostics::emit(call.emitOpError(), encoded.takeError());
            return nullptr;
          }
          site = std::move(*encoded);
          if (!record.occurrences
                   .emplace(
                       protocol::detail::OccurrenceKey{
                           function.getSymName().str(), site},
                       origin)
                   .second) {
            (void)refuse(call, "colliding generated occurrence");
            return nullptr;
          }
        }
        OperationState state(guard ? map.getLoc() : sum->getLoc(),
                             protocol::boundOperationName(contract));
        state.addOperands(inputs);
        if (output)
          state.addTypes(output);
        state.addAttribute("binding",
                           FlatSymbolRefAttr::get(root.getContext(), name));
        state.addAttribute("site", builder.getStringAttr(site));
        state.addAttribute("parameters", builder.getArrayAttr({}));
        return builder.create(state);
      };
      Value rows;
      auto index =
          IntegerType::get(root.getContext(), 64, IntegerType::Unsigned);
      for (auto [i, row] : enumerate(map.getRowwise())) {
        if (!row)
          continue;
        auto length = emit("vector.length", call->getOperand(i), index, true);
        if (!length)
          return failure();
        if (!rows)
          rows = length->getResult(0);
        else {
          auto equal = emit("index.equal", {rows, length->getResult(0)},
                            builder.getI1Type(), true);
          if (!equal || !emit("control.require", equal->getResult(0), {}, true))
            return failure();
        }
      }
      auto [left, right] = products.at(map.getSymName().str());
      auto dot =
          emit("vector.dot", {call->getOperand(left), call->getOperand(right)},
               field, false);
      if (!dot)
        return failure();
      sum->getResult(0).replaceAllUsesWith(dot->getResult(0));
      sum->erase();
      call.erase();
    }
    return success();
  }
};

// A reader of the actual candidate, using source SSA substitution. It neither
// builds replacement IR nor calls Rewriter. Unselected pairs must be identical.
class Correspondence {
  using Values = llvm::DenseMap<Value, Value>;
  SymbolTable originalSymbols, candidateSymbols;
  BindingNames names;
  const Products &products;
  const Record &input;
  Record expected;
  llvm::DenseSet<Operation *> addedBindings;
  std::string function;

  bool charge() {
    if (!expected.checkWork)
      return false;
    --expected.checkWork;
    return true;
  }
  LogicalResult bind(ValueRange before, ValueRange after, Values &values) {
    if (before.size() != after.size())
      return failure();
    for (auto [a, b] : zip(before, after)) {
      if (a.getType() != b.getType())
        return failure();
      values[a] = b;
    }
    return success();
  }
  LogicalResult replacement(local::ApplyOp call, algebra::MapRealizeOp map,
                            Operation *sum, Block &target,
                            Block::iterator &cursor, Values &values) {
    auto saved = protocol::detail::occurrence(input, function,
                                              protocol::attr(call, "site"));
    if (!saved)
      return refuse(call, "missing retained occurrence");
    Occurrence origin = *saved;
    origin.path.emplace_back(origin.originalSite, map.getHelper().str());
    origin.definition = map.getHelper().str();
    origin.declaration = map.getSymName().str();
    ++origin.depth;
    if (origin.depth > 64 || origin.path.size() > 64)
      return refuse(call, "occurrence depth");
    expected.occurrences.erase({function, protocol::attr(call, "site").str()});
    auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
    unsigned nextSite = 0;
    auto primitive = [&](StringRef contract, ValueRange operands, Type result,
                         bool guard) -> Operation * {
      if (!charge() || !expected.work || cursor == target.end())
        return nullptr;
      --expected.work;
      Operation *actual = &*cursor++;
      std::string site = protocol::attr(sum, "site").str();
      if (guard) {
        origin.originalSite = "map_" + std::to_string(nextSite++);
        auto encoded = protocol::algorithmSite(origin.path, origin.originalSite,
                                               expected.checkOriginBytes);
        if (!encoded) {
          consumeError(encoded.takeError());
          return nullptr;
        }
        auto measured = protocol::algorithmSite(
            origin.path, origin.originalSite, expected.originBytes);
        if (!measured) {
          consumeError(measured.takeError());
          return nullptr;
        }
        site = std::move(*encoded);
        if (!expected.occurrences
                 .emplace(protocol::detail::OccurrenceKey{function, site},
                          origin)
                 .second)
          return nullptr;
      }
      auto name = names.get(contract, field.getDomain());
      auto binding = candidateSymbols.lookup<local::OperationBindingOp>(name);
      if (!binding || binding.getContract() != contract ||
          !binding.getImplementation().empty() ||
          binding.getArguments() !=
              arguments(call.getContext(), contract, field.getDomain()) ||
          binding->getAttrs().size() != 4 ||
          actual->getName().getStringRef() !=
              protocol::boundOperationName(contract) ||
          actual->getNumRegions() ||
          actual->getNumResults() != unsigned(bool(result)) ||
          (result && actual->getResult(0).getType() != result) ||
          !llvm::equal(actual->getOperands(), operands) ||
          actual->getAttrs().size() != 3 ||
          protocol::attr(actual, "site") != site ||
          actual->getAttrOfType<FlatSymbolRefAttr>("binding") !=
              FlatSymbolRefAttr::get(call.getContext(), name) ||
          actual->getAttrOfType<ArrayAttr>("parameters") !=
              ArrayAttr::get(call.getContext(), {}))
        return nullptr;
      addedBindings.insert(binding);
      return actual;
    };
    Value rows;
    Type index = IntegerType::get(call.getContext(), 64, IntegerType::Unsigned);
    for (auto [i, row] : enumerate(map.getRowwise())) {
      if (!row)
        continue;
      auto operand = values.lookup(call->getOperand(i));
      if (!operand)
        return refuse(call, "unbound collection");
      auto length = primitive("vector.length", operand, index, true);
      if (!length)
        return refuse(call, "ordered row length");
      if (!rows)
        rows = length->getResult(0);
      else {
        auto equal = primitive("index.equal", {rows, length->getResult(0)},
                               IntegerType::get(call.getContext(), 1), true);
        if (!equal ||
            !primitive("control.require", equal->getResult(0), {}, true))
          return refuse(call, "ordered shape guard");
      }
    }
    auto [left, right] = products.at(map.getSymName().str());
    auto a = values.lookup(call->getOperand(left)),
         b = values.lookup(call->getOperand(right));
    auto dot = a && b ? primitive("vector.dot", {a, b}, field, false) : nullptr;
    if (!dot || failed(bind(sum->getResults(), dot->getResults(), values)))
      return refuse(call, "dot operands or result");
    return success();
  }
  LogicalResult block(Block &source, Block &target, unsigned depth) {
    if (depth > 64)
      return refuse(source.getParentOp(), "region depth");
    Values values;
    if (failed(bind(source.getArguments(), target.getArguments(), values)))
      return refuse(target.getParentOp(), "block arguments");
    auto cursor = target.begin();
    for (auto it = source.begin(); it != source.end(); ++it) {
      Operation &op = *it;
      if (!charge() || cursor == target.end())
        return refuse(&op, "work limit or missing operation");
      auto call = dyn_cast<local::ApplyOp>(op);
      auto map = productMap(call, originalSymbols, products);
      if (map && !isa<local::ApplyOp>(*cursor)) {
        Operation *sum = &*++it;
        if (failed(replacement(call, map, sum, target, cursor, values)))
          return failure();
        continue;
      }
      Operation &actual = *cursor++;
      if (op.getName() != actual.getName() ||
          op.getAttrDictionary() != actual.getAttrDictionary() ||
          op.getNumRegions() != actual.getNumRegions() ||
          op.getResultTypes() != actual.getResultTypes() ||
          op.getNumOperands() != actual.getNumOperands())
        return refuse(&actual, "surrounding operation");
      for (auto [a, b] : zip(op.getOperands(), actual.getOperands()))
        if (!values.lookup(a) || values.lookup(a) != b)
          return refuse(&actual, "surrounding operand or result substitution");
      for (auto [a, b] : zip(op.getRegions(), actual.getRegions()))
        if (!a.hasOneBlock() || !b.hasOneBlock() ||
            failed(block(a.front(), b.front(), depth + 1)))
          return refuse(&actual, "region correspondence");
      if (failed(bind(op.getResults(), actual.getResults(), values)))
        return refuse(&actual, "result correspondence");
    }
    return cursor == target.end()
               ? success()
               : refuse(target.getParentOp(), "extra operation");
  }

public:
  Correspondence(protocol_ir::ProtocolModuleOp original,
                 protocol_ir::ProtocolModuleOp candidate,
                 const Products &products, const Record &input)
      : originalSymbols(original), candidateSymbols(candidate), names(original),
        products(products), input(input), expected(input) {}
  LogicalResult run(protocol_ir::ProtocolModuleOp original,
                    protocol_ir::ProtocolModuleOp candidate, Record &output) {
    llvm::DenseSet<Operation *> retained;
    for (Operation &op : original.getBody().front()) {
      if (!charge())
        return refuse(&op, "declaration work limit");
      auto name = SymbolTable::getSymbolName(&op);
      auto actual = name ? candidateSymbols.lookup(name.getValue()) : nullptr;
      if (!actual)
        return refuse(&op, "missing declaration");
      retained.insert(actual);
      if (auto local = dyn_cast<local::FuncOp>(op)) {
        auto replacement = dyn_cast<local::FuncOp>(actual);
        if (!replacement ||
            local->getAttrDictionary() != actual->getAttrDictionary() ||
            !local.getBody().hasOneBlock() ||
            !replacement.getBody().hasOneBlock())
          return refuse(actual, "local declaration");
        function = local.getSymName().str();
        if (failed(block(local.getBody().front(), replacement.getBody().front(),
                         0)))
          return failure();
      } else if (!OperationEquivalence::isEquivalentTo(
                     &op, actual, OperationEquivalence::IgnoreLocations))
        return refuse(actual, "changed declaration");
    }
    auto originalOrder = original.getBody().front().begin();
    for (Operation &op : candidate.getBody().front()) {
      if (retained.contains(&op)) {
        if (originalOrder == original.getBody().front().end() ||
            SymbolTable::getSymbolName(&*originalOrder++) !=
                SymbolTable::getSymbolName(&op))
          return refuse(&op, "retained declaration order");
      } else if (!addedBindings.contains(&op))
        return refuse(&op, "unexpected declaration");
    }
    if (expected.occurrences != output.occurrences ||
        expected.work != output.work ||
        expected.originBytes != output.originBytes ||
        expected.retained != output.retained ||
        expected.finished != output.finished)
      return refuse(candidate, "occurrence records or cumulative limits");
    output.checkWork = expected.checkWork;
    output.checkOriginBytes = expected.checkOriginBytes;
    return success();
  }
};
LogicalResult check(ModuleOp original, ModuleOp candidate, const Record &input,
                    Record &output) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto before = unit(original), after = unit(candidate);
  if (!input.retained || input.finished || !before || !after ||
      original->getAttrDictionary() != candidate->getAttrDictionary() ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse(candidate, "retained preparation context");
  auto products = describeMapProducts(original);
  if (failed(products))
    return failure();
  return Correspondence(before, after, *products, input)
      .run(before, after, output);
}
} // namespace
LogicalResult verifyVectorReductionsPreserved(
    ModuleOp original, ModuleOp candidate,
    const protocol::AlgorithmExpansionState &originalState,
    const protocol::AlgorithmExpansionState &candidateState) {
  auto output = StateAccess::get(candidateState);
  return check(original, candidate, StateAccess::get(originalState), output);
}
LogicalResult fuseVectorReductions(ModuleOp module,
                                   protocol::AlgorithmExpansionState &state) {
  const auto &input = StateAccess::get(state);
  if (!input.retained || input.finished || !unit(module))
    return refuse(module, "expected retained preparation");
  if (failed(verify(module)))
    return failure();
  // Read every original formula, not just live or eligible applications.
  auto products = describeMapProducts(module);
  if (failed(products))
    return failure();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(module->clone()));
  Record output = input;
  if (failed(Rewriter(unit(*candidate), output).run(*products)) ||
      failed(check(module, *candidate, input, output)))
    return failure();
  module.getBodyRegion().takeBody(candidate->getBodyRegion());
  StateAccess::set(state, std::move(output));
  return success();
}
} // namespace zkc::mathematical
