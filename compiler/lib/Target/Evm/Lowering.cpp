#include "mlir/Conversion/ControlFlowToSCF/ControlFlowToSCF.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "mlir/Transforms/RegionUtils.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Layout.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Target/Evm/Transcript.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
namespace {
using Values = SmallVector<Value>;

bool isTranscript(Type type) {
  auto capability = dyn_cast<runtime::CapabilityType>(type);
  return capability &&
         capability.getKind() == runtime::CapabilityKind::Transcript;
}

class EvmTypes : public TypeConverter {
public:
  explicit EvmTypes(NativeLayouts &layouts, MLIRContext *context)
      : layouts(layouts) {
    addConversion([context, this](Type type, SmallVectorImpl<Type> &out) {
      return convert(type, out, context);
    });
  }

private:
  NativeLayouts &layouts;
  LogicalResult convert(Type type, SmallVectorImpl<Type> &out,
                        MLIRContext *context) const {
    auto i64 = IntegerType::get(context, 64);
    // Control lanes are separate from complete logical Copy/Drop layouts.
    if (auto integer = dyn_cast<IntegerType>(type);
        integer && integer.isSignless()) {
      if (!is_contained({1u, 32u, 64u, 256u}, integer.getWidth()))
        return failure();
      out.push_back(type);
    } else if (isa<IndexType>(type))
      out.push_back(i64);
    else if (auto capability = dyn_cast<runtime::CapabilityType>(type)) {
      if (capability.getKind() == runtime::CapabilityKind::ResourceUnit) {
        auto signature = layouts.signature(TypeRange(type));
        if (!signature) {
          consumeError(signature.takeError());
          return failure();
        }
        append_range(out, signature->lanes);
        return success();
      }
      if (capability.getKind() != runtime::CapabilityKind::Transcript)
        return failure();
      // A transcript lowers only for a suite whose facts the EVM realizes.
      auto realized =
          realizeTranscript(layouts, *context, capability.getIdentity());
      if (!realized) {
        consumeError(realized.takeError());
        return failure();
      }
      out.push_back(i64);
    } else if (isa<runtime::ScopeType, exec::StopType>(type))
      out.push_back(i64);
    else if (auto outcome = dyn_cast<exec::OutcomeType>(type)) {
      for (Type payload : outcome.getPayload())
        if (failed(convert(payload, out, context)))
          return failure();
    } else if (auto transfer = dyn_cast<runtime::TransferType>(type)) {
      out.push_back(i64);
      for (Type payload : transfer.getPayload())
        if (failed(convert(payload, out, context)))
          return failure();
    } else {
      auto layout = layouts.get(type);
      if (!layout) {
        consumeError(layout.takeError());
        return failure();
      }
      append_range(out, (*layout)->lanes);
    }
    return success();
  }
};

struct PreparedFunction {
  std::string name;
  FunctionType signature;
  bool entry;
};
struct PreparedEndpoint {
  llvm::DenseMap<Operation *, PreparedFunction> functions;
  llvm::DenseMap<Operation *, Operation *> references;
  llvm::DenseMap<Operation *, finite::Computation> computations;
  llvm::DenseMap<Operation *, NativeBinding> bindings;
  SmallPtrSet<Block *, 32> omittedBlocks;
  SmallPtrSet<Operation *, 32> omittedOperations;

  LogicalResult prepare(ModuleOp source, ModuleOp target, EvmTypes &types,
                        NativeLayouts &layouts) {
    SymbolTableCollection symbols;
    SmallVector<Operation *> owners;
    source.walk([&](Operation *op) {
      if (isa<func::FuncOp>(op) ||
          op->getName().getStringRef() == "protocol.participant")
        owners.push_back(op);
    });
    unsigned serial = 0, entries = 0;
    for (Operation *owner : owners) {
      bool entry = owner->getName().getStringRef() == "protocol.participant";
      auto attr = owner->getAttrOfType<TypeAttr>("function_type");
      auto signature =
          attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
      if (!signature || (entry && ++entries != 1) ||
          owner->getRegion(0).empty())
        return owner->emitError("[evm.unsupported-operation] expected one "
                                "defined endpoint closure");
      auto capabilities = [&](TypeRange ports) {
        unsigned count = 0;
        std::function<bool(Type)> inspect = [&](Type type) {
          if (isTranscript(type))
            return ++count <= 1;
          if (auto outcome = dyn_cast<exec::OutcomeType>(type))
            return llvm::all_of(outcome.getPayload(), inspect);
          if (auto transfer = dyn_cast<runtime::TransferType>(type))
            return llvm::all_of(transfer.getPayload(), inspect);
          return true;
        };
        return llvm::all_of(ports, inspect);
      };
      if (!capabilities(signature.getInputs()) ||
          !capabilities(signature.getResults()))
        return owner->emitError("[evm.unsupported-operation] multiple "
                                "transcript capabilities are unsupported");
      SmallVector<Type> inputs, outputs;
      if (failed(types.convertTypes(signature.getInputs(), inputs)) ||
          failed(types.convertTypes(signature.getResults(), outputs)))
        return owner->emitError(
            "[evm.unsupported-type] reachable function signature");
      functions[owner] = {
          entry ? "verify_endpoint" : "helper_" + std::to_string(serial++),
          FunctionType::get(source.getContext(), inputs, outputs), entry};
      // Checked failures become immediate terminal EVM effects. Their source
      // propagation blocks are not reached by target execution. Keep the
      // blocks until conversion rewrites their incoming dispatch edges.
      Region &body = owner->getRegion(0);
      SmallPtrSet<Block *, 32> reached;
      SmallVector<Block *> pending{&body.front()};
      while (!pending.empty()) {
        Block *block = pending.pop_back_val();
        if (!reached.insert(block).second)
          continue;
        Operation *terminator = block->getTerminator();
        StringRef name = terminator->getName().getStringRef();
        if (name == "exec.dispatch")
          pending.push_back(terminator->getSuccessor(0));
        else if (name == "exec.match")
          append_range(pending, terminator->getSuccessors().drop_front());
        else
          append_range(pending, terminator->getSuccessors());
      }
      for (Block &block : body) {
        if (!reached.contains(&block)) {
          omittedBlocks.insert(&block);
          for (Operation &op : block)
            op.walk(
                [&](Operation *nested) { omittedOperations.insert(nested); });
          continue;
        }
        SmallVector<Type> lanes;
        if (failed(types.convertTypes(block.getArgumentTypes(), lanes)))
          return owner->emitError(
              "[evm.unsupported-type] reachable block signature");
      }
      WalkResult checked = owner->walk([&](Operation *op) {
        if (omittedOperations.contains(op))
          return WalkResult::advance();
        for (StringRef key : {"binding", "callee"})
          if (auto ref = op->getAttrOfType<SymbolRefAttr>(key)) {
            auto *resolved = symbols.lookupNearestSymbolFrom(op, ref);
            if (!resolved) {
              op->emitError("[evm.unsupported-operation] unresolved checked "
                            "source reference");
              return WalkResult::interrupt();
            }
            references[op] = resolved;
          }
        if (op->getName().getStringRef() == "exec.apply") {
          auto admitted = readNativeBinding([&] { return op->emitOpError(); },
                                            references.lookup(op));
          if (failed(admitted))
            return WalkResult::interrupt();
          auto signature = executableBindingSignature(admitted->valueType);
          auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
          StringRef contract = admitted->declaration.getContract();
          if (!admitted->declaration.getImplementation().empty()) {
            op->emitError("[evm.unsupported-operation] pinned runtime "
                          "implementation has no EVM realization");
            return WalkResult::interrupt();
          }
          bool supported =
              protocol::resourceUnitContract(contract) ||
              llvm::is_contained(
                  ArrayRef<StringRef>{"bool.and",
                                      "bool.equal",
                                      "bool.not",
                                      "bool.or",
                                      "bool.select",
                                      "bool.xor",
                                      "bytes.append",
                                      "bytes.at",
                                      "bytes.empty",
                                      "bytes.get",
                                      "bytes.length",
                                      "field.add",
                                      "field.constant",
                                      "field.embed",
                                      "field.equal",
                                      "field.from_index",
                                      "field.inverse",
                                      "field.mul",
                                      "field.neg",
                                      "field.select",
                                      "field.sub",
                                      "index.add",
                                      "index.bit_and",
                                      "index.constant",
                                      "index.div",
                                      "index.equal",
                                      "index.less",
                                      "index.logical_shift_right",
                                      "index.mod",
                                      "index.mul",
                                      "index.power_of_two",
                                      "index.sub",
                                      "index.wrapping_add",
                                      "index.wrapping_sub",
                                      "indices.append",
                                      "indices.empty",
                                      "sequence.append",
                                      "sequence.at",
                                      "sequence.empty",
                                      "sequence.get",
                                      "sequence.length",
                                      "transcript.native.indexed.challenge",
                                      "transcript.native.indexed.observe.data",
                                      "vector.append",
                                      "vector.at",
                                      "vector.constant",
                                      "vector.empty",
                                      "vector.equal",
                                      "vector.get",
                                      "vector.length",
                                      "vector.split",
                                      "vector.sum"},
                  contract);
          if (!supported || op->getOperandTypes() != signature.getInputs() ||
              op->getResultTypes() != signature.getResults() ||
              failed(verifyInvocationParameters(
                  [&] { return op->emitOpError(); }, contract,
                  admitted->declaration.getArgumentsAttr(), parameters,
                  protocol::ParameterStage::Logical))) {
            op->emitError("[evm.unsupported-operation] unsupported exact "
                          "runtime realization: ")
                << contract;
            return WalkResult::interrupt();
          }
          if (contract == "transcript.native.indexed.challenge" ||
              contract == "transcript.native.indexed.observe.data") {
            auto origin = runtime::exportNativeOrigin(
                cast<runtime::NativeOriginAttr>(parameters[0]));
            if (!origin) {
              consumeError(origin.takeError());
              op->emitError("[evm.unsupported-operation] invalid checked "
                            "occurrence template");
              return WalkResult::interrupt();
            }
            bool selected = llvm::any_of(origin->path, [](const auto &step) {
              return step.kind == protocol::NativeOriginStep::Kind::Branch;
            });
            bool observe = contract.ends_with("observe.data");
            auto *query =
                std::get_if<protocol::NativeQueryOrigin>(&origin->event);
            if (selected ||
                (observe
                     ? !std::holds_alternative<protocol::NativeMessageOrigin>(
                           origin->event)
                     : !query || query->method != "draw")) {
              op->emitError("[evm.unsupported-operation] unsupported "
                            "transcript occurrence kind or selected control");
              return WalkResult::interrupt();
            }
          }
          bindings[op] = *admitted;
        }
        if (finite::isComputation(op)) {
          finite::Computation computation;
          if (failed(finite::describe(op, computation, nullptr, &symbols)) ||
              failed(finite::readCallbackABI(
                  computation, computation.collect
                                   ? finite::CallbackRole::Body
                                   : finite::CallbackRole::Step)) ||
              (computation.predicate &&
               failed(finite::readCallbackABI(
                   computation, finite::CallbackRole::Predicate)))) {
            op->emitError("[evm.unsupported-operation] invalid checked finite "
                          "computation");
            return WalkResult::interrupt();
          }
          // Enumeration descriptors stay in the checked source. Decide their
          // target storage/axis support before conversion moves callback ABIs.
          for (Operation &node :
               computation.domain.getBody().front().without_terminator()) {
            if (isa<data::DomainElementsOp, data::DomainIndicesOp>(node)) {
              auto layout = layouts.get(node.getOperand(0).getType());
              if (!layout) {
                consumeError(layout.takeError());
                node.emitError("[evm.unsupported-operation] unsupported "
                               "complete finite element layout");
                return WalkResult::interrupt();
              }
              auto axis = node.getAttrOfType<IntegerAttr>("axis");
              if (!(*layout)->collection || (*layout)->lanes.size() != 2 ||
                  (*layout)->collection->storage ==
                      CollectionLayout::Storage::PackedBytes ||
                  (isa<data::DomainIndicesOp>(node) &&
                   (!axis || axis.getUInt() != 0))) {
                node.emitError("[evm.unsupported-operation] unsupported "
                               "finite collection storage or axis");
                return WalkResult::interrupt();
              }
            } else if (!isa<data::DomainRangeOp, data::DomainZipOp,
                            data::DomainProductOp>(node)) {
              node.emitError("[evm.unsupported-operation] unsupported finite "
                             "enumeration");
              return WalkResult::interrupt();
            }
          }
          if (computation.collect) {
            TypeRange results = op->getResultTypes();
            if (computation.scoped)
              results = cast<exec::OutcomeType>(results[0]).getPayload();
            auto layout =
                results.size() == 1
                    ? layouts.get(results[0])
                    : Expected<const ValueLayout *>(zkc::error("evm.layout"));
            if (!layout) {
              consumeError(layout.takeError());
              op->emitError("[evm.unsupported-operation] unsupported complete "
                            "collect layout");
              return WalkResult::interrupt();
            }
            if (!(*layout)->collection ||
                (*layout)->collection->storage ==
                    CollectionLayout::Storage::PackedBytes) {
              op->emitError("[evm.unsupported-operation] unsupported collected "
                            "element family");
              return WalkResult::interrupt();
            }
          }
          computations[op] = computation;
        }
        if (op == owner)
          return WalkResult::advance();
        if (auto flags = op->getAttrOfType<arith::IntegerOverflowFlagsAttr>(
                "overflowFlags"))
          if (flags.getValue() != arith::IntegerOverflowFlags::none) {
            op->emitError("[evm.unsupported-operation] arithmetic overflow "
                          "promises are unsupported");
            return WalkResult::interrupt();
          }
        if (op->getName().getStringRef() == "protocol.loop") {
          auto parameter = op->getAttrOfType<BoolAttr>("parameter");
          if (!parameter || parameter.getValue()) {
            op->emitError(
                "[evm.unsupported-operation] parameterized participant "
                "loops have no EVM realization");
            return WalkResult::interrupt();
          }
        }
        bool supported =
            isa<arith::ConstantOp, arith::CmpIOp, arith::AddIOp, arith::SubIOp,
                arith::MulIOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
                arith::SelectOp, arith::ExtUIOp, arith::ExtSIOp,
                arith::TruncIOp, arith::IndexCastOp, arith::IndexCastUIOp>(
                op) ||
            llvm::is_contained(
                ArrayRef<StringRef>{"exec.apply",
                                    "exec.fold",
                                    "exec.collect",
                                    "data.finite_fold",
                                    "data.finite_collect",
                                    "protocol.loop",
                                    "protocol.yield",
                                    "func.return",
                                    "protocol.finish",
                                    "cf.br",
                                    "cf.cond_br",
                                    "exec.dispatch",
                                    "exec.match",
                                    "exec.returned",
                                    "exec.complete",
                                    "exec.test",
                                    "exec.boolean",
                                    "exec.reject",
                                    "exec.failed",
                                    "exec.range",
                                    "runtime.iteration",
                                    "runtime.enter_scope",
                                    "runtime.exit_scope",
                                    "runtime.borrow_transfer",
                                    "runtime.accept_transfer",
                                    "runtime.transfer_values",
                                    "runtime.release_transfer",
                                    "func.call",
                                    "exec.compute",
                                    "protocol.local_call",
                                    "protocol.receive",
                                    "protocol.guard",
                                    "algebra.constant",
                                    "algebra.field_add",
                                    "algebra.field_subtract",
                                    "algebra.field_multiply",
                                    "algebra.field_equal",
                                    "data.make",
                                    "exec.variant",
                                    "data.is",
                                    "data.get",
                                    "data.sequence_empty",
                                    "data.sequence_append",
                                    "data.sequence_length",
                                    "data.bounded_at",
                                    "data.array_at",
                                    "data.array_from_elements",
                                    "data.index",
                                    "data.dim",
                                    "data.index_power_of_two",
                                    "data.index_equal",
                                    "data.index_less",
                                    "data.index_add",
                                    "data.index_subtract",
                                    "data.index_multiply",
                                    "data.index_divide",
                                    "data.index_modulo",
                                    "data.index_wrapping_add",
                                    "data.index_wrapping_subtract",
                                    "data.index_bit_and",
                                    "data.index_logical_shift_right"},
                op->getName().getStringRef());
        if (!supported) {
          op->emitError("[evm.unsupported-operation] no EVM realization for "
                        "this reachable operation");
          return WalkResult::interrupt();
        }

        SmallVector<Type> converted;
        if (failed(types.convertTypes(op->getOperandTypes(), converted)) ||
            failed(types.convertTypes(op->getResultTypes(), converted))) {
          op->emitError(
              "[evm.unsupported-type] reachable signature or payload");
          return WalkResult::interrupt();
        }
        return WalkResult::advance();
      });
      if (checked.wasInterrupted())
        return failure();
    }
    if (entries != 1)
      return source.emitError(
          "[evm.unsupported-operation] missing selected endpoint");
    // Move the original executable owners. The full conversion below is the
    // only producer of lowered instructions and SSA replacements.
    for (Operation *owner : owners)
      owner->moveBefore(target.getBody(), target.getBody()->end());
    return success();
  }
};

class Lowering {
public:
  Lowering(const PreparedEndpoint &prepared, const EvmOptions &options,
           NativeLayouts &layouts, const EvmTypes &types,
           ConversionPatternRewriter &builder, Operation *source,
           ArrayRef<ValueRange> operands)
      : prepared(prepared), options(options), layouts(layouts), types(types),
        builder(builder), source(source), operands(operands) {}
  LogicalResult lowerOperation(Operation *);
  bool replaced = false;

private:
  const PreparedEndpoint &prepared;
  const EvmOptions &options;
  NativeLayouts &layouts;
  const EvmTypes &types;
  ConversionPatternRewriter &builder;
  Operation *source;
  ArrayRef<ValueRange> operands;
  LogicalResult refuse(Operation *op, StringRef reason) {
    return op->emitError("[evm.unsupported-operation] ")
           << op->getName() << ": " << reason;
  }
  FailureOr<SmallVector<Type>> converted(TypeRange input, Operation *at) {
    SmallVector<Type> result;
    if (failed(types.convertTypes(input, result))) {
      at->emitError("[evm.unsupported-type] reachable signature or payload ")
          << input;
      return failure();
    }
    return result;
  }
  Value constant(Location loc, Type type, const APInt &value) {
    return arith::ConstantOp::create(builder, loc, type,
                                     builder.getIntegerAttr(type, value));
  }
  Value integer(Location loc, uint64_t value, unsigned width = 64) {
    return constant(loc, builder.getIntegerType(width), APInt(width, value));
  }
  Values get(ValueRange values) {
    Values result;
    for (Value value : values) {
      auto position = llvm::find(source->getOperands(), value);
      assert(position != source->operand_end() &&
             "expected a source operand in the one-to-many adaptor");
      append_range(result, operands[position - source->operand_begin()]);
    }
    return result;
  }
  Values get(Value value) { return get(ValueRange(value)); }
  LogicalResult bind(Operation *op, ValueRange result) {
    SmallVector<Values> groups;
    unsigned offset = 0;
    for (Value value : op->getResults()) {
      auto lanes = converted(TypeRange(value.getType()), op);
      if (failed(lanes) || offset + lanes->size() > result.size())
        return refuse(op, "invalid realized result signature");
      groups.emplace_back(result.slice(offset, lanes->size()));
      offset += lanes->size();
    }
    if (offset != result.size())
      return refuse(op, "extra realized result values");
    builder.replaceOpWithMultiple(op, std::move(groups));
    replaced = true;
    return success();
  }
  template <typename Op>
  Values emit(Operation *source, TypeRange results, ValueRange operands,
              ArrayRef<NamedAttribute> attrs = {}) {
    return Values(
        Op::create(builder, source->getLoc(), results, operands, attrs)
            ->getResults());
  }
  template <typename Op>
  Values emitResult(Operation *source, ValueRange operands,
                    ArrayRef<NamedAttribute> attrs = {}) {
    auto result = converted(source->getResultTypes(), source);
    return failed(result) ? Values{}
                          : emit<Op>(source, *result, operands, attrs);
  }
  void active(Operation *op, Value scope) {
    emit<ScopeCheckOp>(op, {}, {scope});
  }
  LogicalResult checkCapabilities(Operation *op, TypeRange types) {
    unsigned count = 0;
    std::function<bool(Type)> inspect = [&](Type type) {
      if (isTranscript(type))
        return ++count <= 1;
      if (auto outcome = dyn_cast<exec::OutcomeType>(type))
        return llvm::all_of(outcome.getPayload(), inspect);
      if (auto transfer = dyn_cast<runtime::TransferType>(type))
        return llvm::all_of(transfer.getPayload(), inspect);
      return true;
    };
    if (!llvm::all_of(types, inspect))
      return refuse(op, "multiple transcript capabilities are unsupported");
    return success();
  }
  Operation *resolve(Operation *op, StringRef) {
    return prepared.references.lookup(op);
  }
  LogicalResult lowerFinite(Operation *);
  LogicalResult lowerBinding(Operation *);
  std::optional<LogicalResult> lowerScalar(Operation *, StringRef, ValueRange,
                                           ArrayAttr);
  LogicalResult lowerLoop(Operation *);
  FailureOr<Values> call(Operation *op, Operation *callee, ValueRange args) {
    auto found = prepared.functions.find(callee);
    if (found == prepared.functions.end() ||
        found->second.signature.getNumInputs() != args.size()) {
      (void)refuse(op, "unresolved helper or mismatched expanded signature");
      return failure();
    }
    return Values(
        func::CallOp::create(builder, op->getLoc(), found->second.name,
                             found->second.signature.getResults(), args)
            .getResults());
  }
};

std::optional<LogicalResult> Lowering::lowerScalar(Operation *op,
                                                   StringRef code,
                                                   ValueRange operands,
                                                   ArrayAttr parameters) {
  Location loc = op->getLoc();
  if (code == "field.select") {
    if (!parameters || !parameters.empty() || operands.size() != 3)
      return refuse(op, "field.select requires exact empty parameters");
    return bind(op, {arith::SelectOp::create(builder, loc, operands[0],
                                             operands[1], operands[2])});
  }
  if (code.starts_with("field.")) {
    TypeRange results = op->getResultTypes();
    if (results.size() == 1)
      if (auto outcome = dyn_cast<exec::OutcomeType>(results[0]))
        results = outcome.getPayload();
    TypeRange inputs =
        TypeRange(op->getOperandTypes())
            .drop_front(op->getName().getStringRef() == "exec.apply" ? 1 : 0);
    Type scalar = code == "field.equal" && !inputs.empty() ? inputs.front()
                  : results.size() == 1                    ? results.front()
                                                           : Type();
    if (!isa_and_nonnull<algebra::FieldType>(scalar))
      return refuse(op, "field operation requires exact native field type");
    SmallVector<NamedAttribute> attributes{
        builder.getNamedAttr("value_type", TypeAttr::get(scalar))};
    if (code == "field.constant") {
      if (!parameters || parameters.size() != 1 ||
          !isa<algebra::FieldLiteralAttr>(parameters[0]))
        return refuse(op, "constant requires one exact field literal");
      attributes.push_back(builder.getNamedAttr("value", parameters[0]));
    } else if (!parameters || !parameters.empty())
      return refuse(op, "unsupported field invocation parameters");
    if (code == "field.constant")
      return bind(op, emitResult<FieldConstantOp>(op, operands, attributes));
    if (code == "field.add")
      return bind(op, emitResult<FieldAddOp>(op, operands, attributes));
    if (code == "field.sub")
      return bind(op, emitResult<FieldSubOp>(op, operands, attributes));
    if (code == "field.mul")
      return bind(op, emitResult<FieldMulOp>(op, operands, attributes));
    if (code == "field.neg")
      return bind(op, emitResult<FieldNegOp>(op, operands, attributes));
    if (code == "field.equal")
      return bind(op, emitResult<FieldEqualOp>(op, operands, attributes));
    if (code == "field.from_index")
      return bind(op, emitResult<FieldFromIndexOp>(op, operands, attributes));
    if (code == "field.embed")
      return bind(op, emitResult<FieldEmbedOp>(op, operands, attributes));
    if (code == "field.inverse")
      return bind(op, emitResult<FieldInverseOp>(op, operands, attributes));
    return refuse(op, "unsupported field operation");
  }
  if (!code.starts_with("bool."))
    return std::nullopt;
  if (!parameters || !parameters.empty())
    return refuse(op, "unsupported Boolean invocation parameters");
  if (code == "bool.equal")
    return bind(op,
                {arith::CmpIOp::create(builder, loc, arith::CmpIPredicate::eq,
                                       operands[0], operands[1])});
  if (code == "bool.select")
    return bind(op, {arith::SelectOp::create(builder, loc, operands[0],
                                             operands[1], operands[2])});
  if (code == "bool.and")
    return bind(
        op, {arith::AndIOp::create(builder, loc, operands[0], operands[1])});
  if (code == "bool.or")
    return bind(op,
                {arith::OrIOp::create(builder, loc, operands[0], operands[1])});
  if (code == "bool.xor")
    return bind(
        op, {arith::XOrIOp::create(builder, loc, operands[0], operands[1])});
  if (code == "bool.not")
    return bind(op, {arith::XOrIOp::create(builder, loc, operands[0],
                                           integer(loc, 1, 1))});
  return std::nullopt;
}

LogicalResult Lowering::lowerBinding(Operation *op) {
  auto admitted = prepared.bindings.find(op)->second;
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  StringRef name = admitted.declaration.getContract();
  Values operands = get(op->getOperands().drop_front());
  active(op, get(op->getOperand(0))[0]);
  auto resultTypes = converted(op->getResultTypes(), op);
  if (failed(resultTypes))
    return failure();
  if (protocol::resourceUnitContract(name)) {
    // Exact nominal signatures and affine succession were checked before
    // erasure. Retain the active-scope check above, even for empty results.
    return bind(op, {});
  }
  if (auto scalar = lowerScalar(op, name, operands, parameters))
    return *scalar;
  if (name == "index.constant") {
    if (!parameters || parameters.size() != 1 ||
        !isa<IntegerAttr>(parameters[0]))
      return refuse(op, "index.constant requires an exact u64 parameter");
    return bind(op, {integer(op->getLoc(),
                             cast<IntegerAttr>(parameters[0]).getUInt())});
  }
  if (name == "index.equal" || name == "index.less") {
    auto predicate = name == "index.less" ? arith::CmpIPredicate::ult
                                          : arith::CmpIPredicate::eq;
    return bind(op, {arith::CmpIOp::create(builder, op->getLoc(), predicate,
                                           operands[0], operands[1])});
  }
  if (name.starts_with("transcript.native.indexed.")) {
    bool observe = name == "transcript.native.indexed.observe.data";
    bool challenge = name == "transcript.native.indexed.challenge";
    if ((!observe && !challenge) || !parameters || parameters.size() != 1)
      return refuse(op, "unsupported managed transcript transition");
    auto origin = dyn_cast<runtime::NativeOriginAttr>(parameters[0]);
    auto neutral = runtime::exportNativeOrigin(origin);
    if (!neutral) {
      consumeError(neutral.takeError());
      return refuse(op, "invalid checked occurrence template");
    }
    Values args{get(op->getOperand(0))[0]};
    append_range(args, operands);
    SmallVector<NamedAttribute> attrs{
        builder.getNamedAttr("origin", origin),
        builder.getNamedAttr(
            "value_type",
            TypeAttr::get(observe ? op->getOperand(2).getType()
                                  : admitted.valueType.getResult(0)))};
    return bind(
        op, observe
                ? emit<TranscriptObserveOp>(op, *resultTypes, args, attrs)
                : emit<TranscriptChallengeOp>(op, *resultTypes, args, attrs));
  }
  SmallVector<NamedAttribute> attributes;
  if (name.starts_with("vector.") || name.starts_with("sequence.") ||
      name.starts_with("indices.") || name.starts_with("bytes.")) {
    Type collection;
    for (Type type : admitted.valueType.getInputs())
      if (isa<data::FieldVectorType, data::IndicesType, data::SequenceType,
              data::BytesType>(type)) {
        collection = type;
        break;
      }
    if (!collection && admitted.valueType.getNumResults())
      collection = admitted.valueType.getResult(0);
    if (!collection)
      return refuse(op, "missing collection type");
    attributes.push_back(
        builder.getNamedAttr("value_type", TypeAttr::get(collection)));
    if (name == "vector.constant")
      attributes.push_back(builder.getNamedAttr("values", parameters));
    else if (name == "vector.at") {
      if (!parameters || parameters.size() != 1 ||
          !isa<IntegerAttr>(parameters[0]))
        return refuse(op, "static vector access requires exact index");
      operands.push_back(
          integer(op->getLoc(), cast<IntegerAttr>(parameters[0]).getUInt()));
      name = "vector.get";
    } else if (!parameters || !parameters.empty())
      return refuse(op, "unsupported collection invocation parameters");
    if (name == "sequence.at")
      name = "sequence.get";
    if (name == "bytes.at")
      name = "bytes.get";
  } else if (!parameters || !parameters.empty())
    return refuse(op, "unsupported invocation parameters");
  if (name == "index.add")
    return bind(op, emit<IndexAddOp>(op, *resultTypes, operands, attributes));
  if (name == "index.sub")
    return bind(op, emit<IndexSubOp>(op, *resultTypes, operands, attributes));
  if (name == "index.mul")
    return bind(op, emit<IndexMulOp>(op, *resultTypes, operands, attributes));
  if (name == "index.div")
    return bind(op, emit<IndexDivOp>(op, *resultTypes, operands, attributes));
  if (name == "index.mod")
    return bind(op, emit<IndexModOp>(op, *resultTypes, operands, attributes));
  if (name == "index.power_of_two")
    return bind(
        op, emit<IndexPowerOfTwoOp>(op, *resultTypes, operands, attributes));
  if (name == "index.logical_shift_right")
    return bind(op, emit<IndexLogicalShiftRightOp>(op, *resultTypes, operands,
                                                   attributes));
  if (name == "vector.constant")
    return bind(op,
                emit<VectorConstantOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.empty")
    return bind(op,
                emit<VectorEmptyOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.length")
    return bind(op,
                emit<VectorLengthOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.append")
    return bind(op,
                emit<VectorAppendOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.split")
    return bind(op,
                emit<VectorSplitOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.sum")
    return bind(op, emit<VectorSumOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.get")
    return bind(op, emit<VectorGetOp>(op, *resultTypes, operands, attributes));
  if (name == "vector.equal")
    return bind(op,
                emit<VectorEqualOp>(op, *resultTypes, operands, attributes));
  if (name == "sequence.empty")
    return bind(op,
                emit<SequenceEmptyOp>(op, *resultTypes, operands, attributes));
  if (name == "sequence.append")
    return bind(op,
                emit<SequenceAppendOp>(op, *resultTypes, operands, attributes));
  if (name == "sequence.length")
    return bind(op,
                emit<SequenceLengthOp>(op, *resultTypes, operands, attributes));
  if (name == "sequence.get")
    return bind(op,
                emit<SequenceGetOp>(op, *resultTypes, operands, attributes));
  if (name == "bytes.empty")
    return bind(op, emit<BytesEmptyOp>(op, *resultTypes, operands, attributes));
  if (name == "bytes.length")
    return bind(op,
                emit<BytesLengthOp>(op, *resultTypes, operands, attributes));
  if (name == "bytes.get")
    return bind(op, emit<BytesGetOp>(op, *resultTypes, operands, attributes));
  if (name == "bytes.append")
    return bind(op,
                emit<BytesAppendOp>(op, *resultTypes, operands, attributes));
  if (name == "indices.empty")
    return bind(op,
                emit<IndicesEmptyOp>(op, *resultTypes, operands, attributes));
  if (name == "indices.append")
    return bind(op,
                emit<IndicesAppendOp>(op, *resultTypes, operands, attributes));
  if (name == "index.wrapping_add")
    return bind(op, {arith::AddIOp::create(builder, op->getLoc(), operands[0],
                                           operands[1])});
  if (name == "index.wrapping_sub")
    return bind(op, {arith::SubIOp::create(builder, op->getLoc(), operands[0],
                                           operands[1])});
  if (name == "index.bit_and")
    return bind(op, {arith::AndIOp::create(builder, op->getLoc(), operands[0],
                                           operands[1])});
  return refuse(op, ("unsupported runtime contract: " + name).str());
}

LogicalResult Lowering::lowerLoop(Operation *op) {
  auto carried = op->getAttrOfType<IntegerAttr>("carried");
  auto maximum = op->getAttrOfType<IntegerAttr>("maximum");
  auto parameter = op->getAttrOfType<BoolAttr>("parameter");
  // lowerEndpoint has refused a maximum above the deployment's ceiling.
  if (!carried || !maximum || maximum.getInt() < 0 || !parameter ||
      parameter.getValue() || op->getNumOperands() < 1 ||
      static_cast<uint64_t>(maximum.getInt()) >
          options.limits.participantLoopMaximum)
    return refuse(op, "loop requires an admitted deployment maximum");
  Value count = get(op->getOperand(0))[0];
  emit<LoopBoundOp>(op, {}, {count, integer(op->getLoc(), maximum.getUInt())});
  Values initial = get(op->getOperands().slice(1, carried.getUInt()));
  Value zero = integer(op->getLoc(), 0), one = integer(op->getLoc(), 1);
  auto loop =
      scf::ForOp::create(builder, op->getLoc(), zero, count, one, initial);
  loop.setUnsignedCmpAttr(builder.getUnitAttr());
  Block &body = op->getRegion(0).front();
  TypeConverter::SignatureConversion signature(body.getNumArguments());
  signature.addInputs(0, {builder.getI64Type()});
  for (unsigned i = 0; i < carried.getUInt(); ++i) {
    auto lanes = converted(TypeRange(body.getArgument(i + 1).getType()), op);
    if (failed(lanes))
      return failure();
    signature.addInputs(i + 1, *lanes);
  }
  for (unsigned i = carried.getUInt() + 1; i < body.getNumArguments(); ++i)
    signature.remapInput(i, get(op->getOperand(i)));
  builder.eraseBlock(loop.getBody());
  builder.inlineRegionBefore(op->getRegion(0), loop.getRegion(),
                             loop.getRegion().end());
  if (failed(builder.convertRegionTypes(&loop.getRegion(), types, &signature)))
    return failure();
  return bind(op, loop.getResults());
}

LogicalResult Lowering::lowerFinite(Operation *op) {
  auto computation = prepared.computations.lookup(op);
  bool scoped = computation.scoped, fold = !computation.collect;
  auto entry = finite::partitionEntry(
      computation, op->getOperands().drop_front(scoped ? 1 : 0));
  if (failed(entry))
    return refuse(op, "invalid prepared finite entry ABI");
  if (scoped)
    active(op, get(op->getOperand(0))[0]);
  struct Domain {
    enum Kind { Elements, Indices, Range, Zip, Product } kind;
    Value count, lower;
    Type collection;
    Values carrier;
    SmallVector<std::shared_ptr<Domain>> children;
    SmallVector<Value> suffixes;
  };
  llvm::DenseMap<Value, std::shared_ptr<Domain>> domains;
  llvm::DenseMap<Value, Values> domainArgumentsByFormal;
  Block &body = computation.domain.getBody().front();
  for (auto [formal, actual] : zip(body.getArguments(), entry->domain))
    domainArgumentsByFormal[formal] = get(actual);
  auto typed = [&](Type type) {
    return builder.getNamedAttr("value_type", TypeAttr::get(type));
  };
  auto admitCount = [&](Operation *at, Value count) {
    emit<RangeAdmitOp>(at, {}, {integer(at->getLoc(), 0), count});
  };
  // Every constructor, even unused or empty, contributes its reached admission
  // before callbacks. Descriptor nodes retain exact original collection types.
  for (Operation &child : body.without_terminator()) {
    auto domain = std::make_shared<Domain>();
    if (isa<data::DomainElementsOp, data::DomainIndicesOp>(child)) {
      domain->kind = isa<data::DomainElementsOp>(child) ? Domain::Elements
                                                        : Domain::Indices;
      domain->collection = child.getOperand(0).getType();
      domain->carrier = domainArgumentsByFormal.lookup(child.getOperand(0));
      auto layout = layouts.get(domain->collection);
      if (!layout) {
        consumeError(layout.takeError());
        return refuse(&child, "unsupported complete finite element layout");
      }
      if (!(*layout)->collection ||
          (*layout)->collection->storage ==
              CollectionLayout::Storage::PackedBytes ||
          domain->carrier.size() != 2)
        return refuse(&child,
                      "finite domain requires an admitted rank-one collection");
      if (isa<data::DomainIndicesOp>(child)) {
        auto axis = child.getAttrOfType<IntegerAttr>("axis");
        if (!axis || axis.getUInt() != 0)
          return refuse(&child, "unsupported finite collection axis");
      }
      bool coefficients = (*layout)->collection->storage ==
                          CollectionLayout::Storage::FieldCoefficients;
      domain->count =
          (coefficients ? emit<VectorLengthOp>(&child, {builder.getI64Type()},
                                               domain->carrier,
                                               {typed(domain->collection)})
                        : emit<SequenceLengthOp>(
                              &child, {builder.getI64Type()}, domain->carrier,
                              {typed(domain->collection)}))[0];
      admitCount(&child, domain->count);
    } else if (isa<data::DomainRangeOp>(child)) {
      domain->kind = Domain::Range;
      auto lower = domainArgumentsByFormal.lookup(child.getOperand(0));
      auto upper = domainArgumentsByFormal.lookup(child.getOperand(1));
      if (lower.size() != 1 || upper.size() != 1)
        return refuse(&child, "invalid finite range bounds");
      emit<RangeAdmitOp>(&child, {}, {lower[0], upper[0]});
      domain->lower = lower[0];
      auto increasing =
          arith::CmpIOp::create(builder, child.getLoc(),
                                arith::CmpIPredicate::ult, lower[0], upper[0]);
      auto difference =
          arith::SubIOp::create(builder, child.getLoc(), upper[0], lower[0]);
      domain->count =
          arith::SelectOp::create(builder, child.getLoc(), increasing,
                                  difference, integer(child.getLoc(), 0));
    } else if (isa<data::DomainZipOp, data::DomainProductOp>(child)) {
      domain->kind =
          isa<data::DomainZipOp>(child) ? Domain::Zip : Domain::Product;
      for (Value input : child.getOperands()) {
        auto found = domains.find(input);
        if (found == domains.end())
          return refuse(&child, "unresolved finite descriptor");
        domain->children.push_back(found->second);
      }
      if (domain->children.empty())
        return refuse(&child, "empty finite constructor operand list");
      if (domain->kind == Domain::Zip) {
        domain->count = domain->children.front()->count;
        for (auto &factor : drop_begin(domain->children))
          emit<RangeCheckOp>(&child, {}, {domain->count, factor->count});
      } else {
        domain->count = integer(child.getLoc(), 1);
        // Preserve declaration order for all intermediate cardinality checks.
        for (auto &factor : domain->children) {
          domain->count = emit<IndexMulOp>(&child, {builder.getI64Type()},
                                           {domain->count, factor->count})[0];
          admitCount(&child, domain->count);
        }
        Value suffix = integer(child.getLoc(), 1);
        domain->suffixes.resize(domain->children.size());
        for (unsigned i = domain->children.size(); i-- > 0;) {
          domain->suffixes[i] = suffix;
          // Suffixes are indexing strides, not independent admission prefixes.
          // A zero factor makes traversal empty; do not impose a different
          // reverse-order cardinality refusal on that empty traversal.
          suffix = arith::MulIOp::create(builder, child.getLoc(), suffix,
                                         domain->children[i]->count);
        }
      }
    } else
      return refuse(&child, "unsupported finite enumeration");
    domains[child.getResult(0)] = std::move(domain);
  }
  auto found = domains.find(body.getTerminator()->getOperand(0));
  if (found == domains.end())
    return refuse(op, "unresolved yielded finite descriptor");
  auto domain = found->second;
  Value count = domain->count;
  std::function<FailureOr<Values>(const std::shared_ptr<Domain> &, Value)>
      items;
  items = [&](const std::shared_ptr<Domain> &node,
              Value position) -> FailureOr<Values> {
    if (node->kind == Domain::Range)
      return Values{
          arith::AddIOp::create(builder, op->getLoc(), node->lower, position)};
    if (node->kind == Domain::Indices)
      return Values{position};
    if (node->kind == Domain::Elements) {
      auto layout = layouts.get(node->collection);
      if (!layout) {
        consumeError(layout.takeError());
        return failure();
      }
      auto child = layouts.get((*layout)->collection->element);
      if (!child) {
        consumeError(child.takeError());
        return failure();
      }
      Values args(node->carrier);
      args.push_back(position);
      return (*layout)->collection->storage ==
                     CollectionLayout::Storage::FieldCoefficients
                 ? emit<VectorGetOp>(op, (*child)->lanes, args,
                                     {typed(node->collection)})
                 : emit<SequenceGetOp>(op, (*child)->lanes, args,
                                       {typed(node->collection)});
    }
    Values result;
    for (auto [i, factor] : enumerate(node->children)) {
      Value index = position;
      if (node->kind == Domain::Product) {
        index = emit<IndexDivOp>(op, {builder.getI64Type()},
                                 {position, node->suffixes[i]})[0];
        index = emit<IndexModOp>(op, {builder.getI64Type()},
                                 {index, factor->count})[0];
      }
      auto value = items(factor, index);
      if (failed(value))
        return failure();
      append_range(result, *value);
    }
    return result;
  };
  Values domainArguments = get(entry->domain), captures = get(entry->captures);
  Values initial = get(entry->initialState);
  Type collection;
  const ValueLayout *outputLayout = nullptr;
  Value output, capacity;
  if (!fold) {
    TypeRange results = op->getResultTypes();
    if (scoped)
      results = cast<exec::OutcomeType>(results[0]).getPayload();
    if (results.size() != 1)
      return refuse(op, "collect requires one collection result");
    collection = results.front();
    auto layout = layouts.get(collection);
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(op, "unsupported complete collect layout");
    }
    outputLayout = *layout;
    if (!outputLayout->collection || outputLayout->collection->storage ==
                                         CollectionLayout::Storage::PackedBytes)
      return refuse(op, "unsupported collected element family");
    if (auto array = dyn_cast<data::FieldArrayType>(collection))
      emit<RangeCheckOp>(op, {},
                         {count, integer(op->getLoc(), array.getLength())});
    capacity = count;
    if (!isa<data::FieldArrayType, data::FixedVectorType>(collection)) {
      // Traversal cardinality is independent of selected output cardinality.
      // Reserve once; callbacks still run before each capacity-checked write.
      Value ceiling = integer(op->getLoc(), options.limits.publicElements);
      auto fits = arith::CmpIOp::create(
          builder, op->getLoc(), arith::CmpIPredicate::ult, count, ceiling);
      capacity =
          arith::SelectOp::create(builder, op->getLoc(), fits, count, ceiling);
    }
    output = (outputLayout->collection->storage ==
                      CollectionLayout::Storage::FieldCoefficients
                  ? emit<VectorAllocOp>(op, {builder.getI64Type()}, {capacity},
                                        {typed(collection)})
                  : emit<SequenceAllocOp>(op, {builder.getI64Type()},
                                          {capacity}, {typed(collection)}))[0];
    initial = {integer(op->getLoc(), 0)};
  }
  auto loop =
      scf::ForOp::create(builder, op->getLoc(), integer(op->getLoc(), 0), count,
                         integer(op->getLoc(), 1), initial);
  loop.setUnsignedCmpAttr(builder.getUnitAttr());
  {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(loop.getBody());
    auto item = items(domain, loop.getInductionVar());
    if (failed(item))
      return refuse(op, "unsupported finite item lanes");
    auto arguments = [&](bool state) {
      Values args;
      if (scoped)
        args.push_back(get(op->getOperand(0))[0]);
      if (state)
        append_range(args, loop.getRegionIterArgs());
      append_range(args, *item);
      append_range(args, domainArguments);
      append_range(args, captures);
      return args;
    };
    auto collect = [&]() -> FailureOr<Values> {
      auto result = call(op, computation.helper, arguments(false));
      if (failed(result))
        return failure();
      auto element = layouts.get(outputLayout->collection->element);
      if (!element) {
        consumeError(element.takeError());
        return failure();
      }
      if (!llvm::equal(TypeRange((*element)->lanes),
                       ValueRange(*result).getTypes()))
        return failure();
      Values args{output, capacity, loop.getRegionIterArgs()[0]};
      append_range(args, *result);
      if (outputLayout->collection->storage ==
          CollectionLayout::Storage::FieldCoefficients)
        emit<VectorSetOp>(op, {}, args, {typed(collection)});
      else
        emit<SequenceSetOp>(op, {}, args, {typed(collection)});
      return Values{arith::AddIOp::create(builder, op->getLoc(),
                                          loop.getRegionIterArgs()[0],
                                          integer(op->getLoc(), 1))};
    };
    auto step = [&]() -> FailureOr<Values> {
      return fold ? call(op, computation.helper, arguments(true)) : collect();
    };
    FailureOr<Values> result = failure();
    if (!computation.predicate)
      result = step();
    else {
      auto condition = call(op, computation.predicate, arguments(false));
      if (failed(condition) || condition->size() != 1 ||
          !(*condition)[0].getType().isInteger(1))
        return refuse(op, "finite predicate requires Boolean result");
      auto branch = scf::IfOp::create(builder, op->getLoc(),
                                      ValueRange(initial).getTypes(),
                                      (*condition)[0], true);
      {
        OpBuilder::InsertionGuard branchGuard(builder);
        // SCF creates implicit yields when the converted state has no lanes.
        // Replace them through the conversion rewriter before filling either
        // arm, just as for the enclosing loop's implicit terminator.
        for (Region *arm : {&branch.getThenRegion(), &branch.getElseRegion()})
          if (!arm->front().empty())
            builder.eraseOp(arm->front().getTerminator());
        builder.setInsertionPointToStart(&branch.getThenRegion().front());
        auto value = step();
        if (failed(value) || !llvm::equal(ValueRange(*value).getTypes(),
                                          ValueRange(initial).getTypes()))
          return refuse(op,
                        "finite callback result differs from carried layout");
        scf::YieldOp::create(builder, op->getLoc(), *value);
        builder.setInsertionPointToStart(&branch.getElseRegion().front());
        scf::YieldOp::create(builder, op->getLoc(), loop.getRegionIterArgs());
      }
      result = Values(branch.getResults());
    }
    if (failed(result) || result->size() != initial.size())
      return refuse(op, "finite callback result differs from carried layout");
    if (!loop.getBody()->empty() && isa<scf::YieldOp>(loop.getBody()->back()))
      builder.eraseOp(&loop.getBody()->back());
    builder.setInsertionPointToEnd(loop.getBody());
    scf::YieldOp::create(builder, op->getLoc(), *result);
  }
  return bind(op, fold ? Values(loop.getResults())
                       : Values{output, loop.getResult(0)});
}

LogicalResult Lowering::lowerOperation(Operation *op) {
  StringRef name = op->getName().getStringRef();
  Location loc = op->getLoc();
  Values operands = get(op->getOperands());
  if (name == "exec.apply")
    return lowerBinding(op);
  if (name == "exec.fold" || name == "exec.collect" ||
      name == "data.finite_fold" || name == "data.finite_collect")
    return lowerFinite(op);
  if (name == "protocol.loop")
    return lowerLoop(op);
  if (name == "protocol.yield") {
    scf::YieldOp::create(builder, loc, operands);
    return success();
  }
  if (name == "func.return" || name == "protocol.finish") {
    func::ReturnOp::create(builder, loc, operands);
    return success();
  }
  if (name == "cf.br") {
    cf::BranchOp::create(builder, loc, op->getSuccessor(0), operands);
    return success();
  }
  if (auto branch = dyn_cast<cf::CondBranchOp>(op)) {
    cf::CondBranchOp::create(
        builder, loc, get(branch.getCondition())[0], branch.getTrueDest(),
        get(branch.getTrueDestOperands()), branch.getFalseDest(),
        get(branch.getFalseDestOperands()));
    return success();
  }
  if (name == "exec.dispatch") {
    // Admission checks produced success arguments precede explicit operands.
    auto sizes =
        op->getAttrOfType<DenseI32ArrayAttr>("successor_operand_segments");
    if (!sizes || sizes.size() != 2 || sizes[0] < 0)
      return refuse(op, "invalid checked outcome dispatch");
    Values args = get(op->getOperand(0));
    append_range(args, get(op->getOperands().slice(1, sizes[0])));
    cf::BranchOp::create(builder, loc, op->getSuccessor(0), args);
    return success();
  }
  if (name == "exec.match") {
    active(op, operands[0]);
    auto variant = dyn_cast<data::VariantType>(op->getOperand(1).getType());
    auto segments =
        op->getAttrOfType<DenseI32ArrayAttr>("successor_operand_segments");
    if (!variant || !segments ||
        size_t(segments.size()) != variant.getAlternatives().size() + 1)
      return refuse(op, "invalid checked variant dispatch");
    auto type = builder.getNamedAttr("value_type", TypeAttr::get(variant));
    Value input = get(op->getOperand(1))[0];
    Value tag =
        emit<VariantTagOp>(op, {builder.getI64Type()}, {input}, {type})[0];
    Region *region = builder.getInsertionBlock()->getParent();
    unsigned forwarded = 2 + segments[0];
    // Dispatch to dedicated arm blocks before reading any payload. Inactive
    // alternatives can have different sizes and must never be eagerly loaded.
    for (auto [i, alternative] : enumerate(variant.getAlternatives())) {
      Block *load;
      Block *next = nullptr;
      {
        OpBuilder::InsertionGuard guard(builder);
        load = builder.createBlock(region);
        if (i + 1 != variant.getAlternatives().size())
          next = builder.createBlock(region);
      }
      if (i + 1 == variant.getAlternatives().size())
        cf::BranchOp::create(builder, loc, load);
      else {
        auto selected = arith::CmpIOp::create(
            builder, loc, arith::CmpIPredicate::eq, tag, integer(loc, i));
        cf::CondBranchOp::create(builder, loc, selected, load, ValueRange{},
                                 next, ValueRange{});
      }
      builder.setInsertionPointToStart(load);
      Values args;
      for (auto [index, payload] : enumerate(alternative.getPayload())) {
        auto lanes = converted(TypeRange(payload), op);
        if (failed(lanes))
          return failure();
        append_range(args,
                     emit<VariantGetOp>(
                         op, *lanes, {input},
                         {type,
                          builder.getNamedAttr("alternative",
                                               builder.getI32IntegerAttr(i)),
                          builder.getNamedAttr(
                              "payload", builder.getI32IntegerAttr(index))}));
      }
      append_range(args,
                   get(op->getOperands().slice(forwarded, segments[i + 1])));
      forwarded += segments[i + 1];
      cf::BranchOp::create(builder, loc, op->getSuccessor(i + 1), args);
      if (next)
        builder.setInsertionPointToStart(next);
    }
    return success();
  }
  if (name == "exec.returned")
    return bind(op, operands);
  if (name == "exec.complete" || name == "exec.test") {
    active(op, operands[0]);
    return bind(op, ValueRange(operands).drop_front());
  }
  if (name == "exec.boolean") {
    active(op, operands[0]);
    auto value = op->getAttrOfType<BoolAttr>("value");
    return bind(op, {integer(loc, value.getValue(), 1)});
  }
  if (name == "exec.reject") {
    active(op, operands[0]);
    emit<SourceStopOp>(op, {}, {},
                       {builder.getNamedAttr("site", op->getAttr("site"))});
    return bind(op, {integer(loc, 0)});
  }
  if (name == "exec.failed") {
    // Only a directly rejecting block can still reach this operation; rejection
    // already emitted a nonreturning effect. Retain an explicit second terminal
    // effect rather than manufacturing a successful source outcome.
    emit<SourceStopOp>(op, {}, {});
    auto results = converted(op->getResultTypes(), op);
    if (failed(results))
      return failure();
    Values inactive;
    for (Type type : *results)
      inactive.push_back(
          constant(loc, type, APInt(type.getIntOrFloatBitWidth(), 0)));
    return bind(op, inactive);
  }
  if (name == "exec.range") {
    active(op, operands[0]);
    emit<RangeAdmitOp>(op, {}, ValueRange(operands).drop_front());
    return bind(op, ValueRange(operands).drop_front());
  }
  if (name == "runtime.iteration") {
    active(op, operands[0]);
    return bind(op, {operands[1]});
  }
  if (name == "runtime.enter_scope") {
    if (failed(checkCapabilities(op, op->getOperandTypes())))
      return failure();
    Value generation = integer(loc, UINT64_MAX);
    for (Value value : op->getOperands())
      if (isTranscript(value.getType()))
        generation = get(value)[0];
    return bind(op, emitResult<ScopeEnterOp>(op, {operands[0], generation}));
  }
  if (name == "runtime.exit_scope") {
    if (failed(checkCapabilities(op, op->getOperandTypes())))
      return failure();
    // Exit produces one affine ticket followed by actual outcome payload.
    Value generation = integer(loc, UINT64_MAX);
    auto outcome = cast<exec::OutcomeType>(op->getOperand(1).getType());
    unsigned offset = 1;
    for (Type type : outcome.getPayload()) {
      if (isTranscript(type))
        generation = operands[offset];
      auto convertedTypes = converted(TypeRange(type), op);
      if (failed(convertedTypes))
        return failure();
      offset += convertedTypes->size();
    }
    auto ticket = emit<ScopeExitOp>(op, {builder.getI64Type()},
                                    {operands[0], generation});
    append_range(ticket, ValueRange(operands).drop_front());
    return bind(op, ticket);
  }
  if (name == "runtime.borrow_transfer") {
    auto ticket =
        emit<TransferMakeOp>(op, {builder.getI64Type()}, {operands[0]});
    append_range(ticket, ValueRange(operands).drop_front());
    return bind(op, ticket);
  }
  if (name == "runtime.accept_transfer") {
    emit<TransferAcceptOp>(op, {}, {operands[0], operands[1]});
    return bind(op, ValueRange(operands).drop_front(2));
  }
  if (name == "runtime.transfer_values") {
    emit<TransferCheckOp>(op, {}, {operands[0]});
    return bind(op, ValueRange(operands).drop_front());
  }
  if (name == "runtime.release_transfer") {
    emit<TransferReleaseOp>(op, {}, {operands[0]});
    return success();
  }
  if (name == "func.call" || name == "exec.compute" ||
      name == "protocol.local_call") {
    Operation *callee = resolve(op, "callee");
    bool local = name == "protocol.local_call";
    bool compute = name == "exec.compute";
    Values args = operands;
    Value scope;
    if (compute) {
      active(op, operands[0]);
      args.erase(args.begin());
    }
    if (local) {
      if (failed(checkCapabilities(op, op->getOperandTypes())) ||
          failed(checkCapabilities(op, op->getResultTypes())))
        return failure();
      Value generation = integer(loc, UINT64_MAX);
      for (Value value : op->getOperands())
        if (isTranscript(value.getType()))
          generation = get(value)[0];
      Value parent = emit<ScopeCurrentOp>(op, {builder.getI64Type()}, {})[0];
      scope = emit<ScopeEnterOp>(op, {builder.getI64Type()},
                                 {parent, generation})[0];
      args.insert(args.begin(), scope);
    }
    auto results = call(op, callee, args);
    if (failed(results))
      return failure();
    if (local) {
      Value generation = integer(loc, UINT64_MAX);
      unsigned offset = 0;
      for (Type type : op->getResultTypes()) {
        if (isTranscript(type))
          generation = (*results)[offset];
        auto convertedTypes = converted(TypeRange(type), op);
        if (failed(convertedTypes))
          return failure();
        offset += convertedTypes->size();
      }
      emit<ScopeExitOp>(op, {builder.getI64Type()}, {scope, generation});
    }
    return bind(op, *results);
  }
  if (name == "protocol.receive") {
    if (op->getNumResults() != 1)
      return refuse(op, "receive requires one complete payload");
    return bind(
        op, emitResult<ProofReceiveOp>(
                op, {},
                {builder.getNamedAttr(
                    "value_type", TypeAttr::get(op->getResult(0).getType()))}));
  }
  if (name == "protocol.guard") {
    emit<SourceGuardOp>(op, {}, operands,
                        {builder.getNamedAttr("site", op->getAttr("site"))});
    return success();
  }
  StringRef scalar = llvm::StringSwitch<StringRef>(name)
                         .Case("algebra.constant", "field.constant")
                         .Case("algebra.field_add", "field.add")
                         .Case("algebra.field_subtract", "field.sub")
                         .Case("algebra.field_multiply", "field.mul")
                         .Case("algebra.field_equal", "field.equal")
                         .Default("");
  if (name == "arith.andi" && op->getResult(0).getType().isInteger(1))
    scalar = "bool.and";
  if (name == "arith.ori" && op->getResult(0).getType().isInteger(1))
    scalar = "bool.or";
  if (name == "arith.xori" && op->getResult(0).getType().isInteger(1))
    scalar = "bool.xor";
  if (!scalar.empty())
    return *lowerScalar(op, scalar, operands,
                        name == "algebra.constant"
                            ? builder.getArrayAttr({op->getAttr("value")})
                            : builder.getArrayAttr({}));
  if (name == "data.make" || name == "exec.variant") {
    bool scoped = name == "exec.variant";
    if (scoped)
      active(op, operands[0]);
    Type type = scoped ? cast<exec::OutcomeType>(op->getResult(0).getType())
                             .getPayload()[0]
                       : op->getResult(0).getType();
    auto variant = dyn_cast<data::VariantType>(type);
    auto label = op->getAttrOfType<StringAttr>("alternative");
    if (!variant || !label)
      return refuse(op, "invalid variant construction");
    auto alternatives = variant.getAlternatives();
    auto selected = llvm::find_if(
        alternatives, [&](auto arm) { return arm.getLabel() == label; });
    if (selected == alternatives.end())
      return refuse(op, "unknown variant alternative");
    return bind(
        op, emitResult<VariantMakeOp>(
                op, ValueRange(operands).drop_front(scoped ? 1 : 0),
                {builder.getNamedAttr("value_type", TypeAttr::get(type)),
                 builder.getNamedAttr("alternative",
                                      builder.getI32IntegerAttr(
                                          selected - alternatives.begin()))}));
  }
  if (name == "data.is" || name == "data.get") {
    auto variant = dyn_cast<data::VariantType>(op->getOperand(0).getType());
    if (!variant)
      return refuse(op, "requires complete variant type");
    auto type = builder.getNamedAttr("value_type", TypeAttr::get(variant));
    if (name == "data.get") {
      auto index = op->getAttrOfType<IntegerAttr>("index");
      if (!index || variant.getAlternatives().size() != 1)
        return refuse(op, "total projection requires a single alternative");
      return bind(
          op, emitResult<VariantGetOp>(
                  op, operands,
                  {type,
                   builder.getNamedAttr("alternative",
                                        builder.getI32IntegerAttr(0)),
                   builder.getNamedAttr("payload", builder.getI32IntegerAttr(
                                                       index.getUInt()))}));
    }
    auto label = op->getAttrOfType<StringAttr>("alternative");
    auto alternatives = variant.getAlternatives();
    auto selected = llvm::find_if(
        alternatives, [&](auto arm) { return arm.getLabel() == label; });
    if (selected == alternatives.end())
      return refuse(op, "unknown variant alternative");
    auto tag =
        emit<VariantTagOp>(op, {builder.getI64Type()}, operands, {type})[0];
    return bind(op, {arith::CmpIOp::create(
                        builder, loc, arith::CmpIPredicate::eq, tag,
                        integer(loc, selected - alternatives.begin()))});
  }
  if (name == "data.sequence_empty" || name == "data.sequence_append" ||
      name == "data.sequence_length") {
    Type type = name == "data.sequence_empty" ? op->getResult(0).getType()
                                              : op->getOperand(0).getType();
    SmallVector<NamedAttribute> attrs{
        builder.getNamedAttr("value_type", TypeAttr::get(type))};
    if (name == "data.sequence_empty")
      return bind(op, emitResult<SequenceEmptyOp>(op, operands, attrs));
    if (name == "data.sequence_append")
      return bind(op, emitResult<SequenceAppendOp>(op, operands, attrs));
    return bind(op, emitResult<SequenceLengthOp>(op, operands, attrs));
  }
  if (name == "data.bounded_at" || name == "data.array_at") {
    Type type = op->getOperand(0).getType();
    auto layout = layouts.get(type);
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(op, "unsupported collection access");
    }
    if (!(*layout)->collection)
      return refuse(op, "requires complete collection layout");
    if (name == "data.array_at") {
      auto index = op->getAttrOfType<IntegerAttr>("index");
      if (!index)
        return refuse(op, "missing array index");
      operands.push_back(integer(loc, index.getUInt()));
    }
    SmallVector<NamedAttribute> attrs{
        builder.getNamedAttr("value_type", TypeAttr::get(type))};
    return bind(op, (*layout)->collection->storage ==
                            CollectionLayout::Storage::FieldCoefficients
                        ? emitResult<VectorGetOp>(op, operands, attrs)
                        : emitResult<SequenceGetOp>(op, operands, attrs));
  }
  if (name == "data.array_from_elements") {
    auto array = dyn_cast<data::FieldArrayType>(op->getResult(0).getType());
    if (!array || op->getNumOperands() != array.getLength())
      return refuse(op, "invalid fixed field array construction");
    auto type = builder.getNamedAttr("value_type", TypeAttr::get(array));
    Value count = integer(loc, array.getLength());
    Value pointer =
        emit<VectorAllocOp>(op, {builder.getI64Type()}, {count}, {type})[0];
    for (auto [index, element] : enumerate(op->getOperands())) {
      Values args{pointer, count, integer(loc, index)};
      append_range(args, get(element));
      emit<VectorSetOp>(op, {}, args, {type});
    }
    return bind(op, {pointer, count});
  }
  if (name == "data.index") {
    auto literal = op->getAttrOfType<IntegerAttr>("value");
    return bind(op, {integer(loc, literal.getUInt())});
  }
  if (name == "data.dim") {
    auto axis = op->getAttrOfType<IntegerAttr>("axis");
    auto layout = layouts.get(op->getOperand(0).getType());
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(op, "unsupported collection dimension");
    }
    if (!axis || axis.getUInt() != 0 || !(*layout)->collection ||
        operands.size() != 2)
      return refuse(op, "unsupported collection dimension");
    SmallVector<NamedAttribute> attrs{builder.getNamedAttr(
        "value_type", TypeAttr::get(op->getOperand(0).getType()))};
    if ((*layout)->collection->storage ==
        CollectionLayout::Storage::FieldCoefficients)
      return bind(op, emitResult<VectorLengthOp>(op, operands, attrs));
    if ((*layout)->kind == ValueLayout::Kind::Bytes)
      return bind(op, emitResult<BytesLengthOp>(op, operands, attrs));
    return bind(op, emitResult<SequenceLengthOp>(op, operands, attrs));
  }
  if (name == "data.index_power_of_two") {
    return bind(op, emitResult<IndexPowerOfTwoOp>(op, operands));
  }
  if (name == "data.index_equal" || name == "data.index_less")
    return bind(op, {arith::CmpIOp::create(builder, loc,
                                           name.ends_with("less")
                                               ? arith::CmpIPredicate::ult
                                               : arith::CmpIPredicate::eq,
                                           operands[0], operands[1])});
  if (name.starts_with("data.index_")) {
    if (name == "data.index_add")
      return bind(op, emitResult<IndexAddOp>(op, operands));
    if (name == "data.index_subtract")
      return bind(op, emitResult<IndexSubOp>(op, operands));
    if (name == "data.index_multiply")
      return bind(op, emitResult<IndexMulOp>(op, operands));
    if (name == "data.index_divide")
      return bind(op, emitResult<IndexDivOp>(op, operands));
    if (name == "data.index_modulo")
      return bind(op, emitResult<IndexModOp>(op, operands));
    if (name == "data.index_logical_shift_right")
      return bind(op, emitResult<IndexLogicalShiftRightOp>(op, operands));
    if (name == "data.index_wrapping_add")
      return bind(
          op, {arith::AddIOp::create(builder, loc, operands[0], operands[1])});
    if (name == "data.index_wrapping_subtract")
      return bind(
          op, {arith::SubIOp::create(builder, loc, operands[0], operands[1])});
    if (name == "data.index_bit_and")
      return bind(
          op, {arith::AndIOp::create(builder, loc, operands[0], operands[1])});
  }
  if (auto select = dyn_cast<arith::SelectOp>(op)) {
    auto condition = get(select.getCondition());
    auto yes = get(select.getTrueValue());
    auto no = get(select.getFalseValue());
    if (condition.size() != 1 || yes.size() != no.size())
      return refuse(op, "invalid expanded selection");
    Values results;
    for (auto [a, b] : zip(yes, no))
      results.push_back(
          arith::SelectOp::create(builder, loc, condition[0], a, b));
    return bind(op, results);
  }
  if (name.starts_with("arith.")) {
    // Preserve standard fixed-width arithmetic and predicate semantics. The
    // exporter has an independent positive opcode inventory too.
    if (!isa<arith::ConstantOp, arith::CmpIOp, arith::AddIOp, arith::SubIOp,
             arith::MulIOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
             arith::SelectOp, arith::ExtUIOp, arith::ExtSIOp, arith::TruncIOp,
             arith::IndexCastOp, arith::IndexCastUIOp>(op))
      return refuse(op, "unsupported or potentially undefined arith operation");
    auto resultTypes = converted(op->getResultTypes(), op);
    if (failed(resultTypes))
      return failure();
    if (isa<arith::IndexCastOp, arith::IndexCastUIOp>(op)) {
      if (operands[0].getType() == (*resultTypes)[0])
        return bind(op, operands);
      unsigned from = operands[0].getType().getIntOrFloatBitWidth();
      unsigned to = (*resultTypes)[0].getIntOrFloatBitWidth();
      Value casted;
      if (from > to)
        casted = arith::TruncIOp::create(builder, loc, (*resultTypes)[0],
                                         operands[0]);
      else if (isa<arith::IndexCastOp>(op))
        casted = arith::ExtSIOp::create(builder, loc, (*resultTypes)[0],
                                        operands[0]);
      else
        casted = arith::ExtUIOp::create(builder, loc, (*resultTypes)[0],
                                        operands[0]);
      return bind(op, {casted});
    }
    OperationState state(loc, name);
    state.addOperands(operands);
    state.addTypes(*resultTypes);
    state.addAttributes(op->getAttrs());
    // Reject overflow promises: the source index contract is separately
    // checked.
    if (auto flags =
            op->getAttrOfType<arith::IntegerOverflowFlagsAttr>("overflowFlags"))
      if (flags.getValue() != arith::IntegerOverflowFlags::none)
        return refuse(op, "arithmetic overflow promises are unsupported");
    if (auto literal = op->getAttrOfType<IntegerAttr>("value"))
      state.attributes.set("value", builder.getIntegerAttr((*resultTypes)[0],
                                                           literal.getValue()));
    return bind(op, builder.create(state)->getResults());
  }
  return refuse(op, "no EVM realization for this reachable operation");
}

class EndpointConversion final : public ConversionPattern {
public:
  EndpointConversion(const PreparedEndpoint &prepared,
                     const EvmOptions &options, NativeLayouts &layouts,
                     const EvmTypes &types, MLIRContext *context)
      : ConversionPattern(types, MatchAnyOpTypeTag(), 1, context),
        prepared(prepared), options(options), layouts(layouts), types(types) {}
  LogicalResult
  matchAndRewrite(Operation *op, ArrayRef<ValueRange> operands,
                  ConversionPatternRewriter &rewriter) const override {
    // The one-to-many adaptor is produced by MLIR, not a target SSA map.
    if (operands.size() != op->getNumOperands())
      return failure();
    auto found = prepared.functions.find(op);
    if (found != prepared.functions.end()) {
      const auto &info = found->second;
      auto function = func::FuncOp::create(rewriter, op->getLoc(), info.name,
                                           info.signature);
      function.setPrivate();
      if (info.entry)
        function->setAttr("evm.entry", rewriter.getUnitAttr());
      rewriter.inlineRegionBefore(op->getRegion(0), function.getBody(),
                                  function.end());
      for (Block &block : llvm::make_early_inc_range(function.getBody())) {
        if (prepared.omittedBlocks.contains(&block)) {
          // Source dispatch edges still name these blocks. Erase their
          // omitted instructions through the rewriter; remove the empty
          // unreachable blocks once those incoming edges are converted.
          for (Operation &nested : llvm::reverse(block))
            rewriter.eraseOp(&nested);
          continue;
        }
        auto signature = types.convertBlockSignature(&block);
        if (!signature)
          return failure();
        rewriter.applySignatureConversion(&block, *signature, &types);
      }
      rewriter.eraseOp(op);
      return success();
    }
    Lowering lowering(prepared, options, layouts, types, rewriter, op,
                      operands);
    if (failed(lowering.lowerOperation(op)))
      return failure();
    if (!lowering.replaced)
      rewriter.eraseOp(op);
    return success();
  }

private:
  const PreparedEndpoint &prepared;
  const EvmOptions &options;
  NativeLayouts &layouts;
  const EvmTypes &types;
};

LogicalResult convertEndpoint(ModuleOp module, const PreparedEndpoint &prepared,
                              const EvmOptions &options, NativeLayouts &layouts,
                              const EvmTypes &types) {
  ConversionTarget target(*module.getContext());
  target.addLegalOp<ModuleOp>();
  target.addLegalDialect<EvmDialect>();
  auto legal = [&](Operation *op) {
    if (!types.isLegal(op->getOperandTypes()) ||
        !types.isLegal(op->getResultTypes()))
      return false;
    for (Region &region : op->getRegions())
      for (Block &block : region)
        if (!prepared.omittedBlocks.contains(&block) &&
            !types.isLegal(block.getArgumentTypes()))
          return false;
    if (auto flags =
            op->getAttrOfType<arith::IntegerOverflowFlagsAttr>("overflowFlags"))
      if (flags.getValue() != arith::IntegerOverflowFlags::none)
        return false;
    return true;
  };
  target.addDynamicallyLegalOp<func::FuncOp>([&](func::FuncOp op) {
    return !prepared.functions.count(op) &&
           types.isSignatureLegal(op.getFunctionType()) && legal(op);
  });
  target.addDynamicallyLegalOp<func::CallOp>([&](func::CallOp op) {
    // Source call sites must be rewritten even if their lane counts coincide.
    return !prepared.references.count(op) && legal(op);
  });
  target.addDynamicallyLegalOp<
      func::ReturnOp, cf::BranchOp, cf::CondBranchOp, arith::ConstantOp,
      arith::CmpIOp, arith::AddIOp, arith::SubIOp, arith::MulIOp, arith::AndIOp,
      arith::OrIOp, arith::XOrIOp, arith::SelectOp, arith::ExtUIOp,
      arith::ExtSIOp, arith::TruncIOp, scf::ForOp, scf::IfOp, scf::YieldOp>(
      legal);
  RewritePatternSet patterns(module.getContext());
  patterns.add<EndpointConversion>(prepared, options, layouts, types,
                                   module.getContext());
  return applyFullConversion(module, target, std::move(patterns));
}

// The upstream algorithm only requests fillers for newly introduced inactive
// control lanes. All supported lanes are integers. This is not a source poison
// rewrite: source UB never enters this target, and unreachable requests refuse.
class InactiveIntegerLanes final : public ControlFlowToSCFTransformation {
public:
  Value getUndefValue(Location loc, OpBuilder &builder, Type type) override {
    auto integer = dyn_cast<IntegerType>(type);
    if (!integer)
      llvm_unreachable("prechecked EVM lane must be an integer");
    return arith::ConstantOp::create(
        builder, loc, integer,
        builder.getIntegerAttr(integer, APInt(integer.getWidth(), 0)));
  }
  FailureOr<Operation *> createUnreachableTerminator(Location loc, OpBuilder &,
                                                     Region &) override {
    emitError(loc, "[evm.control-flow] unsupported statically infinite loop");
    return failure();
  }
};
} // namespace

LogicalResult checkTarget(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  TypeConverter types;
  types.addConversion([](IntegerType t) -> Type {
    if (t.isSignless() && is_contained({1u, 32u, 64u, 256u}, t.getWidth()))
      return t;
    return {};
  });
  ConversionTarget target(*module.getContext());
  target.addLegalOp<ModuleOp>();
  auto legalTypes = [&](Operation *op) {
    if (auto flags =
            op->getAttrOfType<arith::IntegerOverflowFlagsAttr>("overflowFlags"))
      if (flags.getValue() != arith::IntegerOverflowFlags::none)
        return false;
    if (!types.isLegal(op->getOperandTypes()) ||
        !types.isLegal(op->getResultTypes()))
      return false;
    for (Region &region : op->getRegions())
      for (Block &block : region)
        if (!types.isLegal(block.getArgumentTypes()))
          return false;
    return true;
  };
  target.addDynamicallyLegalOp<func::FuncOp>([&](func::FuncOp op) {
    return types.isSignatureLegal(op.getFunctionType()) && legalTypes(op);
  });
  target.addDynamicallyLegalOp<
      func::CallOp, func::ReturnOp, arith::ConstantOp, arith::CmpIOp,
      arith::AddIOp, arith::SubIOp, arith::MulIOp, arith::AndIOp, arith::OrIOp,
      arith::XOrIOp, arith::SelectOp, arith::ExtUIOp, arith::ExtSIOp,
      arith::TruncIOp, arith::IndexCastOp, arith::IndexCastUIOp, scf::ForOp,
      scf::IfOp, scf::WhileOp, scf::ConditionOp, scf::YieldOp,
      scf::IndexSwitchOp,
#define GET_OP_LIST
#include "zkc/Dialect/Evm/Ops.cpp.inc"
      >(legalTypes);
  WalkResult checked = module.walk([&](Operation *op) {
    if (target.isLegal(op))
      return WalkResult::advance();
    op->emitError(
        "[evm.target-legality] residual unsupported operation or type");
    return WalkResult::interrupt();
  });
  if (checked.wasInterrupted())
    return failure();
  return success();
}

Expected<OwningOpRef<ModuleOp>> lowerEndpoint(const CheckedEndpoint &endpoint,
                                              const EvmOptions &options) {
  auto source = endpoint.sourceSnapshot();
  auto candidate = endpoint.candidateSnapshot();
  if (auto error = checkEndpointClosure(*source, *candidate, endpoint.role()))
    return std::move(error);
  // The selected closure holds only the verifier's own completions. This
  // target realizes no conditional completion outcome, so one refuses by name
  // before realization rather than through the generic operation refusal.
  Operation *completion = nullptr;
  candidate->walk([&](Operation *op) {
    if (op->getName().getStringRef() != "protocol.finish_if")
      return WalkResult::advance();
    completion = op;
    return WalkResult::interrupt();
  });
  if (completion) {
    completion->emitError("[evm.completion] protocol.finish_if: conditional "
                          "participant completion has no EVM realization");
    return zkc::error("evm.completion", "conditional participant completion "
                                        "has no EVM realization");
  }
  // Each participant loop's checked maximum lies within the deployment's
  // participant loop maximum; the transcript transitions stay the only global
  // bound.
  std::optional<uint64_t> overLimit;
  candidate->walk([&](Operation *op) {
    if (op->getName().getStringRef() != "protocol.loop")
      return WalkResult::advance();
    auto maximum = op->getAttrOfType<IntegerAttr>("maximum");
    if (!maximum || maximum.getInt() < 0 ||
        maximum.getUInt() <= options.limits.participantLoopMaximum)
      return WalkResult::advance();
    overLimit = maximum.getUInt();
    op->emitError("[evm.participant-loop-maximum] protocol.loop: loop "
                  "maximum ")
        << *overLimit << " exceeds the deployment's participant loop maximum "
        << options.limits.participantLoopMaximum;
    return WalkResult::interrupt();
  });
  if (overLimit)
    return zkc::error(
        "evm.participant-loop-maximum",
        "loop maximum " + std::to_string(*overLimit) +
            " exceeds the deployment's participant loop "
            "maximum " +
            std::to_string(options.limits.participantLoopMaximum));
  auto *context = candidate->getContext();
  context->getOrLoadDialect<EvmDialect>();
  context->getOrLoadDialect<scf::SCFDialect>();
  context->getOrLoadDialect<arith::ArithDialect>();
  context->getOrLoadDialect<cf::ControlFlowDialect>();
  context->getOrLoadDialect<func::FuncDialect>();
  OwningOpRef<ModuleOp> target(ModuleOp::create(candidate->getLoc()));
  NativeLayouts layouts(*context);
  EvmTypes types(layouts, context);
  PreparedEndpoint prepared;
  if (failed(prepared.prepare(*candidate, *target, types, layouts)) ||
      failed(convertEndpoint(*target, prepared, options, layouts, types)))
    return zkc::error("evm.lowering", "EVM operation realization failed");
  for (auto function : target->getOps<func::FuncOp>()) {
    IRRewriter cleanup(context);
    (void)eraseUnreachableBlocks(cleanup, function->getRegions());
  }
  if (failed(verify(*target)))
    return zkc::error("evm.lowering",
                      "EVM operation realization failed verification");
  InactiveIntegerLanes policy;
  for (auto function : target->getOps<func::FuncOp>()) {
    DominanceInfo dominance;
    if (failed(transformCFGToSCF(function.getBody(), policy, dominance)))
      return zkc::error("evm.control-flow",
                        "could not structure checked endpoint");
  }
  if (failed(checkTarget(*target)))
    return zkc::error("evm.target-legality", "EVM full conversion failed");
  return target;
}
} // namespace zkc::evm
