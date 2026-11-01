#include "mlir/Conversion/ControlFlowToSCF/ControlFlowToSCF.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Target.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
namespace {
constexpr StringLiteral field = "bls12-381.fr";
constexpr StringLiteral suite = "hash-chain.keccak256.bls12-381.fr64be/0";
constexpr StringLiteral modulus = "52435875175126190479447740508185965837690552"
                                  "500527637822603658699938581184513";
using Values = SmallVector<Value>;
using ValueMap = llvm::DenseMap<Value, Values>;

class EvmTypes : public TypeConverter {
public:
  explicit EvmTypes(MLIRContext *context) {
    addConversion([context, this](Type type, SmallVectorImpl<Type> &out) {
      return convert(type, out, context);
    });
  }

private:
  LogicalResult convert(Type type, SmallVectorImpl<Type> &out,
                        MLIRContext *context) const {
    auto i64 = IntegerType::get(context, 64);
    if (auto integer = dyn_cast<IntegerType>(type)) {
      if (!is_contained({1u, 32u, 64u, 256u}, integer.getWidth()))
        return failure();
      out.push_back(IntegerType::get(context, integer.getWidth()));
    } else if (isa<IndexType>(type)) {
      out.push_back(i64);
    } else if (auto scalar = dyn_cast<algebra::FieldType>(type)) {
      if (scalar.getDomain() != field)
        return failure();
      out.push_back(IntegerType::get(context, 256));
    } else if (auto vector = dyn_cast<algebra::FieldVectorType>(type)) {
      if (vector.getDomain() != field)
        return failure();
      out.append({i64, i64});
    } else if (isa<algebra::IndicesType>(type)) {
      out.append({i64, i64});
    } else if (auto capability = dyn_cast<runtime::CapabilityType>(type)) {
      if (capability.getKind() != runtime::CapabilityKind::Transcript ||
          capability.getIdentity() != suite)
        return failure();
      out.push_back(i64);
    } else if (isa<runtime::ScopeType, exec::StopType>(type)) {
      out.push_back(i64);
    } else if (auto outcome = dyn_cast<exec::OutcomeType>(type)) {
      for (Type payload : outcome.getPayload())
        if (failed(convert(payload, out, context)))
          return failure();
    } else if (auto transfer = dyn_cast<runtime::TransferType>(type)) {
      // An affine transfer owns a runtime ticket independently of its payload.
      out.push_back(i64);
      for (Type payload : transfer.getPayload())
        if (failed(convert(payload, out, context)))
          return failure();
    } else {
      return failure();
    }
    return success();
  }
};

class Lowering {
public:
  Lowering(ModuleOp source, ModuleOp complete, ModuleOp target,
           const EvmOptions &options)
      : source(source), complete(complete), target(target), options(options),
        types(source.getContext()), builder(source.getContext()) {}
  LogicalResult run();

private:
  ModuleOp source, complete, target;
  const EvmOptions &options;
  EvmTypes types;
  OpBuilder builder;
  SymbolTableCollection symbols;
  llvm::DenseMap<Operation *, func::FuncOp> functions;
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
  Value prime(Location loc) {
    return constant(loc, builder.getIntegerType(256), APInt(256, modulus, 10));
  }
  Values get(ValueRange values, const ValueMap &map) {
    Values result;
    for (Value value : values)
      append_range(result, map.lookup(value));
    return result;
  }
  LogicalResult bind(Operation *op, ValueRange result, ValueMap &map) {
    unsigned offset = 0;
    for (Value value : op->getResults()) {
      auto convertedTypes = converted(TypeRange(value.getType()), op);
      if (failed(convertedTypes) ||
          offset + convertedTypes->size() > result.size())
        return refuse(op, "invalid realized result signature");
      map[value] = Values(result.slice(offset, convertedTypes->size()));
      offset += convertedTypes->size();
    }
    if (offset != result.size())
      return refuse(op, "extra realized result values");
    return success();
  }
  Values checked(Operation *op, StringRef opcode, TypeRange result,
                 ValueRange operands,
                 ArrayRef<NamedAttribute> attributes = {}) {
    return Values(CheckedOp::create(builder, op->getLoc(), result, opcode,
                                    operands, attributes)
                      .getResults());
  }
  Values checkedResult(Operation *op, StringRef opcode, ValueRange operands,
                       ArrayRef<NamedAttribute> attributes = {}) {
    auto result = converted(op->getResultTypes(), op);
    if (failed(result))
      return {};
    return checked(op, opcode, *result, operands, attributes);
  }
  void active(Operation *op, Value scope) {
    checked(op, "scope.check", {}, {scope});
  }
  Operation *resolve(Operation *op, StringRef name) {
    auto reference = op->getAttrOfType<SymbolRefAttr>(name);
    return reference ? symbols.lookupNearestSymbolFrom(op, reference) : nullptr;
  }
  LogicalResult lowerBody(Operation *owner, func::FuncOp function);
  LogicalResult lowerOperation(Operation *, ValueMap &,
                               const llvm::DenseMap<Block *, Block *> &);
  LogicalResult lowerFinite(Operation *, ValueMap &);
  LogicalResult lowerBinding(Operation *, ValueMap &);
  std::optional<LogicalResult> lowerScalar(Operation *, StringRef, ValueRange,
                                           ArrayAttr, ValueMap &);
  LogicalResult lowerLoop(Operation *, ValueMap &);
  FailureOr<Values> call(Operation *op, Operation *callee, ValueRange args) {
    auto function = functions.lookup(callee);
    if (!function || function.getNumArguments() != args.size()) {
      (void)refuse(op, "unresolved helper or mismatched expanded signature");
      return failure();
    }
    return Values(func::CallOp::create(builder, op->getLoc(), function, args)
                      .getResults());
  }
};

LogicalResult Lowering::run() {
  SmallVector<Operation *> inventory;
  source.walk([&](Operation *op) {
    if (isa<func::FuncOp>(op) ||
        op->getName().getStringRef() == "protocol.participant")
      inventory.push_back(op);
  });
  unsigned serial = 0, entries = 0;
  for (Operation *owner : inventory) {
    bool entry = owner->getName().getStringRef() == "protocol.participant";
    auto attribute = owner->getAttrOfType<TypeAttr>("function_type");
    auto signature = attribute ? dyn_cast<FunctionType>(attribute.getValue())
                               : FunctionType();
    if (!signature || (entry && ++entries != 1))
      return refuse(owner, "expected exactly one selected endpoint");
    auto inputs = converted(signature.getInputs(), owner);
    auto outputs = converted(signature.getResults(), owner);
    if (failed(inputs) || failed(outputs))
      return failure();
    builder.setInsertionPointToEnd(target.getBody());
    auto function = func::FuncOp::create(
        builder, owner->getLoc(),
        entry ? "verify_endpoint" : "helper_" + std::to_string(serial++),
        builder.getFunctionType(*inputs, *outputs));
    function.setPrivate();
    if (entry) {
      function->setAttr("evm.entry", builder.getUnitAttr());
      function->setAttr("evm.logical_type", attribute);
      // The complete source retains the checked original-to-endpoint ports;
      // executable closure selection deliberately prunes that record.
      complete.walk([&](Operation *record) {
        if (record->getName().getStringRef() != "protocol.projection")
          return;
        for (Attribute item : record->getAttrOfType<ArrayAttr>("interfaces")) {
          auto interface = cast<DictionaryAttr>(item);
          if (interface.get("source") != owner->getAttr("instance"))
            continue;
          for (Attribute port : interface.getAs<ArrayAttr>("participants")) {
            auto participant = cast<DictionaryAttr>(port);
            if (participant.get("role") == owner->getAttr("role"))
              function->setAttr("evm.output_ports", participant.get("outputs"));
          }
        }
      });
    }
    functions[owner] = function;
  }
  if (entries != 1)
    return refuse(source, "missing selected endpoint");
  for (Operation *owner : inventory)
    if (failed(lowerBody(owner, functions.lookup(owner))))
      return failure();
  return success();
}

LogicalResult Lowering::lowerBody(Operation *owner, func::FuncOp function) {
  Region &region = owner->getRegion(0);
  if (region.empty())
    return refuse(owner, "external executable helpers are unsupported");
  // Failure edges are represented by immediate terminal EVM effects. Dispatch
  // therefore reaches only the actual success payload. Do not invent values
  // for failure successors or carry produced successor operands into CFGToSCF.
  SmallPtrSet<Block *, 32> reached;
  SmallVector<Block *> pending{&region.front()};
  while (!pending.empty()) {
    Block *block = pending.pop_back_val();
    if (!reached.insert(block).second)
      continue;
    Operation *term = block->getTerminator();
    if (term->getName().getStringRef() == "exec.dispatch")
      pending.push_back(term->getSuccessor(0));
    else
      append_range(pending, term->getSuccessors());
  }
  ValueMap map;
  llvm::DenseMap<Block *, Block *> blocks;
  for (Block &old : region) {
    if (!reached.contains(&old))
      continue;
    auto *block = new Block;
    function.getBody().push_back(block);
    blocks[&old] = block;
    for (BlockArgument arg : old.getArguments()) {
      auto convertedTypes = converted(TypeRange(arg.getType()), owner);
      if (failed(convertedTypes))
        return failure();
      Values args;
      for (Type type : *convertedTypes)
        args.push_back(block->addArgument(type, arg.getLoc()));
      map[arg] = std::move(args);
    }
  }
  // Block layout need not be dominance order. Use the actual dominator tree.
  DominanceInfo dominance;
  SmallVector<Block *> ordered;
  if (llvm::hasSingleElement(region))
    ordered.push_back(&region.front());
  else
    for (auto *node : depth_first(dominance.getRootNode(&region)))
      ordered.push_back(node->getBlock());
  for (Block *old : ordered) {
    if (!reached.contains(old))
      continue;
    builder.setInsertionPointToEnd(blocks.lookup(old));
    for (Operation &op : *old)
      if (failed(lowerOperation(&op, map, blocks)))
        return failure();
  }
  return success();
}

std::optional<LogicalResult>
Lowering::lowerScalar(Operation *op, StringRef code, ValueRange operands,
                      ArrayAttr parameters, ValueMap &map) {
  Location loc = op->getLoc();
  if (code == "field.constant") {
    auto literal = parameters && parameters.size() == 1
                       ? dyn_cast<algebra::FieldLiteralAttr>(parameters[0])
                       : algebra::FieldLiteralAttr();
    if (!literal || literal.getField().getDomain() != field)
      return refuse(op, "field.constant requires an admitted Fr literal");
    return bind(op,
                {constant(loc, builder.getIntegerType(256),
                          literal.getValue().getValue().zextOrTrunc(256))},
                map);
  }
  if (code == "field.equal")
    return bind(op,
                {arith::CmpIOp::create(builder, loc, arith::CmpIPredicate::eq,
                                       operands[0], operands[1])},
                map);
  if (code == "field.add" || code == "field.sub" || code == "field.mul" ||
      code == "field.neg") {
    Value a = operands[0], b, p = prime(loc);
    if (code == "field.neg") {
      b = arith::SubIOp::create(builder, loc, p, a);
      a = integer(loc, 0, 256);
    } else {
      b = operands[1];
      if (code == "field.sub")
        b = arith::SubIOp::create(builder, loc, p, b);
    }
    return bind(
        op,
        {WordOp::create(builder, loc, code == "field.mul" ? "mulmod" : "addmod",
                        a, b, p)
             ->getResult(0)},
        map);
  }
  if (code == "field.inverse" || code == "field.pow" || code == "field.div")
    return bind(op, checkedResult(op, code, operands), map);
  if (code == "bool.and")
    return bind(op,
                {arith::AndIOp::create(builder, loc, operands[0], operands[1])},
                map);
  if (code == "bool.or")
    return bind(op,
                {arith::OrIOp::create(builder, loc, operands[0], operands[1])},
                map);
  if (code == "bool.xor")
    return bind(op,
                {arith::XOrIOp::create(builder, loc, operands[0], operands[1])},
                map);
  if (code == "bool.not")
    return bind(
        op,
        {arith::XOrIOp::create(builder, loc, operands[0], integer(loc, 1, 1))},
        map);
  return std::nullopt;
}

LogicalResult Lowering::lowerBinding(Operation *op, ValueMap &map) {
  Operation *binding = resolve(op, "binding");
  if (!binding)
    return refuse(op, "missing checked runtime binding");
  auto admitted = readNativeBinding([&] { return op->emitOpError(); }, binding);
  if (failed(admitted))
    return refuse(op, "invalid checked runtime binding");
  if (!admitted->declaration.getImplementation().empty())
    return refuse(op, "EVM cannot honor a pinned runtime implementation");
  auto contract =
      binding ? binding->getAttrOfType<StringAttr>("contract") : StringAttr();
  if (!contract)
    return refuse(op, "missing checked runtime binding");
  StringRef name = contract.getValue();
  Values operands = get(op->getOperands().drop_front(), map);
  active(op, map.lookup(op->getOperand(0))[0]);
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  auto resultTypes = converted(op->getResultTypes(), op);
  if (failed(resultTypes))
    return failure();
  if (auto scalar = lowerScalar(op, name, operands, parameters, map))
    return *scalar;
  if (name == "index.constant") {
    if (!parameters || parameters.size() != 1 ||
        !isa<IntegerAttr>(parameters[0]))
      return refuse(op, "index.constant requires an exact u64 parameter");
    return bind(
        op, {integer(op->getLoc(), cast<IntegerAttr>(parameters[0]).getUInt())},
        map);
  }
  if (name == "index.equal" || name == "index.less") {
    auto predicate = name == "index.less" ? arith::CmpIPredicate::ult
                                          : arith::CmpIPredicate::eq;
    return bind(op,
                {arith::CmpIOp::create(builder, op->getLoc(), predicate,
                                       operands[0], operands[1])},
                map);
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
    auto encoded = protocol::encodeNativeOriginTemplate(*neutral);
    if (!encoded) {
      consumeError(encoded.takeError());
      return refuse(op, "invalid encoded occurrence template");
    }
    Values args{map.lookup(op->getOperand(0))[0]};
    append_range(args, operands);
    return bind(
        op,
        checked(
            op, observe ? "transcript.observe" : "transcript.challenge",
            *resultTypes, args,
            {builder.getNamedAttr("origin", builder.getStringAttr(*encoded))}),
        map);
  }
  if (!isCheckedOpcode(name))
    return refuse(op, ("unsupported runtime contract: " + name).str());
  return bind(op, checked(op, name, *resultTypes, operands), map);
}

LogicalResult Lowering::lowerLoop(Operation *op, ValueMap &map) {
  auto carried = op->getAttrOfType<IntegerAttr>("carried");
  auto maximum = op->getAttrOfType<IntegerAttr>("maximum");
  auto parameter = op->getAttrOfType<BoolAttr>("parameter");
  if (!carried || !maximum || maximum.getInt() < 0 || !parameter ||
      parameter.getValue() || op->getNumOperands() < 1 ||
      static_cast<uint64_t>(maximum.getInt()) > options.limits.rounds)
    return refuse(op, "loop requires an admitted deployment maximum");
  Value count = map.lookup(op->getOperand(0))[0];
  checked(op, "loop.bound", {},
          {count, integer(op->getLoc(), maximum.getUInt())});
  Values initial = get(op->getOperands().slice(1, carried.getUInt()), map);
  Value zero = integer(op->getLoc(), 0), one = integer(op->getLoc(), 1);
  auto loop =
      scf::ForOp::create(builder, op->getLoc(), zero, count, one, initial);
  loop.setUnsignedCmpAttr(builder.getUnitAttr());
  OpBuilder::InsertionGuard guard(builder);
  Block &body = op->getRegion(0).front();
  ValueMap nested = map;
  unsigned offset = 0;
  nested[body.getArgument(0)] = {loop.getInductionVar()};
  for (unsigned i = 0; i < carried.getUInt(); ++i) {
    unsigned n = map.lookup(op->getOperand(i + 1)).size();
    nested[body.getArgument(i + 1)] =
        Values(loop.getRegionIterArgs().slice(offset, n));
    offset += n;
  }
  for (unsigned i = carried.getUInt() + 1; i < body.getNumArguments(); ++i)
    nested[body.getArgument(i)] = map.lookup(op->getOperand(i));
  builder.setInsertionPointToStart(loop.getBody());
  for (Operation &child : body.without_terminator())
    if (failed(
            lowerOperation(&child, nested, llvm::DenseMap<Block *, Block *>())))
      return failure();
  builder.setInsertionPointToEnd(loop.getBody());
  if (!loop.getBody()->empty() && isa<scf::YieldOp>(loop.getBody()->back()))
    loop.getBody()->back().erase();
  scf::YieldOp::create(builder, op->getLoc(),
                       get(body.getTerminator()->getOperands(), nested));
  return bind(op, loop.getResults(), map);
}

LogicalResult Lowering::lowerFinite(Operation *op, ValueMap &map) {
  finite::Computation computation;
  if (failed(finite::describe(op, computation, nullptr, &symbols)))
    return refuse(op, "invalid checked finite computation");
  bool scoped = computation.scoped;
  bool fold = !computation.collect;
  if (computation.predicate)
    return refuse(op, "filtered finite domains are not supported");
  auto inputs = op->getOperands().drop_front(scoped ? 1 : 0);
  auto entry = finite::partitionEntry(computation, inputs);
  auto callback =
      finite::readCallbackABI(computation, fold ? finite::CallbackRole::Step
                                                : finite::CallbackRole::Body);
  if (failed(entry) || failed(callback))
    return refuse(op, "invalid checked finite callback ABI");
  if (scoped)
    active(op, map.lookup(op->getOperand(0))[0]);
  llvm::DenseMap<Value, SmallVector<Values>> domains;
  ValueMap env;
  Block &domainBody = computation.domain.getBody().front();
  for (auto [formal, actual] : zip(domainBody.getArguments(), entry->domain))
    env[formal] = map.lookup(actual);
  // The admitted domain body is also the eager admission sequence. Visit
  // every constructor, including descriptors unused by the yielded traversal.
  for (Operation &child : domainBody.without_terminator()) {
    if (isa<data::DomainElementsOp>(child)) {
      Values vector = env.lookup(child.getOperand(0));
      if (vector.size() != 2)
        return refuse(&child, "domain elements require a bounded vector");
      domains[child.getResult(0)] = {vector};
    } else if (isa<data::DomainZipOp>(child)) {
      SmallVector<Values> sequences;
      for (Value input : child.getOperands()) {
        auto found = domains.find(input);
        if (found == domains.end() || found->second.empty())
          return refuse(&child, "unresolved finite descriptor");
        if (!sequences.empty())
          checked(op, "range.check", {},
                  {sequences.front()[1], found->second.front()[1]});
        append_range(sequences, found->second);
      }
      domains[child.getResult(0)] = std::move(sequences);
    } else {
      return refuse(&child, "unsupported finite enumeration");
    }
  }
  auto sequences = domains.lookup(domainBody.getTerminator()->getOperand(0));
  if (sequences.empty())
    return refuse(op, "finite enumeration has no elements");
  Value count = sequences.front()[1];
  Values domainArguments = get(entry->domain, map);
  Values captures = get(entry->captures, map);
  Values state = get(entry->initialState, map);
  Value vector;
  if (!fold) {
    vector = checked(op, "vector.alloc", {builder.getI64Type()}, {count})[0];
  }
  auto loop =
      scf::ForOp::create(builder, op->getLoc(), integer(op->getLoc(), 0), count,
                         integer(op->getLoc(), 1), state);
  loop.setUnsignedCmpAttr(builder.getUnitAttr());
  {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(loop.getBody());
    Values args;
    if (scoped) {
      // Finite callbacks borrow their supplied scope, including its authority
      // over affine state. Unlike a local protocol call, a traversal does not
      // create a new execution scope for each item.
      args.push_back(map.lookup(op->getOperand(0))[0]);
    }
    if (fold)
      append_range(args, loop.getRegionIterArgs());
    for (auto &sequence : sequences) {
      auto element =
          checked(op, "vector.get", {builder.getIntegerType(256)},
                  {sequence[0], sequence[1], loop.getInductionVar()});
      append_range(args, element);
    }
    append_range(args, domainArguments);
    append_range(args, captures);
    auto result = call(op, callback->symbol, args);
    if (failed(result))
      return failure();
    if (fold) {
      if (result->size() != state.size())
        return refuse(op, "finite state result mismatch");
      if (isa<scf::YieldOp>(loop.getBody()->back()))
        loop.getBody()->back().erase();
      builder.setInsertionPointToEnd(loop.getBody());
      scf::YieldOp::create(builder, op->getLoc(), *result);
    } else {
      if (result->size() != 1 || !(*result)[0].getType().isInteger(256))
        return refuse(op, "collect requires one field result");
      checked(op, "vector.set", {},
              {vector, count, loop.getInductionVar(), (*result)[0]});
    }
  }
  return bind(op, fold ? Values(loop.getResults()) : Values{vector, count},
              map);
}

LogicalResult
Lowering::lowerOperation(Operation *op, ValueMap &map,
                         const llvm::DenseMap<Block *, Block *> &blocks) {
  StringRef name = op->getName().getStringRef();
  Location loc = op->getLoc();
  Values operands = get(op->getOperands(), map);
  if (name == "exec.apply")
    return lowerBinding(op, map);
  if (name == "exec.fold" || name == "exec.collect" ||
      name == "algebra.finite_fold" || name == "algebra.finite_collect")
    return lowerFinite(op, map);
  if (name == "protocol.loop")
    return lowerLoop(op, map);
  if (name == "func.return" || name == "protocol.finish") {
    func::ReturnOp::create(builder, loc, operands);
    return success();
  }
  if (name == "cf.br") {
    cf::BranchOp::create(builder, loc, blocks.lookup(op->getSuccessor(0)),
                         operands);
    return success();
  }
  if (auto branch = dyn_cast<cf::CondBranchOp>(op)) {
    cf::CondBranchOp::create(builder, loc, map.lookup(branch.getCondition())[0],
                             blocks.lookup(branch.getTrueDest()),
                             get(branch.getTrueDestOperands(), map),
                             blocks.lookup(branch.getFalseDest()),
                             get(branch.getFalseDestOperands(), map));
    return success();
  }
  if (name == "exec.dispatch") {
    // Admission checks produced success arguments precede explicit operands.
    auto sizes =
        op->getAttrOfType<DenseI32ArrayAttr>("successor_operand_segments");
    if (!sizes || sizes.size() != 2 || sizes[0] < 0)
      return refuse(op, "invalid checked outcome dispatch");
    Values args = map.lookup(op->getOperand(0));
    append_range(args, get(op->getOperands().slice(1, sizes[0]), map));
    cf::BranchOp::create(builder, loc, blocks.lookup(op->getSuccessor(0)),
                         args);
    return success();
  }
  if (name == "exec.returned")
    return bind(op, operands, map);
  if (name == "exec.complete" || name == "exec.test") {
    active(op, operands[0]);
    return bind(op, ValueRange(operands).drop_front(), map);
  }
  if (name == "exec.boolean") {
    active(op, operands[0]);
    auto value = op->getAttrOfType<BoolAttr>("value");
    return bind(op, {integer(loc, value.getValue(), 1)}, map);
  }
  if (name == "exec.reject") {
    active(op, operands[0]);
    checked(op, "source.stop", {}, {},
            {builder.getNamedAttr("site", op->getAttr("site"))});
    return bind(op, {integer(loc, 0)}, map);
  }
  if (name == "exec.failed") {
    // Only a directly rejecting block can still reach this operation; rejection
    // already emitted a nonreturning effect. Retain an explicit second terminal
    // effect rather than manufacturing a successful source outcome.
    checked(op, "source.stop", {}, {});
    auto results = converted(op->getResultTypes(), op);
    if (failed(results))
      return failure();
    Values inactive;
    for (Type type : *results)
      inactive.push_back(
          constant(loc, type, APInt(type.getIntOrFloatBitWidth(), 0)));
    return bind(op, inactive, map);
  }
  if (name == "exec.range") {
    active(op, operands[0]);
    checked(op, "range.admit", {}, ValueRange(operands).drop_front());
    return bind(op, ValueRange(operands).drop_front(), map);
  }
  if (name == "runtime.iteration") {
    active(op, operands[0]);
    return bind(op, {operands[1]}, map);
  }
  if (name == "runtime.enter_scope") {
    Value generation = integer(loc, UINT64_MAX);
    for (Value value : op->getOperands())
      if (isa<runtime::CapabilityType>(value.getType()))
        generation = map.lookup(value)[0];
    return bind(op, checkedResult(op, "scope.enter", {operands[0], generation}),
                map);
  }
  if (name == "runtime.exit_scope") {
    // Exit produces one affine ticket followed by actual outcome payload.
    Value generation = integer(loc, UINT64_MAX);
    auto outcome = cast<exec::OutcomeType>(op->getOperand(1).getType());
    unsigned offset = 1;
    for (Type type : outcome.getPayload()) {
      if (isa<runtime::CapabilityType>(type))
        generation = operands[offset];
      auto convertedTypes = converted(TypeRange(type), op);
      if (failed(convertedTypes))
        return failure();
      offset += convertedTypes->size();
    }
    auto ticket = checked(op, "scope.exit", {builder.getI64Type()},
                          {operands[0], generation});
    append_range(ticket, ValueRange(operands).drop_front());
    return bind(op, ticket, map);
  }
  if (name == "runtime.borrow_transfer") {
    auto ticket =
        checked(op, "transfer.make", {builder.getI64Type()}, {operands[0]});
    append_range(ticket, ValueRange(operands).drop_front());
    return bind(op, ticket, map);
  }
  if (name == "runtime.accept_transfer") {
    checked(op, "transfer.accept", {}, {operands[0], operands[1]});
    return bind(op, ValueRange(operands).drop_front(2), map);
  }
  if (name == "runtime.transfer_values") {
    checked(op, "transfer.check", {}, {operands[0]});
    return bind(op, ValueRange(operands).drop_front(), map);
  }
  if (name == "runtime.release_transfer") {
    checked(op, "transfer.release", {}, {operands[0]});
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
      Value generation = integer(loc, UINT64_MAX);
      for (Value value : op->getOperands())
        if (isa<runtime::CapabilityType>(value.getType()))
          generation = map.lookup(value)[0];
      Value parent =
          checked(op, "scope.current", {builder.getI64Type()}, {})[0];
      scope = checked(op, "scope.enter", {builder.getI64Type()},
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
        if (isa<runtime::CapabilityType>(type))
          generation = (*results)[offset];
        auto convertedTypes = converted(TypeRange(type), op);
        if (failed(convertedTypes))
          return failure();
        offset += convertedTypes->size();
      }
      checked(op, "scope.exit", {}, {scope, generation});
    }
    return bind(op, *results, map);
  }
  if (name == "protocol.receive") {
    if (op->getNumResults() != 1 ||
        !isa<algebra::FieldType>(op->getResult(0).getType()))
      return refuse(
          op, "proof receives currently require a supported scalar field");
    return bind(op, checkedResult(op, "proof.receive", {}), map);
  }
  if (name == "protocol.guard") {
    checked(op, "source.stop", {}, operands,
            {builder.getNamedAttr("site", op->getAttr("site"))});
    return success();
  }
  StringRef scalar = llvm::StringSwitch<StringRef>(name)
                         .Case("algebra.constant", "field.constant")
                         .Case("algebra.field_add", "field.add")
                         .Case("algebra.field_subtract", "field.sub")
                         .Case("algebra.field_multiply", "field.mul")
                         .Case("algebra.field_negate", "field.neg")
                         .Case("algebra.field_equal", "field.equal")
                         .Case("algebra.field_inverse", "field.inverse")
                         .Case("algebra.field_power", "field.pow")
                         .Case("algebra.field_divide", "field.div")
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
                            : builder.getArrayAttr({}),
                        map);
  if (name == "data.index") {
    auto literal = op->getAttrOfType<IntegerAttr>("value");
    return bind(op, {integer(loc, literal.getUInt())}, map);
  }
  if (name == "data.dim")
    return bind(op, {operands[1]}, map);
  if (name == "data.index_power_of_two") {
    return bind(op, checkedResult(op, "index.power_of_two", operands), map);
  }
  if (name == "data.index_equal" || name == "data.index_less")
    return bind(op,
                {arith::CmpIOp::create(builder, loc,
                                       name.ends_with("less")
                                           ? arith::CmpIPredicate::ult
                                           : arith::CmpIPredicate::eq,
                                       operands[0], operands[1])},
                map);
  if (name.starts_with("data.index_")) {
    auto opcode =
        llvm::StringSwitch<StringRef>(name)
            .Case("data.index_add", "index.add")
            .Case("data.index_subtract", "index.sub")
            .Case("data.index_multiply", "index.mul")
            .Case("data.index_divide", "index.div")
            .Case("data.index_modulo", "index.mod")
            .Case("data.index_wrapping_add", "index.wrapping_add")
            .Case("data.index_wrapping_subtract", "index.wrapping_sub")
            .Case("data.index_bit_and", "index.bit_and")
            .Case("data.index_logical_shift_right", "index.logical_shift_right")
            .Default("");
    if (!opcode.empty())
      return bind(op, checkedResult(op, opcode, operands), map);
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
        return bind(op, operands, map);
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
      return bind(op, {casted}, map);
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
    return bind(op, builder.create(state)->getResults(), map);
  }
  return refuse(op, "no EVM realization for this reachable operation");
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
      scf::IndexSwitchOp, WordOp, CheckedOp>(legalTypes);
  RewritePatternSet patterns(module.getContext());
  if (failed(applyFullConversion(module, target, std::move(patterns)))) {
    module.emitError(
        "[evm.target-legality] residual unsupported operation or type");
    return failure();
  }
  return success();
}

Expected<OwningOpRef<ModuleOp>> lowerEndpoint(const CheckedEndpoint &endpoint,
                                              const EvmOptions &options) {
  auto source = endpoint.sourceSnapshot();
  auto candidate = endpoint.candidateSnapshot();
  if (auto error = checkEndpointClosure(*source, *candidate, endpoint.role()))
    return std::move(error);
  auto *context = candidate->getContext();
  context->getOrLoadDialect<EvmDialect>();
  context->getOrLoadDialect<scf::SCFDialect>();
  context->getOrLoadDialect<arith::ArithDialect>();
  context->getOrLoadDialect<cf::ControlFlowDialect>();
  context->getOrLoadDialect<func::FuncDialect>();
  OwningOpRef<ModuleOp> target(ModuleOp::create(candidate->getLoc()));
  Lowering lowering(*candidate, *source, *target, options);
  if (failed(lowering.run()) || failed(verify(*target)))
    return zkc::error("evm.lowering", "EVM operation realization failed");
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
