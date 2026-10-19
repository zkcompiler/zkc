#include "Schedule.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
bool bridge(Operation *op, Type input, Type output) {
  return op && isa<UnrealizedConversionCastOp>(op) &&
         op->getNumOperands() == 1 && op->getNumResults() == 1 &&
         op->getOperand(0).getType() == input &&
         op->getResult(0).getType() == output && op->getAttrs().empty() &&
         !op->getNumRegions() && !op->getNumSuccessors();
}
bool admission(Operation *op, Value &bound) {
  if (!op || !isa<local::LocalForOp>(op) || op->getNumOperands() != 2 ||
      op->getNumResults() || op->getNumRegions() != 1 ||
      op->getNumSuccessors() || op->getOperand(0) != op->getOperand(1) ||
      !op->getOperand(0).getType().isUnsignedInteger(64) ||
      op->getAttrs().size() != 1 || !op->getAttrOfType<StringAttr>("site") ||
      !op->getRegion(0).hasOneBlock())
    return false;
  auto &body = op->getRegion(0).front();
  if (body.getNumArguments() != 1 ||
      !body.getArgument(0).getType().isUnsignedInteger(64) ||
      !hasSingleElement(body) || !isa<local::LocalYieldOp>(body.front()) ||
      body.front().getNumOperands() || body.front().getNumResults() ||
      body.front().getNumRegions() || body.front().getNumSuccessors() ||
      !body.front().getAttrs().empty())
    return false;
  bound = op->getOperand(0);
  return true;
}
// SCF admits lexical captures; this private profile requires every block to
// declare its entire frame. No outer SSA is available inside a loop/branch.
bool closed(Block &block, uint64_t &remaining, unsigned depth = 0,
            llvm::StringSet<> *sites = nullptr) {
  if (depth > 64)
    return false;
  if (block.getNumArguments() > remaining) {
    remaining = 0;
    return false;
  }
  remaining -= block.getNumArguments();
  llvm::DenseSet<Value> available(block.getArguments().begin(),
                                  block.getArguments().end());
  for (auto &op : block) {
    uint64_t cost = 1 + op.getNumOperands() + op.getNumResults();
    if (cost > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= cost;
    if (op.getNumSuccessors())
      return false;
    if (sites && op.hasAttr("site")) {
      auto site = op.getAttrOfType<StringAttr>("site");
      if (!site || site.getValue().empty() ||
          !sites->insert(site.getValue()).second)
        return false;
    }
    for (Value operand : op.getOperands())
      if (!available.contains(operand))
        return false;
    for (auto &region : op.getRegions()) {
      if (!region.hasOneBlock() ||
          !closed(region.front(), remaining, depth + 1, sites))
        return false;
    }
    for (Value result : op.getResults())
      available.insert(result);
  }
  return true;
}
func::FuncOp scheduledFunction(mlir::ModuleOp module) {
  // Inspect generic shape and attributes (including builtin properties) before
  // using generated region or function-type accessors on untrusted packets.
  if (!module || module->getNumRegions() != 1 || module->getNumOperands() ||
      module->getNumResults() || module->getNumSuccessors() ||
      !module->getAttrs().empty() || !module.getBodyRegion().hasOneBlock() ||
      module.getBody()->getNumArguments())
    return {};
  func::FuncOp function;
  llvm::StringSet<> names;
  uint64_t remaining = 1000000;
  for (auto &op : *module.getBody()) {
    if (!remaining)
      return {};
    --remaining;
    auto name = op.getAttrOfType<StringAttr>("sym_name");
    if (!name || name.getValue().empty() ||
        !names.insert(name.getValue()).second || op.getNumOperands() ||
        op.getNumResults() || op.getNumSuccessors())
      return {};
    if (auto fn = dyn_cast<func::FuncOp>(op)) {
      auto typeAttr = fn->getAttrOfType<TypeAttr>("function_type");
      auto type = typeAttr ? dyn_cast<FunctionType>(typeAttr.getValue())
                           : FunctionType();
      if (function || fn->getNumRegions() != 1 || !type ||
          !fn.getBody().hasOneBlock() || fn.front().empty() ||
          fn->getAttrs().size() != 3 ||
          !fn->getAttrOfType<ArrayAttr>("logical_origin"))
        return {};
      auto origin = fn->getAttrOfType<ArrayAttr>("logical_origin");
      if (origin.size() != 2 || origin[0] != name ||
          origin[1] != ArrayAttr::get(fn.getContext(), {}) ||
          fn.front().getArgumentTypes() != type.getInputs())
        return {};
      auto returned = dyn_cast<func::ReturnOp>(fn.front().back());
      if (!returned || returned.getOperandTypes() != type.getResults() ||
          returned->getNumResults() || returned->getNumRegions() ||
          !returned->getAttrs().empty())
        return {};
      function = fn;
    } else if (isa<local::OperationBindingOp>(op)) {
      auto contract = op.getAttrOfType<StringAttr>("contract");
      auto implementation = op.getAttrOfType<StringAttr>("implementation");
      auto arguments = op.getAttrOfType<ArrayAttr>("arguments");
      if (op.getNumRegions() || op.getAttrs().size() != 4 || !contract ||
          !implementation || !arguments)
        return {};
      if (arguments.size() > remaining)
        return {};
      remaining -= arguments.size();
      std::vector<std::string> values;
      for (auto argument : arguments) {
        auto value = dyn_cast<StringAttr>(argument);
        if (!value)
          return {};
        values.push_back(value.getValue().str());
      }
      if (auto error = protocol::checkBindingDeclaration(
              name.getValue(),
              {contract.getValue().str(), std::move(values),
               implementation.getValue().str()},
              false)) {
        consumeError(std::move(error));
        return {};
      }
    } else
      return {};
  }
  if (!function)
    return {};
  llvm::StringSet<> sites;
  // Bound depth, work and lexical closure before MLIR's recursive verifier.
  // The recipe reader and consumer may use generated casting accessors only
  // after ordinary operation, region, type and required-attribute admission.
  if (!closed(function.front(), remaining, 0, &sites) || failed(verify(module)))
    return {};
  return function;
}
void boundAdmission(OpBuilder &builder, Location loc, Value bound,
                    StringRef site) {
  auto loop = local::LocalForOp::create(builder, loc, TypeRange{},
                                        ValueRange{bound, bound}, site);
  auto *body = builder.createBlock(&loop.getBody(), loop.getBody().end(),
                                   TypeRange{bound.getType()}, {loc});
  builder.setInsertionPointToEnd(body);
  local::LocalYieldOp::create(builder, loc, ValueRange{});
  builder.setInsertionPointAfter(loop);
}
Value bitBridge(OpBuilder &builder, Location loc, Value input, Type output) {
  return UnrealizedConversionCastOp::create(builder, loc, TypeRange{output},
                                            ValueRange{input})
      .getResult(0);
}
// Producer only. The source recipe fragment is already admitted. Both later
// readers inspect the actual resulting packet, not these construction choices.
void scheduleLoop(local::LocalForOp old) {
  auto &body = old.getBody().front();
  auto end = dyn_cast<local::LocalYieldOp>(body.back());
  if (!end || (old.getNumOperands() == 2 && old.getNumResults() == 0 &&
               old.getOperand(0) == old.getOperand(1)))
    return;
  OpBuilder builder(old);
  auto loc = old.getLoc();
  auto index = builder.getI64Type();
  auto site = old.getSite();
  boundAdmission(builder, loc, old.getOperand(0),
                 (site + "_schedule_lower").str());
  boundAdmission(builder, loc, old.getOperand(1),
                 (site + "_schedule_upper").str());
  auto lower = bitBridge(builder, loc, old.getOperand(0), index);
  auto upper = bitBridge(builder, loc, old.getOperand(1), index);
  auto step = arith::ConstantIntOp::create(builder, loc, 1, 64);
  auto loop = scf::ForOp::create(
      builder, loc, lower, upper, step, old.getOperands().drop_front(2),
      [&](OpBuilder &inside, Location where, Value position,
          ValueRange carried) {
        IRMapping values;
        auto native =
            bitBridge(inside, where, position, old.getOperand(0).getType());
        values.map(body.getArgument(0), native);
        values.map(body.getArguments().drop_front(), carried);
        for (auto &op : body.without_terminator())
          inside.clone(op, values);
        SmallVector<Value> next;
        for (Value value : end.getOperands())
          next.push_back(values.lookup(value));
        scf::YieldOp::create(inside, where, next);
      },
      true);
  loop->setAttr("site", old.getSiteAttr());
  loop->setAttr("state_count", builder.getI64IntegerAttr(old.getNumResults()));
  old->replaceAllUsesWith(loop.getResults().take_front(old.getNumResults()));
  old.erase();
}
FailureOr<SmallVector<Value>> mapped(ValueRange operands, IRMapping &values) {
  SmallVector<Value> result;
  for (Value operand : operands) {
    auto value = values.lookupOrNull(operand);
    if (!value)
      return failure();
    result.push_back(value);
  }
  return result;
}
// Executable conversion consumes the actual SCF packet. Domain reasoning and
// source callbacks are deliberately absent from this consumer.
LogicalResult lowerBlock(Block &source, Block &target, IRMapping values,
                         uint64_t &remaining, bool scheduledBody = false) {
  OpBuilder builder(target.getParentOp()->getContext());
  auto *cursor = source.empty() ? nullptr : &source.front();
  if (scheduledBody)
    cursor = cursor->getNextNode();
  while (cursor) {
    builder.setInsertionPointToEnd(&target);
    auto *after = cursor;
    auto parsed = readScheduledLoop(after, remaining);
    if (failed(parsed))
      return failure();
    auto &packet = *parsed;
    if (packet) {
      auto inputs = mapped(packet->inputs, values);
      if (failed(inputs))
        return failure();
      auto loop = local::LocalForOp::create(
          builder, packet->loop.getLoc(),
          packet->loop.getResults().take_front(packet->states).getTypes(),
          *inputs, packet->loop->getAttrOfType<StringAttr>("site").getValue());
      SmallVector<Type> types;
      for (Value value : packet->arguments)
        types.push_back(value.getType());
      auto *body = builder.createBlock(
          &loop.getBody(), loop.getBody().end(), types,
          SmallVector<Location>(types.size(), loop.getLoc()));
      auto nested = values;
      nested.map(packet->arguments, body->getArguments());
      if (failed(lowerBlock(*packet->loop.getBody(), *body, nested, remaining,
                            true)))
        return failure();
      values.map(packet->loop.getResults().take_front(packet->states),
                 loop.getResults());
      cursor = after;
      continue;
    }
    auto *op = cursor;
    cursor = op->getNextNode();
    if (isa<scf::ForOp, UnrealizedConversionCastOp, arith::ConstantOp>(op))
      return failure(); // No partial packets or free representation bridges.
    auto inputs = mapped(op->getOperands(), values);
    if (failed(inputs))
      return failure();
    if (isa<func::ReturnOp, scf::YieldOp>(op)) {
      if (op->getNumResults() || op->getNumRegions() || !op->getAttrs().empty())
        return failure();
      if (isa<func::ReturnOp>(op))
        local::ReturnOp::create(builder, op->getLoc(), *inputs);
      else
        local::LocalYieldOp::create(builder, op->getLoc(), *inputs);
      continue;
    }
    auto *copy = builder.cloneWithoutRegions(*op, values);
    for (auto [a, b] : zip(op->getRegions(), copy->getRegions())) {
      if (!a.hasOneBlock())
        return failure();
      auto &block = a.front();
      auto *out = builder.createBlock(
          &b, b.end(), block.getArgumentTypes(),
          SmallVector<Location>(block.getNumArguments(), op->getLoc()));
      auto nested = values;
      nested.map(block.getArguments(), out->getArguments());
      if (failed(lowerBlock(block, *out, nested, remaining)))
        return failure();
    }
  }
  return success();
}
} // namespace
FailureOr<std::optional<ScheduledLoop>> readScheduledLoop(Operation *&cursor) {
  uint64_t remaining = 1000000;
  return readScheduledLoop(cursor, remaining);
}
FailureOr<std::optional<ScheduledLoop>> readScheduledLoop(Operation *&cursor,
                                                          uint64_t &remaining) {
  auto *first = cursor;
  Value lower, upper;
  if (!admission(first, lower))
    return std::optional<ScheduledLoop>{};
  auto *second = first->getNextNode();
  if (!admission(second, upper))
    return std::optional<ScheduledLoop>{};
  auto *lowerCast = second->getNextNode();
  auto ui64 = lower.getType();
  auto i64 = IntegerType::get(lower.getContext(), 64);
  if (!bridge(lowerCast, ui64, i64) || lowerCast->getOperand(0) != lower)
    return std::optional<ScheduledLoop>{};
  auto *upperCast = lowerCast->getNextNode();
  if (!bridge(upperCast, ui64, i64) || upperCast->getOperand(0) != upper)
    return std::optional<ScheduledLoop>{};
  auto *step = upperCast->getNextNode();
  auto constant = dyn_cast_or_null<arith::ConstantOp>(step);
  auto one =
      constant ? step->getAttrOfType<IntegerAttr>("value") : IntegerAttr();
  if (!one || step->getNumOperands() || step->getNumResults() != 1 ||
      step->getResult(0).getType() != i64 || step->getNumRegions() ||
      step->getNumSuccessors() || one.getType() != i64 || one.getValue() != 1 ||
      step->getAttrs().size() != 1 || !step->getResult(0).hasOneUse())
    return std::optional<ScheduledLoop>{};
  auto loop = dyn_cast_or_null<scf::ForOp>(step->getNextNode());
  if (!loop || loop->getNumOperands() < 3 || loop->getNumRegions() != 1 ||
      loop->getNumSuccessors() ||
      !loop->getAttrOfType<UnitAttr>("unsignedCmp") ||
      !loop.getRegion().hasOneBlock() ||
      loop.getLowerBound() != lowerCast->getResult(0) ||
      loop.getUpperBound() != upperCast->getResult(0) ||
      loop.getStep() != step->getResult(0) ||
      !lowerCast->getResult(0).hasOneUse() ||
      !upperCast->getResult(0).hasOneUse())
    return std::optional<ScheduledLoop>{};
  auto states = loop->getAttrOfType<IntegerAttr>("state_count");
  auto site = loop->getAttrOfType<StringAttr>("site");
  if (!states || !states.getType().isSignlessInteger(64) ||
      states.getValue().isNegative() ||
      states.getValue().ugt(loop.getNumResults()) || !site ||
      site.getValue().empty() || loop->getAttrs().size() != 3 ||
      first->getAttrOfType<StringAttr>("site").getValue() !=
          (site.getValue() + "_schedule_lower").str() ||
      second->getAttrOfType<StringAttr>("site").getValue() !=
          (site.getValue() + "_schedule_upper").str())
    return std::optional<ScheduledLoop>{};
  unsigned count = states.getValue().getZExtValue();
  auto &body = *loop.getBody();
  if (body.empty() || body.getNumArguments() != loop.getNumResults() + 1 ||
      body.getArgument(0).getType() != i64 ||
      loop.getInitArgs().getTypes() != loop.getResultTypes() ||
      ValueRange(body.getArguments().drop_front()).getTypes() !=
          loop.getResultTypes())
    return std::optional<ScheduledLoop>{};
  auto *induction = &body.front();
  if (!bridge(induction, i64, ui64) ||
      induction->getOperand(0) != body.getArgument(0) ||
      !body.getArgument(0).hasOneUse())
    return std::optional<ScheduledLoop>{};
  auto end = dyn_cast<scf::YieldOp>(body.back());
  if (!end || end->getNumResults() || end->getNumRegions() ||
      end->getNumSuccessors() || end->getAttrs().size() ||
      end.getNumOperands() != loop.getNumResults() ||
      end.getOperandTypes() != loop.getResultTypes())
    return std::optional<ScheduledLoop>{};
  for (unsigned i = count; i < loop.getNumResults(); ++i)
    if (!loop.getResult(i).use_empty() ||
        end.getOperand(i) != body.getArgument(i + 1))
      return std::optional<ScheduledLoop>{};
  uint64_t cost = 16 + 2 * uint64_t(loop.getNumOperands()) +
                  2 * uint64_t(loop.getNumResults());
  if (cost > remaining) {
    remaining = 0;
    return failure();
  }
  remaining -= cost;
  if (!closed(body, remaining)) {
    if (!remaining)
      return failure();
    return std::optional<ScheduledLoop>{};
  }
  ScheduledLoop result{
      loop, lower, upper, count, {induction->getResult(0)}, {lower, upper}};
  append_range(result.arguments, body.getArguments().drop_front());
  append_range(result.inputs, loop.getInitArgs());
  cursor = loop->getNextNode();
  return std::optional<ScheduledLoop>(std::move(result));
}
SmallVector<Value> traversalArguments(Block *block) {
  if (!block)
    return {};
  SmallVector<Value> result(block->getArguments());
  if (isa<scf::ForOp>(block->getParentOp()) && !block->empty() &&
      block->front().getNumResults() == 1 && !result.empty())
    result[0] = block->front().getResult(0);
  return result;
}
OwningOpRef<mlir::ModuleOp> scheduleEntry(mlir::ModuleOp source,
                                          uint64_t &remaining) {
  if (!source)
    return {};
  source.getContext()->getOrLoadDialect<scf::SCFDialect>();
  source.getContext()->getOrLoadDialect<arith::ArithDialect>();
  if (failed(verifyRecipeOutput(source)) || !chargeCopy(source, remaining))
    return {};
  auto walk = source.walk([&](local::LocalForOp loop) {
    uint64_t cost = 40 + 8 * uint64_t(loop.getNumOperands());
    if (cost > remaining)
      return WalkResult::interrupt();
    remaining -= cost;
    return WalkResult::advance();
  });
  if (walk.wasInterrupted())
    return {};
  auto owner = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(result->getBody(), result->getBody()->end());
  for (auto &op : owner.getBody().front()) {
    if (auto function = dyn_cast<local::FuncOp>(op)) {
      auto standard = func::FuncOp::create(builder, function.getLoc(),
                                           function.getSymName(),
                                           function.getFunctionType());
      standard->setAttr("logical_origin", function->getAttr("logical_origin"));
      IRMapping values;
      function.getBody().cloneInto(&standard.getBody(), values);
      auto returned = cast<local::ReturnOp>(standard.front().back());
      builder.setInsertionPoint(returned);
      func::ReturnOp::create(builder, returned.getLoc(),
                             returned.getOperands());
      returned.erase();
      SmallVector<local::LocalForOp> loops;
      standard.walk<WalkOrder::PostOrder>(
          [&](local::LocalForOp loop) { loops.push_back(loop); });
      for (auto loop : loops)
        scheduleLoop(loop);
      builder.setInsertionPointToEnd(result->getBody());
    } else
      builder.clone(op);
  }
  if (!scheduledFunction(*result))
    return {};
  return result;
}
OwningOpRef<mlir::ModuleOp> consumeSchedule(mlir::ModuleOp source,
                                            uint64_t &remaining) {
  auto function = scheduledFunction(source);
  if (!function || !chargeCopy(source, remaining))
    return {};
  OwningOpRef<mlir::ModuleOp> result(mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(result->getBody(), result->getBody()->end());
  auto owner = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(), protocol_ir::Profile::Exec);
  owner.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&owner.getBody().front());
  for (auto binding : source.getBody()->getOps<local::OperationBindingOp>())
    builder.clone(*binding.getOperation());
  auto output =
      local::FuncOp::create(builder, function.getLoc(), function.getSymName(),
                            function.getFunctionType());
  output->setAttr("logical_origin", function->getAttr("logical_origin"));
  auto *body = builder.createBlock(
      &output.getBody(), output.getBody().end(), function.getArgumentTypes(),
      SmallVector<Location>(function.getNumArguments(), function.getLoc()));
  IRMapping values;
  values.map(function.getArguments(), body->getArguments());
  if (failed(lowerBlock(function.front(), *body, values, remaining)) ||
      failed(verifyRecipeOutput(*result)))
    return {};
  return result;
}
// Independent structural reader: never invokes lowerBlock or scheduleLoop.
namespace {
class ScheduleReader {
  uint64_t remaining = 1000000;

public:
  bool block(Block &source, Block &target, IRMapping values,
             bool body = false) {
    auto *at = source.empty() ? nullptr : &source.front();
    auto *actual = target.empty() ? nullptr : &target.front();
    if (body)
      at = at->getNextNode();
    while (at) {
      if (!actual || !remaining)
        return false;
      --remaining;
      auto *next = at;
      auto parsed = readScheduledLoop(next, remaining);
      if (failed(parsed))
        return false;
      auto &packet = *parsed;
      if (packet) {
        auto loop = dyn_cast<local::LocalForOp>(actual);
        auto inputs = mapped(packet->inputs, values);
        if (!loop || failed(inputs) ||
            loop.getOperands() != ValueRange(*inputs) ||
            loop.getNumResults() != packet->states ||
            loop.getSiteAttr() != packet->loop->getAttr("site") ||
            loop.getResultTypes() != packet->loop.getResults()
                                         .take_front(packet->states)
                                         .getTypes() ||
            !loop.getBody().hasOneBlock())
          return false;
        auto &out = loop.getBody().front();
        if (ValueRange(packet->arguments).getTypes() != out.getArgumentTypes())
          return false;
        auto nested = values;
        nested.map(packet->arguments, out.getArguments());
        if (!block(*packet->loop.getBody(), out, nested, true))
          return false;
        values.map(packet->loop.getResults().take_front(packet->states),
                   loop.getResults());
        at = next;
        actual = actual->getNextNode();
        continue;
      }
      auto name = at->getName().getStringRef();
      if (isa<func::ReturnOp>(at))
        name = "local.return";
      else if (isa<scf::YieldOp>(at))
        name = "local.yield";
      if (isa<scf::ForOp, UnrealizedConversionCastOp, arith::ConstantOp>(at))
        return false;
      auto inputs = mapped(at->getOperands(), values);
      if (failed(inputs) || actual->getName().getStringRef() != name ||
          actual->getAttrDictionary() != at->getAttrDictionary() ||
          actual->getOperands() != ValueRange(*inputs) ||
          actual->getResultTypes() != at->getResultTypes() ||
          actual->getNumRegions() != at->getNumRegions())
        return false;
      for (auto [a, b] : zip(at->getRegions(), actual->getRegions())) {
        if (!a.hasOneBlock() || !b.hasOneBlock() ||
            a.front().getArgumentTypes() != b.front().getArgumentTypes())
          return false;
        auto nested = values;
        nested.map(a.front().getArguments(), b.front().getArguments());
        if (!block(a.front(), b.front(), nested))
          return false;
      }
      values.map(at->getResults(), actual->getResults());
      at = at->getNextNode();
      actual = actual->getNextNode();
    }
    return !actual;
  }
};
} // namespace
LogicalResult verifyScheduleLowering(mlir::ModuleOp schedule,
                                     mlir::ModuleOp candidate) {
  auto function = scheduledFunction(schedule);
  if (!function || failed(verifyRecipeOutput(candidate)))
    return failure();
  auto owner =
      cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  auto target = SymbolTable(owner).lookup<local::FuncOp>(function.getSymName());
  if (!target || target->getAttrDictionary() != function->getAttrDictionary() ||
      !target.getBody().hasOneBlock())
    return failure();
  auto before = schedule.getBody()->getOps<local::OperationBindingOp>();
  auto after = owner.getBody().front().getOps<local::OperationBindingOp>();
  if (std::distance(before.begin(), before.end()) !=
      std::distance(after.begin(), after.end()))
    return failure();
  for (auto [a, b] : zip(before, after))
    if (!OperationEquivalence::isEquivalentTo(
            a, b, OperationEquivalence::IgnoreLocations))
      return failure();
  unsigned functions = 0;
  for (auto &op : owner.getBody().front())
    if (isa<local::FuncOp>(op))
      ++functions;
    else if (!isa<local::OperationBindingOp>(op))
      return failure();
  IRMapping values;
  values.map(function.getArguments(), target.getArguments());
  return success(functions == 1 &&
                 ScheduleReader().block(function.front(),
                                        target.getBody().front(), values));
}
LogicalResult verifyEntrySchedule(ModuleOp source, mlir::ModuleOp schedule,
                                  StringRef callSite,
                                  MathematicalSelectionPolicy policy,
                                  finite::VerificationLimits limits,
                                  finite::VerificationResult *reported) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                     "numerical schedule differs"};
  auto function = scheduledFunction(schedule);
  auto entry = getEntry(source);
  auto finish = [&](bool valid) {
    if (valid)
      outcome = {finite::VerificationStatus::Verified, {}};
    else if (outcome.status == finite::VerificationStatus::Verified)
      outcome = {finite::VerificationStatus::Mismatch,
                 "numerical schedule results differ"};
    if (reported)
      *reported = outcome;
    return success(valid);
  };
  if (!function || !entry || function.getSymName() != entry.getSymName() ||
      function.getFunctionType() != entry.getFunctionType())
    return finish(false);
  SymbolTable symbols(schedule);
  llvm::DenseSet<Operation *> used;
  function.walk([&](Operation *op) {
    if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
      used.insert(symbols.lookup(ref.getValue()));
  });
  for (auto &op : *schedule.getBody())
    if (&op != function.getOperation() &&
        (!isa<local::OperationBindingOp>(op) || !used.contains(&op)))
      return finish(false);
  uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
  if (!chargeCopy(schedule, remaining))
    return finish(false);
  auto *cursor = &function.front().front();
  auto results =
      verifyKernelRecipes(entry, schedule, callSite, function.getArguments(),
                          cursor, remaining, bytes, policy, limits, outcome);
  auto returned = dyn_cast_or_null<func::ReturnOp>(cursor);
  return finish(succeeded(results) && returned && !returned->getNextNode() &&
                returned.getOperands() == ValueRange(*results));
}
} // namespace zkc::kernel
