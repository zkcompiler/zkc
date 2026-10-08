#include "zkc/Transforms/Mathematical.h"
#include "MathematicalSupport.h"
#include "MathematicalValues.h"
#include "ProtocolApplications.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/CSE.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Relation.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
// Only already-admitted acyclic helpers enter here. Expand on the candidate
// copy, preserving the caller's snapshot and ordinary SSA use-def ownership.
LogicalResult inlineHelpers(Operation *program, unsigned &remaining,
                            uint64_t &indices, SymbolTableCollection &tables,
                            Operation *lookupRoot, uint64_t *work) {
  SmallVector<func::CallOp> pending;
  program->walk([&](func::CallOp call) { pending.push_back(call); });
  while (!pending.empty()) {
    auto call = pending.pop_back_val();
    auto helper = lookupRoot ? tables.lookupSymbolIn<func::FuncOp>(
                                   lookupRoot, call.getCalleeAttr())
                             : tables.lookupNearestSymbolFrom<func::FuncOp>(
                                   call, call.getCalleeAttr());
    if (!helper || helper.isExternal())
      return diagnostics::emit(call.emitError(), "mathematical-helper",
                               "expected a helper body");
    IRMapping mapping;
    for (auto [arg, input] : zip(helper.getArguments(), call.getOperands()))
      mapping.map(arg, input);
    OpBuilder builder(call);
    for (auto &op : helper.front().without_terminator()) {
      if (!remaining)
        return diagnostics::emit(call.emitError(),
                                 "mathematical-expansion-limit");
      --remaining;
      uint64_t slots = op.getNumOperands() + op.getNumResults();
      if (slots > indices)
        return diagnostics::emit(call.emitError(),
                                 "mathematical-expansion-limit");
      if (work && slots + 1 > *work)
        return diagnostics::emit(call.emitError(),
                                 "mathematical-expansion-limit");
      indices -= slots;
      if (work)
        *work -= slots + 1;
      auto *copy = builder.clone(op, mapping);
      copy->setLoc(CallSiteLoc::get(op.getLoc(), call.getLoc()));
      if (auto nested = dyn_cast<func::CallOp>(copy))
        pending.push_back(nested);
    }
    for (auto [result, returned] :
         zip(call.getResults(), helper.front().back().getOperands()))
      result.replaceAllUsesWith(mapping.lookup(returned));
    call.erase();
  }
  return success();
}

namespace {
class Projector {
  OpBuilder builder;
  SymbolTableCollection sourceSymbols;
  Block *declarations;
  llvm::StringSet<> names;
  unsigned next = 0;
  Availability availability;
  unsigned captureWork = 1000000;
  bool captureFailure = false;
  std::string fresh() {
    std::string value;
    do {
      value = "_math_" + std::to_string(next++);
    } while (!names.insert(value).second);
    return value;
  }
  DictionaryAttr interface(zkc::protocol_ir::MathematicalOp program,
                           unsigned role,
                           zkc::protocol_ir::ParticipantOp target) {
    auto roleName = program.getRoles()[role];
    SmallVector<Attribute> inputs, outputs, services;
    for (auto [i, roles] : enumerate(program.getInputRoles()))
      if (is_contained(cast<ArrayAttr>(roles), roleName)) {
        auto &ports = isa<zkc::protocol_ir::ServiceReferenceType>(
                          program.getFunctionType().getInput(i))
                          ? services
                          : inputs;
        ports.push_back(builder.getI64IntegerAttr(i));
      }
    for (auto [i, roles] : enumerate(program.getOutputRoles()))
      if (is_contained(cast<ArrayAttr>(roles), roleName))
        outputs.push_back(builder.getI64IntegerAttr(i));
    return builder.getDictionaryAttr(
        {builder.getNamedAttr(
             "participant",
             FlatSymbolRefAttr::get(builder.getContext(), target.getSymName())),
         builder.getNamedAttr("role", roleName),
         builder.getNamedAttr("inputs", builder.getArrayAttr(inputs)),
         builder.getNamedAttr("service_inputs", builder.getArrayAttr(services)),
         builder.getNamedAttr("outputs", builder.getArrayAttr(outputs))});
  }
  ArrayAttr actionBindings(Block &block, ArrayRef<Attribute> participants) {
    SmallVector<Attribute> actions;
    for (auto &op : block) {
      auto meaning = classify(&op);
      if (!meaning || (meaning->category != Category::Action &&
                       !isa<protocol_ir::RepeatOp>(op)))
        continue;
      SmallVector<Attribute> targets;
      for (auto participant : participants) {
        auto record = cast<DictionaryAttr>(participant);
        auto role = cast<StringAttr>(record.get("role"));
        StringRef operation;
        if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
          if (is_contained(repeat.getRoles(), role))
            operation = protocol_ir::ProtocolLoopOp::getOperationName();
        } else if (auto exchange = dyn_cast<zkc::protocol_ir::ExchangeOp>(op)) {
          if (exchange.getSenderAttr() == role)
            operation = zkc::protocol_ir::EmitOp::getOperationName();
          else if (exchange.getReceiverAttr() == role)
            operation = zkc::protocol_ir::AwaitOp::getOperationName();
        } else if (isa<zkc::protocol_ir::LocalCallOp>(op)) {
          if (op.getAttr("role") == role)
            operation = zkc::local::CallOp::getOperationName();
        } else if (op.getAttr("owner") == role) {
          operation =
              isa<protocol_ir::FinishIfOp>(op)
                  ? protocol_ir::FinishIfOp::getOperationName()
              : isa<zkc::protocol_ir::GuardOp>(op)
                  ? zkc::local::GuardOp::getOperationName()
                  : zkc::protocol_ir::ParticipantQueryOp::getOperationName();
        }
        if (!operation.empty())
          targets.push_back(builder.getDictionaryAttr(
              {builder.getNamedAttr("participant", record.get("participant")),
               builder.getNamedAttr("operation",
                                    builder.getStringAttr(operation))}));
      }
      NamedAttrList action;
      action.set("site", op.getAttr("site"));
      action.set("kind", builder.getStringAttr(op.getName().getStringRef()));
      action.set("targets", builder.getArrayAttr(targets));
      if (isa<zkc::protocol_ir::LocalCallOp>(op))
        action.set("callee", op.getAttr("callee"));
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
        action.set("maximum", repeat.getMaximumAttr());
        action.set("body",
                   actionBindings(repeat.getBody().front(), participants));
      }
      actions.push_back(action.getDictionary(builder.getContext()));
    }
    return builder.getArrayAttr(actions);
  }
  struct Captures {
    SmallVector<unsigned> carried;
    llvm::SetVector<Value> leaves;
    llvm::SetVector<Operation *> recipes;
    SmallVector<std::pair<Value, Value>> values, services;
  };
  void captureLeaves(Value value, Captures &plan) {
    SmallVector<Value> pending{value};
    while (!pending.empty()) {
      Value current = pending.pop_back_val();
      if (!captureWork) {
        captureFailure = true;
        return;
      }
      --captureWork;
      auto *op = current.getDefiningOp();
      if (op && isTotal(op)) {
        if (plan.recipes.insert(op))
          llvm::append_range(pending, op->getOperands());
      } else {
        plan.leaves.insert(current);
      }
    }
  }
  Captures captures(protocol_ir::RepeatOp repeat, unsigned role) {
    Captures plan;
    auto &inner = repeat.getBody().front();
    for (auto [index, input] : enumerate(repeat.getInputs().drop_front())) {
      auto argument = inner.getArgument(index + 1);
      if (!availability.values.lookup(argument).test(role))
        continue;
      if (index < repeat.getNumResults()) {
        plan.carried.push_back(index);
      } else if (isa<protocol_ir::ServiceReferenceType>(input.getType())) {
        plan.services.emplace_back(argument, input);
      } else {
        plan.values.emplace_back(argument, input);
        captureLeaves(input, plan);
      }
    }
    return plan;
  }
  LogicalResult
  projectBlock(Block &source, Block &body, StringAttr roleName, unsigned role,
               ArrayRef<Value> outputs, IRMapping &mapping,
               const llvm::DenseMap<Value, std::string> &serviceNames) {
    // Backward demand is role-specific; only total math is recursively sliced.
    // Every owned action is a root even if none of its results is demanded.
    llvm::DenseSet<Value> demand;
    SmallVector<Value> pending(outputs.begin(), outputs.end());
    for (auto &op : source) {
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
        if (is_contained(repeat.getRoles(), roleName)) {
          auto plan = captures(repeat, role);
          if (captureFailure)
            return diagnostics::emit(repeat.emitError(),
                                     "mathematical-projection-limit",
                                     "capture slicing exceeds its work budget");
          pending.push_back(repeat.getInputs()[0]);
          for (unsigned index : plan.carried)
            pending.push_back(repeat.getInputs()[index + 1]);
          llvm::append_range(pending, plan.leaves);
        }
      }
      if (auto message = dyn_cast<zkc::protocol_ir::ExchangeOp>(op))
        if (message.getSenderAttr() == roleName)
          pending.push_back(message.getInput());
      if (auto guard = dyn_cast<zkc::protocol_ir::GuardOp>(op))
        if (guard.getOwnerAttr() == roleName)
          pending.push_back(guard.getCondition());
      if (auto completion = dyn_cast<protocol_ir::FinishIfOp>(op))
        if (completion.getOwnerAttr() == roleName)
          append_range(pending, completion.getOperands());
      if (auto query = dyn_cast<zkc::protocol_ir::QueryOp>(op))
        if (query.getOwnerAttr() == roleName)
          llvm::append_range(pending, query.getInputs());
      if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op))
        if (call.getRoleAttr() == roleName)
          llvm::append_range(pending, call.getInputs());
    }
    while (!pending.empty()) {
      Value value = pending.pop_back_val();
      if (!demand.insert(value).second)
        continue;
      auto *op = value.getDefiningOp();
      if (!op)
        continue;
      if (isa_and_nonnull<protocol_ir::RestrictRolesOp>(op))
        pending.push_back(op->getOperand(0));
      if (isTotal(op)) {
        auto inputs =
            operandDependencies(op, cast<OpResult>(value).getResultNumber());
        if (failed(inputs))
          return failure();
        for (unsigned input : *inputs)
          pending.push_back(op->getOperand(input));
      }
      if (auto message = dyn_cast<zkc::protocol_ir::ExchangeOp>(op))
        if (message.getSenderAttr() == roleName)
          pending.push_back(message.getInput());
    }
    builder.setInsertionPointToEnd(&body);
    for (auto &op : source) {
      if (auto restriction = dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
        if (is_contained(restriction.getRoles(), roleName) &&
            mapping.contains(restriction.getInput()))
          mapping.map(restriction.getOutput(),
                      mapping.lookup(restriction.getInput()));
        continue;
      }
      if (isTotal(&op)) {
        if (llvm::any_of(op.getResults(),
                         [&](Value value) { return demand.count(value); })) {
          if (llvm::any_of(op.getOperands(), [&](Value value) {
                return !mapping.contains(value);
              })) {
            diagnostics::emit(op.emitError(), "mathematical-projection",
                              "unmapped demanded operand");
            return failure();
          }
          builder.clone(op, mapping);
        }
        continue;
      }
      if (isa<zkc::protocol_ir::StatementOp>(op))
        continue;
      builder.setInsertionPointToEnd(&body);
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
        if (!is_contained(repeat.getRoles(), roleName))
          continue;
        auto plan = captures(repeat, role);
        if (captureFailure)
          return diagnostics::emit(repeat.emitError(),
                                   "mathematical-projection-limit",
                                   "capture slicing exceeds its work budget");
        SmallVector<Value> arguments{mapping.lookup(repeat.getInputs()[0])};
        SmallVector<Type> results;
        SmallVector<Value> yielded;
        auto &inner = repeat.getBody().front();
        for (unsigned index : plan.carried) {
          arguments.push_back(mapping.lookup(repeat.getInputs()[index + 1]));
          results.push_back(repeat.getResult(index).getType());
          yielded.push_back(inner.back().getOperand(index));
        }
        for (Value leaf : plan.leaves) {
          if (!mapping.contains(leaf))
            return diagnostics::emit(repeat.emitError(),
                                     "mathematical-projection",
                                     "unmapped demanded capture");
          arguments.push_back(mapping.lookup(leaf));
        }
        auto loop = protocol_ir::ProtocolLoopOp::create(
            builder, op.getLoc(), results, arguments, repeat.getSite(),
            results.size(), "", false, repeat.getMaximumAttr());
        auto *targetBody = new Block();
        loop.getBody().push_back(targetBody);
        for (Value input : arguments)
          targetBody->addArgument(input.getType(), input.getLoc());
        IRMapping nested, recipes;
        nested.map(inner.getArgument(0), targetBody->getArgument(0));
        unsigned port = 1;
        for (unsigned index : plan.carried) {
          nested.map(inner.getArgument(index + 1),
                     targetBody->getArgument(port));
          mapping.map(repeat.getResult(index), loop.getResult(port - 1));
          ++port;
        }
        for (Value leaf : plan.leaves)
          recipes.map(leaf, targetBody->getArgument(port++));
        auto services = serviceNames;
        builder.setInsertionPointToEnd(targetBody);
        SmallVector<Operation *> ordered(plan.recipes.begin(),
                                         plan.recipes.end());
        llvm::sort(ordered, [](Operation *a, Operation *b) {
          return a->isBeforeInBlock(b);
        });
        for (Operation *recipe : ordered)
          builder.clone(*recipe, recipes);
        for (auto [argument, input] : plan.values)
          nested.map(argument, recipes.lookup(input));
        for (auto [argument, input] : plan.services)
          services[argument] = serviceNames.lookup(input);
        if (failed(projectBlock(inner, *targetBody, roleName, role, yielded,
                                nested, services)))
          return failure();
        builder.setInsertionPointToEnd(&body);
      } else if (auto exchange = dyn_cast<zkc::protocol_ir::ExchangeOp>(op)) {
        if (exchange.getSenderAttr() == roleName) {
          auto value = mapping.lookup(exchange.getInput());
          zkc::protocol_ir::EmitOp::create(
              builder, op.getLoc(), value, exchange.getSite(),
              exchange.getSite(), exchange.getReceiver());
          mapping.map(exchange.getOutput(), value);
        } else if (exchange.getReceiverAttr() == roleName) {
          auto receive = zkc::protocol_ir::AwaitOp::create(
              builder, op.getLoc(), exchange.getOutput().getType(),
              exchange.getSite(), exchange.getSite(), exchange.getSender());
          mapping.map(exchange.getOutput(), receive.getOutput());
        }
      } else if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op)) {
        if (call.getRoleAttr() != roleName)
          continue;
        SmallVector<Value> arguments;
        for (auto input : call.getInputs()) {
          if (!mapping.contains(input)) {
            diagnostics::emit(call.emitError(), "mathematical-projection",
                              "unmapped local operand");
            return failure();
          }
          arguments.push_back(mapping.lookup(input));
        }
        auto invocation = zkc::local::CallOp::create(
            builder, op.getLoc(), call.getResultTypes(), arguments,
            call.getCalleeAttr(), call.getSiteAttr());
        for (auto [old, value] :
             zip(call.getResults(), invocation.getResults()))
          mapping.map(old, value);
      } else if (auto query = dyn_cast<zkc::protocol_ir::QueryOp>(op)) {
        if (query.getOwnerAttr() != roleName)
          continue;
        SmallVector<Value> arguments;
        for (auto input : query.getInputs())
          arguments.push_back(mapping.lookup(input));
        auto action = zkc::protocol_ir::ParticipantQueryOp::create(
            builder, op.getLoc(), query.getResultTypes(), arguments,
            serviceNames.lookup(query.getReference()), query.getMethod(),
            query.getSite());
        for (auto [old, value] : zip(query.getOutputs(), action.getOutputs()))
          mapping.map(old, value);
      } else if (auto completion = dyn_cast<protocol_ir::FinishIfOp>(op)) {
        if (completion.getOwnerAttr() != roleName)
          continue;
        SmallVector<Value> inputs;
        for (Value input : completion.getOperands()) {
          if (!mapping.contains(input)) {
            diagnostics::emit(completion.emitError(), "mathematical-projection",
                              "unmapped completion operand");
            return failure();
          }
          inputs.push_back(mapping.lookup(input));
        }
        auto projected = protocol_ir::FinishIfOp::create(
            builder, op.getLoc(), completion.getResultTypes(), inputs.front(),
            ArrayRef(inputs).drop_front(), completion.getSite(),
            completion.getOwner());
        for (auto [source, target] :
             zip(completion.getResults(), projected.getResults()))
          mapping.map(source, target);
      } else if (auto guard = dyn_cast<zkc::protocol_ir::GuardOp>(op)) {
        if (guard.getOwnerAttr() != roleName)
          continue;
        zkc::local::GuardOp::create(builder, op.getLoc(),
                                    mapping.lookup(guard.getCondition()),
                                    guard.getSite());
      } else if (isa<zkc::protocol_ir::MathematicalReturnOp,
                     zkc::protocol_ir::ProtocolYieldOp>(op)) {
        SmallVector<Value> returned;
        for (auto value : outputs)
          returned.push_back(mapping.lookup(value));
        if (isa<protocol_ir::ProtocolYieldOp>(op))
          protocol_ir::ProtocolYieldOp::create(builder, op.getLoc(), returned);
        else
          protocol_ir::FinishOp::create(builder, op.getLoc(), returned);
      } else {
        return diagnostics::emit(op.emitOpError(), "mathematical-projection",
                                 "unprojectable prepared operation");
      }
    }
    return success();
  }
  zkc::protocol_ir::ParticipantOp
  participant(zkc::protocol_ir::MathematicalOp program, unsigned role) {
    auto &source = program.getBody().front();
    auto roleName = cast<StringAttr>(program.getRoles()[role]);
    SmallVector<Value> inputs, outputs;
    SmallVector<Type> inputTypes, outputTypes;
    SmallVector<Attribute> servicePorts;
    llvm::DenseMap<Value, std::string> serviceNames;
    unsigned inputIndex = 0;
    for (auto [arg, roles] :
         zip(source.getArguments(), program.getInputRoles()))
      if (is_contained(cast<ArrayAttr>(roles), roleName)) {
        if (auto reference = dyn_cast<zkc::protocol_ir::ServiceReferenceType>(
                arg.getType())) {
          auto port = "service_" + std::to_string(inputIndex);
          serviceNames[arg] = port;
          servicePorts.push_back(builder.getArrayAttr(
              {builder.getStringAttr(port),
               builder.getStringAttr(reference.getContract()),
               builder.getI64IntegerAttr(inputIndex)}));
        } else {
          inputs.push_back(arg);
          inputTypes.push_back(arg.getType());
        }
        ++inputIndex;
      }
    for (auto [value, roles] :
         zip(source.back().getOperands(), program.getOutputRoles()))
      if (is_contained(cast<ArrayAttr>(roles), roleName)) {
        outputs.push_back(value);
        outputTypes.push_back(value.getType());
      }
    builder.setInsertionPointToEnd(declarations);
    auto target = zkc::protocol_ir::ParticipantOp::create(
        builder, program.getLoc(), fresh(),
        builder.getFunctionType(inputTypes, outputTypes), program.getSymName(),
        roleName.getValue());
    if (!servicePorts.empty())
      target->setAttr("service_ports", builder.getArrayAttr(servicePorts));
    auto *body = new Block();
    target.getBody().push_back(body);
    IRMapping mapping;
    for (auto input : inputs)
      mapping.map(input, body->addArgument(input.getType(), input.getLoc()));

    if (failed(projectBlock(source, *body, roleName, role, outputs, mapping,
                            serviceNames)))
      return {};
    return target;
  }

public:
  explicit Projector(MLIRContext *context) : builder(context) {}
  OwningOpRef<ModuleOp> run(ModuleOp source) {
    auto common =
        cast<zkc::protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    // Bound the prospective role expansion before allocating participant bodies
    // or performing one dependency traversal per role. Preparation may already
    // have removed valid unused total work, so charge the current SSA graph.
    uint64_t remaining = 100000;
    for (auto program :
         common.getBody().front().getOps<zkc::protocol_ir::MathematicalOp>()) {
      uint64_t nodes = 1 + program.getFunctionType().getNumInputs() +
                       program.getFunctionType().getNumResults();
      program.getBody().walk([&](Operation *op) {
        nodes += 1 + op->getNumOperands() + op->getNumResults();
        for (auto &region : op->getRegions())
          for (auto &block : region)
            nodes += block.getNumArguments();
      });
      uint64_t work = uint64_t(program.getRoles().size()) * nodes;
      if (work > remaining) {
        diagnostics::emit(
            program.emitError(), "mathematical-projection-limit",
            "role expansion exceeds 100000 operation/port visits");
        return {};
      }
      remaining -= work;
    }
    OwningOpRef<ModuleOp> output(ModuleOp::create(source.getLoc()));
    output->getOperation()->setAttrs(source->getAttrs());
    builder.setInsertionPointToEnd(output->getBody());
    auto root = zkc::protocol_ir::ProtocolModuleOp::create(
        builder, source.getLoc(),
        zkc::protocol_ir::ProfileAttr::get(
            builder.getContext(), zkc::protocol_ir::Profile::Participant));
    declarations = new Block();
    root.getBody().push_back(declarations);
    builder.setInsertionPointToEnd(declarations);
    for (auto &op : common.getBody().front()) {
      if (auto symbol = SymbolTable::getSymbolName(&op))
        names.insert(symbol.getValue());
      if (isa<zkc::relation::DeclareOp, zkc::local::FuncOp,
              zkc::local::OperationBindingOp>(op))
        builder.clone(op);
    }
    SmallVector<Attribute> interfaces;
    for (auto program :
         common.getBody().front().getOps<zkc::protocol_ir::MathematicalOp>()) {
      if (failed(analyze(program, availability, sourceSymbols)))
        return {};
      SmallVector<Attribute> targets, participants;
      for (unsigned role = 0; role < program.getRoles().size(); ++role) {
        auto target = participant(program, role);
        if (!target)
          return {};
        participants.push_back(interface(program, role, target));
        targets.push_back(builder.getArrayAttr(
            {program.getRoles()[role],
             FlatSymbolRefAttr::get(builder.getContext(),
                                    target.getSymName())}));
      }
      interfaces.push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr("source",
                                builder.getStringAttr(program.getSymName())),
           builder.getNamedAttr("entry",
                                FlatSymbolRefAttr::get(builder.getContext(),
                                                       program.getSymName())),
           builder.getNamedAttr("original_type", program.getFunctionTypeAttr()),
           builder.getNamedAttr("roles", program.getRoles()),
           builder.getNamedAttr("input_roles", program.getInputRoles()),
           builder.getNamedAttr("output_roles", program.getOutputRoles()),
           builder.getNamedAttr("statements",
                                statementBindings(program, sourceSymbols)),
           builder.getNamedAttr("participants",
                                builder.getArrayAttr(participants)),
           builder.getNamedAttr(
               "actions",
               actionBindings(program.getBody().front(), participants))}));
      builder.setInsertionPointToEnd(declarations);
      zkc::protocol_ir::ProtocolEntryOp::create(builder, program.getLoc(),
                                                program.getSymName(),
                                                builder.getArrayAttr(targets));
    }
    builder.setInsertionPointToEnd(declarations);
    zkc::protocol_ir::ProjectionOp::create(builder, source.getLoc(),
                                           builder.getArrayAttr(interfaces),
                                           builder.getArrayAttr({}));
    return output;
  }
};
} // namespace

LogicalResult verifyNestedDegrees(Operation *root) {
  WalkResult result = root->walk([&](Block *block) {
    poly::Degrees degrees;
    return failed(poly::deriveDegrees(*block, degrees))
               ? WalkResult::interrupt()
               : WalkResult::advance();
  });
  return failure(result.wasInterrupted());
}
namespace {
LogicalResult checkHelperObservations(protocol_ir::ProtocolModuleOp unit,
                                      ArrayRef<StringRef> helpers,
                                      uint64_t &work) {
  SymbolTableCollection symbols;
  auto &table = symbols.getSymbolTable(unit);
  llvm::StringSet<> seen;
  unsigned remaining = std::min<uint64_t>(realizedHelperOperationLimit, work);
  uint64_t indices = std::min<uint64_t>(1000000, work);
  for (auto name : helpers) {
    if (!work)
      return diagnostics::emit(unit.emitError(),
                               "mathematical-expansion-limit");
    --work;
    auto helper = table.lookup<func::FuncOp>(name);
    if (!helper || helper.isExternal() || !seen.insert(name).second)
      return diagnostics::emit(unit.emitError(), "mathematical-helper",
                               "expected distinct pure helper bodies");
    auto traversal = helper.walk([&](Operation *op) {
      uint64_t slots = op->getNumOperands() + op->getNumResults();
      if (!remaining || slots > indices || slots + 1 > work) {
        diagnostics::emit(op->emitError(), "mathematical-expansion-limit");
        return WalkResult::interrupt();
      }
      --remaining;
      indices -= slots;
      work -= slots + 1;
      return WalkResult::advance();
    });
    if (traversal.wasInterrupted())
      return failure();
    // Detached copies use the immutable source symbol table explicitly.
    // Dependencies and unrelated protocol bodies are never cloned or edited.
    OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(helper->clone()));
    auto result =
        inlineHelpers(*scratch, remaining, indices, symbols, unit, &work);
    if (failed(result) || failed(verifyNestedDegrees(*scratch)))
      return failure();
  }
  return success();
}
} // namespace
LogicalResult verifyHelperObservations(ModuleOp original,
                                       ArrayRef<StringRef> helpers) {
  if (failed(verify(original)))
    return failure();
  if (!hasSingleElement(*original.getBody()))
    return diagnostics::emit(original.emitError(), "mathematical-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics::emit(original.emitError(), "mathematical-module");
  uint64_t work = 1000000;
  return checkHelperObservations(unit, helpers, work);
}
Error checkFormulaDefinitions(ModuleOp original, uint64_t &remaining) {
  if (!hasSingleElement(*original.getBody()))
    return error("target.admission", "expected one mathematical module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("target.admission", "expected mathematical protocol profile");
  SymbolTable table(unit);
  SmallVector<std::string> names;
  llvm::StringSet<> roots;
  for (auto &op : unit.getBody().front()) {
    if (!remaining)
      return error("source.limit", "formula admission work limit exceeded");
    --remaining;
    auto declaration = dyn_cast<relation::DeclareOp>(op);
    if (!declaration || declaration.getKind() != "zkc.language.formula/1")
      continue;
    auto name = relation::formulaSymbol(declaration.getKey());
    auto helper = table.lookup<func::FuncOp>(name);
    if (declaration.getKey() != declaration.getSymName() || !helper ||
        helper.isExternal() ||
        helper.getFunctionType() != declaration.getSignature() ||
        helper.getVisibility() != SymbolTable::Visibility::Private ||
        !roots.insert(name).second) {
      declaration.emitError("invalid formula helper binding");
      return error("target.admission", "invalid formula helper binding");
    }
    names.push_back(std::move(name));
  }
  if (names.empty())
    return Error::success();
  auto walk = unit.walk([&](Operation *op) {
    uint64_t work =
        1 + op->getNumOperands() + op->getNumResults() + op->getAttrs().size();
    if (work > remaining)
      return WalkResult::interrupt();
    remaining -= work;
    return WalkResult::advance();
  });
  if (walk.wasInterrupted())
    return error("source.limit", "formula symbol use work limit exceeded");
  auto uses = SymbolTable::getSymbolUses(&unit.getBody());
  if (!uses)
    return error("target.admission", "formula symbol uses cannot be resolved");
  for (const auto &use : *uses) {
    if (!remaining)
      return error("source.limit", "formula symbol use work limit exceeded");
    --remaining;
    if (roots.contains(use.getSymbolRef().getRootReference())) {
      use.getUser()->emitError(
          "specification predicate has executable references");
      return error("target.admission",
                   "specification predicate has executable references");
    }
  }
  SmallVector<StringRef> helpers;
  for (const auto &name : names)
    helpers.push_back(name);
  bool limited = false;
  ScopedDiagnosticHandler limits(original.getContext(), [&](Diagnostic
                                                                &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      limited |= refusal.code == "mathematical-expansion-limit";
    return failure(); // Keep the caller's diagnostic and source attribution.
  });
  if (failed(checkHelperObservations(unit, helpers, remaining)))
    return error(limited ? "source.limit" : "target.admission",
                 limited ? "predicate observation work limit exceeded"
                         : "predicate polynomial observation check failed");
  return Error::success();
}

LogicalResult simplifyCalculations(Operation *body) {
  // Required bounds must be checked before DCE can erase an invalid unused
  // observation. Helpers have been transparently expanded by preparation.
  if (failed(verifyNestedDegrees(body)))
    return failure();
  auto orderedActions = [&] {
    SmallVector<std::pair<Operation *, DictionaryAttr>> result;
    body->getRegion(0).walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (!isTotal(op) && !isa<protocol_ir::RestrictRolesOp>(op))
        result.emplace_back(op, op->getAttrDictionary());
    });
    return result;
  };
  auto actions = orderedActions();
  // Greedy folding and CSE both recurse. Check nested actions before either
  // runs, then compare the same ordered region traversal afterwards.
  for (auto [op, attributes] : actions)
    if (!op->hasTrait<OpTrait::IsTerminator>() &&
        !mightHaveEffect<MemoryEffects::Write>(op))
      return diagnostics::emit(op->emitOpError(),
                               "mathematical-action-effects");
  RewritePatternSet patterns(body->getContext());
  llvm::SmallDenseSet<OperationName> names;
  SmallVector<Operation *> worklist;
  // Select patterns only from the admitted primitive vocabulary present in
  // this body. Do not collect every pattern registered with this context.
  body->walk([&](Operation *op) {
    // Tensor container identity is part of the closed profile. Exclude these
    // operations from both upstream folders and canonicalization patterns.
    if (!isTotal(op) || op->getName().getDialectNamespace() == "tensor")
      return;
    worklist.push_back(op);
    if (names.insert(op->getName()).second)
      op->getName().getCanonicalizationPatterns(patterns, body->getContext());
  });
  FrozenRewritePatternSet frozen(std::move(patterns));
  GreedyRewriteConfig config;
  config.setStrictness(GreedyRewriteStrictness::ExistingOps);
  config.setScope(&body->getRegion(0));
  if (failed(applyOpPatternsGreedily(worklist, frozen, config))) {
    diagnostics::emit(body->emitError(), "mathematical-simplification-limit");
    return failure();
  }
  IRRewriter rewriter(body->getContext());
  DominanceInfo dominance(body);
  eliminateCommonSubExpressions(rewriter, dominance, body);
  if (actions != orderedActions())
    return diagnostics::emit(body->emitOpError(), "mathematical-action-effects",
                             "simplification changed ordered actions");
  return success();
}

namespace {
// Admit the original whole unit before expanding or erasing anything. Every
// rewrite is confined to mathematical protocol bodies on an owned candidate;
// executable local definitions will not be traversed by this optimization.
OwningOpRef<ModuleOp> prepare(ModuleOp source, bool simplify = true) {
  if (failed(verify(source)))
    return {};
  if (!llvm::hasSingleElement(*source.getBody())) {
    diagnostics::emit(source.emitError(), "mathematical-module",
                      "expected one common mathematical module");
    return {};
  }
  auto common =
      dyn_cast<zkc::protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!common || common.getProfile() != zkc::protocol_ir::Profile::Protocol ||
      source->hasAttr("pir.mathematical_interfaces")) {
    diagnostics::emit(source.emitError(), "mathematical-module",
                      "expected the 'protocol' profile without preexisting "
                      "projection metadata");
    return {};
  }
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  if (failed(expandPolynomialRecipes(*candidate)) ||
      failed(expandMathRealizations(*candidate)))
    return {};
  // Algorithm expansion either leaves admitted IR untouched or returns a
  // verified candidate; static application analysis relies on that contract.
  if (failed(zkc::protocol::expandAlgorithms(*candidate)))
    return {};
  auto unit =
      cast<zkc::protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  OwningOpRef<protocol_ir::ProtocolModuleOp> beforeApplications(
      cast<protocol_ir::ProtocolModuleOp>(unit->clone()));
  if (failed(expandApplications(unit)) || failed(verify(*candidate)) ||
      failed(verifyPreparedValues(*beforeApplications, unit)))
    return {};
  OwningOpRef<protocol_ir::ProtocolModuleOp> expanded(
      cast<protocol_ir::ProtocolModuleOp>(unit->clone()));
  // Freeze canonical local application expansion and realized math helpers
  // before participant rewriting. A realization's logical_origin names its
  // original pure helper; its recipes were checked before reaching this point.
  OwningOpRef<ModuleOp> frozenLocals(ModuleOp::create(unit.getLoc()));
  OpBuilder snapshotBuilder(frozenLocals->getBodyRegion());
  for (auto &op : unit.getBody().front())
    if (isa<zkc::local::FuncOp, zkc::local::OperationBindingOp>(op))
      snapshotBuilder.clone(op);
  unsigned remainingHelpers = realizedHelperOperationLimit;
  uint64_t helperIndices = 1000000;
  SymbolTableCollection helperSymbols;
  for (auto program :
       unit.getBody().front().getOps<zkc::protocol_ir::MathematicalOp>()) {
    if (failed(inlineHelpers(program, remainingHelpers, helperIndices,
                             helperSymbols)))
      return {};
    if (simplify ? failed(simplifyCalculations(program))
                 : failed(verifyNestedDegrees(program)))
      return {};
  }
  // Upstream folders/patterns are not profile admission. Refuse a candidate
  // that leaves the closed vocabulary instead of weakening that vocabulary.
  if (failed(verify(*candidate)) ||
      failed(verifyProtocolPreparationPreserved(*expanded, unit)) ||
      failed(verifyAuthoredLocalsPreserved(*frozenLocals, unit)))
    return {};
  return candidate;
}
struct PreparePass : PassWrapper<PreparePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PreparePass)
  PreparePass() = default;
  explicit PreparePass(bool value) { simplify = value; }
  PreparePass(const PreparePass &other) : PassWrapper(other) {}
  Option<bool> simplify{*this, "simplify",
                        llvm::cl::desc("Simplify after expansion"),
                        llvm::cl::init(true)};
  StringRef getArgument() const final { return "zkc-prepare-protocol"; }
  StringRef getDescription() const final {
    return "Admit mathematical definitions, expand pure helpers, and simplify "
           "their callers";
  }
  void runOnOperation() final {
    auto source = getOperation();
    auto candidate = prepare(source, simplify);
    if (!candidate)
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
struct SimplifyParticipantPass
    : PassWrapper<SimplifyParticipantPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SimplifyParticipantPass)
  StringRef getArgument() const final { return "zkc-simplify-participant"; }
  StringRef getDescription() const final {
    return "Simplify admitted total participant expressions while retaining "
           "actions and interfaces";
  }
  void runOnOperation() final {
    auto source = getOperation();
    if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
      return signalPassFailure();
    auto original =
        dyn_cast<zkc::protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    if (!original ||
        original.getProfile() != zkc::protocol_ir::Profile::Participant) {
      diagnostics::emit(source.emitError(),
                        "mathematical-simplification-profile",
                        "expected the 'participant' profile");
      return signalPassFailure();
    }
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
    auto unit =
        cast<zkc::protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    for (auto participant :
         unit.getBody().front().getOps<zkc::protocol_ir::ParticipantOp>())
      if (failed(simplifyCalculations(participant)))
        return signalPassFailure();
    if (failed(verify(*candidate)) ||
        failed(verifyProjectionPreserved(source, *candidate)))
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
struct ProjectPass : PassWrapper<ProjectPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(ProjectPass)
  ProjectPass() = default;
  explicit ProjectPass(bool value) { simplify = value; }
  ProjectPass(const ProjectPass &other) : PassWrapper(other) {}
  Option<bool> simplify{*this, "simplify",
                        llvm::cl::desc("Simplify before projection"),
                        llvm::cl::init(true)};
  StringRef getArgument() const final { return "zkc-project-protocol"; }
  StringRef getDescription() const final {
    return "Project total mathematics and ordered actions into participant "
           "programs";
  }
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<zkc::protocol_ir::ProtocolDialect, zkc::local::LocalDialect,
                    zkc::algebra::AlgebraDialect, func::FuncDialect>();
  }
  void runOnOperation() final {
    auto source = getOperation();
    auto candidate = prepare(source, simplify);
    if (!candidate)
      return signalPassFailure();
    // Retain the actual prepared subject, including its role restrictions.
    // Projection selects the permitted local component without mutating it.
    auto output = Projector(source.getContext()).run(*candidate);
    if (!output || failed(verify(*output)) ||
        failed(verifyAuthoredLocalsPreserved(&candidate->getBody()->front(),
                                             &output->getBody()->front())) ||
        failed(verifyProjectionPreserved(*candidate, *output)))
      return signalPassFailure();
    source->setAttrs(output->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(output->getBodyRegion());
  }
};
} // namespace
} // namespace zkc::mathematical

std::unique_ptr<mlir::Pass>
zkc::protocol::createProjectProtocolPass(bool simplify) {
  return std::make_unique<mathematical::ProjectPass>(simplify);
}

std::unique_ptr<mlir::Pass>
zkc::protocol::createPrepareProtocolPass(bool simplify) {
  return std::make_unique<mathematical::PreparePass>(simplify);
}

std::unique_ptr<mlir::Pass> zkc::protocol::createSimplifyParticipantPass() {
  return std::make_unique<mathematical::SimplifyParticipantPass>();
}
