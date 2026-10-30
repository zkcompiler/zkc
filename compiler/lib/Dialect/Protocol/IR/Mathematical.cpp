#include "zkc/Dialect/Mathematical.h"
#include "OracleAnalysis.h"
#include "ResourceOrigins.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", detail);
}
bool subset(BitVector lhs, const BitVector &rhs) {
  lhs.reset(rhs);
  return lhs.none();
}
bool name(StringRef value) {
  return !value.empty() && (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) { return isAlnum(c) || c == '_'; });
}
class Analysis {
  zkc::protocol_ir::MathematicalOp program;
  unsigned count;
  TotalClosure &helpers;
  SymbolTableCollection &symbols;
  unsigned &remaining;
  uint64_t &remainingAvailabilityWork;
  NativeTypePolicies &types;
  SmallVectorImpl<protocol_ir::RepeatOp> &originQueries;
  llvm::StringSet<> sites;
  LogicalResult chargeAvailability(Operation *op, uint64_t indices) {
    uint64_t words = (uint64_t(count) + 63) / 64;
    uint64_t work = indices * words;
    if (work > remainingAvailabilityWork)
      return diagnostics::emit(op->emitOpError(), "mathematical-analysis-limit",
                               "availability analysis exceeds 1000000 words");
    remainingAvailabilityWork -= work;
    return success();
  }
  std::optional<NativeTypePolicy> commonValuePolicy(Type type) {
    // Logical handles belong to the pre-realization protocol only. Native
    // endpoint/type policies continue rejecting them, including in messages.
    if (isa<protocol_ir::OracleHandleType, protocol_ir::OracleSequenceType>(
            type))
      return NativeTypePolicy{false, true, false, false, false, false};
    return types.get(type);
  }
  LogicalResult initialOracleShape(Value root, Operation *use) {
    return verifyInitialOracleShape(root, program, use, symbols, remaining);
  }
  LogicalResult helper(func::CallOp call, Availability &env) {
    const TotalSummary *summary;
    if (failed(helpers.get(call, summary)))
      return failure();
    if (summary->expandedOperations > remaining)
      return diagnostics::emit(call.emitOpError(),
                               "mathematical-analysis-limit",
                               "expanded analysis exceeds 100000 operations");
    remaining -= summary->expandedOperations;
    if (failed(chargeAvailability(call, summary->replayIndices +
                                            summary->requirements.size() +
                                            summary->results.size())))
      return failure();
    for (const auto &required : summary->requirements) {
      BitVector available(count, true);
      for (unsigned index : required)
        available &= env.values.lookup(call.getOperand(index));
      if (available.none())
        return refuse(call, "helper intermediate has no available component");
    }
    for (auto [result, dependencies] :
         zip(call.getResults(), summary->results)) {
      BitVector available(count, true);
      for (int index = dependencies.find_first(); index >= 0;
           index = dependencies.find_next(index))
        available &= env.values.lookup(call.getOperand(index));
      env.values[result] = std::move(available);
    }
    return success();
  }

public:
  Analysis(zkc::protocol_ir::MathematicalOp program, TotalClosure &helpers,
           unsigned &remaining, uint64_t &remainingAvailabilityWork,
           NativeTypePolicies &types, SymbolTableCollection &symbols,
           SmallVectorImpl<protocol_ir::RepeatOp> &originQueries)
      : program(program), count(program.getRoles().size()), helpers(helpers),
        symbols(symbols), remaining(remaining),
        remainingAvailabilityWork(remainingAvailabilityWork), types(types),
        originQueries(originQueries) {}
  int role(Attribute attribute) {
    auto found = llvm::find(program.getRoles(), attribute);
    return found == program.getRoles().end()
               ? -1
               : int(found - program.getRoles().begin());
  }
  LogicalResult roles(Operation *op, ArrayAttr declared, BitVector &result) {
    result = BitVector(count);
    if (!declared || declared.empty())
      return refuse(op, "role sets must be nonempty");
    for (auto attr : declared) {
      int r = role(attr);
      if (r < 0 || result.test(r))
        return refuse(op, "unknown or repeated role");
      result.set(r);
    }
    return success();
  }
  LogicalResult body(Block &block, Availability &env, unsigned depth = 0) {
    if (depth > 64)
      return refuse(block.getParentOp(), "repeat nesting exceeds 64");
    llvm::DenseSet<Value> consumed;
    for (auto &operation : block) {
      auto *op = &operation;
      if (!remaining--)
        return diagnostics::emit(op->emitOpError(),
                                 "mathematical-analysis-limit",
                                 "expanded analysis exceeds 100000 operations");
      // A nonrecursive enclosing verification must also check helper-local
      // invariants, without relying on an earlier recursive verification.
      if (failed(op->getName().verifyInvariants(op)))
        return failure();
      if (failed(verifyOperation(op, Context::Protocol)))
        return failure();
      if (failed(chargeAvailability(op, uint64_t(op->getNumOperands()) +
                                            op->getNumResults())))
        return failure();
      for (auto type : op->getResultTypes())
        if (!commonValuePolicy(type))
          return refuse(op, "unsupported mathematical data type");
      if (isTotal(op) && failed(verifyTotalTypes(op, types)))
        return failure();
      for (auto input : op->getOperands()) {
        auto policy = commonValuePolicy(input.getType());
        if (policy && policy->affine && !consumed.insert(input).second)
          return refuse(op, "affine component used more than once");
      }
      for (auto input : op->getOperands())
        if (isa<zkc::protocol_ir::ServiceReferenceType>(input.getType()) &&
            !isa<zkc::protocol_ir::QueryOp, zkc::protocol_ir::ApplyOp,
                 zkc::protocol_ir::RepeatOp>(op))
          return refuse(
              op, "service references are entry ports used only by queries");
      for (auto input : op->getOperands())
        if (!env.values.count(input) || env.values.lookup(input).none())
          return refuse(op, "operand has no available component");
      if (isa<zkc::protocol_ir::MathematicalReturnOp,
              zkc::protocol_ir::ProtocolYieldOp>(op)) {
        if (&block.back() != op ||
            (depth == 0) != isa<protocol_ir::MathematicalReturnOp>(op))
          return refuse(op, "wrong mathematical terminator");
        return success();
      }
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
        if (failed(repeat.verifyRegions()))
          return failure();
        if (!name(repeat.getSite()) || !sites.insert(repeat.getSite()).second)
          return refuse(op, "repeat sites must be unique identifiers");
        BitVector participants;
        if (failed(roles(op, repeat.getRoles(), participants)) ||
            !subset(participants, env.values.lookup(repeat.getInputs()[0])))
          return refuse(op,
                        "repeat count requires every participating component");
        auto &nested = repeat.getBody().front();
        env.values[nested.getArgument(0)] = participants;
        for (auto [index, input] : enumerate(repeat.getInputs().drop_front())) {
          auto argument = nested.getArgument(index + 1);
          auto reference =
              isa<protocol_ir::ServiceReferenceType>(input.getType());
          auto policy = commonValuePolicy(input.getType());
          BitVector available = env.values.lookup(input);
          if (index < repeat.getNumResults()) {
            if (reference)
              return refuse(op,
                            "service references must be immutable captures");
            BitVector declared;
            if (failed(roles(
                    op, dyn_cast<ArrayAttr>(repeat.getCarriedRoles()[index]),
                    declared)) ||
                !subset(declared, available) || !subset(declared, participants))
              return refuse(op,
                            "carried role invariant is unavailable at entry");
            if (!policy || (!policy->shared && declared.count() != 1))
              return refuse(op, "owner-local carried values need one owner");
            available = declared;
          } else {
            if (!reference && (!policy || policy->affine))
              return refuse(op, "affine values must be carried, not captured");
            available &= participants;
            if (available.none())
              return refuse(op, "capture has no participating component");
          }
          env.values[argument] = available;
        }
        // A constant in a body is mathematically available everywhere, but
        // cannot authorize an action by a role outside this segment.
        for (auto &action : nested) {
          ArrayAttr actionRoles;
          if (auto child = dyn_cast<protocol_ir::RepeatOp>(action))
            actionRoles = child.getRoles();
          else if (auto assembly =
                       dyn_cast<protocol_ir::AssembleRolesOp>(action))
            actionRoles = assembly.getRoles();
          else if (auto application = dyn_cast<protocol_ir::ApplyOp>(action))
            actionRoles = application.getRoles();
          else if (auto append =
                       dyn_cast<protocol_ir::OracleSequenceAppendOp>(action))
            actionRoles = append.getRoles();
          else if (auto at = dyn_cast<protocol_ir::OracleSequenceAtOp>(action))
            actionRoles = at.getRoles();
          else if (auto virtualOracle =
                       dyn_cast<protocol_ir::OracleVirtualOp>(action))
            actionRoles = virtualOracle.getReceivers();
          else if (auto input = dyn_cast<protocol_ir::OracleInputOp>(action))
            actionRoles = input.getReceivers();
          else if (auto components =
                       dyn_cast<protocol_ir::OracleComponentsOp>(action))
            actionRoles = components.getReceivers();
          else if (auto send = dyn_cast<protocol_ir::OracleSendOp>(action))
            actionRoles = send.getReceivers();
          else if (auto start =
                       dyn_cast<protocol_ir::ConstructionStartOp>(action))
            actionRoles = start.getRoles();
          if (actionRoles) {
            BitVector required;
            if (failed(roles(&action, actionRoles, required)) ||
                !subset(required, participants))
              return refuse(&action, "action adds a nonparticipating role");
          }
          for (StringRef key :
               {"owner", "sender", "receiver", "role", "holder"})
            if (auto owner = action.getAttrOfType<StringAttr>(key)) {
              int r = role(owner);
              if (r < 0 || !participants.test(r))
                return refuse(&action,
                              "action owner does not participate in repeat");
            }
        }
        if (failed(body(nested, env, depth + 1)))
          return failure();
        bool needsOrigin = false;
        for (auto [index, yielded] : enumerate(nested.back().getOperands())) {
          auto argument = nested.getArgument(index + 1);
          const auto &required = env.values.lookup(argument);
          if (!subset(required, env.values.lookup(yielded)))
            return refuse(op,
                          "yield does not preserve the carried role invariant");
          auto policy = commonValuePolicy(yielded.getType());
          needsOrigin |= policy && policy->affine;
          env.values[repeat.getResult(index)] = required;
        }
        if (needsOrigin)
          originQueries.push_back(repeat);
        continue;
      }
      if (isTotal(op)) {
        for (auto [index, output] : enumerate(op->getResults())) {
          BitVector available(count, true);
          auto inputs = operandDependencies(op, index);
          if (failed(inputs))
            return failure();
          for (unsigned input : *inputs)
            available &= env.values.lookup(op->getOperand(input));
          if (available.none())
            return refuse(op, "operation has no available component");
          env.values[output] = available;
        }
        continue;
      }
      if (auto application = dyn_cast<zkc::protocol_ir::ApplyOp>(op)) {
        if (failed(application.verifySymbolUses(symbols)) ||
            failed(
                verifyOracleApplicationPorts(application, symbols, remaining)))
          return failure();
        if (!name(application.getSite()) ||
            !sites.insert(application.getSite()).second)
          return refuse(op, "application sites must be unique identifiers");
        auto callee =
            symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
                application, application.getCalleeAttr());
        auto mapped = [&](Attribute set, BitVector &bits) -> LogicalResult {
          SmallVector<Attribute> names;
          for (auto item : cast<ArrayAttr>(set)) {
            auto found = llvm::find(callee.getRoles(), item);
            if (found == callee.getRoles().end())
              return refuse(op, "invalid callee role interface");
            names.push_back(
                application.getRoles()[found - callee.getRoles().begin()]);
          }
          return roles(op, ArrayAttr::get(op->getContext(), names), bits);
        };
        for (auto [input, owners] :
             zip(application.getInputs(), callee.getInputRoles())) {
          BitVector required;
          if (failed(mapped(owners, required)) ||
              !subset(required, env.values.lookup(input)))
            return refuse(op,
                          "application requires unavailable input components");
        }
        for (auto [output, owners] :
             zip(application.getOutputs(), callee.getOutputRoles()))
          if (failed(mapped(owners, env.values[output])))
            return failure();
        continue;
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        if (failed(helper(call, env)))
          return failure();
        continue;
      }
      if (auto assembly = dyn_cast<protocol_ir::AssembleRolesOp>(op)) {
        auto policy = types.get(assembly.getOutput().getType());
        if (!policy || !policy->shared || !policy->total || policy->affine)
          return refuse(op, "assembly requires ordinary total shared data");
        BitVector selected;
        if (failed(roles(op, assembly.getRoles(), selected)))
          return failure();
        for (auto [input, owner] :
             zip(assembly.getInputs(), assembly.getRoles()))
          if (!env.values.lookup(input).test(role(owner)))
            return refuse(op, "assembly requests an unavailable component");
        env.values[assembly.getOutput()] = std::move(selected);
      } else if (auto restrict =
                     dyn_cast<zkc::protocol_ir::RestrictRolesOp>(op)) {
        auto policy = commonValuePolicy(restrict.getInput().getType());
        if (!policy || !policy->shared)
          return refuse(op, "owner-local values cannot be restricted");
        BitVector selected;
        if (failed(roles(op, restrict.getRoles(), selected)))
          return failure();
        if (!subset(selected, env.values.lookup(restrict.getInput())))
          return refuse(op, "restriction requests an unavailable component");
        env.values[restrict.getOutput()] = std::move(selected);
      } else if (auto forget = dyn_cast<protocol_ir::OracleForgetShapeOp>(op)) {
        env.values[forget.getOutput()] = env.values.lookup(forget.getInput());
      } else if (auto input = dyn_cast<protocol_ir::OracleInputOp>(op)) {
        int holder = role(input.getHolderAttr());
        BitVector available;
        if (holder < 0 || failed(roles(op, input.getReceivers(), available)) ||
            available.test(holder) ||
            !subset(available, env.values.lookup(input.getAnchor())) ||
            !env.values.lookup(input.getData()).test(holder))
          return refuse(
              op, "oracle input requires its holder and receiver components");
        available.set(holder);
        if (failed(verifyOracleInputPair(input, symbols, remaining)))
          return failure();
        env.values[input.getHandle()] = std::move(available);
      } else if (auto components =
                     dyn_cast<protocol_ir::OracleComponentsOp>(op)) {
        int holder = role(components.getHolderAttr());
        BitVector receivers;
        if (holder < 0 ||
            failed(roles(op, components.getReceivers(), receivers)) ||
            receivers.test(holder) ||
            !subset(receivers, env.values.lookup(components.getHandle())) ||
            !env.values.lookup(components.getHandle()).test(holder) ||
            failed(verifyOracleHolder(components.getHandle(),
                                      components.getHolder(), op, remaining)))
          return refuse(
              op,
              "oracle component view requires its actual holder and receivers");
        BitVector data(count);
        data.set(holder);
        env.values[components.getData()] = std::move(data);
        env.values[components.getAnchor()] = std::move(receivers);
      } else if (auto rows = dyn_cast<protocol_ir::OracleShapeOp>(op)) {
        env.values[rows.getExtent()] = env.values.lookup(rows.getHandle());
      } else if (auto virtualOracle =
                     dyn_cast<protocol_ir::OracleVirtualOp>(op)) {
        auto declaration =
            symbols.lookupNearestSymbolFrom<protocol_ir::OracleDefinitionOp>(
                virtualOracle, virtualOracle.getCalleeAttr());
        int holder = role(virtualOracle.getHolderAttr());
        BitVector available;
        if (!declaration || failed(virtualOracle.verifySymbolUses(symbols)) ||
            holder < 0 ||
            failed(roles(op, virtualOracle.getReceivers(), available)) ||
            available.test(holder))
          return refuse(op, "virtual construction requires its holder and "
                            "distinct receivers");
        available.set(holder);
        for (auto [index, input] : enumerate(virtualOracle.getInputs())) {
          if (!subset(available, env.values.lookup(input)))
            return refuse(
                op, "virtual sources and parameters require every component");
          if (index < declaration.getNumSources() &&
              failed(verifyOracleHolder(input, virtualOracle.getHolder(), op,
                                        remaining)))
            return failure();
        }
        for (auto dimension : declaration.getShapeArguments()) {
          auto index =
              cast<IntegerAttr>(dimension.getValue()).getValue().getZExtValue();
          if (failed(initialOracleShape(virtualOracle.getInputs()[index], op)))
            return failure();
        }
        env.values[virtualOracle.getHandle()] = std::move(available);
      } else if (auto contents = dyn_cast<protocol_ir::OracleContentsOp>(op)) {
        int owner = role(contents.getOwnerAttr());
        if (owner < 0 || !env.values.lookup(contents.getHandle()).test(owner))
          return refuse(
              op, "oracle contents require an available holder component");
        if (failed(verifyOracleHolder(contents.getHandle(), contents.getOwner(),
                                      op, remaining)))
          return failure();
        BitVector available(count);
        available.set(owner);
        env.values[contents.getData()] = std::move(available);
      } else if (auto empty =
                     dyn_cast<protocol_ir::OracleSequenceEmptyOp>(op)) {
        env.values[empty.getOutput()] = BitVector(count, true);
      } else if (auto length =
                     dyn_cast<protocol_ir::OracleSequenceLengthOp>(op)) {
        env.values[length.getLength()] =
            env.values.lookup(length.getSequence());
      } else if (auto statement = dyn_cast<zkc::protocol_ir::StatementOp>(op)) {
        if (depth != 0)
          return refuse(
              op,
              "statement must bind protocol entry inputs outside iteration");
        if (statement.getSelectors().size() != statement.getNumOperands() ||
            statement.getAcceptance() < 0 ||
            size_t(statement.getAcceptance()) >=
                program.getFunctionType().getNumResults() ||
            !program.getFunctionType()
                 .getResult(statement.getAcceptance())
                 .isSignlessInteger(1))
          return refuse(op,
                        "statement selector or acceptance interface mismatch");
        for (auto [input, selector] :
             zip(statement.getInputs(), statement.getSelectors())) {
          auto arg = dyn_cast<BlockArgument>(input);
          if (isa<protocol_ir::OracleHandleType>(input.getType())) {
            if (!arg || arg.getOwner() != &program.getBody().front() ||
                !statement.getTargetAttr() ||
                selector != StringAttr::get(op->getContext(), "anchor"))
              return refuse(op, "logical statement anchor requires an owned "
                                "target and entry handle");
            continue;
          }
          int r = role(selector);
          if (!arg || arg.getOwner() != &program.getBody().front() || r < 0 ||
              !env.values.lookup(input).test(r))
            return refuse(op,
                          "statement must bind an available entry component");
        }
      } else if (isa<zkc::protocol_ir::ExchangeOp, zkc::protocol_ir::GuardOp,
                     zkc::protocol_ir::FinishIfOp, zkc::protocol_ir::QueryOp,
                     protocol_ir::OracleSendOp, protocol_ir::OracleQueryOp,
                     protocol_ir::OracleSequenceAppendOp,
                     protocol_ir::OracleSequenceAtOp,
                     zkc::protocol_ir::LocalCallOp,
                     zkc::protocol_ir::ConstructionStartOp>(op)) {
        auto site = op->getAttrOfType<StringAttr>("site");
        if (!site || !name(site.getValue()) ||
            !sites.insert(site.getValue()).second)
          return refuse(op, "ordered sites must be unique identifiers");
        if (isa<protocol_ir::OracleSequenceAppendOp,
                protocol_ir::OracleSequenceAtOp>(op)) {
          BitVector selected;
          if (failed(
                  roles(op, op->getAttrOfType<ArrayAttr>("roles"), selected)))
            return failure();
          for (Value input : op->getOperands())
            if (!subset(selected, env.values.lookup(input)))
              return refuse(op, "oracle sequence operation requires every "
                                "selected component");
          env.values[op->getResult(0)] = std::move(selected);
        } else if (auto send = dyn_cast<protocol_ir::OracleSendOp>(op)) {
          int sender = role(send.getSenderAttr());
          BitVector available;
          if (sender < 0 || failed(roles(op, send.getReceivers(), available)) ||
              available.test(sender) ||
              !env.values.lookup(send.getData()).test(sender))
            return refuse(
                op,
                "oracle send requires its holder data and distinct receivers");
          available.set(sender);
          for (Value dimension : send.getShape()) {
            if (!subset(available, env.values.lookup(dimension)))
              return refuse(op, "oracle shape must be available at the holder "
                                "and every receiver");
            if (failed(initialOracleShape(dimension, op)))
              return failure();
          }
          env.values[send.getHandle()] = std::move(available);
        } else if (auto query = dyn_cast<protocol_ir::OracleQueryOp>(op)) {
          int owner = role(query.getOwnerAttr());
          if (owner < 0 || !env.values.lookup(query.getHandle()).test(owner) ||
              !env.values.lookup(query.getPosition()).test(owner))
            return refuse(
                op, "oracle query requires its owner's handle and position");
          BitVector available(count);
          available.set(owner);
          env.values[query.getAnswer()] = std::move(available);
        } else if (auto start =
                       dyn_cast<protocol_ir::ConstructionStartOp>(op)) {
          BitVector participants;
          if (start.getRoles().size() != 2 ||
              failed(roles(op, start.getRoles(), participants)))
            return refuse(op, "construction start requires two distinct roles");
          for (Value input : start.getInputs()) {
            auto policy = types.get(input.getType());
            if (!policy || !policy->shared ||
                !subset(participants, env.values.lookup(input)))
              return refuse(op,
                            "construction start requires shared data operands");
          }
        } else if (auto completion = dyn_cast<protocol_ir::FinishIfOp>(op)) {
          int owner = role(completion.getOwnerAttr());
          if (owner < 0 || any_of(
                               completion.getOperands(),
                               [&](Value value) {
                                 return !env.values.lookup(value).test(owner);
                               }))
            return refuse(op,
                          "entry completion requires available owner operands");
          for (Value result : completion.getContinuations()) {
            BitVector available(count);
            available.set(owner);
            env.values[result] = std::move(available);
          }
        } else if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op)) {
          int owner = role(call.getRoleAttr());
          if (owner < 0)
            return refuse(op, "local call requires a declared owner");
          for (auto input : call.getInputs())
            if (!env.values.lookup(input).test(owner))
              return refuse(op, "local call requires available owner operands");
          for (auto output : call.getOutputs()) {
            BitVector available(count);
            available.set(owner);
            env.values[output] = std::move(available);
          }
        } else if (auto query = dyn_cast<zkc::protocol_ir::QueryOp>(op)) {
          auto reference = dyn_cast<BlockArgument>(query.getReference());
          auto method =
              protocol::serviceMethod(cast<protocol_ir::ServiceReferenceType>(
                                          query.getReference().getType())
                                          .getContract(),
                                      query.getMethod());
          int owner = role(query.getOwnerAttr());
          auto spelling = [](Type type) {
            auto logical = protocol::encodeBoundType(type, false);
            if (!logical) {
              consumeError(logical.takeError());
              return std::string();
            }
            return logical->spelling();
          };
          if (!reference || reference.getOwner() != &block || owner < 0 ||
              !env.values.lookup(reference).test(owner) ||
              env.values.lookup(reference).count() != 1 || !method ||
              query.getInputs().size() != method->inputs.size() ||
              query.getNumResults() != 1 ||
              spelling(query.getResult(0).getType()) != method->output ||
              any_of(
                  zip(query.getInputs(), method->inputs),
                  [&](auto pair) {
                    auto [input, expected] = pair;
                    return spelling(input.getType()) != expected ||
                           !env.values.lookup(input).test(owner);
                  }))
            return refuse(op, "query requires its singleton owner and the "
                              "installed service signature");
          // The domain is fixed before sampling: a prover message or other
          // runtime value cannot choose the UniformIndex bound.
          if (query.getMethod() == "index") {
            auto bound =
                query.getInputs().front().getDefiningOp<data::IndexOp>();
            if (!bound || !protocol::uniformIndexBound(bound.getValue()))
              return refuse(op, "index query requires a positive constant "
                                "unsigned 64-bit bound");
          }
          BitVector available(count);
          available.set(owner);
          env.values[query.getResult(0)] = std::move(available);
        } else if (auto exchange = dyn_cast<zkc::protocol_ir::ExchangeOp>(op)) {
          auto policy = commonValuePolicy(exchange.getInput().getType());
          if (!policy || !policy->wire)
            return refuse(op, "exchange requires an admitted wire type");
          int sender = role(exchange.getSenderAttr());
          int receiver = role(exchange.getReceiverAttr());
          if (sender < 0 || receiver < 0 || sender == receiver ||
              !env.values.lookup(exchange.getInput()).test(sender))
            return refuse(
                op, "exchange requires distinct roles and an available sender");
          BitVector available(count);
          available.set(sender).set(receiver);
          env.values[exchange.getOutput()] = std::move(available);
        } else {
          auto guard = cast<zkc::protocol_ir::GuardOp>(op);
          int owner = role(guard.getOwnerAttr());
          if (owner < 0 || !env.values.lookup(guard.getCondition()).test(owner))
            return refuse(op, "guard requires an available owner");
        }
      } else
        return refuse(op, "operation has no admitted mathematical meaning");
    }
    return refuse(block.getParentOp(), "missing mathematical return");
  }
  LogicalResult run(Availability &env) {
    for (auto attr : program->getAttrs())
      if (!is_contained(program.getAttributeNames(), attr.getName().getValue()))
        return refuse(program, "unsupported mathematical protocol attribute");
    if (auto origin = program->getAttr("origin")) {
      auto decoded = protocol_ir::readProtocolOrigin(origin);
      if (!decoded) {
        consumeError(decoded.takeError());
        return refuse(program, "invalid protocol origin tree");
      }
    }
    if (!hasSingleElement(program.getBody()))
      return refuse(program, "expected exactly one common block");
    auto ft = program.getFunctionType();
    auto &block = program.getBody().front();
    llvm::StringSet<> names;
    if (!count || count > 1024)
      return refuse(program, "role roster must contain 1 to 1024 roles");
    for (auto attr : program.getRoles()) {
      auto r = dyn_cast<StringAttr>(attr);
      if (!r || !name(r.getValue()) || !names.insert(r.getValue()).second)
        return refuse(program, "role names must be distinct identifiers");
    }
    if (!name(program.getSymName()) || block.empty() ||
        block.getArgumentTypes() != ft.getInputs() ||
        !isa<zkc::protocol_ir::MathematicalReturnOp>(block.back()) ||
        block.back().getOperandTypes() != ft.getResults() ||
        program.getInputRoles().size() != ft.getNumInputs() ||
        program.getOutputRoles().size() != ft.getNumResults())
      return refuse(program, "mathematical interface mismatch");
    for (auto [arg, attr] :
         zip(block.getArguments(), program.getInputRoles())) {
      auto reference =
          dyn_cast<zkc::protocol_ir::ServiceReferenceType>(arg.getType());
      auto policy = types.get(arg.getType());
      bool oracle = isa<protocol_ir::OracleHandleType>(arg.getType());
      if (!policy && !reference && !oracle)
        return refuse(program, "unsupported mathematical input type");
      if (policy && !policy->protocolPort)
        return diagnostics::emit(program.emitOpError(), "variant-boundary");
      if (reference &&
          protocol::randomServiceField(reference.getContract()).empty())
        return refuse(program, "unsupported service contract");
      if (failed(roles(program, dyn_cast<ArrayAttr>(attr), env.values[arg])))
        return failure();
      if ((reference || (policy && !policy->shared)) &&
          env.values[arg].count() != 1)
        return refuse(program, "owner-local inputs require exactly one owner");
    }
    if (failed(verifyOracleEntryPorts(program, remaining)) ||
        failed(protocol_ir::verifyContracts(program, symbols)) ||
        failed(body(block, env)) ||
        failed(verifyOracleResultPorts(program, symbols, remaining)))
      return failure();
    for (auto [value, attr] :
         zip(block.back().getOperands(), program.getOutputRoles())) {
      BitVector exposed;
      if (failed(roles(program, dyn_cast<ArrayAttr>(attr), exposed)))
        return failure();
      auto policy = types.get(value.getType());
      if (policy && !policy->protocolPort)
        return diagnostics::emit(program.emitOpError(), "variant-boundary");
      bool oracle = isa<protocol_ir::OracleHandleType>(value.getType());
      if ((!policy && !oracle) ||
          (policy && !policy->shared && exposed.count() != 1))
        return refuse(program, "owner-local results require exactly one owner");
      if (!subset(exposed, env.values.lookup(value)))
        return refuse(program, "result exposes an unavailable component");
    }
    return success();
  }
};
} // namespace

LogicalResult verifyModule(protocol_ir::ProtocolModuleOp module) {
  if (module.getProfile() == protocol_ir::Profile::Participant)
    return verifyParticipantModule(module);
  if (module.getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics::emit(module.emitOpError(),
                             "protocol-profile-unsupported");
  for (auto attr : module->getAttrs())
    if (attr.getName() != "profile" &&
        !(attr.getName() == "source_declarations" &&
          isa<StringAttr>(attr.getValue())))
      return diagnostics::emit(
          module.emitOpError(), "mathematical-module",
          "unexpected common mathematical module attribute");
  if (!hasSingleElement(module.getBody()))
    return refuse(module, "expected one mathematical symbol-table block");
  SymbolTableCollection tables;
  TotalClosure helpers(module, tables);
  // Func owns both plain mathematics and scoped source execution. The source
  // closure assigns every retained definition to its checking owner and reads
  // actual scoped bodies, including dormant helpers and outlined regions.
  if (auto error = protocol::verifySourceExecutionClosure(module))
    return diagnostics::emit(module.emitOpError(), std::move(error));
  // The enclosing profile also owns finite references in protocol
  // definitions, outside the scoped/Math definition component above.
  if (failed(finite::verifyClosure(module)))
    return failure();
  unsigned programs = 0;
  for (auto &op : module.getBody().front()) {
    if (auto program = dyn_cast<protocol_ir::MathematicalOp>(op)) {
      ++programs;
    } else if (isa<func::FuncOp>(op)) {
      // Complete mathematical/scoped admission was performed above.
    } else if (isa<data::DomainOp>(op)) {
      // The descriptor and finite closure were checked before any liveness.
    } else if (isa<protocol_ir::OracleDefinitionOp, protocol_ir::ConstructionOp,
                   runtime::BindingOp, mlir::ModuleOp, poly::RecipeOp,
                   poly::RealizeOp>(op)) {
      // The owning verifiers check every retained declaration, including
      // dormant computation units and polynomial realizations.
    } else if (auto declaration = dyn_cast<relation::DeclareOp>(op)) {
      for (auto attr : declaration->getAttrs())
        if (!is_contained(declaration.getAttributeNames(),
                          attr.getName().getValue()))
          return refuse(declaration,
                        "unsupported relation declaration attribute");
    } else {
      return diagnostics::emit(
          op.emitOpError(), "mathematical-module",
          "unclassified declaration in the 'protocol' profile");
    }
  }
  if (!programs && module.getBody().front().getOps<func::FuncOp>().empty() &&
      module.getBody()
          .front()
          .getOps<protocol_ir::OracleDefinitionOp>()
          .empty())
    return diagnostics::emit(module.emitOpError(), "mathematical-module",
                             "expected a mathematical definition");
  if (failed(verifyApplications(module)))
    return failure();
  NativeTypePolicies types(module);
  if (failed(relation::verifyDeclarationConsistency({module.getOperation()})))
    return failure();
  // The enclosing isolated symbol table owns cross-definition analysis. Its
  // children have already been verified; sibling definitions are stable here.
  // One cache and work budget cover all mathematical protocols in this unit.
  unsigned remaining = 100000;
  uint64_t remainingAvailabilityWork = 1000000;
  if (failed(verifyOracleDefinitions(module, helpers, types, remaining)))
    return failure();
  SmallVector<protocol_ir::RepeatOp> originQueries;
  for (auto program :
       module.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    Availability availability;
    if (failed(Analysis(program, helpers, remaining, remainingAvailabilityWork,
                        types, tables, originQueries)
                   .run(availability)))
      return failure();
  }
  // Every body is formed before a summary follows a forward callee reference.
  // Root obligations still cover every original repeat, including unused ones.
  ResourceOrigins origins(tables, types);
  for (auto repeat : originQueries)
    if (failed(origins.verify(repeat)))
      return failure();
  return success();
}

LogicalResult analyze(zkc::protocol_ir::MathematicalOp program,
                      Availability &result, SymbolTableCollection &tables) {
  result.values.clear();
  TotalClosure helpers(program->getParentOp(), tables);
  unsigned remaining = 100000;
  uint64_t remainingAvailabilityWork = 1000000;
  NativeTypePolicies types(program);
  SmallVector<protocol_ir::RepeatOp> originQueries;
  if (failed(Analysis(program, helpers, remaining, remainingAvailabilityWork,
                      types, tables, originQueries)
                 .run(result)))
    return failure();
  ResourceOrigins origins(tables, types);
  for (auto repeat : originQueries)
    if (failed(origins.verify(repeat)))
      return failure();
  return success();
}
} // namespace zkc::mathematical

namespace zkc {
LogicalResult zkc::protocol_ir::MathematicalOp::verifyRegions() {
  auto unit = dyn_cast_or_null<ProtocolModuleOp>((*this)->getParentOp());
  if (!unit || !unit.getProfileAttr() || unit.getProfile() != Profile::Protocol)
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "protocol.func requires a symbol table with the 'protocol' profile");
  if (!llvm::hasSingleElement(getBody()) || getBody().front().empty())
    return diagnostics::emit(emitOpError(), "mathematical-formation",
                             "expected one nonempty common block");
  return success();
}
LogicalResult
zkc::protocol_ir::StatementOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto relation = tables.lookupNearestSymbolFrom<zkc::relation::DeclareOp>(
      *this, getRelationAttr());
  SmallVector<Type> logical;
  for (Type type : getOperandTypes()) {
    if (auto anchor = dyn_cast<protocol_ir::OracleHandleType>(type))
      logical.push_back(anchor.getKind().getDataType());
    else
      logical.push_back(type);
  }
  if (!relation || failed(relation->getName().verifyInvariants(relation)) ||
      !llvm::equal(relation.getSignature().getInputs(), logical))
    return diagnostics::emit(emitOpError(), "mathematical-statement",
                             "expected an external relation declaration with "
                             "matching inputs and one bool result");
  return success();
}
} // namespace zkc
