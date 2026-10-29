#include "zkc/Dialect/Protocol/OraclePorts.h"
#include "OracleAnalysis.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", reason);
}
LogicalResult charge(Operation *op, unsigned &remaining) {
  if (!remaining)
    return diagnostics::emit(op->emitOpError(), "mathematical-analysis-limit",
                             "oracle interface budget exhausted");
  --remaining;
  return success();
}
Value stripViews(Value value, Operation *use, unsigned &remaining) {
  while (auto view = value.getDefiningOp<protocol_ir::RestrictRolesOp>()) {
    if (failed(charge(use, remaining)) ||
        failed(view->getName().verifyInvariants(view)))
      return {};
    value = view.getInput();
  }
  return value;
}
bool singleton(Attribute roles, Attribute holder) {
  auto set = dyn_cast<ArrayAttr>(roles);
  return set && set.size() == 1 && set[0] == holder;
}
struct Components {
  SmallVector<Value> data;
  StringAttr holder;
  ArrayAttr receivers;
};
LogicalResult components(Value anchor, Components &result, Operation *use,
                         SymbolTableCollection &symbols, unsigned &remaining,
                         unsigned depth = 0) {
  if (depth > 64 || failed(charge(use, remaining)))
    return refuse(use, "oracle output component closure exceeds its bound");
  anchor = stripViews(anchor, use, remaining);
  if (!anchor)
    return failure();
  auto *producer = anchor.getDefiningOp();
  if (!producer || failed(producer->getName().verifyInvariants(producer)))
    return refuse(use, "oracle interface requires an actual component pair");
  if (auto view = dyn_cast<protocol_ir::OracleComponentsOp>(producer)) {
    if (anchor != view.getAnchor())
      return refuse(use, "oracle interface requires the receiver component");
    result = {{view.getData()}, view.getHolderAttr(), view.getReceivers()};
    return success();
  }
  auto call = dyn_cast<protocol_ir::ApplyOp>(producer);
  if (!call || failed(call.verifySymbolUses(symbols)))
    return refuse(use, "oracle interface requires a paired application result");
  auto callee = symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
      call, call.getCalleeAttr());
  auto returned = callee.getBody().front().back().getOperands();
  if (returned.size() != callee.getOutputRoles().size())
    return refuse(use,
                  "oracle result tuple differs from its declared interface");
  unsigned index = cast<OpResult>(anchor).getResultNumber();
  if (index >= returned.size() ||
      failed(components(returned[index], result, use, symbols, remaining,
                        depth + 1)))
    return failure();
  llvm::DenseSet<Value> sourceData(result.data.begin(), result.data.end());
  SmallVector<Value> data;
  for (unsigned dataIndex = 0; dataIndex < returned.size(); ++dataIndex) {
    if (failed(charge(use, remaining)))
      return failure();
    if (sourceData.contains(stripViews(returned[dataIndex], use, remaining)) &&
        singleton(callee.getOutputRoles()[dataIndex], result.holder))
      data.push_back(call.getResult(dataIndex));
  }
  if (data.empty() || callee.getOutputRoles()[index] != result.receivers)
    return refuse(use, "oracle result lacks its paired holder data");
  auto mapped = [&](Attribute role) -> Attribute {
    auto found = llvm::find(callee.getRoles(), role);
    return found == callee.getRoles().end()
               ? Attribute()
               : call.getRoles()[found - callee.getRoles().begin()];
  };
  auto holder = dyn_cast_or_null<StringAttr>(mapped(result.holder));
  SmallVector<Attribute> receivers;
  for (Attribute receiver : result.receivers) {
    auto role = mapped(receiver);
    if (!role)
      return refuse(use, "oracle result has an unknown formal receiver");
    receivers.push_back(role);
  }
  if (!holder)
    return refuse(use, "oracle result has an unknown formal holder");
  result = {std::move(data), holder,
            ArrayAttr::get(call.getContext(), receivers)};
  return success();
}
LogicalResult paired(Value data, Value anchor, StringAttr holder,
                     ArrayAttr receivers, Operation *use,
                     SymbolTableCollection &symbols, unsigned &remaining) {
  Components actual;
  if (failed(components(anchor, actual, use, symbols, remaining)))
    return failure();
  if (!llvm::is_contained(actual.data, stripViews(data, use, remaining)) ||
      holder != actual.holder || receivers != actual.receivers)
    return refuse(use,
                  "oracle interface mixes data, anchors or role components");
  return success();
}
} // namespace
static LogicalResult
collectOracleEntryPorts(protocol_ir::MathematicalOp program,
                        unsigned &remaining,
                        SmallVectorImpl<OraclePortPair> *pairs = nullptr) {
  if (!program || failed(program->getName().verifyInvariants(program)) ||
      !llvm::hasSingleElement(program.getBody()) ||
      program.getBody().front().empty())
    return failure();
  auto &body = program.getBody().front();
  if (body.getArgumentTypes() != program.getFunctionType().getInputs() ||
      body.getNumArguments() != program.getInputRoles().size())
    return refuse(program, "oracle entry requires a formed protocol signature");
  llvm::DenseSet<unsigned> dataPorts;
  llvm::DenseSet<Operation *> bindings;
  for (BlockArgument argument : body.getArguments()) {
    if (!isa<protocol_ir::OracleHandleType>(argument.getType()))
      continue;
    if (failed(charge(program, remaining)))
      return failure();
    protocol_ir::OracleInputOp input;
    for (OpOperand &use : argument.getUses()) {
      if (failed(charge(use.getOwner(), remaining)))
        return failure();
      if (auto statement = dyn_cast<protocol_ir::StatementOp>(use.getOwner())) {
        // Contract verification checks the exact target projection next. This
        // use is logical metadata; it grants no raw executable handle access.
        unsigned index = use.getOperandNumber();
        if (failed(statement->getName().verifyInvariants(statement)) ||
            statement->getBlock() != &body || !statement.getTargetAttr() ||
            index >= statement.getSelectors().size() ||
            statement.getSelectors()[index] !=
                StringAttr::get(program.getContext(), "anchor"))
          return refuse(
              statement,
              "raw anchor metadata requires a selected logical target");
        continue;
      }
      auto binding = dyn_cast<protocol_ir::OracleInputOp>(use.getOwner());
      if (!binding || input)
        return refuse(program,
                      "a raw oracle entry must have one input binding");
      input = binding;
    }
    if (!input || failed(input->getName().verifyInvariants(input)) ||
        input->getBlock() != &body || input.getAnchor() != argument)
      return refuse(program, "a raw oracle entry must have one input binding");
    auto data = dyn_cast<BlockArgument>(input.getData());
    if (!data || data.getOwner() != &body ||
        !dataPorts.insert(data.getArgNumber()).second ||
        !singleton(program.getInputRoles()[data.getArgNumber()],
                   input.getHolderAttr()) ||
        program.getInputRoles()[argument.getArgNumber()] !=
            input.getReceivers())
      return refuse(input, "oracle input requires distinct paired entry leaves "
                           "with exact roles");
    if (pairs)
      pairs->push_back(
          {data.getArgNumber(), argument.getArgNumber(),
           cast<protocol_ir::OracleHandleType>(argument.getType()).getKind(),
           input.getHolderAttr(), input.getReceivers()});
    bindings.insert(input);
  }
  bool effect = false;
  for (auto &op : body) {
    if (bindings.empty())
      break;
    if (failed(charge(program, remaining)))
      return failure();
    if (bindings.erase(&op)) {
      if (effect)
        return refuse(&op,
                      "root oracle inputs must bind before protocol effects");
    } else if (!isProtocolValueExpression(&op) && !isa<func::CallOp>(op))
      effect = true;
  }
  return success();
}
LogicalResult verifyOracleInputPair(protocol_ir::OracleInputOp input,
                                    SymbolTableCollection &symbols,
                                    unsigned &remaining) {
  auto argument = dyn_cast<BlockArgument>(input.getAnchor());
  auto program = input->getParentOfType<protocol_ir::MathematicalOp>();
  if (argument && program && argument.getOwner() == &program.getBody().front())
    return success(); // The complete entry pairing was checked first.
  return paired(input.getData(), input.getAnchor(), input.getHolderAttr(),
                input.getReceivers(), input, symbols, remaining);
}
static LogicalResult
collectOracleResultPorts(protocol_ir::MathematicalOp program,
                         SymbolTableCollection &symbols, unsigned &remaining,
                         SmallVectorImpl<OraclePortPair> *pairs = nullptr) {
  if (!isa<protocol_ir::MathematicalReturnOp>(program.getBody().front().back()))
    return refuse(program, "oracle results require the protocol return tuple");
  auto returned = program.getBody().front().back().getOperands();
  if (returned.getTypes() != program.getFunctionType().getResults() ||
      returned.size() != program.getOutputRoles().size())
    return refuse(program, "oracle result tuple differs from its interface");
  llvm::DenseSet<unsigned> dataPorts;
  for (auto [index, value] : llvm::enumerate(returned)) {
    if (!isa<protocol_ir::OracleHandleType>(value.getType()))
      continue;
    Components actual;
    if (failed(components(value, actual, program, symbols, remaining)))
      return failure();
    llvm::DenseSet<Value> possibleData(actual.data.begin(), actual.data.end());
    bool pairedData = false;
    for (auto [dataIndex, data] : llvm::enumerate(returned)) {
      if (failed(charge(program, remaining)))
        return failure();
      if (!dataPorts.contains(dataIndex) &&
          possibleData.contains(stripViews(data, program, remaining)) &&
          singleton(program.getOutputRoles()[dataIndex], actual.holder)) {
        dataPorts.insert(dataIndex);
        if (pairs)
          pairs->push_back(
              {unsigned(dataIndex), unsigned(index),
               cast<protocol_ir::OracleHandleType>(value.getType()).getKind(),
               actual.holder, actual.receivers});
        pairedData = true;
        break;
      }
    }
    if (!pairedData || program.getOutputRoles()[index] != actual.receivers)
      return refuse(
          program,
          "oracle result requires its holder data and exact receiver roles");
  }
  return success();
}
LogicalResult verifyOracleApplicationPorts(protocol_ir::ApplyOp application,
                                           SymbolTableCollection &symbols,
                                           unsigned &remaining) {
  auto callee = symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
      application, application.getCalleeAttr());
  SmallVector<OraclePortPair> inputs;
  if (failed(collectOracleEntryPorts(callee, remaining, &inputs)))
    return failure();
  auto mapped = [&](Attribute role) {
    size_t index =
        llvm::find(callee.getRoles(), role) - callee.getRoles().begin();
    return index < callee.getRoles().size() ? application.getRoles()[index]
                                            : Attribute();
  };
  for (const auto &input : inputs) {
    auto holder = dyn_cast_or_null<StringAttr>(mapped(input.holder));
    SmallVector<Attribute> receivers;
    for (auto receiver : input.receivers) {
      auto role = mapped(receiver);
      if (!role)
        return refuse(application, "unknown oracle input receiver");
      receivers.push_back(role);
    }
    if (!holder ||
        failed(paired(application.getOperand(input.data),
                      application.getOperand(input.anchor), holder,
                      ArrayAttr::get(application.getContext(), receivers),
                      application, symbols, remaining)))
      return failure();
  }
  return success();
}
LogicalResult verifyOracleEntryPorts(protocol_ir::MathematicalOp program,
                                     unsigned &remaining) {
  return collectOracleEntryPorts(program, remaining);
}
LogicalResult verifyOracleResultPorts(protocol_ir::MathematicalOp program,
                                      SymbolTableCollection &symbols,
                                      unsigned &remaining) {
  return collectOracleResultPorts(program, symbols, remaining);
}
FailureOr<OraclePortLayout>
readOraclePortLayout(protocol_ir::MathematicalOp program,
                     SymbolTableCollection &symbols, unsigned &remaining) {
  OraclePortLayout result;
  if (failed(collectOracleEntryPorts(program, remaining, &result.inputs)) ||
      failed(collectOracleResultPorts(program, symbols, remaining,
                                      &result.outputs)))
    return failure();
  return result;
}
} // namespace zkc::mathematical
