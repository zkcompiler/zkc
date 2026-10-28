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
LogicalResult verifyOracleEntryPorts(protocol_ir::MathematicalOp program,
                                     unsigned &remaining) {
  if (failed(program->getName().verifyInvariants(program)) ||
      !llvm::hasSingleElement(program.getBody()))
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
    auto input =
        argument.hasOneUse()
            ? dyn_cast<protocol_ir::OracleInputOp>(*argument.getUsers().begin())
            : protocol_ir::OracleInputOp();
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
LogicalResult verifyOracleResultPorts(protocol_ir::MathematicalOp program,
                                      SymbolTableCollection &symbols,
                                      unsigned &remaining) {
  auto returned = program.getBody().front().back().getOperands();
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
  if (failed(verifyOracleEntryPorts(callee, remaining)))
    return failure();
  auto mapped = [&](Attribute role) {
    size_t index =
        llvm::find(callee.getRoles(), role) - callee.getRoles().begin();
    return index < callee.getRoles().size() ? application.getRoles()[index]
                                            : Attribute();
  };
  for (BlockArgument argument : callee.getBody().front().getArguments()) {
    if (!isa<protocol_ir::OracleHandleType>(argument.getType()))
      continue;
    auto input = cast<protocol_ir::OracleInputOp>(*argument.getUsers().begin());
    auto holder = dyn_cast_or_null<StringAttr>(mapped(input.getHolderAttr()));
    SmallVector<Attribute> receivers;
    for (auto receiver : input.getReceivers()) {
      auto role = mapped(receiver);
      if (!role)
        return refuse(application, "unknown oracle input receiver");
      receivers.push_back(role);
    }
    if (!holder ||
        failed(paired(application.getOperand(
                          cast<BlockArgument>(input.getData()).getArgNumber()),
                      application.getOperand(argument.getArgNumber()), holder,
                      ArrayAttr::get(application.getContext(), receivers),
                      application, symbols, remaining)))
      return failure();
  }
  return success();
}
} // namespace zkc::mathematical
