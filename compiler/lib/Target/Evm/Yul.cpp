#include "Arithmetic.h"
#include "Runtime.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/BindingTypes.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Target/Evm/Transcript.h"
#include "zkc/Target/Evm/Wire.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
namespace {
struct StaticData {
  std::string name, bytes;
};
class Exporter {
public:
  Exporter(ModuleOp module, const EvmEndpoint &endpoint,
           const NativeProofPolicy &policy, const EvmLimits &limits)
      : module(module), endpoint(endpoint), policy(policy), limits(limits),
        layouts(*module.getContext()), arithmetic(layouts, limits),
        wire(layouts, limits), out(text) {}
  Expected<std::string> run();

private:
  ModuleOp module;
  const EvmEndpoint &endpoint;
  const NativeProofPolicy &policy;
  const EvmLimits &limits;
  NativeLayouts layouts;
  /// The realized transcript suite of the checked policy, when it has one.
  std::optional<TranscriptRealization> realizedSuite;
  detail::Arithmetic arithmetic;
  WireGenerator wire;
  std::string text;
  raw_string_ostream out;
  llvm::DenseMap<Value, std::string> names;
  SmallVector<StaticData> data;
  StringMap<std::string> dataNames;
  std::vector<std::string> returns;
  uint64_t serial = 0;
  std::string fresh() { return "v" + std::to_string(serial++); }
  std::string name(Value value) {
    auto &result = names[value];
    if (result.empty())
      result = fresh();
    return result;
  }
  std::string list(ValueRange values) {
    std::string result;
    for (Value value : values) {
      if (!result.empty())
        result += ", ";
      result += name(value);
    }
    return result;
  }
  std::string staticData(StringRef bytes) {
    auto found = dataNames.find(bytes);
    if (found != dataNames.end())
      return found->second;
    std::string name = "bytes_" + std::to_string(data.size());
    data.push_back({name, bytes.str()});
    dataNames[bytes] = name;
    return name;
  }
  void copyStatic(StringRef bytes, StringRef destination) {
    std::string name = staticData(bytes);
    out << "datacopy(" << destination << ", dataoffset(\"" << name
        << "\"), datasize(\"" << name << "\"))\n";
  }
  void declare(ValueRange results) {
    for (Value value : results)
      out << "let " << name(value) << " := 0\n";
  }
  void assignment(ArrayRef<std::string> target, ValueRange values) {
    SmallVector<std::string> temporary;
    for (Value value : values) {
      auto temp = fresh();
      out << "let " << temp << " := " << name(value) << "\n";
      temporary.push_back(std::move(temp));
    }
    for (auto [destination, source] : zip(target, temporary))
      out << destination << " := " << source << "\n";
  }
  void assignment(ValueRange target, ValueRange values) {
    SmallVector<std::string> destinations;
    for (Value value : target)
      destinations.push_back(name(value));
    assignment(destinations, values);
  }
  LogicalResult operation(Operation *);
  LogicalResult block(Block &, bool terminator = false);
  LogicalResult transcript(Operation *);
  LogicalResult function(func::FuncOp);
  LogicalResult outer(func::FuncOp);
  LogicalResult refuse(Operation *op, StringRef reason) {
    return op->emitError("[evm.yul] ") << reason;
  }
};

std::string number(const APInt &value) {
  SmallString<80> text;
  value.toString(text, 16, false);
  return "0x" + text.str().str();
}
std::string mask(Type type, StringRef value) {
  unsigned width = cast<IntegerType>(type).getWidth();
  if (width == 256)
    return value.str();
  return "and(" + value.str() + ", " +
         number(APInt::getLowBitsSet(256, width)) + ")";
}
std::string sign(Type type, StringRef value) {
  unsigned width = cast<IntegerType>(type).getWidth();
  if (width == 256)
    return value.str();
  if (width == 1)
    return "sub(0, " + value.str() + ")";
  return "signextend(" + std::to_string(width / 8 - 1) + ", " + value.str() +
         ")";
}

LogicalResult Exporter::transcript(Operation *op) {
  auto origin = runtime::exportNativeOrigin(
      op->getAttrOfType<runtime::NativeOriginAttr>("origin"));
  if (!origin) {
    consumeError(origin.takeError());
    return refuse(op, "invalid transcript origin");
  }
  json::Array steps;
  unsigned depth = 0;
  for (const auto &step : origin->path) {
    // A branch step carries its alternative; the EVM transcript has no
    // selected-control occurrence encoding, so it must not become an apply.
    if (step.kind == protocol::NativeOriginStep::Kind::Branch)
      return refuse(op, "unsupported selected-control transcript origin");
    bool repeat = step.kind == protocol::NativeOriginStep::Kind::Repeat;
    depth += repeat;
    steps.push_back(
        json::Array{repeat ? "repeat" : "apply", step.protocol, step.site});
  }
  json::Array event;
  if (auto *message =
          std::get_if<protocol::NativeMessageOrigin>(&origin->event)) {
    event = json::Array{"message",       message->protocol, message->site,
                        message->schema, message->sender,   message->receiver};
  } else if (auto *query =
                 std::get_if<protocol::NativeQueryOrigin>(&origin->event)) {
    if (query->method != "draw")
      return refuse(op, "unsupported transcript query method");
    event = json::Array{
        "query",        query->protocol,
        query->site,    "input_" + std::to_string(query->serviceInput),
        query->service, query->method,
        query->owner};
  } else {
    return refuse(op, "unsupported transcript occurrence kind");
  }
  // The five-element origin: the coordinates and the event follow the three
  // static elements.
  auto prefix = encodeLogicalTreePrefix(
      json::Array{"zkc.native-origin/0", origin->entry, std::move(steps)}, 5);
  auto suffix = encodeLogicalTree(std::move(event));
  if (!prefix || !suffix) {
    if (!prefix)
      consumeError(prefix.takeError());
    if (!suffix)
      consumeError(suffix.takeError());
    return refuse(op, "invalid logical origin tree");
  }
  if (prefix->size() + suffix->size() + 9 + depth * 29 > 4096)
    return refuse(op,
                  "origin template exceeds the bounded transition workspace");
  unsigned coordinates = op->getNumOperands() - 2;
  Value coordinateData = op->getOperand(coordinates);
  Value coordinateLength = op->getOperand(coordinates + 1);
  out << "{\nlet occurrence := evm_alloc(4096)\n";
  out << "if iszero(eq(" << name(coordinateLength) << ", " << depth
      << ")) { evm_fault(8) }\n";
  copyStatic(*prefix, "occurrence");
  out << "let end := evm_tree_header(add(occurrence, " << prefix->size()
      << "), 1, " << depth << ")\n";
  out << "for { let i := 0 } lt(i, " << depth << ") { i := add(i, 1) } {\n"
      << "evm_memory(" << name(coordinateData) << ", mul("
      << name(coordinateLength) << ", 32))\n"
      << "let coordinate := mload(add(" << name(coordinateData)
      << ", mul(i, 32)))\n"
      << "end := evm_tree_natural(end, coordinate)\n}\n";
  copyStatic(*suffix, "end");
  out << "end := add(end, " << suffix->size() << ")\n"
      << "if gt(sub(end, occurrence), 4096) { evm_resource(9) }\n";
  if (isa<TranscriptObserveOp>(op)) {
    auto type = op->getAttrOfType<TypeAttr>("value_type");
    if (!type)
      return refuse(op, "observation lacks exact native value_type");
    auto encoder = wire.encoder(type.getValue());
    if (!encoder) {
      auto reason = toString(encoder.takeError());
      return refuse(op, reason);
    }
    out << "let frame, frameLength := " << *encoder << "("
        << list(op->getOperands().slice(2, coordinates - 2)) << ")\n";
    out << list(op->getResults()) << " := evm_transcript_observe("
        << name(op->getOperand(0)) << ", " << name(op->getOperand(1))
        << ", frame, frameLength, occurrence, sub(end, occurrence))\n";
  } else {
    out << list(op->getResults()) << " := evm_transcript_challenge("
        << name(op->getOperand(0)) << ", " << name(op->getOperand(1))
        << ", occurrence, sub(end, occurrence))\n";
  }
  out << "mstore(0x40, occurrence)\n}\n";
  return success();
}

LogicalResult Exporter::operation(Operation *op) {
  if (auto value = dyn_cast<arith::ConstantOp>(op)) {
    auto literal = dyn_cast<IntegerAttr>(value.getValue());
    if (!literal)
      return refuse(op, "noninteger arithmetic constant");
    out << "let " << name(op->getResult(0))
        << " := " << number(literal.getValue()) << "\n";
    return success();
  }
  if (isa<EvmDialect>(op->getDialect())) {
    declare(op->getResults());
    if (isa<TranscriptObserveOp, TranscriptChallengeOp>(op))
      return transcript(op);
    if (isa<SourceStopOp, SourceGuardOp>(op)) {
      uint64_t code = 0;
      if (auto site = op->getAttrOfType<StringAttr>("site")) {
        // Stable bounded FNV-1a site code, not a source admission identity.
        code = 2166136261;
        for (unsigned char c : site.getValue())
          code = ((code ^ c) * 16777619) & 0xffffffff;
      }
      if (op->getNumOperands())
        out << "if iszero(" << name(op->getOperand(0)) << ") { ";
      out << "evm_source(" << code << ")";
      if (op->getNumOperands())
        out << " }";
      out << "\n";
      return success();
    }
    Expected<std::string> helper =
        zkc::error("evm.yul", "unsupported checked helper");
    if (isa<FieldConstantOp, FieldAddOp, FieldSubOp, FieldMulOp, FieldNegOp,
            FieldEqualOp, FieldFromIndexOp, FieldEmbedOp, FieldInverseOp,
            VectorConstantOp, VectorEmptyOp, VectorLengthOp, VectorAppendOp,
            VectorSplitOp, VectorSumOp, VectorAllocOp, VectorGetOp, VectorSetOp,
            VectorEqualOp>(op))
      helper = arithmetic.helper(op);
    else if (isa<ProofReceiveOp, SequenceEmptyOp, SequenceAppendOp,
                 SequenceLengthOp, SequenceGetOp, SequenceAllocOp,
                 SequenceSetOp, VariantMakeOp, VariantTagOp, VariantGetOp,
                 BytesEmptyOp, BytesLengthOp, BytesGetOp, BytesAppendOp>(op))
      helper = wire.operation(op);
    else {
      StringRef name =
          llvm::TypeSwitch<Operation *, StringRef>(op)
              .Case<IndexAddOp>([](IndexAddOp) { return "evm_index_add"; })
              .Case<IndexSubOp>([](IndexSubOp) { return "evm_index_sub"; })
              .Case<IndexMulOp>([](IndexMulOp) { return "evm_index_mul"; })
              .Case<IndexDivOp>([](IndexDivOp) { return "evm_index_div"; })
              .Case<IndexModOp>([](IndexModOp) { return "evm_index_mod"; })
              .Case<IndexPowerOfTwoOp>(
                  [](IndexPowerOfTwoOp) { return "evm_index_power_of_two"; })
              .Case<IndexLogicalShiftRightOp>([](IndexLogicalShiftRightOp) {
                return "evm_index_logical_shift_right";
              })
              .Case<IndicesEmptyOp>(
                  [](IndicesEmptyOp) { return "evm_indices_empty"; })
              .Case<IndicesAppendOp>(
                  [](IndicesAppendOp) { return "evm_indices_append"; })
              .Case<ScopeCurrentOp>(
                  [](ScopeCurrentOp) { return "evm_scope_current"; })
              .Case<ScopeEnterOp>(
                  [](ScopeEnterOp) { return "evm_scope_enter"; })
              .Case<ScopeExitOp>([](ScopeExitOp) { return "evm_scope_exit"; })
              .Case<ScopeCheckOp>(
                  [](ScopeCheckOp) { return "evm_scope_check"; })
              .Case<TransferMakeOp>(
                  [](TransferMakeOp) { return "evm_transfer_make"; })
              .Case<TransferAcceptOp>(
                  [](TransferAcceptOp) { return "evm_transfer_accept"; })
              .Case<TransferReleaseOp>(
                  [](TransferReleaseOp) { return "evm_transfer_release"; })
              .Case<TransferCheckOp>(
                  [](TransferCheckOp) { return "evm_transfer_check"; })
              .Case<LoopBoundOp>([](LoopBoundOp) { return "evm_loop_bound"; })
              .Case<RangeCheckOp>(
                  [](RangeCheckOp) { return "evm_range_check"; })
              .Case<RangeAdmitOp>(
                  [](RangeAdmitOp) { return "evm_range_admit"; })
              .Default(StringRef());
      if (name.empty())
        return refuse(op, "no typed runtime helper");
      helper = name.str();
    }
    if (!helper) {
      auto reason = toString(helper.takeError());
      return refuse(op, reason);
    }
    if (op->getNumResults())
      out << list(op->getResults()) << " := ";
    out << *helper << "(" << list(op->getOperands()) << ")";
    out << "\n";
    return success();
  }
  if (auto call = dyn_cast<func::CallOp>(op)) {
    if (op->getNumResults())
      out << "let " << list(op->getResults()) << " := ";
    out << call.getCallee() << "(" << list(op->getOperands()) << ")\n";
    return success();
  }
  if (isa<func::ReturnOp>(op)) {
    assignment(returns, op->getOperands());
    out << "leave\n";
    return success();
  }
  if (auto branch = dyn_cast<scf::IfOp>(op)) {
    declare(op->getResults());
    out << "switch " << name(branch.getCondition()) << "\ncase 0 {\n";
    if (!branch.getElseRegion().empty()) {
      if (failed(block(branch.getElseRegion().front())))
        return failure();
      assignment(op->getResults(),
                 branch.getElseRegion().front().getTerminator()->getOperands());
    }
    out << "}\ndefault {\n";
    if (failed(block(branch.getThenRegion().front())))
      return failure();
    assignment(op->getResults(),
               branch.getThenRegion().front().getTerminator()->getOperands());
    out << "}\n";
    return success();
  }
  if (auto loop = dyn_cast<scf::ForOp>(op)) {
    declare(op->getResults());
    assignment(op->getResults(), loop.getInitArgs());
    for (auto [arg, result] : zip(loop.getRegionIterArgs(), op->getResults()))
      names[arg] = name(result);
    std::string index = name(loop.getInductionVar());
    std::string upper = name(loop.getUpperBound());
    if (!loop.getUnsignedCmp()) {
      index = sign(loop.getInductionVar().getType(), index);
      upper = sign(loop.getUpperBound().getType(), upper);
    }
    out << "for { let " << name(loop.getInductionVar())
        << " := " << name(loop.getLowerBound()) << " } "
        << (loop.getUnsignedCmp() ? "lt(" : "slt(") << index << ", " << upper
        << ") { " << name(loop.getInductionVar()) << " := evm_index_add("
        << name(loop.getInductionVar()) << ", " << name(loop.getStep())
        << ") } {\n";
    if (failed(block(*loop.getBody())))
      return failure();
    assignment(op->getResults(),
               loop.getBody()->getTerminator()->getOperands());
    out << "}\n";
    return success();
  }
  if (auto loop = dyn_cast<scf::WhileOp>(op)) {
    declare(op->getResults());
    Block &before = loop.getBefore().front();
    Block &after = loop.getAfter().front();
    declare(before.getArguments());
    assignment(before.getArguments(), loop.getInits());
    std::string continuing = fresh();
    out << "for { let " << continuing << " := 1 } " << continuing << " {} {\n";
    if (failed(block(before)))
      return failure();
    auto condition = cast<scf::ConditionOp>(before.getTerminator());
    out << "switch " << name(condition.getCondition()) << "\ncase 0 {\n";
    assignment(op->getResults(), condition.getArgs());
    out << continuing << " := 0\n}\ndefault {\n";
    declare(after.getArguments());
    assignment(after.getArguments(), condition.getArgs());
    if (failed(block(after)))
      return failure();
    assignment(before.getArguments(), after.getTerminator()->getOperands());
    out << "}\n}\n";
    return success();
  }
  if (auto branch = dyn_cast<scf::IndexSwitchOp>(op)) {
    declare(op->getResults());
    out << "switch " << name(branch.getArg()) << "\n";
    for (auto [value, region] :
         zip(branch.getCases(), branch.getCaseRegions())) {
      out << "case " << value << " {\n";
      if (failed(block(region.front())))
        return failure();
      assignment(op->getResults(),
                 region.front().getTerminator()->getOperands());
      out << "}\n";
    }
    out << "default {\n";
    if (failed(block(branch.getDefaultRegion().front())))
      return failure();
    assignment(
        op->getResults(),
        branch.getDefaultRegion().front().getTerminator()->getOperands());
    out << "}\n";
    return success();
  }
  if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
    std::string a = name(compare.getLhs()), b = name(compare.getRhs());
    auto predicate = compare.getPredicate();
    bool signedCompare = predicate == arith::CmpIPredicate::slt ||
                         predicate == arith::CmpIPredicate::sle ||
                         predicate == arith::CmpIPredicate::sgt ||
                         predicate == arith::CmpIPredicate::sge;
    if (signedCompare) {
      a = sign(compare.getLhs().getType(), a);
      b = sign(compare.getRhs().getType(), b);
    }
    StringRef code;
    bool invert = false;
    switch (predicate) {
    case arith::CmpIPredicate::eq:
      code = "eq";
      break;
    case arith::CmpIPredicate::ne:
      code = "eq";
      invert = true;
      break;
    case arith::CmpIPredicate::ult:
      code = "lt";
      break;
    case arith::CmpIPredicate::ule:
      code = "gt";
      invert = true;
      break;
    case arith::CmpIPredicate::ugt:
      code = "gt";
      break;
    case arith::CmpIPredicate::uge:
      code = "lt";
      invert = true;
      break;
    case arith::CmpIPredicate::slt:
      code = "slt";
      break;
    case arith::CmpIPredicate::sle:
      code = "sgt";
      invert = true;
      break;
    case arith::CmpIPredicate::sgt:
      code = "sgt";
      break;
    case arith::CmpIPredicate::sge:
      code = "slt";
      invert = true;
      break;
    }
    out << "let " << name(op->getResult(0)) << " := ";
    if (invert)
      out << "iszero(";
    out << code << "(" << a << ", " << b << ")";
    if (invert)
      out << ")";
    out << "\n";
    return success();
  }
  if (auto select = dyn_cast<arith::SelectOp>(op)) {
    out << "let " << name(select.getResult())
        << " := " << name(select.getTrueValue()) << "\nif iszero("
        << name(select.getCondition()) << ") { " << name(select.getResult())
        << " := " << name(select.getFalseValue()) << " }\n";
    return success();
  }
  if (isa<arith::ExtUIOp, arith::ExtSIOp, arith::TruncIOp, arith::IndexCastOp,
          arith::IndexCastUIOp>(op)) {
    std::string value = name(op->getOperand(0));
    unsigned from = op->getOperand(0).getType().getIntOrFloatBitWidth();
    unsigned to = op->getResult(0).getType().getIntOrFloatBitWidth();
    if (from < to && isa<arith::ExtSIOp, arith::IndexCastOp>(op))
      value = sign(op->getOperand(0).getType(), value);
    out << "let " << name(op->getResult(0))
        << " := " << mask(op->getResult(0).getType(), value) << "\n";
    return success();
  }
  auto instruction = llvm::TypeSwitch<Operation *, StringRef>(op)
                         .Case<arith::AddIOp>([](auto) { return "add"; })
                         .Case<arith::SubIOp>([](auto) { return "sub"; })
                         .Case<arith::MulIOp>([](auto) { return "mul"; })
                         .Case<arith::AndIOp>([](auto) { return "and"; })
                         .Case<arith::OrIOp>([](auto) { return "or"; })
                         .Case<arith::XOrIOp>([](auto) { return "xor"; })
                         .Default(StringRef());
  if (!instruction.empty()) {
    std::string expression =
        instruction.str() + "(" + list(op->getOperands()) + ")";
    out << "let " << name(op->getResult(0))
        << " := " << mask(op->getResult(0).getType(), expression) << "\n";
    return success();
  }
  return refuse(op, "unsupported target operation");
}

LogicalResult Exporter::block(Block &body, bool terminator) {
  for (Operation &op : body) {
    if (!terminator && op.hasTrait<OpTrait::IsTerminator>())
      break;
    if (failed(operation(&op)))
      return failure();
  }
  return success();
}
LogicalResult Exporter::function(func::FuncOp function) {
  if (!llvm::hasSingleElement(function.getBody()))
    return refuse(function, "unstructured function body");
  returns.clear();
  out << "function " << function.getName() << "("
      << list(function.getArguments()) << ")";
  if (function.getNumResults()) {
    out << " -> ";
    for (unsigned i = 0; i < function.getNumResults(); ++i) {
      if (i)
        out << ", ";
      returns.push_back(fresh());
      out << returns.back();
    }
  }
  out << " {\n";
  if (failed(block(function.getBody().front(), true)))
    return failure();
  out << "}\n";
  return success();
}

LogicalResult Exporter::outer(func::FuncOp function) {
  const bool hasTranscript = !policy.suite.empty();
  if (endpoint.transcript != hasTranscript)
    return refuse(function, "endpoint differs from managed transcript policy");
  if (hasTranscript) {
    auto realized =
        realizeTranscript(layouts, *module.getContext(), policy.suite);
    if (!realized)
      return refuse(function, "unsupported checked construction policy: " +
                                  toString(realized.takeError()));
    realizedSuite = *realized;
  }
  if (!policy.construction.empty() ||
      (!hasTranscript && (!policy.services.empty() || !policy.draws.empty() ||
                          !policy.gates.empty())) ||
      policy.format != protocol::ProofFormat::Native)
    return refuse(function, "unsupported checked construction policy");
  // The endpoint's checked schemas, expanded to the target's lanes.
  SmallVector<Type> inputs, outputs;
  for (const auto &input : endpoint.publicInputs) {
    auto layout = layouts.get(input.type);
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(function, "unsupported public layout");
    }
    append_range(inputs, (*layout)->lanes);
  }
  unsigned acceptance = 0;
  for (auto [i, type] : enumerate(endpoint.results)) {
    auto layout = layouts.get(type);
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(function, "unsupported or affine data result");
    }
    if (i == endpoint.acceptance)
      acceptance = outputs.size();
    append_range(outputs, (*layout)->lanes);
  }
  unsigned generation = outputs.size();
  if (hasTranscript) {
    inputs.push_back(IntegerType::get(module.getContext(), 64));
    outputs.push_back(IntegerType::get(module.getContext(), 64));
  }
  if (function.getArgumentTypes() != ArrayRef<Type>(inputs) ||
      function.getResultTypes() != ArrayRef<Type>(outputs))
    return refuse(function,
                  "expanded endpoint signature differs from logical lanes");
  const std::string *prefix = &endpoint.rootPrefix;
  if (prefix->size() + 18 > limits.rootBytes)
    return refuse(
        function,
        "[evm.root-limit] static invocation root exceeds deployment ceiling");
  out << "if callvalue() { evm_decode(7) }\n"
      << "if gt(calldatasize(), " << limits.calldataBytes
      << ") { evm_resource(10) }\n"
      << "if lt(calldatasize(), 100) { evm_decode(7) }\n"
      << "if iszero(eq(shr(224, calldataload(0)), 0x@SELECTOR@)) { "
         "evm_decode(7) }\n"
      << "if iszero(eq(calldataload(4), 96)) { evm_decode(8) }\n"
      << "let count := calldataload(100)\n"
      << "if iszero(eq(count, " << endpoint.publicInputs.size()
      << ")) { evm_decode(9) }\n"
      << "evm_calldata(132, mul(count, 32))\n"
      << "let root := evm_alloc(" << limits.rootBytes << ")\n";
  copyStatic(*prefix, "root");
  out << "let rootEnd := evm_tree_header(add(root, " << prefix->size()
      << "), 1, count)\n"
      << "let next := add(132, mul(count, 32))\nlet publicBytes := 0\n";
  SmallVector<std::string> arguments;
  unsigned index = 0;
  for (const auto &input : endpoint.publicInputs) {
    Type type = input.type;
    auto decoder = wire.decoder(type);
    if (!decoder) {
      auto reason = toString(decoder.takeError());
      return refuse(function, reason);
    }
    auto layout = layouts.get(type);
    if (!layout) {
      consumeError(layout.takeError());
      return refuse(function, "unsupported public layout");
    }
    const std::string *rowPrefix = &input.rowPrefix;
    // Each dynamic element head is relative to the element-head base 132.
    out << "if iszero(eq(calldataload(" << 132 + 32 * index
        << "), sub(next, 132))) { evm_decode(8) }\n"
        << "let public_" << index << ", public_length_" << index << ", next_"
        << index << " := evm_abi_tail(next, " << limits.frameBytes << ")\n"
        << "next := next_" << index << "\n"
        << "publicBytes := add(publicBytes, public_length_" << index << ")\n"
        << "if gt(publicBytes, " << limits.publicBytes
        << ") { evm_resource(11) }\n";
    out << "let ";
    for (unsigned lane = 0; lane < (*layout)->lanes.size(); ++lane) {
      if (lane)
        out << ", ";
      std::string argument =
          "input_" + std::to_string(index) + "_" + std::to_string(lane);
      out << argument;
      arguments.push_back(argument);
    }
    out << " := " << *decoder << "(public_" << index << ", public_length_"
        << index << ")\n"
        << "if gt(add(sub(rootEnd, root), add(" << rowPrefix->size() + 9
        << ", mul(public_length_" << index << ", 2))), " << limits.rootBytes
        << ") { evm_resource(12) }\n";
    copyStatic(*rowPrefix, "rootEnd");
    out << "rootEnd := evm_tree_hex(add(rootEnd, " << rowPrefix->size()
        << "), public_" << index << ", public_length_" << index << ")\n";
    ++index;
  }
  out << "if iszero(eq(calldataload(36), sub(next, 4))) { evm_decode(8) }\n"
      << "let context, contextLength, contextNext := evm_abi_tail(next, "
      << limits.contextBytes << ")\n"
      << "next := contextNext\n"
      << "if gt(add(sub(rootEnd, root), add(9, mul(contextLength, 2))), "
      << limits.rootBytes << ") { evm_resource(12) }\n"
      << "rootEnd := evm_tree_hex(rootEnd, context, contextLength)\n"
      << "if iszero(eq(calldataload(68), sub(next, 4))) { evm_decode(8) }\n"
      << "let proof, proofLength, proofNext := evm_abi_tail(next, "
      << limits.proofBytes << ")\n"
      << "if iszero(eq(proofNext, calldatasize())) { evm_decode(10) }\n"
      << "if lt(proofLength, 40) { evm_decode(11) }\n"
      << "if iszero(eq(shr(192, mload(proof)), 0x5a4b435052463030)) { "
         "evm_decode(11) }\n"
      << "let binding := evm_sha256(root, sub(rootEnd, root))\n"
      << "if iszero(eq(mload(add(proof, 8)), binding)) { evm_decode(12) }\n"
      << "mstore(0x140, add(proof, 40)) mstore(0x160, add(proof, "
         "proofLength))\n"
      << "let rootScope := evm_alloc(64) mstore(rootScope, 0)\n"
      << "mstore(0x80, rootScope) mstore(0x1e0, rootScope)\n";
  if (hasTranscript) {
    out << "mstore(0xa0, rootScope) mstore(0xc0, 0) mstore(0xe0, 0) "
           "mstore(0x100, "
        << limits.transcriptTransitions << ")\n";
    // Bind the complete invocation tree, not just its SHA256 digest.
    std::string bindPrefix = "zkc.hash-chain.bind/0";
    bindPrefix.push_back('\0');
    auto frame = [&](uint8_t tag, StringRef label, StringRef bytes) {
      bindPrefix.push_back(tag);
      for (int shift = 56; shift >= 0; shift -= 8)
        bindPrefix.push_back(
            static_cast<char>(uint64_t(label.size()) >> shift));
      bindPrefix += label;
      for (int shift = 56; shift >= 0; shift -= 8)
        bindPrefix.push_back(
            static_cast<char>(uint64_t(bytes.size()) >> shift));
      bindPrefix += bytes;
    };
    frame(0, "domain", "zkc.artifact/0");
    frame(0, "suite", policy.suite);
    bindPrefix.push_back(1);
    for (int shift = 56; shift >= 0; shift -= 8)
      bindPrefix.push_back(static_cast<char>(uint64_t(7) >> shift));
    bindPrefix += "binding";
    out << "{\nlet input := evm_alloc(add(" << bindPrefix.size() + 8
        << ", sub(rootEnd, root)))\n";
    copyStatic(bindPrefix, "input");
    out << "mstore(add(input, " << bindPrefix.size()
        << "), shl(192, sub(rootEnd, root)))\n"
        << "mcopy(add(input, " << bindPrefix.size() + 8
        << "), root, sub(rootEnd, root))\n"
        << "let boundState := keccak256(input, add(" << bindPrefix.size() + 8
        << ", sub(rootEnd, root)))\nverbatim_1i_0o(hex\"50\", boundState)\n"
        << "mstore(0x120, boundState)\nmstore(0x40, input)\n}\n";
  }
  if (hasTranscript)
    arguments.push_back("0"); // The actual internally issued generation.
  if (function.getNumArguments() != arguments.size())
    return refuse(function, "decoded public inputs differ from endpoint lanes");
  SmallVector<std::string> results;
  out << "let ";
  for (unsigned i = 0; i < function.getNumResults(); ++i) {
    if (i)
      out << ", ";
    results.push_back(fresh());
    out << results.back();
  }
  out << " := " << function.getName() << "(";
  for (auto [i, argument] : enumerate(arguments)) {
    if (i)
      out << ", ";
    out << argument;
  }
  out << ")\n"
      << "if iszero(eq(mload(0x140), mload(0x160))) { evm_decode(13) }\n";
  if (hasTranscript)
    out << "if iszero(eq(" << results[generation]
        << ", mload(0xc0))) { evm_fault(5) }\n";
  if (hasTranscript)
    out << "if iszero(eq(mload(0xa0), rootScope)) { evm_fault(5) }\n";
  out << "if iszero(eq(mload(0x80), rootScope)) { evm_fault(5) }\n"
      << "mstore(0, " << results[acceptance] << ") return(0, 32)\n";
  return success();
}

Expected<std::string> Exporter::run() {
  if (failed(checkTarget(module)))
    return zkc::error("evm.target-legality",
                      "Yul export requires a fully legal target");
  func::FuncOp entry;
  for (auto function : module.getOps<func::FuncOp>())
    if (function->hasAttr("evm.entry")) {
      if (entry)
        return zkc::error("evm.entry", "multiple EVM entry functions");
      entry = function;
    }
  if (!entry)
    return zkc::error("evm.entry", "missing EVM entry function");
  out << "object \"Verifier\" {\ncode {\n"
      << "datacopy(0, dataoffset(\"Runtime\"), datasize(\"Runtime\"))\n"
      << "return(0, datasize(\"Runtime\"))\n}\nobject \"Runtime\" {\ncode {\n"
      << "{\n"
      << "let allocationBase := memoryguard(0x400)\n"
      << "mstore(0x40, allocationBase) mstore(0x200, allocationBase)\n";
  if (failed(outer(entry)))
    return zkc::error("evm.yul",
                      "could not emit canonical invocation boundary");
  out << "}\n";
  out << detail::runtimeHelpers(
      limits, realizedSuite ? &realizedSuite->challenge->modulus : nullptr);
  for (auto function : module.getOps<func::FuncOp>())
    if (failed(this->function(function)))
      return zkc::error("evm.yul", "could not emit target function");
  out << arithmetic.helpers() << wire.definitions();
  out << "}\n";
  for (const auto &item : data)
    out << "data \"" << item.name << "\" hex\"" << toHex(item.bytes, true)
        << "\"\n";
  out << "}\n}\n";
  // The installed target declaration states the selector, and its validators
  // check it against the Keccak-256 of the declared signature.
  const std::string marker = "@SELECTOR@";
  size_t at = text.find(marker);
  if (at != std::string::npos)
    text.replace(at, marker.size(), evm_target::abiSelector);
  return std::move(text);
}
} // namespace

Expected<EvmEndpoint>
describeEndpoint(FunctionType logical, ArrayRef<uint64_t> inputPorts,
                 ArrayRef<uint64_t> outputPorts, const json::Value &descriptor,
                 const NativeProofPolicy &policy, StringRef originalSha256) {
  auto refuse = [](const Twine &reason) {
    return zkc::error("evm.endpoint", reason);
  };
  const auto *descriptorRows = descriptor.getAsArray();
  const auto *rows = descriptorRows && descriptorRows->size() == 9
                         ? (*descriptorRows)[4].getAsArray()
                         : nullptr;
  if (!logical || !rows ||
      (*descriptorRows)[0].getAsString() != "zkc.native-proof-descriptor/0" ||
      (*descriptorRows)[1] != encodeNativeProofPolicy(policy))
    return refuse("invalid descriptor or checked construction policy");
  EvmEndpoint endpoint;
  endpoint.transcript = !policy.suite.empty();
  const unsigned capabilities = endpoint.transcript;
  if (inputPorts.size() != rows->size() ||
      logical.getNumInputs() != rows->size() + capabilities ||
      logical.getNumResults() != outputPorts.size() + capabilities)
    return refuse("unconsumed endpoint inputs or affine results");
  auto transcriptType = [&](Type type) {
    auto capability = dyn_cast<runtime::CapabilityType>(type);
    return capability &&
           capability.getKind() == runtime::CapabilityKind::Transcript &&
           capability.getIdentity() == policy.suite;
  };
  if (endpoint.transcript && (!transcriptType(logical.getInputs().back()) ||
                              !transcriptType(logical.getResults().back())))
    return refuse("endpoint differs from managed transcript policy");
  NativeLayouts layouts(*logical.getContext());
  // Each checked row names the validator, the projected original port and
  // the endpoint input's nominal type; its codec is the construction's.
  for (auto [i, value] : enumerate(*rows)) {
    Type type = logical.getInput(i);
    if (auto layout = layouts.get(type); !layout)
      return layout.takeError();
    auto neutral = protocol::encodeBoundType(type, false);
    if (!neutral) {
      consumeError(neutral.takeError());
      return refuse("cannot export complete endpoint public type");
    }
    auto *row = value.getAsArray();
    if (!row || row->size() != 4 ||
        (*row)[0].getAsString() != StringRef(policy.validator) ||
        (*row)[1].getAsString() != StringRef(std::to_string(inputPorts[i])) ||
        (*row)[2].getAsString() != StringRef(neutral->spelling()) ||
        !(*row)[3].getAsString())
      return refuse("public row differs from the endpoint's checked port");
    // The four-element public row: the value bytes follow.
    auto prefix = encodeLogicalTreePrefix(
        json::Array{(*row)[0], (*row)[1], (*row)[2]}, 4);
    if (!prefix)
      return prefix.takeError();
    endpoint.publicInputs.push_back({type, std::move(*prefix)});
  }
  std::optional<unsigned> acceptance;
  for (auto [i, port] : enumerate(outputPorts)) {
    if (i && outputPorts[i - 1] >= port)
      return refuse("output projection is not in canonical source order");
    Type type = logical.getResult(i);
    if (port == policy.acceptance) {
      if (acceptance || !type.isSignlessInteger(1))
        return refuse("selected acceptance is not one Boolean");
      acceptance = i;
    }
    if (auto layout = layouts.get(type); !layout) {
      consumeError(layout.takeError());
      return refuse("unsupported or affine data result");
    }
    endpoint.outputs.push_back(port);
    endpoint.results.push_back(type);
  }
  if (!acceptance)
    return refuse("selected acceptance is absent from endpoint");
  endpoint.acceptance = *acceptance;
  json::Array root{"zkc.native-proof-binding/0",
                   "sha256",
                   (*descriptorRows)[2],
                   originalSha256,
                   policy.entry,
                   policy.producer,
                   policy.validator,
                   descriptor};
  // The ten-element root: the public rows and the context follow the eight
  // static elements.
  auto prefix = encodeLogicalTreePrefix(root, 10);
  if (!prefix)
    return prefix.takeError();
  endpoint.rootPrefix = std::move(*prefix);
  return endpoint;
}

Expected<EvmEndpoint> describeEndpoint(const CheckedEndpoint &checked,
                                       const json::Value &descriptor,
                                       const NativeProofPolicy &policy,
                                       StringRef originalSha256) {
  auto refuse = [](const Twine &reason) {
    return zkc::error("evm.endpoint", reason);
  };
  auto source = checked.sourceSnapshot();
  auto candidate = checked.candidateSnapshot();
  SmallVector<protocol_ir::ParticipantOp> participants;
  candidate->walk(
      [&](protocol_ir::ParticipantOp op) { participants.push_back(op); });
  if (participants.size() != 1 ||
      participants.front().getRole() != policy.validator)
    return refuse("expected exactly one selected validator endpoint");
  auto participant = participants.front();
  // The checked projection record assigns one participant to each role of
  // the participant's instance; its ports are the validator's original ports.
  auto ports = [](DictionaryAttr record,
                  StringRef key) -> std::optional<SmallVector<uint64_t>> {
    auto values = record.getAs<ArrayAttr>(key);
    if (!values)
      return std::nullopt;
    SmallVector<uint64_t> result;
    for (Attribute value : values) {
      auto port = dyn_cast<IntegerAttr>(value);
      if (!port || port.getInt() < 0)
        return std::nullopt;
      result.push_back(port.getUInt());
    }
    return result;
  };
  unsigned matches = 0;
  std::optional<SmallVector<uint64_t>> inputs, outputs;
  source->walk([&](protocol_ir::ProjectionOp record) {
    for (Attribute item : record.getInterfaces()) {
      auto interface = dyn_cast<DictionaryAttr>(item);
      auto roles =
          interface ? interface.getAs<ArrayAttr>("participants") : ArrayAttr();
      if (!roles || interface.get("source") != participant.getInstanceAttr())
        continue;
      for (Attribute role : roles) {
        auto mapping = dyn_cast<DictionaryAttr>(role);
        if (!mapping || mapping.get("role") != participant.getRoleAttr())
          continue;
        ++matches;
        inputs = ports(mapping, "inputs");
        outputs = ports(mapping, "outputs");
      }
    }
  });
  if (matches != 1 || !inputs || !outputs)
    return refuse("no checked projection of the selected endpoint");
  return describeEndpoint(participant.getFunctionType(), *inputs, *outputs,
                          descriptor, policy, originalSha256);
}

Expected<std::string> exportYul(ModuleOp module, const EvmEndpoint &endpoint,
                                const NativeProofPolicy &policy,
                                const EvmLimits &limits) {
  return Exporter(module, endpoint, policy, limits).run();
}
} // namespace zkc::evm
