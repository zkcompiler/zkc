#include "MathematicalSupport.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
bool isCalculationContract(StringRef contract) {
  return is_contained(
      ArrayRef<StringRef>{
          "field.constant",   "field.add",       "field.sub",
          "field.mul",        "field.equal",     "curve.add",
          "curve.scale",      "curve.equal",     "curve.length",
          "pairing.apply",    "field_array.at",  "field_array.from_vector",
          "vector.empty",     "vector.append",   "vector.length",
          "matrix.dimension", "indices.length",  "index.constant",
          "index.equal",      "index.less",      "sequence.empty",
          "sequence.append",  "sequence.length", "bool.and",
          "bool.or",          "bool.not"},
      contract);
}
namespace {
// Names are allocated over the entire isolated symbol table, including retained
// relation declarations and authored executable definitions.
class BindingSymbols {
  protocol_ir::ProtocolModuleOp unit;
  llvm::StringSet<> names;
  unsigned next = 0;
  struct Occurrences {
    llvm::StringSet<> names;
    unsigned next = 0;
  };
  llvm::DenseMap<Operation *, std::unique_ptr<Occurrences>> occurrences;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;

public:
  explicit BindingSymbols(protocol_ir::ProtocolModuleOp unit) : unit(unit) {
    for (auto &op : unit.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  std::string fresh() {
    std::string result;
    do {
      result = "_calculation_" + std::to_string(next++);
    } while (!names.insert(result).second);
    return result;
  }
  std::string freshSite(local::FuncOp function, StringRef prefix) {
    auto &sites = occurrences[function];
    if (!sites) {
      sites = std::make_unique<Occurrences>();
      function.walk([&](Operation *op) {
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          sites->names.insert(site.getValue());
      });
    }
    // Preserve the readable base when available (including guard trace sites).
    // Recipe roots already occupy their base, so intermediates use suffixes.
    if (sites->names.insert(prefix).second)
      return prefix.str();
    std::string result;
    do {
      result = (prefix + "_recipe_" + Twine(sites->next++)).str();
    } while (!sites->names.insert(result).second);
    return result;
  }
  FlatSymbolRefAttr get(protocol::BindingApplication application,
                        Location location, OpBuilder &builder) {
    assert(isCalculationContract(application.contract) &&
           "mathematical recipe contract is outside the closed vocabulary");
    auto key = std::make_pair(application.contract, application.arguments);
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      auto name = fresh();
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(&unit.getBody().front());
      SmallVector<Attribute> arguments;
      for (auto &argument : application.arguments)
        arguments.push_back(builder.getStringAttr(argument));
      local::OperationBindingOp::create(builder, location, name,
                                        application.contract,
                                        builder.getArrayAttr(arguments), "");
      found = bindings.emplace(std::move(key), name).first;
    }
    return FlatSymbolRefAttr::get(builder.getContext(), found->second);
  }
};

// Execution recipes belong to lowering; the IR exposes mathematical identity
// and dependencies without selecting an executable contract.
protocol::BindingApplication algebraBinding(Operation *op) {
  protocol::BindingApplication result;
  if (isa<zkc::algebra::SubtractFieldOp>(op))
    result.contract = "field.sub";
  if (isa<zkc::algebra::FieldAddOp>(op))
    result.contract = "field.add";
  if (isa<zkc::algebra::FieldMultiplyOp>(op))
    result.contract = "field.mul";
  if (isa<zkc::algebra::FieldEqualOp>(op))
    result.contract = "field.equal";
  if (isa<zkc::algebra::GroupAddOp>(op))
    result.contract = "curve.add";
  if (isa<zkc::algebra::GroupScaleOp>(op))
    result.contract = "curve.scale";
  if (isa<zkc::algebra::GroupEqualOp>(op))
    result.contract = "curve.equal";
  if (isa<zkc::algebra::PairingOp>(op)) {
    result.contract = "pairing.apply";
    auto group = cast<zkc::algebra::GroupType>(op->getOperand(0).getType());
    result.arguments = {protocol::installedDomains()
                            .associatedIdentity(group.getDomain(), "Scalar")
                            .str()};
    return result;
  }
  if (result.contract.empty() || op->getNumOperands() == 0)
    return result;
  if (auto t = dyn_cast<zkc::algebra::FieldType>(op->getOperand(0).getType()))
    result.arguments = {t.getDomain().str()};
  if (auto t = dyn_cast<zkc::algebra::GroupType>(op->getOperand(0).getType()))
    result.arguments = {t.getDomain().str()};
  return result;
}
// Every illegal total expression must be consumed by a checked recipe. The
// conversion target rejects any leftover expression or guard in the candidate.
class Recipe : public ConversionPattern {
  BindingSymbols &symbols;

public:
  Recipe(MLIRContext *context, BindingSymbols &symbols)
      : ConversionPattern(MatchAnyOpTypeTag(), 1, context), symbols(symbols) {}
  LogicalResult
  matchAndRewrite(Operation *op, ArrayRef<Value> inputs,
                  ConversionPatternRewriter &rewriter) const override {
    // Conversion disables pattern rollback. Each recipe must finish all
    // refusal checks before allocating sites/bindings or changing IR; after
    // its first mutation, rewriting is infallible.
    if (!isTotal(op) && !isa<local::GuardOp>(op))
      return failure();
    if (!op->getParentOfType<local::FuncOp>())
      return rewriter.notifyMatchFailure(
          op, "recipe requires an outlined local function");
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!site)
      return rewriter.notifyMatchFailure(op, "missing generated occurrence");
    if (isa<data::SequenceEmptyOp, data::SequenceAppendOp,
            data::SequenceLengthOp>(op)) {
      auto sequence = cast<data::SequenceType>(
          isa<data::SequenceEmptyOp>(op) ? op->getResult(0).getType()
                                         : op->getOperand(0).getType());
      auto element =
          protocol::encodeBoundType(sequence.getElementType(), false);
      if (!element) {
        llvm::consumeError(element.takeError());
        return failure();
      }
      protocol::BindingApplication application;
      application.contract = isa<data::SequenceEmptyOp>(op) ? "sequence.empty"
                             : isa<data::SequenceAppendOp>(op)
                                 ? "sequence.append"
                                 : "sequence.length";
      application.arguments = {element->spelling()};
      OperationState state(op->getLoc(),
                           protocol::boundOperationName(application.contract));
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("parameters", rewriter.getArrayAttr({}));
      state.addAttribute("binding",
                         symbols.get(application, op->getLoc(), rewriter));
      rewriter.replaceOp(op, rewriter.create(state)->getResults());
      return success();
    }
    if (auto dim = dyn_cast<data::DimOp>(op)) {
      auto tensor = dim.getInput().getType();
      auto axis = dim.getAxisAttr().getInt();
      protocol::BindingApplication application;
      SmallVector<Attribute> parameters;
      ValueRange operands = inputs;
      if (!tensor.isDynamicDim(axis)) {
        application.contract = "index.constant";
        parameters.push_back(
            rewriter.getStringAttr(std::to_string(tensor.getDimSize(axis))));
        operands = {};
      } else if (auto field =
                     dyn_cast<algebra::FieldType>(tensor.getElementType())) {
        application.contract =
            tensor.getRank() == 2 ? "matrix.dimension" : "vector.length";
        application.arguments = {field.getDomain().str()};
        if (tensor.getRank() == 2)
          parameters.push_back(rewriter.getStringAttr(std::to_string(axis)));
      } else if (auto group =
                     dyn_cast<algebra::GroupType>(tensor.getElementType())) {
        application.contract = "curve.length";
        application.arguments = {group.getDomain().str()};
      } else {
        application.contract = "indices.length";
      }
      auto name = protocol::boundOperationName(application.contract);
      if (name.empty())
        return failure();
      OperationState state(op->getLoc(), name);
      state.addOperands(operands);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("parameters", rewriter.getArrayAttr(parameters));
      state.addAttribute("binding",
                         symbols.get(application, op->getLoc(), rewriter));
      rewriter.replaceOp(op, rewriter.create(state)->getResults());
      return success();
    }
    if (isa<data::IndexOp, data::EqualOp, data::LessOp>(op)) {
      protocol::BindingApplication application;
      application.contract = isa<data::IndexOp>(op)   ? "index.constant"
                             : isa<data::EqualOp>(op) ? "index.equal"
                                                      : "index.less";
      auto name = protocol::boundOperationName(application.contract);
      if (name.empty())
        return failure();
      SmallVector<Attribute> parameters;
      if (auto constant = dyn_cast<data::IndexOp>(op))
        parameters.push_back(rewriter.getStringAttr(constant.getValue()));
      OperationState state(op->getLoc(), name);
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("parameters", rewriter.getArrayAttr(parameters));
      state.addAttribute("binding",
                         symbols.get(application, op->getLoc(), rewriter));
      rewriter.replaceOp(op, rewriter.create(state)->getResults());
      return success();
    }
    if (auto make = dyn_cast<data::MakeOp>(op)) {
      OperationState state(op->getLoc(),
                           local::VariantInjectOp::getOperationName());
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("alternative", make.getAlternativeAttr());
      rewriter.replaceOp(op, rewriter.create(state)->getResults());
      return success();
    }
    if (isa<data::GetOp, data::IsOp>(op)) {
      auto type = cast<local::VariantType>(op->getOperand(0).getType());
      auto descriptor = protocol::decodeVariant(type.getDescriptor());
      if (!descriptor)
        return failure();
      SmallVector<SmallVector<Type>> payloads;
      SmallVector<Attribute> labels;
      for (const auto &arm : descriptor->alternatives) {
        SmallVector<Type> types;
        for (const auto &spelling : arm.payload) {
          auto bound = protocol::parseBoundType(spelling, false);
          if (!bound) {
            consumeError(bound.takeError());
            return failure();
          }
          auto decoded = protocol::decodeBoundType(op->getContext(), *bound);
          if (!decoded)
            return failure();
          types.push_back(decoded);
        }
        payloads.push_back(std::move(types));
        labels.push_back(rewriter.getStringAttr(arm.label));
      }
      OperationState state(op->getLoc(),
                           local::LocalMatchOp::getOperationName());
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("alternatives", rewriter.getArrayAttr(labels));
      for (size_t i = 0; i < payloads.size(); ++i)
        state.addRegion();
      auto *match = rewriter.create(state);
      for (auto [i, types] : enumerate(payloads)) {
        OpBuilder::InsertionGuard insertion(rewriter);
        auto *body = new Block();
        match->getRegion(i).push_back(body);
        body->addArguments(types,
                           SmallVector<Location>(types.size(), op->getLoc()));
        rewriter.setInsertionPointToEnd(body);
        Value value;
        if (auto get = dyn_cast<data::GetOp>(op)) {
          value = body->getArgument(get.getIndexAttr().getInt());
        } else {
          auto label = cast<data::IsOp>(op).getAlternative();
          auto occurrence = symbols.freshSite(
              op->getParentOfType<local::FuncOp>(), site.getValue());
          value = local::BoolConstantOp::create(
                      rewriter, op->getLoc(), rewriter.getI1Type(),
                      rewriter.getBoolAttr(descriptor->alternatives[i].label ==
                                           label),
                      rewriter.getStringAttr(occurrence))
                      .getOutput();
        }
        local::LocalYieldOp::create(rewriter, op->getLoc(), ValueRange{value});
      }
      rewriter.replaceOp(op, match->getResults());
      return success();
    }
    if (isa<arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
            arith::CmpIOp, arith::SelectOp>(op)) {
      auto model = dyn_cast<MathematicalOpInterface>(op);
      auto identity = model ? model.getMathematicalIdentity() : std::nullopt;
      if (!identity)
        return rewriter.notifyMatchFailure(
            op, "missing closed arithmetic identity");
      bool supported = false;
      switch (*identity) {
      case MathematicalIdentity::BooleanConstant:
        supported = isa<arith::ConstantOp>(op);
        break;
      case MathematicalIdentity::BooleanAnd:
        supported = isa<arith::AndIOp>(op);
        break;
      case MathematicalIdentity::BooleanOr:
        supported = isa<arith::OrIOp>(op);
        break;
      case MathematicalIdentity::BooleanXor:
        supported = isa<arith::XOrIOp>(op);
        break;
      case MathematicalIdentity::BooleanEqual:
        supported =
            isa<arith::CmpIOp>(op) &&
            cast<arith::CmpIOp>(op).getPredicate() == arith::CmpIPredicate::eq;
        break;
      case MathematicalIdentity::BooleanNotEqual:
        supported =
            isa<arith::CmpIOp>(op) &&
            cast<arith::CmpIOp>(op).getPredicate() == arith::CmpIPredicate::ne;
        break;
      case MathematicalIdentity::Select:
        supported = isa<arith::SelectOp>(op);
        break;
      default:
        break;
      }
      if (!supported)
        return rewriter.notifyMatchFailure(
            op, "arithmetic identity has no lowering recipe");
    }
    if (isa<arith::SelectOp>(op)) {
      // Captures have distinct names in executable local control. Identical
      // arms share one capture, without relying on an upstream fold.
      llvm::SetVector<Value> captures;
      captures.insert(inputs[1]);
      captures.insert(inputs[2]);
      SmallVector<Value> operands{inputs[0]};
      append_range(operands, captures);
      auto select = local::LocalIfOp::create(
          rewriter, op->getLoc(), op->getResultTypes(), operands, site);
      for (auto [i, region] : enumerate(select->getRegions())) {
        OpBuilder::InsertionGuard guard(rewriter);
        auto *block = rewriter.createBlock(&region);
        for (auto value : captures)
          block->addArgument(value.getType(), op->getLoc());
        unsigned selected = std::distance(captures.begin(),
                                          llvm::find(captures, inputs[i + 1]));
        local::LocalYieldOp::create(rewriter, op->getLoc(),
                                    ValueRange{block->getArgument(selected)});
      }
      rewriter.replaceOp(op, select.getResults());
      return success();
    }
    if (isa<local::GuardOp>(op)) {
      // Protocol rejection is an explicit control outcome. The installed
      // control.require binding reports a backend failure on false, so that
      // binding is not a semantics-preserving recipe for this source guard.
      auto controlSite = symbols.freshSite(op->getParentOfType<local::FuncOp>(),
                                           "guard_control");
      auto branch = local::LocalIfOp::create(rewriter, op->getLoc(),
                                             TypeRange{}, inputs, controlSite);
      {
        OpBuilder::InsertionGuard insertion(rewriter);
        rewriter.createBlock(&branch.getThenRegion());
        local::LocalYieldOp::create(rewriter, op->getLoc(), ValueRange{});
      }
      {
        OpBuilder::InsertionGuard insertion(rewriter);
        rewriter.createBlock(&branch.getElseRegion());
        local::StopOp::create(rewriter, op->getLoc(), site.getValue(),
                              "reject");
      }
      rewriter.eraseOp(op);
      return success();
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      auto attribute = dyn_cast<IntegerAttr>(constant.getValue());
      if (!attribute || !attribute.getType().isSignlessInteger(1) ||
          !constant.getType().isSignlessInteger(1))
        return rewriter.notifyMatchFailure(op,
                                           "expected scalar Boolean constant");
      auto value = attribute.getValue().getBoolValue();
      auto literal = local::BoolConstantOp::create(
          rewriter, op->getLoc(), rewriter.getI1Type(), value, site.getValue());
      rewriter.replaceOp(op, literal.getResult());
      return success();
    }
    if (isa<arith::AndIOp, arith::OrIOp, arith::XOrIOp, arith::CmpIOp>(op)) {
      if (!op->getResult(0).getType().isSignlessInteger(1) ||
          !all_of(inputs, [](Value value) {
            return value.getType().isSignlessInteger(1);
          }))
        return rewriter.notifyMatchFailure(op,
                                           "expected scalar Boolean operands");
      for (StringRef contract : {"bool.and", "bool.or", "bool.not"})
        if (protocol::boundOperationName(contract).empty())
          return rewriter.notifyMatchFailure(
              op, "missing Boolean execution binding");
      auto emit = [&](StringRef contract, ValueRange operands,
                      bool last) -> Value {
        std::string occurrence = site.getValue().str();
        if (!last)
          occurrence = symbols.freshSite(op->getParentOfType<local::FuncOp>(),
                                         site.getValue());
        protocol::BindingApplication application;
        application.contract = contract.str();
        OperationState state(op->getLoc(),
                             protocol::boundOperationName(contract));
        state.addOperands(operands);
        state.addTypes(rewriter.getI1Type());
        state.addAttribute("site", rewriter.getStringAttr(occurrence));
        state.addAttribute("parameters", rewriter.getArrayAttr({}));
        state.addAttribute("binding",
                           symbols.get(application, op->getLoc(), rewriter));
        return rewriter.create(state)->getResult(0);
      };
      Value result;
      if (isa<arith::AndIOp, arith::OrIOp>(op))
        result =
            emit(isa<arith::AndIOp>(op) ? "bool.and" : "bool.or", inputs, true);
      else {
        bool equal =
            isa<arith::CmpIOp>(op) &&
            cast<arith::CmpIOp>(op).getPredicate() == arith::CmpIPredicate::eq;
        auto disjunction = emit("bool.or", inputs, false);
        auto conjunction = emit("bool.and", inputs, false);
        auto inverse = emit("bool.not", ValueRange{conjunction}, false);
        result = emit("bool.and", ValueRange{disjunction, inverse}, !equal);
        if (equal)
          result = emit("bool.not", ValueRange{result}, true);
      }
      rewriter.replaceOp(op, result);
      return success();
    }
    if (isa<algebra::ConstantFieldOp, algebra::ArrayAtOp,
            tensor::FromElementsOp>(op)) {
      // Formation has established exact finite shapes and canonical literals.
      // Check the complete recipe vocabulary before making any mutation.
      for (StringRef contract :
           {"field.constant", "field_array.at", "field_array.from_vector",
            "vector.empty", "vector.append"})
        if (protocol::boundOperationName(contract).empty())
          return failure();
      auto emit = [&](StringRef contract, ArrayRef<std::string> arguments,
                      ValueRange operands, Type output,
                      ArrayRef<std::string> parameters, bool last) -> Value {
        auto occurrence =
            last ? site.getValue().str()
                 : symbols.freshSite(op->getParentOfType<local::FuncOp>(),
                                     site.getValue());
        protocol::BindingApplication application{
            contract.str(),
            std::vector<std::string>(arguments.begin(), arguments.end()),
            {}};
        OperationState state(op->getLoc(),
                             protocol::boundOperationName(contract));
        state.addOperands(operands);
        state.addTypes(output);
        state.addAttribute("site", rewriter.getStringAttr(occurrence));
        SmallVector<Attribute> attrs;
        for (const auto &parameter : parameters)
          attrs.push_back(rewriter.getStringAttr(parameter));
        state.addAttribute("parameters", rewriter.getArrayAttr(attrs));
        state.addAttribute("binding",
                           symbols.get(application, op->getLoc(), rewriter));
        return rewriter.create(state)->getResult(0);
      };
      Value result;
      if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
        auto field = constant.getResult().getType().getDomain().str();
        result =
            emit("field.constant", {field}, {}, constant.getResult().getType(),
                 {constant.getValue().str()}, true);
      } else if (auto at = dyn_cast<algebra::ArrayAtOp>(op)) {
        auto array = at.getArray().getType();
        auto field =
            cast<algebra::FieldType>(array.getElementType()).getDomain().str();
        result =
            emit("field_array.at", {field, std::to_string(array.getDimSize(0))},
                 inputs, at.getResult().getType(),
                 {std::to_string(at.getIndexAttr().getInt())}, true);
      } else {
        auto array = cast<RankedTensorType>(op->getResult(0).getType());
        auto field =
            cast<algebra::FieldType>(array.getElementType()).getDomain().str();
        auto vector = RankedTensorType::get({ShapedType::kDynamic},
                                            array.getElementType());
        result = emit("vector.empty", {field}, {}, vector, {}, false);
        for (auto value : inputs)
          result = emit("vector.append", {field}, ValueRange{result, value},
                        vector, {}, false);
        result = emit("field_array.from_vector",
                      {field, std::to_string(array.getDimSize(0))},
                      ValueRange{result}, array, {}, true);
      }
      rewriter.replaceOp(op, result);
      return success();
    }
    auto application = algebraBinding(op);
    auto name = protocol::boundOperationName(application.contract);
    if (application.contract.empty() || name.empty())
      return rewriter.notifyMatchFailure(
          op, "no execution recipe for this operation");
    auto reference = symbols.get(application, op->getLoc(), rewriter);
    OperationState state(op->getLoc(), name);
    state.addOperands(inputs);
    state.addTypes(op->getResultTypes());
    state.addAttribute("site", site);
    state.addAttribute("parameters", rewriter.getArrayAttr({}));
    state.addAttribute("binding", reference);
    auto *result = rewriter.create(state);
    rewriter.replaceOp(op, result->getResults());
    return success();
  }
};

class Outliner {
  protocol_ir::ProtocolModuleOp unit;
  BindingSymbols &symbols;
  OpBuilder builder;
  SmallVector<Attribute> calculations;

  LogicalResult participant(protocol_ir::ParticipantOp participant) {
    llvm::StringSet<> sites;
    participant.walk([&](Operation *op) {
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        sites.insert(site.getValue());
    });
    unsigned nextSite = 0;
    return block(participant, participant.getBody().front(), sites, nextSite);
  }
  LogicalResult block(protocol_ir::ParticipantOp participant, Block &body,
                      llvm::StringSet<> &sites, unsigned &nextSite) {
    llvm::DenseMap<Operation *, unsigned> order;
    unsigned ordinal = 0;
    for (auto &op : body)
      order[&op] = ordinal++;
    SmallVector<Operation *> cuts;
    for (auto &op : body)
      if (!isTotal(&op))
        cuts.push_back(&op);
    IRMapping computed;
    auto updateOperands = [&](Operation *cut) {
      for (auto &operand : cut->getOpOperands())
        operand.set(computed.lookupOrDefault(operand.get()));
    };
    for (auto *cut : cuts) {
      if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(cut))
        if (failed(block(participant, loop.getBody().front(), sites, nextSite)))
          return failure();
      // Collect only work demanded at this cut. Already computed values are
      // ordinary participant SSA call results and stop this backwards walk.
      llvm::DenseSet<Operation *> needed;
      SmallVector<Operation *> operations;
      SmallVector<Value> pending(cut->operand_begin(), cut->operand_end());
      while (!pending.empty()) {
        auto value = pending.pop_back_val();
        if (computed.contains(value))
          continue;
        auto *definition = value.getDefiningOp();
        if (!definition || !isTotal(definition) ||
            !needed.insert(definition).second)
          continue;
        operations.push_back(definition);
        auto dependencies = operandDependencies(
            definition, cast<OpResult>(value).getResultNumber());
        if (failed(dependencies))
          return failure();
        for (auto index : *dependencies)
          pending.push_back(definition->getOperand(index));
      }
      auto guard = dyn_cast<local::GuardOp>(cut);
      if (needed.empty() && !guard) {
        updateOperands(cut);
        continue;
      }
      llvm::sort(operations, [&](Operation *lhs, Operation *rhs) {
        return order.lookup(lhs) < order.lookup(rhs);
      });
      llvm::SetVector<Value> captures;
      SmallVector<Value> results;
      for (auto *op : operations) {
        for (auto value : op->getOperands())
          if (!needed.count(value.getDefiningOp()))
            captures.insert(value);
        for (auto value : op->getResults())
          if (any_of(value.getUsers(), [&](Operation *user) {
                return !needed.count(user) && (!guard || user != cut);
              }))
            results.push_back(value);
      }
      if (guard && !needed.count(guard.getCondition().getDefiningOp()))
        captures.insert(guard.getCondition());
      SmallVector<Type> inputTypes, resultTypes;
      for (auto value : captures)
        inputTypes.push_back(value.getType());
      for (auto value : results)
        resultTypes.push_back(value.getType());
      builder.setInsertionPoint(participant);
      auto function = local::FuncOp::create(
          builder, cut->getLoc(), symbols.fresh(),
          builder.getFunctionType(inputTypes, resultTypes));
      function->setAttr(
          "logical_origin",
          builder.getArrayAttr({builder.getStringAttr(function.getSymName()),
                                builder.getArrayAttr({})}));
      auto *entry = function.addEntryBlock();
      builder.setInsertionPointToEnd(entry);
      IRMapping mapping;
      for (auto [value, argument] : zip(captures, entry->getArguments()))
        mapping.map(value, argument);
      unsigned occurrence = 0;
      for (auto *op : operations) {
        auto *copy = builder.clone(*op, mapping);
        std::string occurrenceSite;
        do {
          occurrenceSite = "value_" + std::to_string(occurrence++);
        } while (guard && occurrenceSite == guard.getSite());
        copy->setAttr("site", builder.getStringAttr(occurrenceSite));
      }
      if (guard)
        builder.clone(*guard, mapping);
      SmallVector<Value> returned;
      for (auto value : results)
        returned.push_back(mapping.lookup(value));
      local::ReturnOp::create(builder, cut->getLoc(), returned);
      std::string site;
      if (guard)
        site = guard.getSite().str();
      else {
        do {
          site = "calculation_" + std::to_string(nextSite++);
        } while (!sites.insert(site).second);
      }
      builder.setInsertionPoint(cut);
      SmallVector<Value> arguments;
      for (auto value : captures)
        arguments.push_back(computed.lookupOrDefault(value));
      auto call = local::CallOp::create(builder, cut->getLoc(), resultTypes,
                                        arguments, function.getSymName(), site);
      calculations.push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr(
               "participant", FlatSymbolRefAttr::get(builder.getContext(),
                                                     participant.getSymName())),
           builder.getNamedAttr("callee", call.getCalleeAttr()),
           builder.getNamedAttr("site", call.getSiteAttr())}));
      for (auto [old, replacement] : zip(results, call.getResults()))
        computed.map(old, replacement);
      if (guard)
        guard.erase();
      else
        updateOperands(cut);
      // Keep original total definitions until all cuts have been rewritten.
      // Replacing their earlier uses with this later call result would create
      // a transient dominance violation. Later slices use the explicit map.
    }
    // Original admission happened before DCE. Any remaining total expressions
    // are unobserved and can be removed without creating physical work.
    for (auto &op : make_early_inc_range(reverse(body)))
      if (isTotal(&op) && op.use_empty())
        op.erase();
    return success();
  }

public:
  Outliner(protocol_ir::ProtocolModuleOp unit, BindingSymbols &symbols)
      : unit(unit), symbols(symbols), builder(unit.getContext()) {}
  LogicalResult run() {
    SmallVector<protocol_ir::ParticipantOp> participants;
    for (auto value :
         unit.getBody().front().getOps<protocol_ir::ParticipantOp>())
      participants.push_back(value);
    for (auto value : participants)
      if (failed(participant(value)))
        return failure();
    auto records = unit.getBody().front().getOps<protocol_ir::ProjectionOp>();
    if (records.empty())
      return diagnostics::emit(
          unit.emitError(), "mathematical-lowering-profile",
          "lowering requires retained projection metadata");
    auto record = *records.begin();
    record.setCalculationsAttr(builder.getArrayAttr(calculations));
    // Dead original expressions can have kept intermediate result ports alive
    // while outlining. Remove those ports after participant DCE, without
    // removing the invocation or any executable operation in its body.
    SymbolTable outlinedSymbols(unit);
    llvm::DenseSet<Attribute> generatedCallees;
    for (auto item : calculations)
      generatedCallees.insert(cast<DictionaryAttr>(item).get("callee"));
    SmallVector<local::CallOp> calls;
    for (auto participant : participants)
      participant.walk([&](local::CallOp call) { calls.push_back(call); });
    for (auto call : calls) {
      if (!generatedCallees.contains(call.getCalleeAttr()))
        continue;
      llvm::BitVector unused(call.getNumResults());
      SmallVector<Type> types;
      for (auto [index, result] : enumerate(call.getResults())) {
        if (result.use_empty())
          unused.set(index);
        else
          types.push_back(result.getType());
      }
      if (unused.none())
        continue;
      auto function =
          cast<local::FuncOp>(outlinedSymbols.lookup(call.getCallee()));
      auto returned = cast<local::ReturnOp>(function.getBody().front().back());
      returned->eraseOperands(unused);
      function.setFunctionType(builder.getFunctionType(
          function.getFunctionType().getInputs(), types));
      builder.setInsertionPoint(call);
      auto replacement =
          local::CallOp::create(builder, call.getLoc(), types, call.getInputs(),
                                call.getCalleeAttr(), call.getSiteAttr());
      unsigned next = 0;
      for (auto [index, result] : enumerate(call.getResults()))
        if (!unused[index])
          result.replaceAllUsesWith(replacement.getResult(next++));
      call.erase();
    }
    return success();
  }
};

LogicalResult lowerRecipes(protocol_ir::ProtocolModuleOp unit,
                           const llvm::DenseSet<Operation *> &generated,
                           BindingSymbols &symbols) {
  ConversionTarget target(*unit.getContext());
  target.markUnknownOpDynamicallyLegal([&](Operation *op) {
    return !generated.contains(op->getParentOfType<local::FuncOp>()) ||
           (!isTotal(op) && !isa<local::GuardOp>(op));
  });
  RewritePatternSet patterns(unit.getContext());
  patterns.add<Recipe>(unit.getContext(), symbols);
  ConversionConfig config;
  // Lowering schedules explicit recipes. Mathematical folding belongs to
  // preparation/simplification, where generated constants have no sites yet.
  config.foldingMode = DialectConversionFoldingMode::Never;
  // Symbol/site allocation is monotone on this owned candidate. A failure
  // discards the candidate, so conversion need not roll individual recipes
  // back.
  config.allowPatternRollback = false;
  return applyFullConversion(unit, target, std::move(patterns), config);
}

struct LowerMathPass : PassWrapper<LowerMathPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(LowerMathPass)
  void getDependentDialects(DialectRegistry &registry) const final {
    registry.insert<local::LocalDialect, algebra::AlgebraDialect>();
  }
  StringRef getArgument() const final { return "zkc-lower-math"; }
  StringRef getDescription() const final {
    return "Schedule participant mathematics at first consumers and lower to "
           "complete execution recipes";
  }
  void runOnOperation() final {
    auto source = getOperation();
    if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
      return signalPassFailure();
    auto original =
        dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
    if (!original ||
        original.getProfile() != protocol_ir::Profile::Participant) {
      diagnostics::emit(source.emitError(), "mathematical-lowering-profile",
                        "expected the 'participant' profile");
      return signalPassFailure();
    }
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    BindingSymbols symbols(unit);
    if (failed(Outliner(unit, symbols).run()))
      return signalPassFailure();
    llvm::DenseSet<Operation *> generated;
    {
      SymbolTable outlinedSymbols(unit);
      auto record =
          *unit.getBody().front().getOps<protocol_ir::ProjectionOp>().begin();
      for (auto item : record.getCalculations()) {
        auto reference =
            cast<DictionaryAttr>(item).getAs<FlatSymbolRefAttr>("callee");
        generated.insert(outlinedSymbols.lookup(reference.getValue()));
      }
    }
    if (failed(lowerRecipes(unit, generated, symbols)))
      return signalPassFailure();
    unit.setProfile(protocol_ir::Profile::Exec);
    if (failed(verify(*candidate)) ||
        failed(verifyProjectionPreserved(source, *candidate)))
      return signalPassFailure();
    source->setAttrs(candidate->getOperation()->getAttrs());
    source.getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
} // namespace
LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                ArrayRef<local::FuncOp> functions) {
  BindingSymbols symbols(unit);
  llvm::DenseSet<Operation *> selected;
  for (auto function : functions)
    selected.insert(function);
  // Preserve the admitted, polynomial-free mathematical bodies for the same
  // independent recipe matcher used by participant lowering. This transient
  // candidate is not an executable module until conversion finishes.
  OwningOpRef<protocol_ir::ProtocolModuleOp> original(
      cast<protocol_ir::ProtocolModuleOp>(unit->clone()));
  if (failed(lowerRecipes(unit, selected, symbols)))
    return failure();
  return verifyCalculationRecipes(*original, unit, functions);
}
} // namespace zkc::mathematical
std::unique_ptr<mlir::Pass> zkc::protocol::createLowerMathPass() {
  return std::make_unique<mathematical::LowerMathPass>();
}
