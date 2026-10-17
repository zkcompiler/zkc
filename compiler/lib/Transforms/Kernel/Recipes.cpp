#include "../CollectionRealization.h"
#include "../MathematicalSupport.h"
#include "../RealizationTrace.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Interfaces/Collection.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Transforms/Finite.h"
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
  return is_contained(ArrayRef<StringRef>{"index.add",
                                          "index.sub",
                                          "index.mul",
                                          "index.div",
                                          "index.mod",
                                          "control.require",
                                          "vector.sum",
                                          "vector.product",
                                          "vector.dot",
                                          "vector.fill",
                                          "vector.scale",
                                          "vector.add",
                                          "vector.sub",
                                          "vector.mul",
                                          "curve.msm",
                                          "curve.empty",
                                          "curve.append",
                                          "indices.empty",
                                          "indices.append",
                                          "matrix.mul_vector",
                                          "matrix.transpose_mul_vector",
                                          "matrix.bilinear",
                                          "vector.get",
                                          "curve.get",
                                          "indices.at",
                                          "sequence.at",
                                          "field_array.get",
                                          "matrix.get",
                                          "field.constant",
                                          "field.add",
                                          "field.sub",
                                          "field.mul",
                                          "field.equal",
                                          "curve.identity",
                                          "curve.add",
                                          "curve.scale",
                                          "curve.equal",
                                          "curve.length",
                                          "pairing.apply",
                                          "field_array.at",
                                          "field_array.from_vector",
                                          "vector.empty",
                                          "vector.append",
                                          "vector.length",
                                          "matrix.dimension",
                                          "bytes.length",
                                          "indices.length",
                                          "index.constant",
                                          "index.equal",
                                          "index.less",
                                          "sequence.empty",
                                          "sequence.append",
                                          "sequence.length",
                                          "bool.and",
                                          "bool.or",
                                          "bool.not"},
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
  if (auto identity = dyn_cast<algebra::GroupIdentityOp>(op)) {
    result.contract = "curve.identity";
    result.arguments = {identity.getResult().getType().getDomain().str()};
    return result;
  }
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
// conversion target rejects any leftover total expression in the candidate.
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
    if (!isTotal(op))
      return failure();
    if (!op->getParentOfType<local::FuncOp>())
      return rewriter.notifyMatchFailure(
          op, "recipe requires an outlined local function");
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!site)
      return rewriter.notifyMatchFailure(op, "missing generated occurrence");
    if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(op)) {
      auto collection = collectionRealization(inputs[0].getType());
      if (!collection || !collection->get)
        return rewriter.notifyMatchFailure(op, "no admitted collection access");
      const auto &application = *collection->get;
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
      auto collection = cast<CollectionTypeInterface>(dim.getInput().getType());
      auto axis = dim.getAxisAttr().getInt();
      protocol::BindingApplication application;
      SmallVector<Attribute> parameters;
      ValueRange operands = inputs;
      if (auto extent = collection.getStaticExtent(axis)) {
        application.contract = "index.constant";
        parameters.push_back(rewriter.getStringAttr(std::to_string(*extent)));
        operands = {};
      } else if (auto field = dyn_cast<algebra::FieldType>(
                     collection.getElementType())) {
        application.contract =
            collection.getRank() == 2 ? "matrix.dimension" : "vector.length";
        application.arguments = {field.getDomain().str()};
        if (collection.getRank() == 2)
          parameters.push_back(rewriter.getStringAttr(std::to_string(axis)));
      } else if (auto group = dyn_cast<algebra::GroupType>(
                     collection.getElementType())) {
        application.contract = "curve.length";
        application.arguments = {group.getDomain().str()};
      } else {
        application.contract =
            collection.getCollectionKind() == CollectionKind::Bytes
                ? "bytes.length"
                : "indices.length";
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
            algebra::ArrayFromElementsOp>(op)) {
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
            emit("field_array.at", {field, std::to_string(array.getLength())},
                 inputs, at.getResult().getType(),
                 {std::to_string(at.getIndexAttr().getInt())}, true);
      } else {
        auto array = cast<algebra::FieldArrayType>(op->getResult(0).getType());
        auto field =
            cast<algebra::FieldType>(array.getElementType()).getDomain().str();
        auto vector = algebra::FieldVectorType::get(array.getContext(),
                                                    array.getDomain());
        result = emit("vector.empty", {field}, {}, vector, {}, false);
        for (auto value : inputs)
          result = emit("vector.append", {field}, ValueRange{result, value},
                        vector, {}, false);
        result = emit("field_array.from_vector",
                      {field, std::to_string(array.getLength())},
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

LogicalResult
lowerRecipes(protocol_ir::ProtocolModuleOp unit,
             const llvm::DenseSet<Operation *> &generated,
             BindingSymbols &symbols, MathematicalSelectionPolicy policy = {},
             RealizationWork *work = nullptr, RealizationTrace *trace = nullptr,
             RealizationScope *attempt = nullptr, bool orderedRetry = false) {
  // Finite bodies emit directly before primitive conversion. Callback
  // expansion and polynomial normalization still use a checked scratch clone
  // and can fail after mutation, so this phase cannot yet satisfy the
  // infallible-after-mutation recipe contract.
  RealizationWork standalone;
  auto &realizationWork = work ? *work : standalone;
  auto &finiteWork = realizationWork.finiteExpressions;
  while (true) {
    Operation *next = nullptr;
    unit.walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (!next && finite::isComputation(op) &&
          generated.contains(op->getParentOfType<local::FuncOp>()))
        next = op;
    });
    if (!next)
      break;
    if (!finiteWork) {
      if (attempt)
        attempt->failure(RequiredFailure{
            "finite expression work",
            CapacityCause{WorkOwner::FiniteExpressions, 1, finiteWork}});
      return diagnostics::emit(next->emitError(), "finite-analysis-limit");
    }
    --finiteWork;
    IRRewriter builder(next->getContext());
    builder.setInsertionPoint(next);
    auto result =
        finite::realizeExpression(next, next->getOperands(), builder, policy,
                                  &realizationWork, trace, orderedRetry);
    if (failed(result))
      return failure();
    builder.replaceOp(next, *result);
  }
  ConversionTarget target(*unit.getContext());
  target.markUnknownOpDynamicallyLegal([&](Operation *op) {
    return !generated.contains(op->getParentOfType<local::FuncOp>()) ||
           !isTotal(op);
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

} // namespace
LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                ArrayRef<local::FuncOp> functions,
                                MathematicalSelectionPolicy policy,
                                RealizationWork *work,
                                RealizationTrace *trace) {
  return lowerCalculations(unit, functions, policy, work, {}, trace);
}
LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                ArrayRef<local::FuncOp> functions,
                                MathematicalSelectionPolicy policy,
                                RealizationWork *work,
                                finite::VerificationLimits limits,
                                RealizationTrace *trace) {
  SmallVector<StringAttr> names;
  for (auto function : functions)
    names.push_back(function.getSymNameAttr());
  RealizationWork standalone;
  auto &available = work ? *work : standalone;
  RealizationScope scope(trace, "lower-calculations", unit, policy, &available);
  if (!functions.empty())
    scope.propose(policy);
  bool orderedRetry = false;
  for (;;) {
    // This unit is an intermediate outlined subject, so whole-module formation
    // belongs to the enclosing service. Keep its exact mathematical bodies
    // immutable for independent reading and any one ordered retry.
    auto attemptWork = available;
    RealizationScope attempt(trace, "calculation-attempt", unit, policy);
    if (!functions.empty())
      attempt.propose(policy);
    OwningOpRef<protocol_ir::ProtocolModuleOp> candidate(
        cast<protocol_ir::ProtocolModuleOp>(unit->clone()));
    SymbolTable table(*candidate);
    SmallVector<local::FuncOp> replacements;
    llvm::DenseSet<Operation *> selected;
    for (auto name : names) {
      auto function = table.lookup<local::FuncOp>(name.getValue());
      if (!function)
        return failure();
      replacements.push_back(function);
      selected.insert(function);
    }
    BindingSymbols symbols(*candidate);
    if (failed(lowerRecipes(*candidate, selected, symbols, policy, &attemptWork,
                            trace, &attempt, orderedRetry)))
      return failure();
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto checked = verifyCalculationRecipes(unit, *candidate, replacements,
                                            limits, outcome);
    available.matching = attemptWork.matching;
    available.lanes = attemptWork.lanes;
    if (succeeded(checked)) {
      // Preserve caller-owned function handles. The only mutable subjects are
      // these checked bodies and newly emitted bindings; all other declarations
      // and their order must match before any part is published.
      SymbolTable originalSymbols(unit);
      llvm::DenseSet<Operation *> selectedOriginal;
      for (auto function : functions)
        selectedOriginal.insert(function);
      SmallVector<Operation *> newBindings;
      auto original = unit.getBody().front().begin();
      bool seenOriginal = false;
      for (auto &definition : candidate->getBody().front()) {
        auto name = SymbolTable::getSymbolName(&definition);
        if (name && !originalSymbols.lookup(name)) {
          if (seenOriginal || !isa<local::OperationBindingOp>(definition))
            return diagnostics::emit(unit.emitError(),
                                     "mathematical-lowering-preservation",
                                     "unexpected calculation declaration");
          newBindings.push_back(&definition);
          continue;
        }
        seenOriginal = true;
        // Projection records and other unnamed definitions still belong to
        // the ordered context; they are not generated symbol declarations.
        auto *prior =
            original == unit.getBody().front().end() ? nullptr : &*original++;
        if (!prior || SymbolTable::getSymbolName(prior) != name ||
            (!selectedOriginal.contains(prior) &&
             !OperationEquivalence::isEquivalentTo(
                 prior, &definition, OperationEquivalence::IgnoreLocations)))
          return diagnostics::emit(
              unit.emitError(), "mathematical-lowering-preservation",
              "calculation changed surrounding declarations");
      }
      if (original != unit.getBody().front().end() ||
          unit->getAttrDictionary() != (*candidate)->getAttrDictionary())
        return diagnostics::emit(unit.emitError(),
                                 "mathematical-lowering-preservation",
                                 "calculation changed its enclosing unit");
      auto insertion = unit.getBody().front().begin();
      for (auto *binding : newBindings)
        binding->moveBefore(&unit.getBody().front(), insertion);
      for (unsigned i = 0; i < functions.size(); ++i) {
        auto originalFunction = functions[i];
        originalFunction.getBody().takeBody(replacements[i].getBody());
      }
      available = attemptWork;
      if (functions.empty()) {
        attempt.complete(CompletionKind::Unchanged);
        scope.complete(CompletionKind::Unchanged);
      } else {
        attempt.publish();
        scope.publish();
      }
      return success();
    }
    attempt.discard(verificationDecision(outcome));
    if (outcome.status == finite::VerificationStatus::OptionalCapacity &&
        policy.finiteBulk) {
      policy.finiteBulk = false;
      orderedRetry = true;
      attempt.retry(policy);
      continue;
    }
    if (outcome.status == finite::VerificationStatus::OptionalCapacity ||
        outcome.status == finite::VerificationStatus::RequiredCapacity)
      return diagnostics::emit(unit.emitError(), "finite-verification-capacity",
                               outcome.detail);
    return failure();
  }
}
} // namespace zkc::mathematical
