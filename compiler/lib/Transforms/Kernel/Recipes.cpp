#include "../CollectFold.h"
#include "../CollectionRealization.h"
#include "../MathematicalSupport.h"
#include "../RealizationTrace.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Analysis/Finite.h"
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
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
using namespace zkc::mathematical;
namespace zkc::kernel {
namespace {
// Reserve the complete numerical symbol context before allocating executable
// bindings. Retained helper/domain names never become generated identities.
class BindingSymbols {
  mlir::ModuleOp unit;
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
  explicit BindingSymbols(mlir::ModuleOp unit) : unit(unit) {
    for (auto &op : *unit.getBody())
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
  std::string freshSite(func::FuncOp function, StringRef prefix) {
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
    assert(!protocol::boundOperationName(application.contract).empty() &&
           "mathematical recipe requires an installed execution contract");
    auto key = std::make_pair(application.contract, application.arguments);
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      auto name = fresh();
      OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(unit.getBody());
      SmallVector<Attribute> arguments;
      for (auto &argument : application.arguments)
        arguments.push_back(builder.getStringAttr(argument));
      local::OperationBindingOp::create(
          builder, location, name, application.contract,
          builder.getArrayAttr(arguments), "", mlir::ArrayAttr{});
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
    if (!op->getParentOfType<func::FuncOp>())
      return rewriter.notifyMatchFailure(
          op, "recipe requires a numerical standard function");
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
              op->getParentOfType<func::FuncOp>(), site.getValue());
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
          occurrence = symbols.freshSite(op->getParentOfType<func::FuncOp>(),
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
                 : symbols.freshSite(op->getParentOfType<func::FuncOp>(),
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

LogicalResult lowerRecipes(func::FuncOp entry, BindingSymbols &symbols,
                           MathematicalSelectionPolicy policy = {},
                           RealizationWork *work = nullptr,
                           RealizationTrace *trace = nullptr,
                           RealizationScope *attempt = nullptr,
                           bool orderedRetry = false,
                           NumericalSelection *selection = nullptr,
                           ArrayRef<RealizationSubject> subjects = {}) {
  // Finite bodies emit directly before primitive conversion. Callback
  // expansion and polynomial normalization still use a checked scratch clone
  // and can fail after mutation, so this phase cannot yet satisfy the
  // infallible-after-mutation recipe contract.
  RealizationWork standalone;
  auto &realizationWork = work ? *work : standalone;
  auto &finiteWork = realizationWork.finiteExpressions;
  llvm::DenseMap<Operation *, RealizationSubject> sourceSubjects;
  if (selection)
    for (auto [op, subject] : zip(entry.front().without_terminator(), subjects))
      sourceSubjects[&op] = subject;
  while (true) {
    Operation *next = nullptr;
    entry.walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (!next && finite::isComputation(op))
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
    auto sourceSubject = sourceSubjects.lookup(next);
    auto *previous = next->getPrevNode();
    auto attributeChildren = [&] {
      unsigned child = 0;
      auto *first =
          previous ? previous->getNextNode() : &next->getBlock()->front();
      for (auto *at = first; at != next; at = at->getNextNode())
        at->walk<WalkOrder::PreOrder>([&](Operation *nested) {
          if (finite::isComputation(nested))
            sourceSubjects[nested] = NumericalSelection::childSubject(
                sourceSubject, nested->getName().getStringRef(), child++);
        });
    };
    auto effective = policy;
    std::optional<NumericalOccurrence> occurrence;
    if (selection) {
      auto selected = selection->discover(sourceSubject, policy.finiteBulk,
                                          policy.numericalExpressions);
      if (!selected) {
        diagnostics::emit(next->emitError(), selected.takeError());
        return failure();
      }
      occurrence = *selected;
      effective = selection->policy(*selected, policy);
    }
    realizationWork.numericalSelection = selection;
    realizationWork.numericalOccurrence = occurrence;
    if (effective.collectFoldFusion && finiteWork &&
        (!policy.finiteBulk || !selection ||
         selection->alternative(*occurrence) ==
             NumericalAlternative::Specialized)) {
      auto pair = finite::readCollectFold(next, next->getNextNode(),
                                          realizationWork.collectFoldDiscovery);
      if (succeeded(pair)) {
        auto results = finite::realizeCollectFold(
            *pair, next->getOperands(), pair->consumer.operation->getOperands(),
            builder, realizationWork);
        if (failed(results))
          return failure();
        --finiteWork;
        attributeChildren();
        builder.replaceOp(pair->consumer.operation, *results);
        builder.eraseOp(next);
        continue;
      }
    }
    auto result =
        finite::realizeExpression(next, next->getOperands(), builder, effective,
                                  &realizationWork, trace, orderedRetry);
    if (failed(result))
      return failure();
    attributeChildren();
    builder.replaceOp(next, *result);
  }
  ConversionTarget target(*entry.getContext());
  target.markUnknownOpDynamicallyLegal(
      [&](Operation *op) { return !isTotal(op); });
  RewritePatternSet patterns(entry.getContext());
  patterns.add<Recipe>(entry.getContext(), symbols);
  ConversionConfig config;
  // Lowering schedules explicit recipes. Mathematical folding belongs to
  // preparation/simplification, where generated constants have no sites yet.
  config.foldingMode = DialectConversionFoldingMode::Never;
  // Symbol/site allocation is monotone on this owned candidate. A failure
  // discards the candidate, so conversion need not roll individual recipes
  // back.
  config.allowPatternRollback = false;
  return applyFullConversion(entry, target, std::move(patterns), config);
}

// The private builtin module is a conversion workspace. Standard functions
// retain the mathematical input until recipes have replaced it; only then is
// the entry converted to the existing executable Local function vocabulary.
OwningOpRef<mlir::ModuleOp>
recipeCandidate(ModuleOp source, StringRef callSite, func::FuncOp &function,
                uint64_t &remaining, uint64_t &remainingBytes,
                std::optional<CapacityCause> &capacity) {
  auto entry = getEntry(source);
  if (!entry || !entry.getBody().hasOneBlock() || callSite.empty() ||
      !chargeCopy(source, remaining, &capacity))
    return {};
  OwningOpRef<mlir::ModuleOp> candidate(
      mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(candidate->getBody(), candidate->getBody()->end());
  for (auto &definition : source.getBody().front())
    builder.clone(definition);
  // Keep source declarations intact, including dormant references to the
  // public entry. Only this separately named working copy is converted.
  if (!chargeCopy(entry, remaining, &capacity))
    return {};
  function = cast<func::FuncOp>(entry->clone());
  function.setSymName("_recipe_entry");
  SymbolTable(*candidate).insert(function, candidate->getBody()->end());
  unsigned ordinal = 0;
  for (auto &op : function.front().without_terminator()) {
    if (!isTotal(&op) || op.getNumRegions() || isa<func::CallOp>(op) ||
        op.getName().getDialectNamespace() == "poly")
      return {};
    auto site =
        protocol::algorithmSite({{callSite.str(), "kernel"}},
                                std::to_string(ordinal++), remainingBytes);
    if (!site) {
      consumeError(site.takeError());
      capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes};
      return {};
    }
    op.setAttr("site", builder.getStringAttr(*site));
  }
  return candidate;
}
void executableCandidate(mlir::ModuleOp candidate, func::FuncOp working,
                         func::FuncOp source) {
  // Completed executable IR uses its existing owner and closed admission.
  // Mathematical declarations were conversion inputs and do not escape into
  // the executable result.
  OpBuilder builder(candidate.getBody(), candidate.getBody()->end());
  auto owner = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(), protocol_ir::Profile::Exec);
  owner.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&owner.getBody().front());
  auto output = local::FuncOp::create(
      builder, source.getLoc(), source.getSymName(), source.getFunctionType());
  output->setAttr("logical_origin",
                  builder.getArrayAttr(
                      {source.getSymNameAttr(), builder.getArrayAttr({})}));
  output.getBody().takeBody(working.getBody());
  auto returned = cast<func::ReturnOp>(output.getBody().front().back());
  builder.setInsertionPoint(returned);
  local::ReturnOp::create(builder, returned.getLoc(), returned.getOperands());
  returned.erase();
  for (auto &declaration : make_early_inc_range(*candidate.getBody())) {
    if (&declaration == owner.getOperation())
      continue;
    if (isa<local::OperationBindingOp>(declaration))
      declaration.moveBefore(output);
    else
      declaration.erase();
  }
}
} // namespace
OwningOpRef<mlir::ModuleOp>
realizeEntry(ModuleOp source, StringRef callSite,
             MathematicalSelectionPolicy policy, RealizationWork &available,
             uint64_t &remaining, uint64_t &remainingBytes,
             finite::VerificationLimits limits, RealizationTrace *trace,
             NumericalSelection *selection, VerificationDecision *reported,
             bool optionalConstruction) {
  if (reported)
    *reported = {VerificationObservation::Mismatch,
                 "Kernel construction differs"};
  auto entry = getEntry(source);
  if (!entry)
    return {};
  if (!limits.sharedReader)
    limits.sharedReader = &available.requiredFiniteChecking;
  if (!limits.sharedComparison)
    limits.sharedComparison = &available.optionalFiniteChecking;
  if (!limits.sharedContext)
    limits.sharedContext = &available.numericalContextChecking;
  if (!limits.sharedSiteBytes)
    limits.sharedSiteBytes = &available.numericalCheckSiteBytes;
  RealizationScope scope(trace, "kernel-recipes", source, policy, &available);
  // Each speculative construction is capped by the remaining discard
  // reserve before copying. Its selected debit is settled into the caller's
  // quotas; optional verification failure instead debits that reserve.
  scope.propose(policy);
  SmallVector<RealizationSubject> subjects;
  if (!finite::consumeComputationWork(available.selectionBookkeeping,
                                      entry.front().getOperations().size()))
    return {};
  for (auto &op : entry.front().without_terminator())
    subjects.push_back(finite::isComputation(&op) ? realizationSubject(&op)
                                                  : RealizationSubject{});
  NumericalSelection localSelection(&available);
  if (!selection) {
    localSelection.remainingCopy = remaining;
    localSelection.remainingSiteBytes = remainingBytes;
    selection = &localSelection;
  }
  for (auto &op : entry.front().without_terminator())
    if (finite::isComputation(&op)) {
      auto occurrence =
          selection->discover(realizationSubject(&op), policy.finiteBulk,
                              policy.numericalExpressions);
      if (!occurrence) {
        diagnostics::emit(op.emitError(), occurrence.takeError());
        return {};
      }
    }
  bool orderedRetry = false;
  for (;;) {
    // Retry from the immutable numerical unit. Optional matching allowances
    // remain cumulative; required construction keeps its ordered reserve.
    auto &attemptWork = available;
    RecipeConstructionWork construction(available);
    bool speculative = !reported && policy.finiteBulk &&
                       selection->canSpeculate() &&
                       selection->hasInvocationAlternatives() &&
                       construction.canDiscard(available) &&
                       remaining <= available.discardedRecipeCopy &&
                       remainingBytes <= available.discardedRecipeSiteBytes;
    if (!reported && policy.finiteBulk && !speculative &&
        selection->hasInvocationAlternatives())
      scope.selection(entry, DecisionFamily::Finite, RealizationChoice::Ordered,
                      {OptimizationStatus::Capacity, OptimizationReason::Work});
    bool previousPermission = true;
    if (!reported)
      previousPermission = selection->allowSpeculation(speculative);
    auto restorePermission = llvm::scope_exit([&] {
      if (!reported)
        selection->allowSpeculation(previousPermission);
    });
    auto copyCeiling = speculative
                           ? std::min(remaining, available.discardedRecipeCopy)
                           : remaining;
    auto byteCeiling =
        speculative
            ? std::min(remainingBytes, available.discardedRecipeSiteBytes)
            : remainingBytes;
    auto attemptRemaining = copyCeiling;
    auto attemptBytes = byteCeiling;
    auto commitConstruction = llvm::scope_exit([&] {
      remaining -= copyCeiling - attemptRemaining;
      remainingBytes -= byteCeiling - attemptBytes;
    });
    RealizationScope attempt(trace, "kernel-recipe-attempt", source, policy);
    attempt.propose(policy);
    func::FuncOp function;
    std::optional<CapacityCause> constructionCapacity;
    auto candidate =
        recipeCandidate(source, callSite, function, attemptRemaining,
                        attemptBytes, constructionCapacity);
    auto retryConstruction = [&] {
      if (constructionCapacity && reported)
        *reported = {optionalConstruction
                         ? VerificationObservation::OptionalCapacity
                         : VerificationObservation::RequiredCapacity,
                     "Kernel construction capacity", constructionCapacity};
      if (!constructionCapacity || !speculative)
        return false;
      auto advanced = selection->advanceInvocation();
      if (!advanced) {
        diagnostics::emit(source.emitError(), advanced.takeError());
        return false;
      }
      if (!*advanced)
        return false;
      if (candidate)
        candidate->walk([&](Operation *op) { selection->origins.erase(op); });
      if (!construction.discard(available))
        return false;
      available.discardedRecipeCopy -= copyCeiling - attemptRemaining;
      available.discardedRecipeSiteBytes -= byteCeiling - attemptBytes;
      commitConstruction.release();
      attempt.discard(VerificationDecision{
          VerificationObservation::OptionalCapacity,
          "optional recipe construction capacity", constructionCapacity});
      return true;
    };
    if (!candidate) {
      if (retryConstruction())
        continue;
      return {};
    }
    attempt.declarationOrigin(function.getSymName(), entry.getSymName());
    BindingSymbols symbols(*candidate);
    auto lowered = lowerRecipes(function, symbols, policy, &attemptWork, trace,
                                &attempt, orderedRetry, selection, subjects);
    // Every performed helper, equation and emission debit survives a retry.
    available.numericalSelection = nullptr;
    available.numericalOccurrence.reset();
    if (failed(lowered))
      return {};
    executableCandidate(*candidate, function, entry);
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    auto schedule =
        scheduleEntry(*candidate, attemptRemaining, &constructionCapacity);
    if (!schedule) {
      if (retryConstruction())
        continue;
      return {};
    }
    auto checked = verifyEntrySchedule(source, *schedule, callSite, policy,
                                       limits, &outcome);
    if (succeeded(checked)) {
      // The returned executable is consumed from the actual scheduled payload.
      // The earlier recipe workspace supplies no final body or SSA values.
      auto executable =
          consumeSchedule(*schedule, attemptRemaining, &constructionCapacity);
      if (!executable) {
        if (retryConstruction())
          continue;
        return {};
      }
      if (failed(verifyScheduleLowering(*schedule, *executable,
                                        limits.sharedContext, &outcome))) {
        if (reported)
          *reported = verificationDecision(outcome);
        return {};
      }
      candidate = std::move(executable);
      checked = verifyEntryRecipes(source, *candidate, callSite, policy, limits,
                                   &outcome, selection);
    }
    if (succeeded(checked)) {
      attempt.publish();
      scope.publish();
      return candidate;
    }
    candidate->walk([&](Operation *op) { selection->origins.erase(op); });
    attempt.discard(verificationDecision(outcome));
    if (reported) {
      *reported = verificationDecision(outcome);
      return {};
    }
    bool retry = false;
    if (outcome.status == finite::VerificationStatus::OptionalCapacity &&
        policy.finiteBulk) {
      auto ordered = selection->order(outcome.subject);
      if (!ordered) {
        diagnostics::emit(source.emitError(), ordered.takeError());
        return {};
      }
      retry = *ordered;
    }
    if (retry) {
      // Transfer the discarded construction debit to its cumulative reserve.
      // The ordered attempt keeps both incoming quotas. Terminal failures
      // instead retain their actual debit through commitConstruction.
      if (!construction.discard(available))
        return {};
      available.discardedRecipeCopy -= copyCeiling - attemptRemaining;
      available.discardedRecipeSiteBytes -= byteCeiling - attemptBytes;
      commitConstruction.release();
      orderedRetry = true;
      attempt.retry(policy, outcome.subject);
      continue;
    }
    if (outcome.status == finite::VerificationStatus::OptionalCapacity ||
        outcome.status == finite::VerificationStatus::RequiredCapacity)
      diagnostics::emit(source.emitError(), "finite-verification-capacity",
                        outcome.detail);
    return {};
  }
}
} // namespace zkc::kernel
