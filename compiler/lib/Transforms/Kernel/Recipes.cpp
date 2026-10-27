#include "../CollectFold.h"
#include "../CollectionRealization.h"
#include "../MathematicalSupport.h"
#include "../RealizationTrace.h"
#include "../ScopedFinite.h"
#include "Schedule.h"
#include "Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
  Operation *unit;
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
  explicit BindingSymbols(Operation *unit, Operation *source) : unit(unit) {
    for (auto &op : source->getRegion(0).front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  std::string fresh() {
    std::string result;
    do {
      result = "_calculation_" + std::to_string(next++);
    } while (!names.insert(result).second ||
             SymbolTable::lookupSymbolIn(unit, result));
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
      builder.setInsertionPointToStart(&unit->getRegion(0).front());
      SmallVector<Attribute> arguments;
      for (auto &argument : application.arguments)
        arguments.push_back(builder.getStringAttr(argument));
      runtime::BindingOp::create(builder, location, name, application.contract,
                                 builder.getArrayAttr(arguments), "",
                                 mlir::ArrayAttr{});
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
// Recipes read immutable mathematical expressions and emit scoped operations.
// No Local function, conversion cast or intermediate executable recipe is
// built.
class Recipes {
  Operation *sourceRoot;
  protocol_ir::ProtocolModuleOp owner;
  OpBuilder &rewriter;
  BindingSymbols symbols;
  MathematicalSelectionPolicy policy;
  RealizationWork &work;
  RealizationTrace *trace;
  NumericalSelection *selection;
  finite::ScopedEmissionBudget &budget;
  bool orderedRetry;
  bool valid = true;
  std::optional<RealizationSubject> activeSubject;
  unsigned nextChild = 0;

  bool reserve(uint64_t amount) {
    if (!valid)
      return false;
    if (amount > budget.work) {
      budget.capacity =
          CapacityCause{WorkOwner::AlgorithmExpansion, amount, budget.work};
      valid = false;
      return false;
    }
    budget.work -= amount;
    return true;
  }
  func::FuncOp region(TypeRange inputs, TypeRange outputs) {
    if (!reserve(32 + 8 * (inputs.size() + outputs.size())))
      return {};
    rewriter.setInsertionPointToEnd(&owner.getBody().front());
    SmallVector<Type> args{runtime::ScopeType::get(rewriter.getContext())};
    append_range(args, inputs);
    auto function = func::FuncOp::create(
        rewriter, owner.getLoc(), symbols.fresh(),
        rewriter.getFunctionType(
            args, {exec::OutcomeType::get(rewriter.getContext(),
                                          SmallVector<Type>(outputs))}));
    function.setPrivate();
    function.setNoInline(true);
    function->setAttr("runtime.region", rewriter.getUnitAttr());
    function.addEntryBlock();
    return function;
  }
  LogicalResult scalar(Operation *op, ArrayRef<Value> inputs,
                       exec::ScopedExecutionBuilder &control,
                       SmallVector<Value> &results) {
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!isTotal(op) || !site ||
        !reserve(64 + 16 * (inputs.size() + op->getNumResults())))
      return failure();
    control.setLocation(op->getLoc());
    // Reserve the root before allocating intermediate occurrence names.
    (void)symbols.freshSite(control.getFunction(), site.getValue());
    auto replace = [&](ValueRange values) {
      results.assign(values.begin(), values.end());
    };
    auto refuse = [](Operation *, StringRef) { return failure(); };
    auto emitState = [&](const OperationState &state) -> SmallVector<Value> {
      if (!reserve(32 + 8 * (state.operands.size() + state.types.size())))
        return SmallVector<Value>(state.types.size());
      return control.invoke(state.attributes.get("binding")
                                ? "exec.apply"
                                : state.name.getStringRef(),
                            state.types, control.scoped(state.operands),
                            state.attributes.getAttrs());
    };
    if (isa<poly::ProjectQuotientOp, poly::ObserveQuotientOp,
            poly::AddQuotientOp, poly::SubtractQuotientOp,
            poly::MultiplyQuotientOp>(op)) {
      if (isa<poly::ObserveQuotientOp>(op)) {
        replace(inputs[0]);
        return success();
      }
      bool project = isa<poly::ProjectQuotientOp>(op);
      auto type = cast<poly::QuotientType>(op->getResult(0).getType());
      StringRef contract = project                        ? "quotient.project"
                           : isa<poly::AddQuotientOp>(op) ? "quotient.add"
                           : isa<poly::SubtractQuotientOp>(op)
                               ? "quotient.subtract"
                               : "quotient.multiply";
      if (protocol::boundOperationName(contract).empty() ||
          protocol::boundOperationName("index.constant").empty())
        return failure();
      auto emit = [&](StringRef name, ValueRange operands, Type result,
                      ArrayRef<std::string> parameters, bool root) {
        OperationState state(op->getLoc(), protocol::boundOperationName(name));
        state.addOperands(operands);
        state.addTypes(result);
        auto occurrence =
            root ? site.getValue().str()
                 : symbols.freshSite(control.getFunction(), site.getValue());
        state.addAttribute("site", rewriter.getStringAttr(occurrence));
        SmallVector<Attribute> attrs;
        for (const auto &value : parameters)
          attrs.push_back(rewriter.getStringAttr(value));
        state.addAttribute("parameters", rewriter.getArrayAttr(attrs));
        state.addAttribute("binding", symbols.get({name.str(), {}, {}},
                                                  op->getLoc(), rewriter));
        return emitState(state).front();
      };
      auto index = protocol::decodeBoundType(
          op->getContext(), cantFail(protocol::parseBoundType("index", false)));
      SmallVector<Value> operands(inputs);
      operands.push_back(emit("index.constant", {}, index,
                              {std::to_string(type.getModulus())}, false));
      if (project)
        operands.push_back(emit("index.constant", {}, index,
                                {std::to_string(type.getDegree())}, false));
      auto output = algebra::IndicesType::get(op->getContext());
      replace(emit(contract, operands, output, {}, true));
      return success();
    }
    if (isa<data::BoundedAtOp, data::BoundedMatrixAtOp>(op)) {
      auto collection = collectionRealization(inputs[0].getType());
      if (!collection || !collection->get)
        return refuse(op, "no admitted collection access");
      const auto &application = *collection->get;
      OperationState state(op->getLoc(),
                           protocol::boundOperationName(application.contract));
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("parameters", rewriter.getArrayAttr({}));
      state.addAttribute("binding",
                         symbols.get(application, op->getLoc(), rewriter));
      replace(emitState(state));
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
      replace(emitState(state));
      return success();
    }
    if (isa<data::PowerOfTwoOp>(op)) {
      for (StringRef contract :
           {"index.constant", "index.equal", "bool.and", "bool.or"})
        if (protocol::boundOperationName(contract).empty())
          return failure();
      auto emit = [&](StringRef contract, ValueRange operands, Type type,
                      ArrayRef<Attribute> parameters = {},
                      bool last = false) -> Value {
        protocol::BindingApplication application;
        application.contract = contract.str();
        OperationState state(op->getLoc(),
                             protocol::boundOperationName(contract));
        state.addOperands(operands);
        state.addTypes(type);
        auto occurrence =
            last ? site.getValue().str()
                 : symbols.freshSite(control.getFunction(), site.getValue());
        state.addAttribute("site", rewriter.getStringAttr(occurrence));
        state.addAttribute("parameters", rewriter.getArrayAttr(parameters));
        state.addAttribute("binding",
                           symbols.get(application, op->getLoc(), rewriter));
        return emitState(state).front();
      };
      Value result;
      // The VM has no shift contract. Enumerating its 64 representable powers
      // implements r < 64 && n == (1 << r), with no runtime shift or overflow.
      for (unsigned exponent = 0; exponent < 64; ++exponent) {
        auto constant = [&](uint64_t value) {
          return emit("index.constant", {}, inputs[0].getType(),
                      {rewriter.getStringAttr(std::to_string(value))});
        };
        auto r = constant(exponent), n = constant(uint64_t(1) << exponent);
        auto equalR = emit("index.equal", {inputs[1], r}, rewriter.getI1Type());
        auto equalN = emit("index.equal", {inputs[0], n}, rewriter.getI1Type());
        auto current = emit("bool.and", {equalR, equalN}, rewriter.getI1Type());
        result = exponent == 0 ? current
                               : emit("bool.or", {result, current},
                                      rewriter.getI1Type(), {}, exponent == 63);
      }
      replace(result);
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
      replace(emitState(state));
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
      replace(emitState(state));
      return success();
    }
    if (auto make = dyn_cast<data::MakeOp>(op)) {
      OperationState state(op->getLoc(), exec::VariantOp::getOperationName());
      state.addOperands(inputs);
      state.addTypes(op->getResultTypes());
      state.addAttribute("site", site);
      state.addAttribute("alternative", make.getAlternativeAttr());
      replace(emitState(state));
      return success();
    }
    if (isa<data::GetOp, data::IsOp>(op)) {
      auto type = cast<data::VariantType>(op->getOperand(0).getType());
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
      SmallVector<std::string> alternatives;
      for (const auto &arm : descriptor->alternatives)
        alternatives.push_back(arm.label);
      auto outline = [&](unsigned i) {
        OpBuilder::InsertionGuard restore(rewriter);
        auto function = region(payloads[i], op->getResultTypes());
        if (!function)
          return func::FuncOp();
        rewriter.setInsertionPointToEnd(&function.front());
        exec::ScopedExecutionBuilder nested(rewriter, function,
                                            control.getLoopForm());
        Value value;
        if (auto get = dyn_cast<data::GetOp>(op))
          value = function.getArgument(1 + get.getIndexAttr().getInt());
        else {
          auto occurrence =
              symbols.freshSite(control.getFunction(), site.getValue());
          if (!reserve(32 + occurrence.size()))
            return func::FuncOp();
          value =
              nested
                  .invoke(
                      "exec.boolean", rewriter.getI1Type(), nested.scoped({}),
                      {rewriter.getNamedAttr(
                           "value", rewriter.getBoolAttr(
                                        descriptor->alternatives[i].label ==
                                        cast<data::IsOp>(op).getAlternative())),
                       rewriter.getNamedAttr(
                           "site", rewriter.getStringAttr(occurrence))})
                  .front();
        }
        nested.complete(value);
        return function;
      };
      replace(control.match(inputs[0], {}, op->getResultTypes(), alternatives,
                            site.getValue(), outline));
      return success(valid);
    }
    if (isa<arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
            arith::CmpIOp, arith::SelectOp>(op)) {
      auto model = dyn_cast<MathematicalOpInterface>(op);
      auto identity = model ? model.getMathematicalIdentity() : std::nullopt;
      if (!identity)
        return refuse(op, "missing closed arithmetic identity");
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
        return refuse(op, "arithmetic identity has no lowering recipe");
    }
    if (isa<arith::SelectOp>(op)) {
      llvm::SetVector<Value> captures;
      captures.insert(inputs[1]);
      captures.insert(inputs[2]);
      SmallVector<Value> captured(captures.begin(), captures.end());
      auto outline = [&](unsigned i) {
        OpBuilder::InsertionGuard restore(rewriter);
        auto function =
            region(ValueRange(captured).getTypes(), op->getResultTypes());
        if (!function)
          return func::FuncOp();
        rewriter.setInsertionPointToEnd(&function.front());
        exec::ScopedExecutionBuilder nested(rewriter, function,
                                            control.getLoopForm());
        unsigned selected = std::distance(captures.begin(),
                                          llvm::find(captures, inputs[i + 1]));
        nested.complete(function.getArgument(1 + selected));
        return function;
      };
      replace(control.conditional(inputs[0], captured, op->getResultTypes(),
                                  site.getValue(), outline));
      return success(valid);
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      auto attribute = dyn_cast<IntegerAttr>(constant.getValue());
      if (!attribute || !attribute.getType().isSignlessInteger(1) ||
          !constant.getType().isSignlessInteger(1))
        return refuse(op, "expected scalar Boolean constant");
      auto value = attribute.getValue().getBoolValue();
      replace(control.invoke(
          "exec.boolean", rewriter.getI1Type(), control.scoped({}),
          {rewriter.getNamedAttr("value", rewriter.getBoolAttr(value)),
           rewriter.getNamedAttr("site", site)}));
      return success();
    }
    if (isa<arith::AndIOp, arith::OrIOp, arith::XOrIOp, arith::CmpIOp>(op)) {
      if (!op->getResult(0).getType().isSignlessInteger(1) ||
          !all_of(inputs, [](Value value) {
            return value.getType().isSignlessInteger(1);
          }))
        return refuse(op, "expected scalar Boolean operands");
      for (StringRef contract : {"bool.and", "bool.or", "bool.not"})
        if (protocol::boundOperationName(contract).empty())
          return refuse(op, "missing Boolean execution binding");
      auto emit = [&](StringRef contract, ValueRange operands,
                      bool last) -> Value {
        std::string occurrence = site.getValue().str();
        if (!last)
          occurrence =
              symbols.freshSite(control.getFunction(), site.getValue());
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
        return emitState(state).front();
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
      replace(result);
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
                 : symbols.freshSite(control.getFunction(), site.getValue());
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
        return emitState(state).front();
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
      replace(result);
      return success();
    }
    auto application = algebraBinding(op);
    auto name = protocol::boundOperationName(application.contract);
    if (application.contract.empty() || name.empty())
      return refuse(op, "no execution recipe for this operation");
    auto reference = symbols.get(application, op->getLoc(), rewriter);
    OperationState state(op->getLoc(), name);
    state.addOperands(inputs);
    state.addTypes(op->getResultTypes());
    state.addAttribute("site", site);
    state.addAttribute("parameters", rewriter.getArrayAttr({}));
    state.addAttribute("binding", reference);
    replace(emitState(state));
    return success();
  }

public:
  Recipes(Operation *sourceRoot, protocol_ir::ProtocolModuleOp owner,
          OpBuilder &builder, MathematicalSelectionPolicy policy,
          RealizationWork &work, RealizationTrace *trace,
          NumericalSelection *selection, finite::ScopedEmissionBudget &budget,
          bool orderedRetry)
      : sourceRoot(sourceRoot), owner(owner), rewriter(builder),
        symbols(owner, sourceRoot), policy(policy), work(work), trace(trace),
        selection(selection), budget(budget), orderedRetry(orderedRetry) {}

  FailureOr<SmallVector<Value>>
  expression(Operation *source, ValueRange inputs,
             exec::ScopedExecutionBuilder &control,
             std::optional<RealizationSubject> root = std::nullopt,
             const finite::CollectFold *pair = nullptr,
             ValueRange consumerInputs = {}) {
    if (!valid)
      return failure();
    if (!finite::isComputation(source)) {
      SmallVector<Value> values;
      if (failed(scalar(source, SmallVector<Value>(inputs), control, values)) ||
          !valid)
        return failure();
      return values;
    }
    if (!work.finiteExpressions) {
      budget.capacity = CapacityCause{WorkOwner::FiniteExpressions, 1, 0};
      return failure();
    }
    --work.finiteExpressions;
    auto subject =
        root ? *root
        : activeSubject
            ? NumericalSelection::childSubject(
                  *activeSubject, source->getName().getStringRef(), nextChild++)
            : realizationSubject(source);
    auto parent = activeSubject;
    auto parentChild = nextChild;
    auto parentSelection = work.numericalSelection;
    auto parentOccurrence = work.numericalOccurrence;
    auto restore = llvm::scope_exit([&] {
      activeSubject = parent;
      nextChild = parentChild;
      work.numericalSelection = parentSelection;
      work.numericalOccurrence = parentOccurrence;
    });
    activeSubject = subject;
    nextChild = 0;
    auto effective = policy;
    work.numericalSelection = selection;
    work.numericalOccurrence.reset();
    if (selection) {
      auto occurrence = selection->discover(subject, policy.finiteBulk,
                                            policy.numericalExpressions);
      if (!occurrence) {
        diagnostics::emit(source->emitError(), occurrence.takeError());
        return failure();
      }
      work.numericalOccurrence = *occurrence;
      effective = selection->policy(*occurrence, policy);
    }
    auto callback = [&](Operation *op, ValueRange actuals,
                        exec::ScopedExecutionBuilder &nested) {
      return expression(op, actuals, nested);
    };
    return finite::realizeScopedTotalExpression(
        source, sourceRoot, inputs, rewriter, control, callback, work,
        effective, trace, budget, orderedRetry, pair, consumerInputs);
  }

  LogicalResult body(func::FuncOp source, func::FuncOp target,
                     ArrayRef<RealizationSubject> subjects) {
    IRMapping mapping;
    mapping.map(source.getArguments(), target.getArguments().drop_front());
    rewriter.setInsertionPointToEnd(&target.front());
    exec::ScopedExecutionBuilder control(
        rewriter, target, exec::ScopedExecutionBuilder::LoopForm::Structured);
    Operation *consumed = nullptr;
    unsigned ordinal = 0;
    for (auto &op : source.front().without_terminator()) {
      auto subject = subjects[ordinal++];
      if (&op == consumed)
        continue;
      SmallVector<Value> inputs;
      for (Value operand : op.getOperands()) {
        auto value = mapping.lookupOrNull(operand);
        if (!value)
          return failure();
        inputs.push_back(value);
      }
      std::optional<finite::CollectFold> pair;
      SmallVector<Value> consumerInputs;
      if (finite::isComputation(&op) && policy.collectFoldFusion &&
          work.finiteExpressions > 1) {
        auto effective = policy;
        bool specialized = true;
        if (selection) {
          auto occurrence = selection->discover(subject, policy.finiteBulk,
                                                policy.numericalExpressions);
          if (!occurrence) {
            consumeError(occurrence.takeError());
            return failure();
          }
          effective = selection->policy(*occurrence, policy);
          specialized = selection->alternative(*occurrence) ==
                        NumericalAlternative::Specialized;
        }
        if (effective.collectFoldFusion &&
            (!policy.finiteBulk || !selection || specialized)) {
          auto found = finite::readCollectFold(&op, op.getNextNode(),
                                               work.collectFoldDiscovery);
          if (succeeded(found)) {
            pair = *found;
            for (Value operand : pair->consumer.operation->getOperands()) {
              auto value = operand == pair->collected
                               ? operand
                               : mapping.lookupOrNull(operand);
              if (!value)
                return failure();
              consumerInputs.push_back(value);
            }
            --work.finiteExpressions;
            consumed = pair->consumer.operation;
          }
        }
      }
      auto values = expression(&op, inputs, control, subject,
                               pair ? &*pair : nullptr, consumerInputs);
      auto results =
          pair ? pair->consumer.operation->getResults() : op.getResults();
      if (failed(values) || values->size() != results.size())
        return failure();
      mapping.map(results, *values);
    }
    SmallVector<Value> results;
    for (Value operand : source.front().back().getOperands()) {
      auto value = mapping.lookupOrNull(operand);
      if (!value)
        return failure();
      results.push_back(value);
    }
    if (!reserve(16 + 4 * results.size()))
      return failure();
    control.returned(results);
    return success();
  }
};
// The private builtin module holds immutable mathematical input and its symbol
// closure. Executable recipes are emitted into a separate scoped owner.
OwningOpRef<mlir::ModuleOp>
recipeCandidate(mlir::ModuleOp source, StringRef callSite,
                func::FuncOp &function, uint64_t &remaining,
                uint64_t &remainingBytes,
                std::optional<CapacityCause> &capacity) {
  auto entry = mathematical::getComputationEntry(source);
  if (!entry || !entry.getBody().hasOneBlock() || callSite.empty() ||
      !chargeCopy(source, remaining, &capacity))
    return {};
  OwningOpRef<mlir::ModuleOp> candidate(
      mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(candidate->getBody(), candidate->getBody()->end());
  for (auto &definition : *source.getBody())
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
        poly::isPolynomialNormalizationOperation(&op))
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
OwningOpRef<mlir::ModuleOp>
scheduledCandidate(mlir::ModuleOp mathematical, func::FuncOp working,
                   func::FuncOp source, MathematicalSelectionPolicy policy,
                   RealizationWork &work, RealizationTrace *trace,
                   NumericalSelection *selection,
                   finite::ScopedEmissionBudget &budget, bool orderedRetry,
                   ArrayRef<RealizationSubject> subjects) {
  uint64_t envelope = 48 +
                      8 * (source.getNumArguments() + source.getNumResults()) +
                      source.getSymName().size();
  if (envelope > budget.work) {
    budget.capacity =
        CapacityCause{WorkOwner::AlgorithmExpansion, envelope, budget.work};
    return {};
  }
  budget.work -= envelope;
  OwningOpRef<mlir::ModuleOp> candidate(
      mlir::ModuleOp::create(source.getLoc()));
  OpBuilder builder(candidate->getBody(), candidate->getBody()->end());
  auto owner = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(), protocol_ir::Profile::Exec);
  owner.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&owner.getBody().front());
  SmallVector<Type> arguments{runtime::ScopeType::get(builder.getContext())};
  append_range(arguments, source.getArgumentTypes());
  auto output = func::FuncOp::create(
      builder, source.getLoc(), source.getSymName(),
      builder.getFunctionType(
          arguments, {exec::OutcomeType::get(builder.getContext(),
                                             source.getResultTypes())}));
  output.setPrivate();
  output.setNoInline(true);
  output->setAttr("runtime.origin",
                  builder.getArrayAttr(
                      {source.getSymNameAttr(), builder.getArrayAttr({})}));
  output.addEntryBlock();
  Recipes recipes(mathematical, owner, builder, policy, work, trace, selection,
                  budget, orderedRetry);
  if (failed(recipes.body(working, output, subjects)))
    return {};
  return candidate;
}
} // namespace
OwningOpRef<mlir::ModuleOp>
realizeEntry(mlir::ModuleOp source, StringRef callSite,
             MathematicalSelectionPolicy policy, RealizationWork &available,
             uint64_t &remaining, uint64_t &remainingBytes,
             finite::VerificationLimits limits, RealizationTrace *trace,
             NumericalSelection *selection, VerificationDecision *reported,
             bool optionalConstruction,
             OwningOpRef<mlir::ModuleOp> *selectedSchedule) {
  if (reported)
    *reported = {VerificationObservation::Mismatch,
                 "Kernel construction differs"};
  auto entry = mathematical::getComputationEntry(source);
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
      // Only the speculative copy/site envelope belongs to this retry owner.
      // Exhausting required finite work cannot be recast as an optional
      // construction failure or replenished from the discard reserve.
      bool retryable =
          constructionCapacity &&
          (constructionCapacity->owner == WorkOwner::AlgorithmExpansion ||
           constructionCapacity->owner == WorkOwner::AlgorithmOriginBytes);
      if (constructionCapacity && reported)
        *reported = {optionalConstruction && retryable
                         ? VerificationObservation::OptionalCapacity
                         : VerificationObservation::RequiredCapacity,
                     "Kernel construction capacity", constructionCapacity};
      if (!retryable || !speculative)
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
    finite::ScopedEmissionBudget emission{attemptRemaining, attemptBytes,
                                          constructionCapacity};
    auto schedule =
        scheduledCandidate(*candidate, function, entry, policy, attemptWork,
                           trace, selection, emission, orderedRetry, subjects);
    available.numericalSelection = nullptr;
    available.numericalOccurrence.reset();
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
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
      if (selectedSchedule)
        *selectedSchedule = std::move(schedule);
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
