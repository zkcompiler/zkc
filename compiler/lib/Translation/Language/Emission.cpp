#include "DataPreconditions.h"
#include "Finite.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Language.h"
#include "zkc/Translation/Packing.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
using Values = SmallVector<mlir::Value>;
class Emitter {
  const ClosedEntry &project;
  const Limits &limits;
  mlir::MLIRContext &context;
  mlir::OpBuilder builder;
  mlir::Location location;
  StringRef declaration;
  Layouts layouts;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  mlir::Block *definitions = nullptr;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
  std::map<std::string, std::string> realizations;
  std::map<std::pair<std::string, std::vector<bool>>, std::string> maps;
  std::set<std::string> symbols;
  Error failure = Error::success();
  uint64_t operations = 0, siteOrdinal = 0, remaining;
  template <class T> std::optional<T> take(Expected<T> value) {
    if (!value) {
      failure = value.takeError();
      return {};
    }
    return std::move(*value);
  }
  mlir::ArrayAttr strings(ArrayRef<std::string> values) {
    SmallVector<mlir::Attribute> out;
    for (auto &s : values)
      out.push_back(builder.getStringAttr(s));
    return builder.getArrayAttr(out);
  }
  mlir::NamedAttribute attr(StringRef name, mlir::Attribute value) {
    return builder.getNamedAttr(name, value);
  }
  mlir::NamedAttribute text(StringRef name, StringRef value) {
    return attr(name, builder.getStringAttr(value));
  }
  mlir::Operation *make(StringRef name, mlir::TypeRange outputs,
                        mlir::ValueRange inputs,
                        ArrayRef<mlir::NamedAttribute> attrs,
                        unsigned regions = 0) {
    if (++operations > limits.operations) {
      failure = error("source.limit", "emitted operation limit exceeded");
      return nullptr;
    }
    mlir::OperationState state(location, name);
    state.addTypes(outputs);
    state.addOperands(inputs);
    state.addAttributes(attrs);
    for (unsigned i = 0; i < regions; ++i)
      state.addRegion()->push_back(new mlir::Block());
    return builder.create(state);
  }
  std::optional<SmallVector<mlir::Type>> types(const Layout &layout) {
    SmallVector<mlir::Type> result;
    for (auto &leaf : layout.leaves) {
      if (leaf.cost() > remaining) {
        failure =
            error("source.limit", "native type emission work limit exceeded");
        return {};
      }
      remaining -= leaf.cost();
      if (const auto *polynomial = leaf.polynomial()) {
        std::string diagnostics;
        mlir::ScopedDiagnosticHandler handler(
            &context, [&](mlir::Diagnostic &diagnostic) {
              raw_string_ostream stream(diagnostics);
              diagnostic.print(stream);
              return mlir::success();
            });
        auto type = poly::PolynomialType::getChecked(
            [&] { return mlir::emitError(location); }, &context,
            StringRef(polynomial->field), polynomial->arity);
        if (!type) {
          failure = error("target.admission",
                          "in " + declaration + ": " + diagnostics);
          return {};
        }
        result.push_back(type);
        continue;
      }
      auto bound = take(protocol::parseBoundType(*leaf.data(), false));
      if (!bound)
        return {};
      auto type = protocol::decodeBoundType(&context, *bound);
      if (!type) {
        failure = error("source.layout", "native type dialect unavailable");
        return {};
      }
      result.push_back(type);
    }
    return result;
  }
  std::optional<Values> primitive(StringRef contract, mlir::ValueRange inputs,
                                  mlir::TypeRange outputs,
                                  ArrayRef<std::string> parameters,
                                  StringRef site,
                                  std::optional<ArrayRef<Type>> statics = {}) {
    if (!statics && contract == "bool.constant") {
      auto *op = make(
          "local.bool_constant", outputs, {},
          {attr("value", builder.getBoolAttr(parameters.front() == "true")),
           text("site", site)});
      return op ? std::optional<Values>(Values(op->getResults()))
                : std::nullopt;
    }
    if (!statics && contract == "bool.equal") {
      auto a = primitive("bool.and", inputs, outputs, {}, site.str() + "_both");
      if (!a)
        return {};
      auto n0 =
          primitive("bool.not", inputs[0], outputs, {}, site.str() + "_left");
      if (!n0)
        return {};
      auto n1 =
          primitive("bool.not", inputs[1], outputs, {}, site.str() + "_right");
      if (!n1)
        return {};
      Values neg{(*n0)[0], (*n1)[0]};
      auto b = primitive("bool.and", neg, outputs, {}, site.str() + "_neither");
      if (!b)
        return {};
      Values either{(*a)[0], (*b)[0]};
      return primitive("bool.or", either, outputs, {}, site);
    }
    std::vector<std::string> arguments;
    if (statics) {
      auto roots = take(layouts.kernelArguments(contract, *statics));
      if (!roots)
        return {};
      arguments = std::move(*roots);
    } else if (contract.starts_with("field.") ||
               contract.starts_with("curve.") ||
               contract.starts_with("resource_unit.")) {
      auto type = take(protocol::encodeBoundType(
          inputs.empty() ? outputs.front() : inputs.front().getType(), false));
      if (!type)
        return {};
      arguments.push_back(type->identity);
    }
    const auto key = std::make_pair(contract.str(), arguments);
    auto found = bindings.find(key);
    if (found == bindings.end()) {
      auto name = "zkl_binding_" + std::to_string(bindings.size());
      if (name.size() > limits.symbolBytes) {
        failure = error("source.limit", "binding symbol exceeds byte limit");
        return {};
      }
      mlir::OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToStart(definitions);
      if (!make("local.binding", {}, {},
                {text("sym_name", name), text("contract", contract),
                 attr("arguments", strings(arguments)),
                 text("implementation", "")}))
        return {};
      found = bindings.emplace(key, std::move(name)).first;
    }
    auto operationName = protocol::boundOperationName(contract);
    if (operationName.empty()) {
      failure = error("source.emission",
                      "no installed ordered operation for " + contract);
      return {};
    }
    auto *op = make(
        operationName, outputs, inputs,
        {attr("binding", mlir::FlatSymbolRefAttr::get(&context, found->second)),
         attr("parameters", strings(parameters)), text("site", site)});
    return op ? std::optional<Values>(Values(op->getResults())) : std::nullopt;
  }
  std::optional<std::string> realization(const Declaration &helper,
                                         mlir::TypeRange inputs,
                                         mlir::TypeRange outputs) {
    if (auto found = realizations.find(helper.symbol);
        found != realizations.end())
      return found->second;
    std::string identity =
        "zkc.local.realization:" + std::to_string(helper.symbol.size()) + ":" +
        helper.symbol;
    auto digest = SHA256::hash(arrayRefFromStringRef(identity));
    std::string name =
        "zkl_realization_" + toHex(ArrayRef<uint8_t>(digest), true);
    if (name.size() > limits.symbolBytes) {
      failure = error("source.limit", "realization symbol exceeds byte limit");
      return {};
    }
    if (!symbols.insert(name).second) {
      failure = error("source.symbol", "realization symbol collision");
      return {};
    }
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(definitions);
    if (!make(
            "local.realize", {}, {},
            {text("sym_name", name),
             attr("helper",
                  mlir::FlatSymbolRefAttr::get(&context, helper.symbol)),
             attr("function_type", mlir::TypeAttr::get(builder.getFunctionType(
                                       inputs, outputs)))}))
      return {};
    realizations.emplace(helper.symbol, name);
    return name;
  }
  // One declaration per helper instance and row mask. Its signature follows
  // from both, so the name binds exactly that pair.
  std::optional<std::string> map(const Declaration &helper,
                                 ArrayRef<bool> rowwise, mlir::TypeRange inputs,
                                 mlir::TypeRange outputs) {
    auto key = std::make_pair(
        helper.symbol, std::vector<bool>(rowwise.begin(), rowwise.end()));
    if (auto found = maps.find(key); found != maps.end())
      return found->second;
    std::string identity =
        "zkc.local.map:" + std::to_string(helper.symbol.size()) + ":" +
        helper.symbol + ":";
    for (bool row : rowwise)
      identity += row ? '1' : '0';
    auto digest = SHA256::hash(arrayRefFromStringRef(identity));
    std::string name = "zkl_map_" + toHex(ArrayRef<uint8_t>(digest), true);
    if (name.size() > limits.symbolBytes) {
      failure = error("source.limit", "map symbol exceeds byte limit");
      return {};
    }
    if (!symbols.insert(name).second) {
      failure = error("source.symbol", "map symbol collision");
      return {};
    }
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(definitions);
    SmallVector<bool> mask(rowwise.begin(), rowwise.end());
    if (!make(
            "algebra.map_realize", {}, {},
            {text("sym_name", name),
             attr("helper",
                  mlir::FlatSymbolRefAttr::get(&context, helper.symbol)),
             attr("function_type", mlir::TypeAttr::get(builder.getFunctionType(
                                       inputs, outputs))),
             attr("rowwise", builder.getDenseBoolArrayAttr(mask))}))
      return {};
    maps.emplace(std::move(key), name);
    return name;
  }
  bool retire(mlir::Value value, StringRef site) {
    return bool(primitive("resource_unit.consume", value, {}, {}, site));
  }
  mlir::ArrayAttr roles(ArrayRef<unsigned> indices) {
    SmallVector<mlir::Attribute> result;
    for (auto index : indices)
      result.push_back(builder.getStringAttr(nativeRoleName(index)));
    return builder.getArrayAttr(result);
  }
  std::optional<std::string> alternative(const Layout &layout, StringRef name) {
    for (unsigned i = 0; i < layout.alternatives.size(); ++i) {
      const auto &candidate = layout.alternatives[i].name;
      if (candidate.size() + 1 > remaining) {
        failure = error("source.limit", "variant label work limit exceeded");
        return {};
      }
      remaining -= candidate.size() + 1;
      if (candidate == name)
        return nativeAlternativeName(i);
    }
    failure = error("source.emission", "unknown source variant alternative");
    return {};
  }
  bool body(const Declaration &decl, const Body &source, mlir::Block &block,
            bool region = false) {
    builder.setInsertionPointToEnd(&block);
    std::vector<Values> values(source.values.size());
    assert(block.getNumArguments() == 0 && "body requires a fresh block");
    for (unsigned i = 0; i < source.inputs; ++i) {
      auto layout = take(layouts.get(source.values[i].type));
      if (!layout)
        return false;
      auto ts = types(**layout);
      if (!ts)
        return false;
      for (auto type : *ts)
        values[i].push_back(block.addArgument(type, location));
    }
    Values services;
    for (const auto &port : source.services) {
      auto type =
          protocol_ir::ServiceReferenceType::get(&context, port.contract);
      services.push_back(block.addArgument(type, location));
    }
    const auto &proof = project.entry().proof();
    if (!region && decl.id.index == project.protocol().id.index && proof &&
        proof->target) {
      const auto &clause = decl.specifications[*proof->target];
      const auto &relation =
          project.declarations()[clause.subject.relation.index];
      Values operands;
      std::vector<std::string> selectors;
      for (const auto &operand : clause.subject.operands) {
        auto slice = take(layouts.select(decl, operand));
        if (!slice)
          return false;
        for (unsigned i = 0; i < slice->layout->leaves.size(); ++i) {
          operands.push_back(block.getArgument(slice->offset + i));
          selectors.push_back(nativeRoleName(operand.role));
        }
      }
      auto acceptance = take(layouts.select(decl, proof->acceptance));
      if (!acceptance)
        return false;
      if (!make("protocol.statement", {}, operands,
                {attr("relation",
                      mlir::FlatSymbolRefAttr::get(&context, relation.symbol)),
                 attr("selectors", strings(selectors)),
                 attr("acceptance",
                      builder.getI64IntegerAttr(acceptance->offset))}))
        return false;
    }
    auto flatten = [&](ArrayRef<ValueId> ids) {
      Values result;
      for (auto id : ids)
        llvm::append_range(result, values[id.index]);
      return result;
    };
    for (auto &op : source.operations) {
      std::vector<std::shared_ptr<const Layout>> resultLayouts;
      SmallVector<mlir::Type> resultTypes;
      for (auto id : op.results) {
        auto layout = take(layouts.get(source.values[id.index].type));
        if (!layout)
          return false;
        auto native = types(**layout);
        if (!native)
          return false;
        llvm::append_range(resultTypes, *native);
        resultLayouts.push_back(*layout);
      }
      auto site = nativeSiteName(op.site.value_or(""), siteOrdinal++);
      Values result;
      if (auto *projection = std::get_if<Projection>(&op.action)) {
        auto selected =
            take(layouts.get(source.values[projection->input.index].type));
        if (!selected)
          return false;
        unsigned offset = 0;
        for (auto field : projection->path) {
          offset += (**selected).fields[field].offset;
          selected = (**selected).fields[field].layout;
        }
        auto &input = values[projection->input.index];
        result.append(input.begin() + offset,
                      input.begin() + offset + (**selected).leaves.size());
      } else if (auto *construct = std::get_if<Construct>(&op.action)) {
        auto input = flatten(construct->operands);
        if (construct->kind == Construct::Kind::Unpack) {
          auto origin = take(layouts.get(
              source.values[construct->operands.front().index].type));
          if (!origin)
            return false;
          if ((**origin).custody) {
            if (!retire(input.front(), site + "_unpack"))
              return false;
            input.erase(input.begin());
          }
          result = std::move(input);
        } else {
          if (resultLayouts.front()->custody) {
            auto created = primitive("resource_unit.create", {},
                                     resultTypes.front(), {}, site + "_create");
            if (!created)
              return false;
            llvm::append_range(result, *created);
          }
          if (source.values[op.results.front().index].type.kind ==
              Type::Kind::Variant) {
            auto label =
                alternative(*resultLayouts.front(), construct->alternative);
            if (!label)
              return false;
            auto *actual =
                make("local.variant_inject", resultTypes.back(), input,
                     {text("site", site), text("alternative", *label)});
            if (!actual)
              return false;
            result.push_back(actual->getResult(0));
          } else
            llvm::append_range(result, input);
        }
      } else if (auto *consume = std::get_if<Consume>(&op.action)) {
        auto input =
            take(layouts.get(source.values[consume->input.index].type));
        if (!input)
          return false;
        for (unsigned i = 0; i < (**input).leaves.size(); ++i)
          if ((**input).leaves[i].data() &&
              StringRef(*(**input).leaves[i].data())
                  .starts_with("resource_unit:") &&
              !retire(values[consume->input.index][i],
                      site + "_" + std::to_string(i)))
            return false;
      } else if (auto *math = std::get_if<MathValue>(&op.action)) {
        auto operands = flatten(math->operands);
        auto outputs = resultTypes;
        std::optional<PackedLayout> packed;
        if (math->identity == MathematicalIdentity::ContainerAt &&
            source.values[math->operands.front().index].type.domain ==
                "sequence") {
          packed = take(
              layouts.packed(source.values[op.results.front().index].type));
          if (!packed)
            return false;
          auto carrier = protocol::decodeBoundType(&context, packed->carrier);
          if (!carrier) {
            failure = error("source.layout",
                            "total sequence result dialect unavailable");
            return false;
          }
          outputs = {carrier};
        }
        mlir::Operation *actual = nullptr;
        switch (math->identity) {
        case MathematicalIdentity::BooleanConstant:
          actual = make(
              "arith.constant", resultTypes, {},
              {attr("value", builder.getIntegerAttr(builder.getI1Type(),
                                                    math->literal == "true"))});
          break;
        case MathematicalIdentity::BooleanEqual:
          actual =
              make("arith.cmpi", resultTypes, operands,
                   {attr("predicate", builder.getI64IntegerAttr(int64_t(
                                          mlir::arith::CmpIPredicate::eq)))});
          break;
        default: {
          StringRef name;
          switch (math->identity) {
          case MathematicalIdentity::ContainerAt:
            name = "data.bounded_at";
            break;
          case MathematicalIdentity::MatrixAt:
            name = "data.bounded_matrix_at";
            break;
          case MathematicalIdentity::IndexConstant:
            name = "data.index";
            break;
          case MathematicalIdentity::IndexEqual:
            name = "data.index_equal";
            break;
          case MathematicalIdentity::IndexLess:
            name = "data.index_less";
            break;
          case MathematicalIdentity::BooleanAnd:
            name = "arith.andi";
            break;
          case MathematicalIdentity::BooleanOr:
            name = "arith.ori";
            break;
          case MathematicalIdentity::BooleanXor:
            name = "arith.xori";
            break;
          case MathematicalIdentity::FieldConstant:
            name = "algebra.constant";
            break;
          case MathematicalIdentity::FieldAdd:
            name = "algebra.field_add";
            break;
          case MathematicalIdentity::FieldSubtract:
            name = "algebra.field_subtract";
            break;
          case MathematicalIdentity::FieldMultiply:
            name = "algebra.field_multiply";
            break;
          case MathematicalIdentity::FieldEqual:
            name = "algebra.field_equal";
            break;
          case MathematicalIdentity::GroupAdd:
            name = "algebra.group_add";
            break;
          case MathematicalIdentity::GroupIdentity:
            name = "algebra.group_identity";
            break;
          case MathematicalIdentity::GroupScale:
            name = "algebra.group_scale";
            break;
          case MathematicalIdentity::GroupEqual:
            name = "algebra.group_equal";
            break;
          case MathematicalIdentity::ArrayFromElements:
            name = "tensor.from_elements";
            break;
          case MathematicalIdentity::ArrayAt:
            name = "algebra.array_at";
            break;
          case MathematicalIdentity::PolynomialConstant:
            name = "poly.constant";
            break;
          case MathematicalIdentity::PolynomialFromCoefficients:
            name = "poly.from_coefficients";
            break;
          case MathematicalIdentity::PolynomialMLE:
            name = "poly.mle";
            break;
          case MathematicalIdentity::PolynomialAdd:
            name = "poly.add";
            break;
          case MathematicalIdentity::PolynomialMultiply:
            name = "poly.multiply";
            break;
          case MathematicalIdentity::PolynomialFix:
            name = "poly.fix";
            break;
          case MathematicalIdentity::PolynomialSum:
            name = "poly.sum_suffix";
            break;
          case MathematicalIdentity::PolynomialEvaluate:
            name = "poly.evaluate";
            break;
          case MathematicalIdentity::PolynomialCoefficients:
            name = "poly.coefficients";
            break;
          case MathematicalIdentity::PolynomialEvaluateDomain:
            name = "poly.evaluate_domain";
            break;
          case MathematicalIdentity::PolynomialInterpolate:
            name = "poly.interpolate";
            break;
          case MathematicalIdentity::PolynomialFixTable:
            name = "poly.fix_table";
            break;
          default:
            failure =
                error("source.emission", "unsupported mathematical identity");
            return false;
          }
          SmallVector<mlir::NamedAttribute> attrs;
          if (!math->literal.empty())
            attrs.push_back(text("value", math->literal));
          else if (math->identity == MathematicalIdentity::IndexConstant)
            attrs.push_back(text(
                "value",
                std::to_string(
                    math->staticArguments.front().dimension.closedValue())));
          if (math->identity == MathematicalIdentity::ArrayAt ||
              math->identity == MathematicalIdentity::PolynomialSum) {
            auto value = math->staticArguments[2].dimension.closedValue();
            attrs.push_back(attr(math->identity == MathematicalIdentity::ArrayAt
                                     ? "index"
                                     : "count",
                                 builder.getI64IntegerAttr(value)));
          }
          if (math->identity ==
                  MathematicalIdentity::PolynomialEvaluateDomain ||
              math->identity == MathematicalIdentity::PolynomialInterpolate)
            attrs.push_back(attr("points", strings(math->parameters)));
          actual = make(name, outputs, operands, attrs);
          break;
        }
        }
        if (!actual)
          return false;
        result = Values(actual->getResults());
        if (packed && packed->product) {
          if (packed->flat->leaves.size() > limits.operations - operations) {
            failure = error("source.limit",
                            "total sequence projection operation limit");
            return false;
          }
          operations += packed->flat->leaves.size();
          auto decoded =
              take(emitUnpack(builder, location, *packed, result.front(),
                              PackingMode::Mathematical, site + "_unpack"));
          if (!decoded)
            return false;
          result = std::move(*decoded);
        }
      } else if (auto *local = std::get_if<LocalPrimitive>(&op.action)) {
        auto operands = flatten(local->operands);
        std::optional<PackedLayout> packed;
        auto outputs = resultTypes;
        if (isSequenceKernel(local->contract)) {
          if (!local->bindingArguments ||
              local->bindingArguments->size() != 1) {
            failure = error("source.emission",
                            "sequence binding requires its element type");
            return false;
          }
          packed = take(layouts.packed(local->bindingArguments->front()));
          if (!packed)
            return false;
          if (local->contract == "sequence.append") {
            if (packed->product && ++operations > limits.operations) {
              failure =
                  error("source.limit", "emitted operation limit exceeded");
              return false;
            }
            auto item = take(emitPack(builder, location, *packed,
                                      values[local->operands[1].index],
                                      PackingMode::Local, site + "_pack"));
            if (!item)
              return false;
            operands = values[local->operands[0].index];
            operands.push_back(*item);
          }
          if (local->contract == "sequence.at")
            outputs = {protocol::decodeBoundType(&context, packed->carrier)};
        }
        auto emitted = primitive(
            local->contract, operands, outputs, local->parameters, site,
            local->bindingArguments
                ? std::optional<ArrayRef<Type>>(*local->bindingArguments)
                : std::nullopt);
        if (!emitted)
          return false;
        result = std::move(*emitted);
        if (packed && local->contract == "sequence.at") {
          operations += packed->product ? 2 : 0;
          if (operations > limits.operations) {
            failure = error("source.limit", "emitted operation limit exceeded");
            return false;
          }
          auto flat =
              take(emitUnpack(builder, location, *packed, result.front(),
                              PackingMode::Local, site + "_unpack"));
          if (!flat)
            return false;
          result = std::move(*flat);
        }
      } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
        const auto &target = project.declarations()[call->callee.index];
        auto operands = flatten(call->operands);
        std::string callee = target.symbol;
        if (target.kind == Declaration::Kind::Math &&
            source.mode == Body::Mode::Local) {
          auto symbol = realization(
              target, mlir::ValueRange(operands).getTypes(), resultTypes);
          if (!symbol)
            return false;
          callee = *symbol;
        }
        SmallVector<mlir::NamedAttribute> attrs{
            attr("callee", mlir::FlatSymbolRefAttr::get(&context, callee))};
        StringRef name = "func.call";
        if (target.kind == Declaration::Kind::Local ||
            source.mode == Body::Mode::Local) {
          name = source.mode == Body::Mode::Protocol ? "protocol.local_call"
                                                     : "local.apply";
          attrs.push_back(text("site", site));
          if (call->owner)
            attrs.push_back(text("role", nativeRoleName(*call->owner)));
        }
        auto *actual = make(name, resultTypes, operands, attrs);
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *finite = std::get_if<FiniteComputation>(&op.action)) {
        auto emitted =
            take(emitFinite(project, source, *finite,
                            source.values[op.results.front().index].type,
                            values, builder, location, *definitions, layouts,
                            "finite_" + decl.symbol + "_" + site, site, limits,
                            operations, remaining));
        if (!emitted)
          return false;
        result = std::move(*emitted);
      } else if (auto *bulk = std::get_if<BulkApplication>(&op.action)) {
        if (source.mode != Body::Mode::Local) {
          failure = error("source.mode", "map requires local mode");
          return false;
        }
        const auto &target = project.declarations()[bulk->callee.index];
        auto operands = flatten(bulk->operands);
        SmallVector<bool> mask(bulk->mapped.begin(), bulk->mapped.end());
        auto symbol = map(target, mask, mlir::ValueRange(operands).getTypes(),
                          resultTypes);
        if (!symbol)
          return false;
        auto *actual = make(
            "local.apply", resultTypes, operands,
            {attr("callee", mlir::FlatSymbolRefAttr::get(&context, *symbol)),
             text("site", site)});
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *query = std::get_if<ServiceQuery>(&op.action)) {
        const auto &port = source.services[query->service.index];
        SmallVector<mlir::Value> operands{services[query->service.index]};
        if (query->bound) {
          // The static domain becomes the query's constant bound operand.
          if (!query->bound->isClosed()) {
            failure = error("source.service", "index domain is not closed");
            return false;
          }
          auto *bound = make(
              "data.index", resultTypes, {},
              {text("value", std::to_string(query->bound->closedValue()))});
          if (!bound)
            return false;
          operands.push_back(bound->getResult(0));
        }
        auto *actual = make("protocol.query", resultTypes, operands,
                            {text("method", query->bound ? "index" : "draw"),
                             text("owner", nativeRoleName(port.owner)),
                             text("site", site)});
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *completion =
                     std::get_if<ProtocolCompletion>(&op.action)) {
        auto outputs = flatten(completion->values);
        auto inputs = values[completion->condition.index];
        llvm::append_range(inputs, outputs);
        mathematical::NativeTypePolicies policies(module.get());
        SmallVector<mlir::Type> affineTypes;
        SmallVector<bool> affine;
        for (auto value : outputs) {
          auto policy = policies.get(value.getType());
          if (!policy) {
            failure = error("source.layout",
                            "completion output has no native policy");
            return false;
          }
          affine.push_back(policy->affine);
          if (policy->affine)
            affineTypes.push_back(value.getType());
        }
        auto *actual = make("protocol.finish_if", affineTypes, inputs,
                            {text("owner", nativeRoleName(completion->owner)),
                             text("site", site)});
        if (!actual)
          return false;
        unsigned successor = 0;
        for (unsigned i = 0; i < outputs.size(); ++i)
          if (affine[i])
            outputs[i] = actual->getResult(successor++);
        unsigned offset = 0;
        for (unsigned i = 0; i < completion->values.size(); ++i) {
          unsigned width = values[completion->values[i].index].size();
          if (llvm::is_contained(completion->continuations, i))
            result.append(outputs.begin() + offset,
                          outputs.begin() + offset + width);
          offset += width;
        }
      } else if (auto *check = std::get_if<Require>(&op.action)) {
        const bool protocol = source.mode == Body::Mode::Protocol;
        if (source.mode == Body::Mode::Math ||
            protocol != check->owner.has_value()) {
          failure = error("source.mode",
                          "require owner does not match its body mode");
          return false;
        }
        if (protocol) {
          if (!make("protocol.guard", {}, values[check->condition.index],
                    {text("owner", nativeRoleName(*check->owner)),
                     text("site", site)}))
            return false;
        } else {
          auto *branch = make("local.if", {}, values[check->condition.index],
                              {text("site", site)}, 2);
          if (!branch)
            return false;
          mlir::OpBuilder::InsertionGuard insertion(builder);
          builder.setInsertionPointToEnd(&branch->getRegion(0).front());
          if (!make("local.yield", {}, {}, {}))
            return false;
          builder.setInsertionPointToEnd(&branch->getRegion(1).front());
          if (!make("local.stop", {}, {},
                    {text("site", site + "_reject"), text("reason", "reject")}))
            return false;
        }
      } else if (auto *application =
                     std::get_if<ProtocolApplication>(&op.action)) {
        const auto &target = project.declarations()[application->callee.index];
        auto operands = flatten(application->operands);
        for (auto service : application->services)
          operands.push_back(services[service.index]);
        auto *actual = make(
            "protocol.apply", resultTypes, operands,
            {attr("callee",
                  mlir::FlatSymbolRefAttr::get(&context, target.symbol)),
             text("site", site), attr("roles", roles(application->roles))});
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *exchange = std::get_if<Exchange>(&op.action)) {
        if (resultTypes.empty()) {
          failure = error("source.wire",
                          "empty layouts have no native message occurrence");
          return false;
        }
        for (unsigned i = 0; i < resultTypes.size(); ++i) {
          auto *sent =
              make("protocol.exchange", resultTypes[i],
                   values[exchange->payload.index][i],
                   {text("sender", nativeRoleName(exchange->sender)),
                    text("receiver", nativeRoleName(exchange->receiver)),
                    text("site", site + "_" + std::to_string(i))});
          if (!sent)
            return false;
          auto *received = make("protocol.restrict_roles", resultTypes[i],
                                sent->getResult(0),
                                {attr("roles", roles({exchange->receiver}))});
          if (!received)
            return false;
          result.push_back(received->getResult(0));
        }
      } else if (auto *restriction = std::get_if<Restriction>(&op.action)) {
        for (unsigned i = 0; i < resultTypes.size(); ++i) {
          auto *actual = make("protocol.restrict_roles", resultTypes[i],
                              values[restriction->input.index][i],
                              {attr("roles", roles(restriction->roles))});
          if (!actual)
            return false;
          result.push_back(actual->getResult(0));
        }
      } else if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        auto inputs = values[repeat->count.index];
        llvm::append_range(inputs, flatten(repeat->carried));
        llvm::append_range(inputs, flatten(repeat->captures));
        for (auto service : repeat->services)
          inputs.push_back(services[service.index]);
        SmallVector<mlir::Attribute> carriedRoles;
        for (unsigned i = 0; i < op.results.size(); ++i)
          for (unsigned j = 0; j < resultLayouts[i]->leaves.size(); ++j)
            carriedRoles.push_back(
                roles(source.values[op.results[i].index].components));
        auto *actual = make(
            "protocol.repeat", resultTypes, inputs,
            {text("site", site),
             attr("carried", builder.getI64IntegerAttr(resultTypes.size())),
             attr("maximum",
                  builder.getI64IntegerAttr(repeat->maximum.closedValue())),
             attr("roles", roles(repeat->roles)),
             attr("carried_roles", builder.getArrayAttr(carriedRoles))},
            1);
        if (!actual)
          return false;
        result = Values(actual->getResults());
        mlir::OpBuilder::InsertionGuard guard(builder);
        if (!body(decl, *repeat->region, actual->getRegion(0).front(), true))
          return false;
      } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
        auto inputs = flatten(control->operands);
        bool match = control->kind == LocalControl::Kind::Match;
        std::vector<std::string> labels;
        if (match) {
          auto subject = take(
              layouts.get(source.values[control->operands.front().index].type));
          if (!subject)
            return false;
          // Arms retain authored order; labels come from the type's roster.
          for (const auto &name : control->alternatives) {
            auto label = alternative(**subject, name);
            if (!label)
              return false;
            labels.push_back(std::move(*label));
          }
          if ((**subject).custody) {
            if (!retire(inputs.front(), site + "_match"))
              return false;
            inputs.erase(inputs.begin());
          }
        }
        SmallVector<mlir::NamedAttribute> attrs{text("site", site)};
        if (match)
          attrs.push_back(attr("alternatives", strings(labels)));
        auto *actual =
            make(match                                      ? "local.match"
                 : control->kind == LocalControl::Kind::For ? "local.for"
                                                            : "local.if",
                 resultTypes, inputs, attrs, control->regions.size());
        if (!actual)
          return false;
        result = Values(actual->getResults());
        for (unsigned i = 0; i < control->regions.size(); ++i) {
          mlir::OpBuilder::InsertionGuard guard(builder);
          if (!body(decl, *control->regions[i], actual->getRegion(i).front(),
                    true))
            return false;
        }
      } else {
        failure = error("source.emission", "source operation has no emitter");
        return false;
      }
      if (result.size() != resultTypes.size()) {
        failure = error("source.layout", "operation result layout differs");
        return false;
      }
      unsigned offset = 0;
      for (unsigned i = 0; i < op.results.size(); ++i) {
        const auto count = resultLayouts[i]->leaves.size();
        values[op.results[i].index] =
            Values(result.begin() + offset, result.begin() + offset + count);
        offset += count;
      }
    }
    if (source.stopped)
      return make("local.stop", {}, {},
                  {text("site", "stop" + std::to_string(siteOrdinal++)),
                   text("reason", source.stopReason)});
    auto results = flatten(source.results);
    return make(region && source.mode == Body::Mode::Protocol ? "protocol.yield"
                : region                                      ? "local.yield"
                : source.mode == Body::Mode::Protocol ? "protocol.return"
                : source.mode == Body::Mode::Local    ? "local.return"
                                                      : "func.return",
                {}, results, {});
  }

  std::set<unsigned> emittedConstructions;
  bool construction(const Declaration &definition) {
    if (!emittedConstructions.insert(definition.id.index).second)
      return true;
    const auto &plan = *definition.construction;
    const auto &target = project.declarations()[definition.target->index];
    SmallVector<mlir::Attribute> applications;
    for (const auto &application : plan.applications) {
      const auto &child =
          project.declarations()[application.construction.index];
      if (!construction(child))
        return false;
      std::string site;
      for (const auto &part : application.path) {
        auto label = nativeSiteName(part, 0);
        site = site.empty()
                   ? label
                   : mathematical::expandedApplicationSite(site, label);
      }
      applications.push_back(builder.getDictionaryAttr(
          {text("site", site),
           attr("construction",
                mlir::FlatSymbolRefAttr::get(&context, child.symbol))}));
    }
    auto stateLayout = take(layouts.get(*plan.state));
    if (!stateLayout)
      return false;
    auto state = types(**stateLayout);
    if (!state)
      return false;
    auto typeAttrs = [&](mlir::TypeRange values) {
      SmallVector<mlir::Attribute> attrs;
      for (auto type : values)
        attrs.push_back(mlir::TypeAttr::get(type));
      return builder.getArrayAttr(attrs);
    };
    std::vector<unsigned> offsets{0};
    for (const auto &port : target.inputs) {
      auto layout = take(layouts.get(port.type));
      if (!layout)
        return false;
      offsets.push_back(offsets.back() + (*layout)->leaves.size());
    }
    SmallVector<mlir::Attribute> rules;
    for (const auto &rule : plan.rules) {
      const auto &handler = project.declarations()[rule.handler.index];
      SmallVector<mlir::Type> payload, chunks;
      SmallVector<int64_t> inputs;
      std::vector<std::string> sites;
      StringRef kind = protocol::constructionRuleName(rule.kind);
      if (rule.kind == ConstructionRule::Kind::Start) {
        for (auto port : rule.inputs)
          for (unsigned i = offsets[port]; i < offsets[port + 1]; ++i)
            inputs.push_back(i);
      } else {
        auto layout = take(layouts.get(*rule.payload));
        if (!layout)
          return false;
        auto native = types(**layout);
        if (!native)
          return false;
        payload = *native;
        if (rule.chunks) {
          auto wire = take(layouts.get(*rule.chunks));
          if (!wire)
            return false;
          auto values = types(**wire);
          if (!values)
            return false;
          chunks = *values;
        }
        auto qualified = [&](std::string site) {
          std::string prefix;
          for (auto &part : ArrayRef(rule.path).drop_back()) {
            auto label = nativeSiteName(part, 0);
            prefix = prefix.empty()
                         ? label
                         : mathematical::expandedApplicationSite(prefix, label);
          }
          return prefix.empty()
                     ? site
                     : mathematical::expandedApplicationSite(prefix, site);
        };
        auto label = nativeSiteName(rule.path.back(), 0);
        if (kind == "query")
          sites.push_back(qualified(label));
        else
          for (unsigned i = 0; i < payload.size(); ++i)
            sites.push_back(qualified(label + "_" + std::to_string(i)));
      }
      rules.push_back(builder.getDictionaryAttr(
          {text("kind", kind),
           attr("handler",
                mlir::FlatSymbolRefAttr::get(&context, handler.symbol)),
           attr("sites", strings(sites)),
           attr("inputs", builder.getDenseI64ArrayAttr(inputs)),
           attr("payload", typeAttrs(payload)),
           attr("chunks", typeAttrs(chunks))}));
    }
    SmallVector<int64_t> replaced;
    for (auto port : plan.services)
      replaced.push_back(offsets.back() + port);
    SmallVector<mlir::NamedAttribute> attrs{
        text("sym_name", definition.symbol),
        attr("target", mlir::FlatSymbolRefAttr::get(&context, target.symbol)),
        text("provider", typeIdentity(*plan.provider)),
        text("root", plan.root == ConstructionDefinition::Root::Local ? "local"
                                                                      : "host"),
        attr("state", typeAttrs(*state)),
        text("suite", plan.suite),
        attr("services", builder.getDenseI64ArrayAttr(replaced)),
        attr("native_base", builder.getBoolAttr(plan.nativeBase)),
        attr("root_only",
             builder.getBoolAttr(definition.proofFormat.has_value() ||
                                 plan.nativeBase)),
        attr("rules", builder.getArrayAttr(rules)),
        attr("applications", builder.getArrayAttr(applications))};
    if (plan.codec) {
      const auto &codec = *plan.codec;
      auto layout = take(layouts.get(codec.record));
      if (!layout)
        return false;
      auto recordTypes = types(**layout);
      if (!recordTypes)
        return false;
      SmallVector<int64_t> inputs;
      for (unsigned port : codec.inputs)
        for (unsigned i = offsets[port]; i < offsets[port + 1]; ++i)
          inputs.push_back(i);
      auto method = [&](const ConstructionMethod &method) {
        return mlir::FlatSymbolRefAttr::get(
            &context,
            project.declarations()[method.target.declaration.index].symbol);
      };
      attrs.push_back(
          attr("codec",
               builder.getDictionaryAttr(
                   {text("provider", typeIdentity(codec.provider)),
                    attr("record", typeAttrs(*recordTypes)),
                    attr("initialize", method(codec.initialize)),
                    attr("write", method(codec.write)),
                    attr("finish", method(codec.finish)),
                    attr("inputs", builder.getDenseI64ArrayAttr(inputs))})));
    }
    if (plan.initializer)
      attrs.push_back(
          attr("initializer",
               mlir::FlatSymbolRefAttr::get(
                   &context,
                   project.declarations()[plan.initializer->declaration.index]
                       .symbol)));
    builder.setInsertionPointToEnd(definitions);
    return make("protocol.construction", {}, {}, attrs);
  }

public:
  Emitter(const ClosedEntry &project, mlir::MLIRContext &context,
          const Limits &limits)
      : project(project), limits(limits), context(context), builder(&context),
        location(builder.getUnknownLoc()), layouts(project, limits),
        module(mlir::ModuleOp::create(location)), remaining(limits.work) {
    for (const auto &decl : project.declarations())
      if ((decl.body || (decl.relation && decl.origin)) &&
          decl.parameters.empty()) {
        symbols.insert(decl.symbol);
        if (decl.relation && decl.body)
          symbols.insert(formulaSymbol(decl));
      }
    (void)!!failure;
  }
  Expected<std::string> run() {
    builder.setInsertionPointToEnd(module->getBody());
    auto *unit =
        make("protocol.module", {}, {},
             {attr("profile", protocol_ir::ProfileAttr::get(
                                  &context, protocol_ir::Profile::Protocol))},
             1);
    if (!unit)
      return std::move(failure);
    definitions = &unit->getRegion(0).front();
    for (auto &decl : project.declarations()) {
      if (!decl.body || !decl.parameters.empty())
        continue;
      declaration = decl.qualifiedName;
      SmallVector<mlir::Type> ins, outs;
      SmallVector<mlir::Attribute> inRoles, outRoles;
      for (bool input : {true, false})
        for (auto &port : input ? decl.inputs : decl.outputs) {
          auto layout = take(layouts.get(port.type));
          if (!layout)
            return std::move(failure);
          auto ts = types(**layout);
          if (!ts)
            return std::move(failure);
          llvm::append_range(input ? ins : outs, *ts);
          for (unsigned i = 0; i < ts->size(); ++i)
            (input ? inRoles : outRoles).push_back(roles(port.roles));
        }
      for (const auto &port : decl.services) {
        ins.push_back(
            protocol_ir::ServiceReferenceType::get(&context, port.contract));
        inRoles.push_back(roles({port.owner}));
      }
      SmallVector<mlir::NamedAttribute> attrs{
          text("sym_name", decl.relation ? formulaSymbol(decl) : decl.symbol),
          attr("function_type",
               mlir::TypeAttr::get(builder.getFunctionType(ins, outs)))};
      if (!decl.dataPreconditions.empty()) {
        auto conditions = take(flattenDataPreconditions(decl, layouts));
        if (!conditions)
          return std::move(failure);
        attrs.push_back(attr("data.preconditions",
                             emitDataPreconditions(&context, *conditions)));
      }
      bool protocol = decl.kind == Declaration::Kind::Protocol,
           local = decl.kind == Declaration::Kind::Local;
      if (protocol) {
        std::vector<std::string> roster;
        for (unsigned i = 0; i < decl.roles.size(); ++i)
          roster.push_back(nativeRoleName(i));
        attrs.append({attr("roles", strings(roster)),
                      attr("input_roles", builder.getArrayAttr(inRoles)),
                      attr("output_roles", builder.getArrayAttr(outRoles))});
      } else {
        if (!local)
          attrs.push_back(text("sym_visibility", "private"));
        if (local)
          attrs.push_back(
              attr("logical_origin",
                   builder.getArrayAttr(
                       {builder.getStringAttr(logicalOrigin(project, decl)),
                        builder.getArrayAttr({})})));
      }
      builder.setInsertionPointToEnd(definitions);
      auto *function = make(protocol ? "protocol.func"
                            : local  ? "local.func"
                                     : "func.func",
                            {}, {}, attrs, 1);
      if (!function)
        return std::move(failure);
      siteOrdinal = 0;
      if (!body(decl, *decl.body, function->getRegion(0).front()))
        return std::move(failure);
    }
    if (const auto *proof = project.entry().proof();
        proof && proof->construction == ProofEntry::Construction::Derived)
      if (!construction(
              project.declarations()[proof->selectedConstruction->index]))
        return std::move(failure);
    mlir::SymbolTable table(unit);
    relation::FormulaIdentities formulas(remaining, limits.irBytes);
    LayoutIdentities schemaIdentities(remaining);
    for (const auto &decl : project.declarations()) {
      if (!decl.relation || !decl.origin)
        continue;
      const auto &definition = *decl.relation;
      declaration = decl.qualifiedName;
      SmallVector<mlir::Type> inputs;
      std::vector<std::string> purposes, logicalInputs, logicalPurposes;
      for (unsigned i = 0; i < decl.inputs.size(); ++i) {
        auto layout = take(layouts.get(decl.inputs[i].type));
        if (!layout)
          return std::move(failure);
        auto native = types(**layout);
        if (!native)
          return std::move(failure);
        llvm::append_range(inputs, *native);
        auto purpose =
            definition.purposes[i] == RelationPurpose::Parameter   ? "parameter"
            : definition.purposes[i] == RelationPurpose::Statement ? "statement"
                                                                   : "witness";
        purposes.insert(purposes.end(), native->size(), purpose);
        logicalPurposes.push_back(purpose);
        auto schema = take(schemaIdentities.get(**layout));
        if (!schema)
          return std::move(failure);
        logicalInputs.push_back(std::move(*schema));
      }
      std::string kind = definition.externalKind, key = definition.key,
                  revision = definition.revision;
      using K = RelationDefinition::Kind;
      if (definition.kind == K::Formula) {
        auto helper = table.lookup<mlir::func::FuncOp>(formulaSymbol(decl));
        auto identity =
            take(formulas.get(helper, logicalInputs, logicalPurposes));
        if (!identity)
          return std::move(failure);
        kind = "zkc.language.formula/0";
        key = decl.symbol;
        revision = std::move(*identity);
      } else if (definition.kind != K::Opaque) {
        const auto &asset = project.project().assets()[*definition.asset];
        kind = definition.kind == K::R1CS  ? "zkc.relation.r1cs/0"
               : definition.kind == K::AIR ? "zkc.relation.air/0"
                                           : "zkc.relation.bundle/0";
        key = asset.identity().str();
        revision = "0";
      }
      builder.setInsertionPointToEnd(definitions);
      if (!make("relation.declare", {}, {},
                {text("sym_name", decl.symbol), text("kind", kind),
                 text("key", key), text("revision", revision),
                 attr("signature", mlir::TypeAttr::get(builder.getFunctionType(
                                       inputs, {builder.getI1Type()}))),
                 attr("purposes", strings(purposes))}))
        return std::move(failure);
    }
    std::string result;
    mlir::AsmState state(*module, canonicalPrintingFlags());
    BoundedStream stream(result, limits.irBytes);
    module->print(stream, state);
    stream << '\n';
    if (stream.overflow())
      return error("source.limit", "emitted MLIR byte limit exceeded");
    return result;
  }
};
} // namespace
namespace {
Expected<SmallVector<mlir::Type>> packedLeafTypes(mlir::MLIRContext *context,
                                                  const PackedLayout &layout) {
  SmallVector<mlir::Type> types;
  for (const auto &leaf : layout.flat->leaves) {
    if (!leaf.data())
      return error("source.layout", "packed payload contains formal data");
    auto bound = protocol::parseBoundType(*leaf.data(), false);
    if (!bound)
      return bound.takeError();
    auto type = protocol::decodeBoundType(context, *bound);
    if (!type)
      return error("source.layout", "packed payload dialect unavailable");
    types.push_back(type);
  }
  return types;
}
} // namespace
Expected<mlir::Value> emitPack(mlir::OpBuilder &builder,
                               mlir::Location location,
                               const PackedLayout &layout,
                               mlir::ValueRange leaves, PackingMode mode,
                               StringRef site) {
  auto types = packedLeafTypes(builder.getContext(), layout);
  if (!types)
    return types.takeError();
  if (leaves.getTypes() != mlir::TypeRange(*types))
    return error("source.layout", "pack operands differ from the flat layout");
  auto carrier =
      protocol::decodeBoundType(builder.getContext(), layout.carrier);
  if (!carrier)
    return error("source.layout", "packed carrier dialect unavailable");
  if (!layout.product) {
    if (leaves.size() != 1 || leaves.front().getType() != carrier)
      return error("source.layout", "native element carrier differs");
    return leaves.front();
  }
  mlir::OperationState state(location, mode == PackingMode::Local
                                           ? "local.variant_inject"
                                           : "data.make");
  state.addTypes(carrier);
  state.addOperands(leaves);
  state.addAttribute("alternative", builder.getStringAttr(layout.alternative));
  if (mode == PackingMode::Local)
    state.addAttribute("site", builder.getStringAttr(site));
  return builder.create(state)->getResult(0);
}
Expected<SmallVector<mlir::Value>>
emitUnpack(mlir::OpBuilder &builder, mlir::Location location,
           const PackedLayout &layout, mlir::Value value, PackingMode mode,
           StringRef site) {
  auto types = packedLeafTypes(builder.getContext(), layout);
  if (!types)
    return types.takeError();
  auto carrier =
      protocol::decodeBoundType(builder.getContext(), layout.carrier);
  if (!carrier || value.getType() != carrier)
    return error("source.layout", "unpack operand differs from its carrier");
  if (!layout.product) {
    if (types->size() != 1 || types->front() != carrier)
      return error("source.layout", "native element flat layout differs");
    return SmallVector<mlir::Value>{value};
  }
  if (mode == PackingMode::Mathematical) {
    SmallVector<mlir::Value> leaves;
    for (unsigned i = 0; i < types->size(); ++i) {
      mlir::OperationState state(location, "data.get");
      state.addOperands(value);
      state.addTypes((*types)[i]);
      state.addAttribute("index", builder.getI64IntegerAttr(i));
      leaves.push_back(builder.create(state)->getResult(0));
    }
    return leaves;
  }
  mlir::OperationState state(location, "local.match");
  state.addOperands(value);
  state.addTypes(*types);
  state.addAttribute("site", builder.getStringAttr(site));
  state.addAttribute("alternatives",
                     builder.getStrArrayAttr({layout.alternative}));
  state.addRegion()->push_back(new mlir::Block());
  auto *match = builder.create(state);
  auto &arm = match->getRegion(0).front();
  for (auto type : *types)
    arm.addArgument(type, location);
  mlir::OpBuilder::InsertionGuard guard(builder);
  builder.setInsertionPointToEnd(&arm);
  mlir::OperationState yield(location, "local.yield");
  yield.addOperands(arm.getArguments());
  builder.create(yield);
  return SmallVector<mlir::Value>(match->getResults());
}
Expected<std::string> emitOriginal(const ClosedEntry &project,
                                   mlir::MLIRContext &context,
                                   const Limits &limits) {
  if (auto e = checkLimits(limits))
    return e;
  if (project.project().checkedWork() > limits.work ||
      uint64_t(llvm::count_if(project.declarations(), [](const auto &decl) {
        return bool(decl.body);
      })) > limits.declarations)
    return error("source.limit",
                 "checked project exceeds requested emission limits");
  if (auto e = checkScopedElaboration(project.project(), limits))
    return e;
  if (auto e = checkScopedSpecialization(project, limits))
    return e;
  if (!hasProtocolDialects(context))
    return error("source.dialects",
                 "native dialects must be loaded before source emission");
  return Emitter(project, context, limits).run();
}
} // namespace zkc::language
