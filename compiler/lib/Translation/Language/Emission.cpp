#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Language.h"
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
  Layouts layouts;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  mlir::Block *definitions = nullptr;
  std::map<std::pair<std::string, std::vector<std::string>>, std::string>
      bindings;
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
      if (leaf.size() + 1 > remaining) {
        failure =
            error("source.limit", "native type emission work limit exceeded");
        return {};
      }
      remaining -= leaf.size() + 1;
      auto bound = take(protocol::parseBoundType(leaf, false));
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
                                  StringRef site) {
    if (contract == "bool.constant") {
      auto *op = make(
          "local.bool_constant", outputs, {},
          {attr("value", builder.getBoolAttr(parameters.front() == "true")),
           text("site", site)});
      return op ? std::optional<Values>(Values(op->getResults()))
                : std::nullopt;
    }
    if (contract == "bool.equal") {
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
    if (contract.starts_with("field.") || contract.starts_with("curve.") ||
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
  bool retire(mlir::Value value, StringRef site) {
    return bool(primitive("resource_unit.consume", value, {}, {}, site));
  }
  mlir::ArrayAttr roles(const Declaration &decl, ArrayRef<unsigned> indices) {
    SmallVector<mlir::Attribute> result;
    for (auto index : indices)
      result.push_back(builder.getStringAttr(decl.roles[index]));
    return builder.getArrayAttr(result);
  }
  bool body(const Declaration &decl, const Body &source, mlir::Block &block,
            bool region = false) {
    builder.setInsertionPointToEnd(&block);
    std::vector<Values> values(source.values.size());
    unsigned cursor = 0;
    for (unsigned i = 0; i < source.inputs; ++i) {
      auto layout = take(layouts.get(source.values[i].type));
      if (!layout)
        return false;
      auto ts = types(**layout);
      if (!ts)
        return false;
      for (auto type : *ts) {
        if (cursor < block.getNumArguments())
          values[i].push_back(block.getArgument(cursor));
        else
          values[i].push_back(block.addArgument(type, location));
        ++cursor;
      }
    }
    Values services;
    for (const auto &port : source.services) {
      auto type =
          protocol_ir::ServiceReferenceType::get(&context, port.contract);
      services.push_back(cursor < block.getNumArguments()
                             ? block.getArgument(cursor)
                             : block.addArgument(type, location));
      ++cursor;
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
      auto site = "s" + std::to_string(siteOrdinal++);
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
            auto *actual =
                make("local.variant_inject", resultTypes.back(), input,
                     {text("site", site),
                      text("alternative", construct->alternative)});
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
          if (StringRef((**input).leaves[i]).starts_with("resource_unit:") &&
              !retire(values[consume->input.index][i],
                      site + "_" + std::to_string(i)))
            return false;
      } else if (auto *math = std::get_if<MathValue>(&op.action)) {
        auto operands = flatten(math->operands);
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
          case MathematicalIdentity::GroupScale:
            name = "algebra.group_scale";
            break;
          case MathematicalIdentity::GroupEqual:
            name = "algebra.group_equal";
            break;
          default:
            failure =
                error("source.emission", "unsupported mathematical identity");
            return false;
          }
          SmallVector<mlir::NamedAttribute> attrs;
          if (!math->literal.empty())
            attrs.push_back(text("value", math->literal));
          actual = make(name, resultTypes, operands, attrs);
          break;
        }
        }
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *local = std::get_if<LocalPrimitive>(&op.action)) {
        auto emitted = primitive(local->contract, flatten(local->operands),
                                 resultTypes, local->parameters, site);
        if (!emitted)
          return false;
        result = std::move(*emitted);
      } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
        const auto &target = project.declarations()[call->callee.index];
        SmallVector<mlir::NamedAttribute> attrs{attr(
            "callee", mlir::FlatSymbolRefAttr::get(&context, target.symbol))};
        StringRef name = "func.call";
        if (target.kind == Declaration::Kind::Local) {
          name = source.mode == Body::Mode::Protocol ? "protocol.local_call"
                                                     : "local.apply";
          attrs.push_back(text("site", site));
          if (call->owner)
            attrs.push_back(text("role", decl.roles[*call->owner]));
        }
        auto *actual = make(name, resultTypes, flatten(call->operands), attrs);
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *query = std::get_if<ServiceQuery>(&op.action)) {
        const auto &port = source.services[query->service.index];
        auto *actual =
            make("protocol.query", resultTypes, services[query->service.index],
                 {text("method", "draw"), text("owner", decl.roles[port.owner]),
                  text("site", site)});
        if (!actual)
          return false;
        result = Values(actual->getResults());
      } else if (auto *guard = std::get_if<ProtocolGuard>(&op.action)) {
        if (!make(
                "protocol.guard", {}, values[guard->condition.index],
                {text("owner", decl.roles[guard->owner]), text("site", site)}))
          return false;
      } else if (auto *application =
                     std::get_if<ProtocolApplication>(&op.action)) {
        const auto &target = project.declarations()[application->callee.index];
        auto operands = flatten(application->operands);
        for (auto service : application->services)
          operands.push_back(services[service.index]);
        auto *actual =
            make("protocol.apply", resultTypes, operands,
                 {attr("callee",
                       mlir::FlatSymbolRefAttr::get(&context, target.symbol)),
                  text("site", site),
                  attr("roles", roles(decl, application->roles))});
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
          auto *sent = make("protocol.exchange", resultTypes[i],
                            values[exchange->payload.index][i],
                            {text("sender", decl.roles[exchange->sender]),
                             text("receiver", decl.roles[exchange->receiver]),
                             text("site", site + "_" + std::to_string(i))});
          if (!sent)
            return false;
          auto *received = make(
              "protocol.restrict_roles", resultTypes[i], sent->getResult(0),
              {attr("roles", roles(decl, {exchange->receiver}))});
          if (!received)
            return false;
          result.push_back(received->getResult(0));
        }
      } else if (auto *restriction = std::get_if<Restriction>(&op.action)) {
        for (unsigned i = 0; i < resultTypes.size(); ++i) {
          auto *actual = make("protocol.restrict_roles", resultTypes[i],
                              values[restriction->input.index][i],
                              {attr("roles", roles(decl, restriction->roles))});
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
                roles(decl, source.values[op.results[i].index].components));
        auto *actual = make(
            "protocol.repeat", resultTypes, inputs,
            {text("site", site),
             attr("carried", builder.getI64IntegerAttr(resultTypes.size())),
             attr("maximum",
                  builder.getI64IntegerAttr(repeat->maximum.closedValue())),
             attr("roles", roles(decl, repeat->roles)),
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
        if (match) {
          auto subject = take(
              layouts.get(source.values[control->operands.front().index].type));
          if (!subject)
            return false;
          if ((**subject).custody) {
            if (!retire(inputs.front(), site + "_match"))
              return false;
            inputs.erase(inputs.begin());
          }
        }
        SmallVector<mlir::NamedAttribute> attrs{text("site", site)};
        if (match)
          attrs.push_back(attr("alternatives", strings(control->alternatives)));
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

public:
  Emitter(const ClosedEntry &project, mlir::MLIRContext &context,
          const Limits &limits)
      : project(project), limits(limits), context(context), builder(&context),
        location(builder.getUnknownLoc()), layouts(project, limits),
        module(mlir::ModuleOp::create(location)), remaining(limits.work) {
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
            (input ? inRoles : outRoles).push_back(roles(decl, port.roles));
        }
      for (const auto &port : decl.services) {
        ins.push_back(
            protocol_ir::ServiceReferenceType::get(&context, port.contract));
        inRoles.push_back(roles(decl, {port.owner}));
      }
      SmallVector<mlir::NamedAttribute> attrs{
          text("sym_name", decl.symbol),
          attr("function_type",
               mlir::TypeAttr::get(builder.getFunctionType(ins, outs)))};
      bool protocol = decl.kind == Declaration::Kind::Protocol,
           local = decl.kind == Declaration::Kind::Local;
      if (protocol)
        attrs.append({attr("roles", strings(decl.roles)),
                      attr("input_roles", builder.getArrayAttr(inRoles)),
                      attr("output_roles", builder.getArrayAttr(outRoles))});
      else {
        if (!local)
          attrs.push_back(text("sym_visibility", "private"));
        if (local)
          attrs.push_back(attr(
              "logical_origin",
              builder.getArrayAttr(
                  {builder.getStringAttr(
                       decl.origin
                           ? project.declarations()[decl.origin->index].symbol
                           : decl.symbol),
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
    std::string result;
    mlir::OpPrintingFlags flags;
    flags.printGenericOpForm(true)
        .enableDebugInfo(false)
        .skipRegions(false)
        .assumeVerified(false)
        .useLocalScope(false)
        .printValueUsers(false)
        .printUniqueSSAIDs(false)
        .printNameLocAsPrefix(false);
    mlir::AsmState state(*module, flags);
    BoundedStream stream(result, limits.irBytes);
    module->print(stream, state);
    stream << '\n';
    if (stream.overflow())
      return error("source.limit", "emitted MLIR byte limit exceeded");
    return result;
  }
};
} // namespace
Expected<std::string> emitOriginal(const ClosedEntry &project,
                                   mlir::MLIRContext &context,
                                   const Limits &limits) {
  if (auto e = checkLimits(limits))
    return e;
  if (project.project().checkedWork() > limits.work ||
      project.declarations().size() > limits.declarations)
    return error("source.limit",
                 "checked project exceeds requested emission limits");
  if (!hasProtocolDialects(context))
    return error("source.dialects",
                 "native dialects must be loaded before source emission");
  return Emitter(project, context, limits).run();
}
} // namespace zkc::language
