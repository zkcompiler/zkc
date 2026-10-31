#include "Native.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Layout.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
using namespace llvm;
namespace zkc::language::entry_detail {
namespace {
class Emitter {
  const ClosedEntry &entry;
  const Limits &limits;
  Layouts layouts;
  mlir::OpBuilder builder;
  mlir::Location location;
  NativeHost result;
  mlir::Region *functionBody = nullptr;
  mlir::Block *failure = nullptr;
  exec::OutcomeType outcome;
  uint64_t operations = 0;
  std::map<const Layout *, data::LayoutAttr> nativeLayouts;
  using Environment = std::map<unsigned, mlir::Value>;

  Expected<data::LayoutAttr> layout(const Layout &source) {
    if (auto found = nativeLayouts.find(&source); found != nativeLayouts.end())
      return found->second;
    if (source.formal || source.custody || !source.permissions.copy)
      return error("entry.value", "Host values require ordinary Copy data");
    auto *context = builder.getContext();
    auto fields = [&](ArrayRef<LayoutField> source)
        -> Expected<SmallVector<data::LayoutFieldAttr>> {
      SmallVector<data::LayoutFieldAttr> result;
      for (const auto &field : source) {
        auto nested = layout(*field.layout);
        if (!nested)
          return nested.takeError();
        result.push_back(data::LayoutFieldAttr::get(
            context, builder.getStringAttr(field.name), field.offset, *nested));
      }
      return result;
    };
    auto members = fields(source.fields);
    if (!members)
      return members.takeError();
    SmallVector<data::LayoutAlternativeAttr> alternatives;
    for (const auto &arm : source.alternatives) {
      auto payload = fields(arm.fields);
      if (!payload)
        return payload.takeError();
      alternatives.push_back(data::LayoutAlternativeAttr::get(
          context, builder.getStringAttr(arm.name), *payload));
    }
    SmallVector<mlir::Type> leaves;
    for (const auto &leaf : source.leaves) {
      if (!leaf.data())
        return error("entry.value", "Host layout contains a nondata leaf");
      // This is the checked-language/native lowering boundary. Native layouts
      // thereafter retain actual Types; no JSON schema is built or imported.
      auto bound = protocol::parseBoundType(*leaf.data(), false);
      if (!bound)
        return bound.takeError();
      auto native = protocol::decodeBoundType(context, *bound);
      if (!native)
        return error("entry.value", "Host leaf has no native owner");
      leaves.push_back(native);
    }
    auto identity = toHex(
        SHA256::hash(arrayRefFromStringRef(typeIdentity(source.type))), true);
    auto native = data::LayoutAttr::getChecked(
        location, context,
        builder.getStringAttr(typeKindName(source.type.kind)),
        builder.getStringAttr(identity),
        builder.getStringAttr(spelling(source.type)), source.custody,
        source.constructible, source.permissions.copy, source.permissions.drop,
        ArrayRef<data::LayoutFieldAttr>(*members),
        ArrayRef<data::LayoutAlternativeAttr>(alternatives),
        ArrayRef<mlir::Type>(leaves));
    if (!native)
      return error("entry.value", "Host native layout failed formation");
    nativeLayouts.emplace(&source, native);
    return native;
  }
  Expected<mlir::Type> type(const Type &source) {
    auto schema = layouts.get(source);
    if (!schema)
      return schema.takeError();
    auto native = layout(**schema);
    if (!native)
      return native.takeError();
    return data::valueType(*native);
  }
  Expected<SmallVector<mlir::Type>> types(ArrayRef<Type> source) {
    SmallVector<mlir::Type> result;
    for (const auto &value : source) {
      auto native = type(value);
      if (!native)
        return native.takeError();
      result.push_back(*native);
    }
    return result;
  }
  mlir::Operation *make(StringRef name, mlir::TypeRange outputs,
                        mlir::ValueRange inputs,
                        ArrayRef<mlir::NamedAttribute> attrs = {},
                        ArrayRef<mlir::Block *> successors = {}) {
    mlir::OperationState state(location, name);
    state.addTypes(outputs);
    state.addOperands(inputs);
    state.addAttributes(attrs);
    state.addSuccessors(successors);
    return builder.create(state);
  }
  mlir::Block *block(mlir::TypeRange types = {}) {
    auto *result = new mlir::Block;
    functionBody->push_back(result);
    for (auto type : types)
      result->addArgument(type, location);
    return result;
  }
  void branch(mlir::Block *target, mlir::ValueRange values = {}) {
    mlir::cf::BranchOp::create(builder, location, target, values);
  }
  SmallVector<mlir::Value> fallible(StringRef name, mlir::TypeRange outputs,
                                    mlir::ValueRange inputs,
                                    ArrayRef<mlir::NamedAttribute> attrs = {}) {
    SmallVector<mlir::Type> payload(outputs);
    auto type = exec::OutcomeType::get(builder.getContext(), payload);
    auto *call = make(name, type, inputs, attrs);
    auto *next = block(outputs);
    make("exec.dispatch", {}, call->getResults(), {}, {next, failure});
    builder.setInsertionPointToEnd(next);
    return SmallVector<mlir::Value>(next->getArguments());
  }
  Expected<SmallVector<mlir::Value>> operands(ArrayRef<ValueId> inputs,
                                              const Environment &env) {
    SmallVector<mlir::Value> result;
    for (auto input : inputs) {
      auto found = env.find(input.index);
      if (found == env.end())
        return error("entry.scope", "Host operand does not dominate");
      result.push_back(found->second);
    }
    return result;
  }
  Error body(const Declaration &owner, const Body &source, mlir::Block *start,
             mlir::ValueRange incoming, mlir::Block *continuation,
             unsigned depth, std::optional<ArrayRef<Type>> loopState = {}) {
    if (depth > limits.callDepth || incoming.size() != source.inputs)
      return error("source.limit", "Host region depth or input signature");
    Environment env;
    for (auto [i, value] : enumerate(incoming))
      env.emplace(i, value);
    builder.setInsertionPointToEnd(start);
    for (const auto &operation : source.operations) {
      if (++operations > limits.operations)
        return error("source.limit", "Host operation limit");
      SmallVector<Type> resultTypes;
      for (auto output : operation.results)
        resultTypes.push_back(source.values[output.index].type);
      auto outputTypes = types(resultTypes);
      if (!outputTypes)
        return outputTypes.takeError();
      std::vector<ValueId> inputIds;
      StringRef name;
      SmallVector<mlir::NamedAttribute> attrs;
      SmallVector<mlir::Value> values;
      if (auto *control = std::get_if<LocalControl>(&operation.action)) {
        auto inputs = operands(control->operands, env);
        if (!inputs)
          return inputs.takeError();
        if (control->kind == LocalControl::Kind::If) {
          auto captures = ArrayRef(*inputs).drop_front();
          auto captureTypes = mlir::ValueRange(captures).getTypes();
          auto *next = block(*outputTypes), *yes = block(captureTypes),
               *no = block(captureTypes);
          mlir::cf::CondBranchOp::create(builder, location, inputs->front(),
                                         yes, captures, no, captures);
          mlir::Block *arms[] = {yes, no};
          for (auto [region, target] : zip(control->regions, arms))
            if (auto error = body(owner, *region, target,
                                  target->getArguments(), next, depth + 1))
              return error;
          builder.setInsertionPointToEnd(next);
          append_range(values, next->getArguments());
        } else if (control->kind == LocalControl::Kind::Match) {
          auto *next = block(*outputTypes);
          SmallVector<mlir::Block *> arms;
          for (const auto &region : control->regions) {
            SmallVector<Type> arguments;
            for (unsigned i = 0; i < region->inputs; ++i)
              arguments.push_back(region->values[i].type);
            auto native = types(arguments);
            if (!native)
              return native.takeError();
            arms.push_back(block(*native));
          }
          SmallVector<mlir::Attribute> names;
          for (const auto &alternative : control->alternatives)
            names.push_back(builder.getStringAttr(alternative));
          SmallVector<mlir::Value> forwarded{inputs->front()};
          SmallVector<int32_t> segments;
          for (size_t i = 0; i < arms.size(); ++i) {
            append_range(forwarded, ArrayRef(*inputs).drop_front());
            segments.push_back(inputs->size() - 1);
          }
          make("data.match", {}, forwarded,
               {builder.getNamedAttr("alternatives",
                                     builder.getArrayAttr(names)),
                builder.getNamedAttr("successor_operand_segments",
                                     builder.getDenseI32ArrayAttr(segments))},
               arms);
          for (auto [region, target] : zip(control->regions, arms))
            if (auto error = body(owner, *region, target,
                                  target->getArguments(), next, depth + 1))
              return error;
          builder.setInsertionPointToEnd(next);
          append_range(values, next->getArguments());
        } else {
          SmallVector<Type> carried;
          for (unsigned i = 0; i < control->carried; ++i)
            carried.push_back(
                source.values[control->operands[2 + i].index].type);
          auto carriedTypes = types(carried);
          if (!carriedTypes)
            return carriedTypes.takeError();
          auto captures = ArrayRef(*inputs).drop_front(2 + control->carried);
          SmallVector<mlir::Type> headerTypes{builder.getI64Type()};
          append_range(headerTypes, *carriedTypes);
          SmallVector<mlir::Type> iterationTypes(headerTypes);
          append_range(iterationTypes, mlir::ValueRange(captures).getTypes());
          auto *next = block(*carriedTypes), *header = block(headerTypes),
               *iteration = block(iterationTypes),
               *latch = block(*carriedTypes);
          SmallVector<mlir::Value> initial{inputs->front()};
          append_range(initial, ArrayRef(*inputs).slice(2, control->carried));
          branch(header, initial);
          builder.setInsertionPointToEnd(header);
          auto condition = mlir::arith::CmpIOp::create(
              builder, location, mlir::arith::CmpIPredicate::ult,
              header->getArgument(0), (*inputs)[1]);
          SmallVector<mlir::Value> arguments(header->getArguments());
          append_range(arguments, captures);
          mlir::cf::CondBranchOp::create(builder, location, condition,
                                         iteration, arguments, next,
                                         header->getArguments().drop_front());
          if (auto error = body(owner, *control->regions.front(), iteration,
                                iteration->getArguments(), latch, depth + 1,
                                ArrayRef<Type>(carried)))
            return error;
          builder.setInsertionPointToEnd(latch);
          auto one =
              mlir::arith::ConstantIntOp::create(builder, location, 1, 64);
          auto successor = mlir::arith::AddIOp::create(
              builder, location, header->getArgument(0), one);
          SmallVector<mlir::Value> advanced{successor};
          append_range(advanced, latch->getArguments());
          branch(header, advanced);
          builder.setInsertionPointToEnd(next);
          if (carried.size() == 1)
            append_range(values, next->getArguments());
          else {
            if (outputTypes->size() != 1)
              return error("entry.control", "loop requires one packed result");
            auto *packed =
                make("data.construct", *outputTypes, next->getArguments(),
                     {builder.getNamedAttr("alternative",
                                           builder.getStringAttr(""))});
            append_range(values, packed->getResults());
          }
        }
      } else {
        if (auto *construct = std::get_if<Construct>(&operation.action)) {
          name = construct->kind == Construct::Kind::Unpack ? "data.unpack"
                                                            : "data.construct";
          inputIds = construct->operands;
          if (name == "data.construct")
            attrs.push_back(builder.getNamedAttr(
                "alternative", builder.getStringAttr(construct->alternative)));
        } else if (auto *projection =
                       std::get_if<Projection>(&operation.action)) {
          name = "data.project";
          inputIds = {projection->input};
          SmallVector<int64_t> path(projection->path.begin(),
                                    projection->path.end());
          attrs.push_back(
              builder.getNamedAttr("path", builder.getDenseI64ArrayAttr(path)));
        } else if (auto *require = std::get_if<Require>(&operation.action)) {
          name = "exec.require";
          inputIds = {require->condition};
        } else if (auto *consume = std::get_if<Consume>(&operation.action)) {
          auto input = operands({consume->input}, env);
          if (!input)
            return input.takeError();
          auto *copy = make(
              "data.project", input->front().getType(), *input,
              {builder.getNamedAttr("path", builder.getDenseI64ArrayAttr({}))});
          fallible("exec.drop", {}, copy->getResults());
          name = "data.construct";
          attrs.push_back(
              builder.getNamedAttr("alternative", builder.getStringAttr("")));
        } else if (auto *call = std::get_if<HelperCall>(&operation.action);
                   call && entry.declarations()[call->callee.index].kind ==
                               Declaration::Kind::EntryFunction) {
          name = "func.call";
          inputIds = call->operands;
          attrs.push_back(builder.getNamedAttr(
              "callee", mlir::FlatSymbolRefAttr::get(
                            builder.getContext(),
                            entry.declarations()[call->callee.index].symbol)));
        } else if (auto *invoke =
                       std::get_if<HostInvocation>(&operation.action)) {
          name = "exec.invoke";
          inputIds = invoke->operands;
          attrs.push_back(builder.getNamedAttr(
              "deployment",
              builder.getStringAttr(entryDeploymentId(
                  invoke->kind,
                  entry.project().declarations()[invoke->target.index].symbol,
                  invoke->arguments))));
        } else {
          auto calculation = extractCalculation(owner, source, operation,
                                                result.calculations.size());
          if (!calculation)
            return calculation.takeError();
          name = "exec.numeric";
          inputIds = std::move(calculation->inputs);
          attrs.push_back(builder.getNamedAttr(
              "calculation", builder.getStringAttr(calculation->fragment.id)));
          result.calculations.push_back(std::move(calculation->fragment));
        }
        auto inputs = operands(inputIds, env);
        if (!inputs)
          return inputs.takeError();
        if (name.starts_with("data."))
          append_range(values,
                       make(name, *outputTypes, *inputs, attrs)->getResults());
        else
          values = fallible(name, *outputTypes, *inputs, attrs);
      }
      if (values.size() != operation.results.size())
        return error("entry.control", "Host result signature differs");
      for (auto [source, value] : zip(operation.results, values))
        if (!env.emplace(source.index, value).second)
          return error("entry.scope", "duplicate checked Host value");
    }
    if (source.stopped) {
      auto *stop =
          make("exec.stop", exec::StopType::get(builder.getContext()), {},
               {builder.getNamedAttr(
                   "reason", builder.getStringAttr(source.stopReason))});
      branch(failure, stop->getResults());
      return Error::success();
    }
    auto outputs = operands(source.results, env);
    if (!outputs)
      return outputs.takeError();
    if (loopState) {
      // The checked frontend returns packed state followed by unchanged Copy
      // captures. Native CFG keeps those invariants on the dominating edge;
      // only state belongs to the latch. Check the transport before erasing it.
      auto captures = incoming.drop_front(1 + loopState->size());
      if (outputs->size() != 1 + captures.size() ||
          mlir::ValueRange(*outputs).drop_front() != captures)
        return error("entry.control",
                     "loop must return packed state and unchanged captures");
      outputs->resize(1);
      if (loopState->empty())
        outputs->clear();
      else if (loopState->size() != 1) {
        auto unpackedTypes = types(*loopState);
        if (!unpackedTypes)
          return unpackedTypes.takeError();
        auto *unpack = make("data.unpack", *unpackedTypes, *outputs);
        *outputs = SmallVector<mlir::Value>(unpack->getResults());
      }
    }
    if (continuation)
      branch(continuation, *outputs);
    else {
      auto *returned = make("exec.returned", outcome, *outputs);
      make("func.return", {}, returned->getResults());
    }
    return Error::success();
  }

public:
  Emitter(const ClosedEntry &entry, mlir::MLIRContext &context,
          const Limits &limits)
      : entry(entry), limits(limits), layouts(entry, limits), builder(&context),
        location(builder.getUnknownLoc()) {}
  Expected<NativeHost> run() {
    result.module = mlir::ModuleOp::create(location);
    (*result.module)
        ->setAttr("entry.root", builder.getStringAttr(entry.root().symbol));
    unsigned count = 0;
    for (const auto &decl : entry.declarations()) {
      if (decl.kind != Declaration::Kind::EntryFunction || !decl.body ||
          !decl.parameters.empty())
        continue;
      if (++count > limits.instances || decl.outputs.size() != 1)
        return error("entry.closure",
                     "Host function inventory or result arity");
      SmallVector<Type> inputTypes;
      SmallVector<mlir::Attribute> names;
      for (const auto &port : decl.inputs) {
        inputTypes.push_back(port.type);
        names.push_back(builder.getStringAttr(port.name));
      }
      auto inputs = types(inputTypes);
      if (!inputs)
        return inputs.takeError();
      auto output = type(decl.outputs.front().type);
      if (!output)
        return output.takeError();
      outcome = exec::OutcomeType::get(builder.getContext(), {*output});
      builder.setInsertionPointToEnd(result.module->getBody());
      auto function = mlir::func::FuncOp::create(
          builder, location, decl.symbol,
          builder.getFunctionType(*inputs, {outcome}));
      function->setAttr("entry.parameters", builder.getArrayAttr(names));
      functionBody = &function.getBody();
      auto *start = block(*inputs);
      failure = block(exec::StopType::get(builder.getContext()));
      builder.setInsertionPointToEnd(failure);
      auto *stopped = make("exec.failed", outcome, failure->getArguments());
      make("func.return", {}, stopped->getResults());
      if (auto error =
              body(decl, *decl.body, start, start->getArguments(), nullptr, 0))
        return std::move(error);
    }
    if (!count || result.calculations.size() > limits.instances)
      return error("entry.closure", "Host closure is empty or exceeds limits");
    return std::move(result);
  }
};
} // namespace
Expected<NativeHost> emitNativeHost(const ClosedEntry &entry,
                                    mlir::MLIRContext &context,
                                    const Limits &limits) {
  return Emitter(entry, context, limits).run();
}
} // namespace zkc::language::entry_detail
