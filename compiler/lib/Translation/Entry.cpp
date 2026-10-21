#include "zkc/Translation/Entry.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Entry/IR/EntryOps.h"
#include "zkc/Dialect/Printing.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
std::string hash(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
json::Array indices(ArrayRef<unsigned> values) {
  json::Array result;
  for (auto value : values)
    result.push_back(value);
  return result;
}
} // namespace
std::string entryDeploymentId(HostInvocation::Kind kind, StringRef target,
                              ArrayRef<Type> arguments) {
  auto operation = kind == HostInvocation::Kind::Run     ? "run"
                   : kind == HostInvocation::Kind::Prove ? "prove"
                                                         : "verify";
  auto id = std::string(operation) + ":" + target.str();
  if (!arguments.empty()) {
    std::string material;
    for (const auto &argument : arguments) {
      auto key = typeIdentity(argument);
      material += std::to_string(key.size()) + ":" + key;
    }
    id += ":" + hash(material);
  }
  return id;
}
json::Value encodeEntrySchema(const Layout &layout) {
  auto fields = [](ArrayRef<LayoutField> fields) {
    json::Array result;
    for (const auto &field : fields)
      result.push_back(
          json::Object{{"name", field.name},
                       {"offset", field.offset},
                       {"schema", encodeEntrySchema(*field.layout)}});
    return result;
  };
  json::Array alternatives, permissions, leaves;
  for (const auto &alternative : layout.alternatives)
    alternatives.push_back(json::Object{
        {"name", alternative.name}, {"fields", fields(alternative.fields)}});
  if (layout.permissions.copy)
    permissions.push_back("Copy");
  if (layout.permissions.drop)
    permissions.push_back("Drop");
  for (const auto &leaf : layout.leaves) {
    if (leaf.data())
      leaves.push_back(*leaf.data());
  }
  return json::Object{{"kind", typeKindName(layout.type.kind)},
                      {"identity", hash(typeIdentity(layout.type))},
                      {"type", spelling(layout.type)},
                      {"custody", layout.custody},
                      {"constructible", layout.constructible},
                      {"permissions", std::move(permissions)},
                      {"fields", fields(layout.fields)},
                      {"alternatives", std::move(alternatives)},
                      {"leaves", std::move(leaves)}};
}
namespace {
class Planner {
  const ClosedEntry &entry;
  const Limits &limits;
  Layouts layouts;
  HostPlan plan;
  uint64_t operations = 0;
  unsigned next = 0;
  Expected<json::Value> schema(const Type &type) {
    auto layout = layouts.get(type);
    if (!layout)
      return layout.takeError();
    if ((*layout)->formal || (*layout)->custody || !(*layout)->permissions.copy)
      return error("entry.value",
                   "Host values must be ordinary copyable native data");
    return encodeEntrySchema(**layout);
  }
  Expected<json::Value> value(const Type &type) {
    auto s = schema(type);
    if (!s)
      return s.takeError();
    return json::Object{{"id", next++}, {"schema", std::move(*s)}};
  }
  Expected<json::Value> block(const Declaration &owner, const Body &body,
                              unsigned depth,
                              std::optional<ArrayRef<Type>> loopState = {}) {
    if (depth > limits.callDepth)
      return error("source.limit", "Host region nesting limit");
    std::map<unsigned, unsigned> ids;
    json::Array arguments, steps, returns;
    for (unsigned i = 0; i < body.inputs; ++i) {
      ids.emplace(i, next);
      auto v = value(body.values[i].type);
      if (!v)
        return v.takeError();
      arguments.push_back(std::move(*v));
    }
    for (const auto &source : body.operations) {
      if (++operations > limits.operations)
        return error("source.limit", "Host operation limit");
      json::Object op;
      std::vector<ValueId> inputs;
      std::optional<std::vector<Type>> carried;
      if (auto *construct = std::get_if<Construct>(&source.action)) {
        op["op"] =
            construct->kind == Construct::Kind::Unpack ? "unpack" : "construct";
        if (construct->kind != Construct::Kind::Unpack)
          op["alternative"] = construct->alternative;
        inputs = construct->operands;
      } else if (auto *projection = std::get_if<Projection>(&source.action)) {
        op["op"] = "project";
        op["path"] = indices(projection->path);
        inputs = {projection->input};
      } else if (auto *control = std::get_if<LocalControl>(&source.action)) {
        op["op"] = control->kind == LocalControl::Kind::If      ? "if"
                   : control->kind == LocalControl::Kind::Match ? "match"
                                                                : "for";
        inputs = control->operands;
        if (control->kind == LocalControl::Kind::For) {
          carried.emplace();
          for (unsigned i = 0; i < control->carried; ++i)
            carried->push_back(body.values[inputs[2 + i].index].type);
        }
        json::Array regions;
        for (const auto &region : control->regions) {
          auto nested = block(owner, *region, depth + 1,
                              carried ? std::optional<ArrayRef<Type>>(*carried)
                                      : std::nullopt);
          if (!nested)
            return nested.takeError();
          regions.push_back(std::move(*nested));
        }
        op["regions"] = std::move(regions);
        if (control->kind == LocalControl::Kind::For)
          op["carried"] = control->carried;
        if (control->kind == LocalControl::Kind::Match) {
          json::Array names;
          for (const auto &name : control->alternatives)
            names.push_back(name);
          op["alternatives"] = std::move(names);
        }
      } else if (auto *require = std::get_if<Require>(&source.action)) {
        op["op"] = "require";
        inputs = {require->condition};
      } else if (auto *consume = std::get_if<Consume>(&source.action)) {
        op["op"] = "drop";
        inputs = {consume->input};
      } else if (auto *call = std::get_if<HelperCall>(&source.action);
                 call && entry.declarations()[call->callee.index].kind ==
                             Declaration::Kind::EntryFunction) {
        op["op"] = "call";
        op["callee"] = entry.declarations()[call->callee.index].symbol;
        inputs = call->operands;
      } else if (auto *invoke = std::get_if<HostInvocation>(&source.action)) {
        op["op"] = "invoke";
        inputs = invoke->operands;
        op["deployment"] = entryDeploymentId(
            invoke->kind,
            entry.project().declarations()[invoke->target.index].symbol,
            invoke->arguments);
      } else {
        // Only this boundary handles Local/Math operations. Retain their exact
        // checked action and operands for the existing emitter and comparator.
        auto action = source;
        std::vector<ValueId *> coordinates;
        std::visit(
            [&](auto &a) {
              using T = std::decay_t<decltype(a)>;
              if constexpr (std::is_same_v<T, MathValue> ||
                            std::is_same_v<T, LocalPrimitive> ||
                            std::is_same_v<T, HelperCall> ||
                            std::is_same_v<T, BulkApplication>) {
                for (auto &v : a.operands)
                  coordinates.push_back(&v);
              } else if constexpr (std::is_same_v<T, FiniteComputation>) {
                for (auto &v : a.domainOperands)
                  coordinates.push_back(&v);
                for (auto &v : a.operands)
                  coordinates.push_back(&v);
                for (auto &v : a.body.captures)
                  coordinates.push_back(&v);
                if (a.predicate)
                  for (auto &v : a.predicate->captures)
                    coordinates.push_back(&v);
              }
            },
            action.action);
        if (!std::holds_alternative<MathValue>(source.action) &&
            !std::holds_alternative<LocalPrimitive>(source.action) &&
            !std::holds_alternative<HelperCall>(source.action) &&
            !std::holds_alternative<BulkApplication>(source.action) &&
            !std::holds_alternative<FiniteComputation>(source.action))
          return error("entry.operation", "unsupported checked Host operation");
        auto fragment = std::make_shared<Body>();
        fragment->mode = Body::Mode::Local;
        std::map<unsigned, unsigned> mapped;
        for (auto *coordinate : coordinates) {
          auto original = coordinate->index;
          if (!mapped.count(original)) {
            mapped.emplace(original, fragment->values.size());
            inputs.push_back({original});
            fragment->values.push_back(body.values[original]);
          }
          coordinate->index = mapped.at(original);
        }
        fragment->inputs = fragment->values.size();
        fragment->effects = body.effects;
        for (auto &result : action.results) {
          auto original = result.index;
          result.index = fragment->values.size();
          fragment->values.push_back(body.values[original]);
          fragment->results.push_back(result);
        }
        action.binding.reset();
        fragment->operations.push_back(std::move(action));
        Declaration definition = owner;
        definition.kind = Declaration::Kind::Local;
        definition.symbol =
            "entry_calculation_" + std::to_string(plan.calculations.size());
        definition.inputs.clear();
        definition.outputs.clear();
        definition.services.clear();
        definition.dataPreconditions.clear();
        definition.body = fragment;
        for (unsigned i = 0; i < fragment->inputs; ++i)
          definition.inputs.push_back({"input" + std::to_string(i),
                                       fragment->values[i].type,
                                       {},
                                       source.span});
        for (auto id : fragment->results)
          definition.outputs.push_back(
              {"output" + std::to_string(definition.outputs.size()),
               fragment->values[id.index].type,
               {},
               source.span});
        op["op"] = "numeric";
        op["calculation"] = definition.symbol;
        plan.calculations.push_back({definition.symbol, std::move(definition)});
      }
      json::Array operands, results;
      for (auto input : inputs) {
        auto found = ids.find(input.index);
        if (found == ids.end())
          return error("entry.scope", "checked Host operand does not dominate");
        operands.push_back(found->second);
      }
      if (carried) {
        // Checked Local controls pack their successors into one logical value.
        // SCF and the Host carrier instead expose each loop-carried value.
        json::Array successors;
        for (const auto &type : *carried) {
          successors.push_back(next);
          auto v = value(type);
          if (!v)
            return v.takeError();
          results.push_back(std::move(*v));
        }
        op["operands"] = std::move(operands);
        op["results"] = std::move(results);
        steps.push_back(std::move(op));
        if (source.results.size() != 1)
          return error("entry.control", "checked loop needs one packed result");
        auto output = source.results.front();
        if (carried->size() == 1)
          ids.emplace(output.index, *successors.front().getAsInteger());
        else {
          ids.emplace(output.index, next);
          auto v = value(body.values[output.index].type);
          if (!v)
            return v.takeError();
          json::Array packed;
          packed.push_back(std::move(*v));
          steps.push_back(json::Object{{"op", "construct"},
                                       {"alternative", ""},
                                       {"operands", std::move(successors)},
                                       {"results", std::move(packed)}});
        }
      } else {
        for (auto output : source.results) {
          ids.emplace(output.index, next);
          auto v = value(body.values[output.index].type);
          if (!v)
            return v.takeError();
          results.push_back(std::move(*v));
        }
        op["operands"] = std::move(operands);
        op["results"] = std::move(results);
        steps.push_back(std::move(op));
      }
    }
    if (body.stopped)
      steps.push_back(json::Object{{"op", "stop"},
                                   {"operands", json::Array{}},
                                   {"results", json::Array{}},
                                   {"reason", body.stopReason}});
    if (loopState && !body.stopped) {
      if (body.results.empty())
        return error("entry.control",
                     "continuing loop needs packed successors");
      auto packed = ids.at(body.results.front().index);
      if (loopState->size() == 1)
        returns.push_back(packed);
      else if (!loopState->empty()) {
        json::Array outputs;
        for (const auto &type : *loopState) {
          returns.push_back(next);
          auto v = value(type);
          if (!v)
            return v.takeError();
          outputs.push_back(std::move(*v));
        }
        steps.push_back(json::Object{{"op", "unpack"},
                                     {"operands", json::Array{packed}},
                                     {"results", std::move(outputs)}});
      }
    } else {
      for (auto output : body.results) {
        if (!ids.count(output.index))
          return error("entry.scope", "Host return is undefined");
        returns.push_back(ids.at(output.index));
      }
    }
    return json::Object{{"arguments", std::move(arguments)},
                        {"operations", std::move(steps)},
                        {"returns", std::move(returns)}};
  }

public:
  Planner(const ClosedEntry &entry, const Limits &limits)
      : entry(entry), limits(limits), layouts(entry, limits) {}
  Expected<HostPlan> run() {
    for (const auto &decl : entry.declarations()) {
      if (decl.kind != Declaration::Kind::EntryFunction || !decl.body ||
          !decl.parameters.empty())
        continue;
      next = 0;
      json::Array parameters;
      for (const auto &port : decl.inputs) {
        auto s = schema(port.type);
        if (!s)
          return s.takeError();
        parameters.push_back(
            json::Object{{"name", port.name}, {"schema", std::move(*s)}});
      }
      if (decl.outputs.size() != 1)
        return error("entry.signature",
                     "Host function requires one logical result");
      auto result = schema(decl.outputs.front().type);
      if (!result)
        return result.takeError();
      json::Object signature{{"symbol", decl.symbol},
                             {"parameters", std::move(parameters)},
                             {"result", std::move(*result)}};
      plan.signatures.push_back(json::Object(signature));
      auto b = block(decl, *decl.body, 0);
      if (!b)
        return b.takeError();
      plan.functions.push_back(json::Object{{"signature", std::move(signature)},
                                            {"body", std::move(*b)}});
    }
    if (plan.functions.empty() || plan.functions.size() > limits.instances ||
        plan.calculations.size() > limits.instances)
      return error("entry.closure",
                   "Host function closure is empty or exceeds limit");
    return std::move(plan);
  }
};
mlir::Type nativeType(mlir::MLIRContext *context, const json::Value &schema) {
  auto *object = schema.getAsObject();
  auto kind = object ? object->getString("kind") : std::nullopt;
  if (!kind)
    return {};
  if (kind == "boolean")
    return mlir::IntegerType::get(context, 1);
  if (kind == "Index" || kind == "index")
    return mlir::IntegerType::get(context, 64);
  return entry::ValueType::get(context, printJson(schema));
}
class Writer {
  mlir::OpBuilder builder;
  mlir::Location location;
  using Environment = std::map<int64_t, mlir::Value>;
  mlir::Operation *make(StringRef name, mlir::TypeRange types,
                        mlir::ValueRange inputs,
                        ArrayRef<mlir::NamedAttribute> attrs = {},
                        unsigned regions = 0) {
    mlir::OperationState state(location, name);
    state.addTypes(types);
    state.addOperands(inputs);
    state.addAttributes(attrs);
    for (unsigned i = 0; i < regions; ++i)
      state.addRegion()->push_back(new mlir::Block);
    return builder.create(state);
  }
  SmallVector<mlir::Type> types(const json::Array &values) {
    SmallVector<mlir::Type> result;
    for (const auto &v : values)
      result.push_back(
          nativeType(builder.getContext(), *v.getAsObject()->get("schema")));
    return result;
  }
  SmallVector<mlir::Value> operands(const json::Array &ids,
                                    const Environment &env) {
    SmallVector<mlir::Value> result;
    for (const auto &id : ids)
      result.push_back(env.at(*id.getAsInteger()));
    return result;
  }
  void bind(const json::Array &values, mlir::ValueRange native,
            Environment &env) {
    for (auto [v, n] : zip(values, native))
      env.emplace(*v.getAsObject()->getInteger("id"), n);
  }
  void body(const json::Value &value, mlir::Block &block, Environment env,
            mlir::ValueRange incoming = {},
            StringRef terminator = "func.return",
            mlir::TypeRange continuation = {}) {
    auto &b = *value.getAsObject();
    auto &args = *b.getArray("arguments");
    if (incoming.empty()) {
      for (auto type : types(args))
        block.addArgument(type, location);
      bind(args, block.getArguments(), env);
    } else
      bind(args, incoming, env);
    builder.setInsertionPointToEnd(&block);
    for (const auto &v : *b.getArray("operations")) {
      const auto &op = *v.getAsObject();
      auto name = *op.getString("op");
      auto inputs = operands(*op.getArray("operands"), env);
      auto outputs = types(*op.getArray("results"));
      json::Object descriptor(op);
      descriptor.erase("operands");
      descriptor.erase("results");
      descriptor.erase("regions");
      auto attr = builder.getNamedAttr(
          "descriptor",
          builder.getStringAttr(printJson(json::Object(descriptor))));
      mlir::Operation *actual;
      if (name == "call") {
        actual = make(
            "func.call", outputs, inputs,
            {builder.getNamedAttr(
                "callee", mlir::FlatSymbolRefAttr::get(
                              builder.getContext(), *op.getString("callee")))});
      } else if (name == "if") {
        actual = make("scf.if", outputs, mlir::ValueRange(inputs).take_front(),
                      {}, 2);
        actual->setAttr("entry.descriptor", builder.getStringAttr(printJson(
                                                json::Object(descriptor))));
        for (unsigned i = 0; i < 2; ++i) {
          mlir::OpBuilder::InsertionGuard guard(builder);
          body((*op.getArray("regions"))[i], actual->getRegion(i).front(), env,
               mlir::ValueRange(inputs).drop_front(), "scf.yield", outputs);
        }
      } else if (name == "for") {
        auto step =
            mlir::arith::ConstantIntOp::create(builder, location, 1, 64);
        SmallVector<mlir::Value> loopInputs{inputs[0], inputs[1], step};
        append_range(loopInputs,
                     mlir::ValueRange(inputs).slice(2, outputs.size()));
        actual = make(
            "scf.for", outputs, loopInputs,
            {builder.getNamedAttr("unsignedCmp", builder.getUnitAttr())}, 1);
        actual->setAttr("entry.descriptor", builder.getStringAttr(printJson(
                                                json::Object(descriptor))));
        auto &region = actual->getRegion(0).front();
        region.addArgument(builder.getI64Type(), location);
        for (auto t : outputs)
          region.addArgument(t, location);
        SmallVector<mlir::Value> incoming(region.getArguments());
        append_range(incoming,
                     mlir::ValueRange(inputs).drop_front(2 + outputs.size()));
        mlir::OpBuilder::InsertionGuard guard(builder);
        body((*op.getArray("regions"))[0], region, env, incoming, "scf.yield",
             outputs);
      } else if (name == "stop") {
        actual = make("entry.stop", continuation, {}, {attr});
        make(terminator, {}, actual->getResults());
        return;
      } else {
        // Match remains a typed payload-eliminating region boundary.
        actual = make("entry." + name.str(), outputs, inputs, {attr},
                      name == "match" ? op.getArray("regions")->size() : 0);
        if (name == "match")
          for (auto [i, arm] : enumerate(*op.getArray("regions"))) {
            mlir::OpBuilder::InsertionGuard guard(builder);
            body(arm, actual->getRegion(i).front(), env, {}, "entry.yield",
                 outputs);
          }
      }
      // Source-local block structure and captures are retained as schema data;
      // executable operands/results always come from the actual SSA.
      bind(*op.getArray("results"), actual->getResults(), env);
    }
    make(terminator, {}, operands(*b.getArray("returns"), env));
  }

public:
  Writer(mlir::MLIRContext &context)
      : builder(&context), location(builder.getUnknownLoc()) {}
  mlir::OwningOpRef<mlir::ModuleOp> run(const HostPlan &plan, StringRef root) {
    auto module = mlir::ModuleOp::create(location);
    module->setAttr("entry.root", builder.getStringAttr(root));
    for (const auto &f : plan.functions) {
      builder.setInsertionPointToEnd(module.getBody());
      auto &signature = *f.getAsObject()->getObject("signature");
      SmallVector<mlir::Type> inputs;
      for (const auto &p : *signature.getArray("parameters"))
        inputs.push_back(nativeType(&*builder.getContext(),
                                    *p.getAsObject()->get("schema")));
      auto result = nativeType(builder.getContext(), *signature.get("result"));
      auto function = mlir::func::FuncOp::create(
          builder, location, *signature.getString("symbol"),
          builder.getFunctionType(inputs, {result}));
      function->setAttr("entry.signature", builder.getStringAttr(printJson(
                                               json::Object(signature))));
      function->setAttr("entry.body", builder.getStringAttr(printJson(
                                          *f.getAsObject()->get("body"))));
      auto &block = function.getBody().emplaceBlock();
      body(*f.getAsObject()->get("body"), block, {}, {}, "func.return",
           function.getResultTypes());
    }
    return module;
  }
};
} // namespace
Expected<HostPlan> planHost(const ClosedEntry &entry, const Limits &limits) {
  return Planner(entry, limits).run();
}
Expected<std::vector<Declaration>>
numericalDefinitions(const ClosedEntry &entry, const Declaration &fragment) {
  std::set<unsigned> reached;
  Error failure = Error::success();
  std::function<void(const Body &)> scan;
  auto select = [&](DeclarationId id) {
    if (failure || !reached.insert(id.index).second)
      return;
    if (id.index >= entry.declarations().size()) {
      failure = error("entry.reference",
                      "numerical helper is outside the checked closure");
      return;
    }
    const auto &decl = entry.declarations()[id.index];
    if (!decl.body || !decl.parameters.empty() ||
        (decl.kind != Declaration::Kind::Math &&
         decl.kind != Declaration::Kind::Local)) {
      failure =
          error("entry.reference",
                "numerical dependency is not a closed Local or Math helper");
      return;
    }
    scan(*decl.body);
  };
  scan = [&](const Body &body) {
    for (const auto &operation : body.operations) {
      std::visit(
          [&](const auto &action) {
            using T = std::decay_t<decltype(action)>;
            if constexpr (std::is_same_v<T, HelperCall> ||
                          std::is_same_v<T, BulkApplication>)
              select(action.callee);
            else if constexpr (std::is_same_v<T, FiniteComputation>) {
              select(action.body.helper);
              if (action.predicate)
                select(action.predicate->helper);
            } else if constexpr (std::is_same_v<T, LocalControl>)
              for (const auto &region : action.regions)
                scan(*region);
          },
          operation.action);
    }
  };
  scan(*fragment.body);
  if (failure)
    return std::move(failure);
  std::vector<Declaration> definitions;
  for (const auto &decl : entry.declarations())
    if (reached.count(decl.id.index))
      definitions.push_back(decl);
  definitions.push_back(fragment);
  return definitions;
}
Expected<std::string> emitHostOriginal(const ClosedEntry &entry,
                                       mlir::MLIRContext &context,
                                       const Limits &limits) {
  auto plan = planHost(entry, limits);
  if (!plan)
    return plan.takeError();
  auto module = Writer(context).run(*plan, entry.root().symbol);
  for (const auto &calculation : plan->calculations) {
    auto nested =
        buildNumericalOriginal(entry, calculation.definition, context, limits);
    if (!nested)
      return nested.takeError();
    (**nested)->setAttr("entry.calculation",
                        mlir::StringAttr::get(&context, calculation.id));
    module->getBody()->push_back(nested->release());
  }
  if (mlir::failed(mlir::verify(*module)))
    return error("target.admission", "Host original failed MLIR verification");
  std::string text;
  BoundedStream stream(text, limits.irBytes);
  mlir::AsmState state(*module, canonicalPrintingFlags());
  module->print(stream, state);
  stream << '\n';
  if (stream.overflow())
    return error("source.limit", "Host original byte limit");
  return text;
}
namespace {
class SSAReader {
  const Limits &limits;
  uint64_t count = 0;
  using Environment = std::map<int64_t, mlir::Value>;
  bool bind(const json::Array &values, mlir::ValueRange native,
            Environment &env) {
    if (values.size() != native.size())
      return false;
    for (auto [v, n] : zip(values, native)) {
      auto *o = v.getAsObject();
      if (!o || o->size() != 2 || !o->getInteger("id") || !o->get("schema") ||
          nativeType(n.getContext(), *o->get("schema")) != n.getType() ||
          !env.emplace(*o->getInteger("id"), n).second)
        return false;
    }
    return true;
  }
  bool inputs(const json::Array &ids, mlir::ValueRange native,
              const Environment &env) {
    if (ids.size() != native.size())
      return false;
    for (auto [id, n] : zip(ids, native)) {
      auto i = id.getAsInteger();
      if (!i)
        return false;
      auto found = env.find(*i);
      if (found == env.end() || found->second != n)
        return false;
    }
    return true;
  }
  bool body(const json::Value &shape, mlir::Block &block, Environment env,
            mlir::ValueRange incoming = {},
            StringRef terminator = "func.return", unsigned depth = 0) {
    if (depth > limits.callDepth)
      return false;
    auto *b = shape.getAsObject();
    if (!b || b->size() != 3 || !b->getArray("arguments") ||
        !b->getArray("operations") || !b->getArray("returns"))
      return false;
    auto actualArgs = incoming.empty() ? block.getArguments() : incoming;
    if (!bind(*b->getArray("arguments"), actualArgs, env))
      return false;
    auto cursor = block.begin();
    for (const auto &value : *b->getArray("operations")) {
      if (++count > limits.operations || cursor == block.end())
        return false;
      auto *o = value.getAsObject();
      if (!o || !o->getString("op") || !o->getArray("operands") ||
          !o->getArray("results"))
        return false;
      auto name = *o->getString("op");
      SmallVector<mlir::Value> data;
      for (const auto &id : *o->getArray("operands")) {
        auto i = id.getAsInteger();
        if (!i || !env.count(*i))
          return false;
        data.push_back(env.at(*i));
      }
      mlir::Operation *step = &*cursor++;
      if (name == "for") {
        auto constant = mlir::dyn_cast<mlir::arith::ConstantIntOp>(step);
        if (!constant || constant.value() != 1 || cursor == block.end() ||
            !constant.getType().isInteger(64) || step->getAttrs().size() != 1)
          return false;
        auto stepValue = step->getResult(0);
        step = &*cursor++;
        if (step->getNumOperands() != 3 + o->getArray("results")->size() ||
            step->getOperand(2) != stepValue)
          return false;
      }
      json::Object descriptor(*o);
      descriptor.erase("operands");
      descriptor.erase("results");
      descriptor.erase("regions");
      if (name == "call") {
        auto call = mlir::dyn_cast<mlir::func::CallOp>(step);
        if (!call || call.getCallee() != o->getString("callee") ||
            !inputs(*o->getArray("operands"), step->getOperands(), env) ||
            step->getAttrs().size() != 1)
          return false;
      } else if (name == "if" || name == "for") {
        if (step->getName().getStringRef() !=
                (name == "if" ? "scf.if" : "scf.for") ||
            !step->getAttrOfType<mlir::StringAttr>("entry.descriptor") ||
            step->getAttrOfType<mlir::StringAttr>("entry.descriptor")
                    .getValue() != printJson(json::Object(descriptor)))
          return false;
        if (step->getAttrs().size() != (name == "if" ? 1 : 2) ||
            (name == "for" &&
             !step->getAttrOfType<mlir::UnitAttr>("unsignedCmp")))
          return false;
        auto *regions = o->getArray("regions");
        if (!regions || regions->size() != step->getNumRegions() ||
            data.empty())
          return false;
        if (name == "if" && (step->getNumOperands() != 1 ||
                             data.front() != step->getOperand(0)))
          return false;
        if (name == "for" &&
            (data.size() < 2 + step->getNumResults() ||
             step->getOperand(0) != data[0] || step->getOperand(1) != data[1]))
          return false;
        for (auto [i, region] : enumerate(step->getRegions())) {
          if (!hasSingleElement(region))
            return false;
          SmallVector<mlir::Value> incoming;
          if (name == "if")
            append_range(incoming, ArrayRef(data).drop_front());
          else {
            append_range(incoming, region.front().getArguments());
            append_range(incoming,
                         ArrayRef(data).drop_front(2 + step->getNumResults()));
            for (unsigned j = 0; j < step->getNumResults(); ++j)
              if (step->getOperand(j + 3) != data[j + 2])
                return false;
          }
          if (!body((*regions)[i], region.front(), env, incoming, "scf.yield",
                    depth + 1))
            return false;
        }
      } else {
        if (step->getName().getStringRef() != "entry." + name.str() ||
            !step->getAttrOfType<mlir::StringAttr>("descriptor") ||
            step->getAttrOfType<mlir::StringAttr>("descriptor").getValue() !=
                printJson(json::Object(descriptor)) ||
            !inputs(*o->getArray("operands"), step->getOperands(), env) ||
            step->getAttrs().size() != 1)
          return false;
        if (name == "match") {
          auto *regions = o->getArray("regions");
          if (!regions || regions->size() != step->getNumRegions())
            return false;
          for (auto [i, region] : enumerate(step->getRegions()))
            if (!hasSingleElement(region) ||
                !body((*regions)[i], region.front(), env, {}, "entry.yield",
                      depth + 1))
              return false;
        } else if (step->getNumRegions())
          return false;
      }
      if (name == "stop") {
        auto parent = block.getParentOp();
        mlir::TypeRange continuation = parent->getResultTypes();
        if (auto function = mlir::dyn_cast<mlir::func::FuncOp>(parent))
          continuation = function.getResultTypes();
        if (!o->getArray("results")->empty() ||
            !b->getArray("returns")->empty() ||
            step->getResultTypes() != continuation || cursor == block.end())
          return false;
        auto &last = *cursor++;
        return cursor == block.end() &&
               last.getName().getStringRef() == terminator &&
               last.getAttrs().empty() && last.getNumResults() == 0 &&
               last.getNumRegions() == 0 &&
               last.getOperands() == step->getResults();
      }
      if (!bind(*o->getArray("results"), step->getResults(), env))
        return false;
    }
    if (cursor == block.end())
      return false;
    auto &last = *cursor++;
    return cursor == block.end() &&
           last.getName().getStringRef() == terminator &&
           last.getAttrs().empty() &&
           inputs(*b->getArray("returns"), last.getOperands(), env);
  }

public:
  SSAReader(const Limits &limits) : limits(limits) {}
  Expected<json::Array> run(mlir::ModuleOp module) {
    json::Array functions;
    for (auto function : module.getOps<mlir::func::FuncOp>()) {
      auto signature =
          function->getAttrOfType<mlir::StringAttr>("entry.signature");
      auto shape = function->getAttrOfType<mlir::StringAttr>("entry.body");
      if (!signature || !shape || function->getAttrs().size() != 4 ||
          function.getBody().empty() || !hasSingleElement(function.getBody()))
        return error("source.correspondence", "invalid Host function");
      auto s = json::parse(signature.getValue()),
           b = json::parse(shape.getValue());
      if (!s)
        return s.takeError();
      if (!b)
        return b.takeError();
      auto *sig = s->getAsObject();
      if (!sig || sig->size() != 3 ||
          sig->getString("symbol") != function.getSymName() ||
          !sig->getArray("parameters") || !sig->get("result") ||
          function.getNumArguments() != sig->getArray("parameters")->size() ||
          function.getFunctionType().getNumResults() != 1 ||
          function.getFunctionType().getResult(0) !=
              nativeType(module.getContext(), *sig->get("result")))
        return error("source.correspondence",
                     "Host signature differs from SSA");
      for (auto [arg, p] :
           zip(function.getArguments(), *sig->getArray("parameters")))
        if (!p.getAsObject() || !p.getAsObject()->get("schema") ||
            arg.getType() != nativeType(module.getContext(),
                                        *p.getAsObject()->get("schema")))
          return error("source.correspondence",
                       "Host parameter differs from SSA");
      if (!body(*b, function.getBody().front(), {}))
        return error("source.correspondence",
                     "Host body differs from actual scoped SSA");
      functions.push_back(
          json::Object{{"signature", std::move(*s)}, {"body", std::move(*b)}});
    }
    return functions;
  }
};
} // namespace
Expected<json::Array> readHostFunctions(mlir::ModuleOp module,
                                        const Limits &limits) {
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission", "Host original failed verification");
  return SSAReader(limits).run(module);
}
Expected<Correspondence> compareHostOriginal(const ClosedEntry &entry,
                                             mlir::ModuleOp module,
                                             const Limits &limits) {
  auto plan = planHost(entry, limits);
  if (!plan)
    return plan.takeError();
  auto actual = readHostFunctions(module, limits);
  if (!actual)
    return actual.takeError();
  auto root = module->getAttrOfType<mlir::StringAttr>("entry.root");
  if (!root || root.getValue() != entry.root().symbol ||
      module->getAttrs().size() != 1 || *actual != plan->functions)
    return error("source.correspondence",
                 "Host function/source closure differs");
  std::map<std::string, mlir::ModuleOp> numeric;
  for (auto &op : *module.getBody()) {
    if (mlir::isa<mlir::func::FuncOp>(op))
      continue;
    auto nested = mlir::dyn_cast<mlir::ModuleOp>(op);
    auto id = op.getAttrOfType<mlir::StringAttr>("entry.calculation");
    if (!nested || !id || nested->getAttrs().size() != 1 ||
        !numeric.emplace(id.getValue().str(), nested).second)
      return error("source.correspondence", "unexpected Host definition");
  }
  if (numeric.size() != plan->calculations.size())
    return error("source.correspondence", "numerical closure differs");
  Correspondence report;
  report.declarations = actual->size();
  for (const auto &fragment : plan->calculations) {
    auto found = numeric.find(fragment.id);
    if (found == numeric.end())
      return error("source.correspondence", "missing numerical original");
    auto copy = mlir::OwningOpRef<mlir::ModuleOp>(
        mlir::cast<mlir::ModuleOp>(found->second->clone()));
    copy->getOperation()->removeAttr("entry.calculation");
    auto checked =
        compareNumericalOriginal(entry, fragment.definition, *copy, limits);
    if (!checked)
      return checked.takeError();
    report.declarations += checked->declarations;
    report.operations += checked->operations;
    append_range(report.locations, checked->locations);
  }
  module.walk([&](mlir::Operation *op) {
    if (op->getName().getDialectNamespace() == "entry" ||
        mlir::isa<mlir::scf::IfOp, mlir::scf::ForOp>(op))
      ++report.operations;
  });
  return report;
}
} // namespace zkc::language
