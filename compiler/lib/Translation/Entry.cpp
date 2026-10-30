#include "zkc/Translation/Entry.h"
#include "Entry/Native.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Verifier.h"
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
namespace entry_detail {
Expected<Calculation> extractCalculation(const Declaration &owner,
                                         const Body &body,
                                         const Operation &source,
                                         unsigned ordinal) {
  std::vector<ValueId> inputs;
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
  definition.symbol = "entry_calculation_" + std::to_string(ordinal);
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
  return Calculation{{definition.symbol, std::move(definition)},
                     std::move(inputs)};
}
} // namespace entry_detail
namespace {
struct SourceArtifactView {
  json::Array functions;
  std::vector<NumericalFragment> calculations;
};
class SourceArtifact {
  const ClosedEntry &entry;
  const Limits &limits;
  Layouts layouts;
  SourceArtifactView view;
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
        // Host values are Copy. Dispose of a copy, since artifact drop removes
        // its operand from scope while source disposal preserves Copy values.
        auto found = ids.find(consume->input.index);
        if (found == ids.end())
          return error("entry.scope", "checked Host operand does not dominate");
        auto temporary = next;
        auto copy = value(body.values[consume->input.index].type);
        if (!copy)
          return copy.takeError();
        steps.push_back(
            json::Object{{"op", "project"},
                         {"path", json::Array{}},
                         {"operands", json::Array{found->second}},
                         {"results", json::Array{std::move(*copy)}}});
        steps.push_back(json::Object{{"op", "drop"},
                                     {"operands", json::Array{temporary}},
                                     {"results", json::Array{}}});
        // The checked action still produces a logical unit; artifact drop has
        // no results, so materialize that unit with ordinary construction.
        op["op"] = "construct";
        op["alternative"] = "";
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
        // Only this boundary handles scoped execution and mathematical
        // operations. Retain their exact checked action and operands for the
        // existing emitter and comparator.
        auto calculation = entry_detail::extractCalculation(
            owner, body, source, view.calculations.size());
        if (!calculation)
          return calculation.takeError();
        inputs = std::move(calculation->inputs);
        op["op"] = "numeric";
        op["calculation"] = calculation->fragment.id;
        view.calculations.push_back(std::move(calculation->fragment));
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
        // Native CFG and the Host carrier expose each loop-carried value.
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
  SourceArtifact(const ClosedEntry &entry, const Limits &limits)
      : entry(entry), limits(limits), layouts(entry, limits) {}
  Expected<SourceArtifactView> run() {
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
      auto b = block(decl, *decl.body, 0);
      if (!b)
        return b.takeError();
      view.functions.push_back(json::Object{{"signature", std::move(signature)},
                                            {"body", std::move(*b)}});
    }
    if (view.functions.empty() || view.functions.size() > limits.instances ||
        view.calculations.size() > limits.instances)
      return error("entry.closure",
                   "Host function closure is empty or exceeds limit");
    return std::move(view);
  }
};
} // namespace
Expected<json::Array> renderHostSignatures(const ClosedEntry &entry,
                                           const Limits &limits) {
  Layouts layouts(entry, limits);
  json::Array signatures;
  auto schema = [&](const Type &type) -> Expected<json::Value> {
    auto layout = layouts.get(type);
    if (!layout)
      return layout.takeError();
    if ((*layout)->formal || (*layout)->custody || !(*layout)->permissions.copy)
      return error("entry.value", "Host signatures require ordinary Copy data");
    return encodeEntrySchema(**layout);
  };
  for (const auto &decl : entry.declarations()) {
    if (decl.kind != Declaration::Kind::EntryFunction || !decl.body ||
        !decl.parameters.empty())
      continue;
    json::Array parameters;
    for (const auto &port : decl.inputs) {
      auto value = schema(port.type);
      if (!value)
        return value.takeError();
      parameters.push_back(
          json::Object{{"name", port.name}, {"schema", std::move(*value)}});
    }
    if (decl.outputs.size() != 1)
      return error("entry.signature", "Host requires one logical result");
    auto result = schema(decl.outputs.front().type);
    if (!result)
      return result.takeError();
    signatures.push_back(json::Object{{"symbol", decl.symbol},
                                      {"parameters", std::move(parameters)},
                                      {"result", std::move(*result)}});
  }
  if (signatures.empty() || signatures.size() > limits.instances)
    return error("entry.closure", "Host signature inventory exceeds limits");
  return signatures;
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
  auto native = entry_detail::emitNativeHost(entry, context, limits);
  if (!native)
    return native.takeError();
  auto module = std::move(native->module);
  for (const auto &calculation : native->calculations) {
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
Expected<json::Array> readHostFunctions(mlir::ModuleOp module,
                                        const Limits &limits) {
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission", "Host original failed verification");
  return entry_detail::reconstructNativeHost(module, limits);
}
Expected<HostAnalysis> analyzeHostOriginal(const ClosedEntry &entry,
                                           mlir::ModuleOp module,
                                           const Limits &limits) {
  auto expected = SourceArtifact(entry, limits).run();
  if (!expected)
    return expected.takeError();
  auto actual = readHostFunctions(module, limits);
  if (!actual)
    return actual.takeError();
  auto root = module->getAttrOfType<mlir::StringAttr>("entry.root");
  if (!root || root.getValue() != entry.root().symbol ||
      module->getAttrs().size() != 1 || *actual != expected->functions)
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
  if (numeric.size() != expected->calculations.size())
    return error("source.correspondence", "numerical closure differs");
  Correspondence report;
  report.declarations = actual->size();
  for (const auto &fragment : expected->calculations) {
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
  // Nested numerical modules already contributed their checked operations.
  for (auto function : module.getOps<mlir::func::FuncOp>())
    function.walk([&](mlir::Operation *op) {
      if (op != function.getOperation())
        ++report.operations;
    });
  return HostAnalysis{std::move(expected->calculations), std::move(*actual),
                      std::move(report)};
}
Expected<Correspondence> compareHostOriginal(const ClosedEntry &entry,
                                             mlir::ModuleOp module,
                                             const Limits &limits) {
  auto analysis = analyzeHostOriginal(entry, module, limits);
  if (!analysis)
    return analysis.takeError();
  return std::move(analysis->correspondence);
}
} // namespace zkc::language
