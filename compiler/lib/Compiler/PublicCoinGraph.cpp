#include "PublicCoinGraph.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
using Summary = ProtocolObservationSummary;
using Origin = ProtocolValueOrigin;
using Pending = ProtocolPendingTransfer;
constexpr unsigned maxDependencies = 65536;
constexpr uint64_t maxBytes = 8 * 1024 * 1024;
// A limit applies while printing too: a large attribute never accumulates an
// unbounded temporary string before the report's final byte check.
class BoundedText : public raw_ostream {
  std::string value;
  uint64_t size = 0;
  void write_impl(const char *data, size_t count) override {
    size += count;
    if (size <= maxBytes)
      value.append(data, count);
  }
  uint64_t current_pos() const override { return size; }

public:
  BoundedText() { SetUnbuffered(); }
  bool exceeded() const { return size > maxBytes; }
  std::string take() { return std::move(value); }
};
class Graph {
  ModuleOp module;
  ProtocolObservationAnalysis &analysis;
  facts::Work &work;
  SymbolTableCollection symbols;
  llvm::DenseMap<Operation *, unsigned> operations;
  llvm::DenseMap<const Summary *, unsigned> definitions;
  llvm::DenseMap<Operation *, unsigned> numericalDefinitions;
  json::Array definitionRows, numericalRows, draws;
  unsigned dependencyCount = 0, textualBytes = 0;
  std::string refusal, detail;
  ArrayRef<std::pair<std::string, std::string>> selected;
  std::optional<unsigned> pending;
  unsigned queries = 0;

  bool fail(StringRef code, StringRef why) {
    if (refusal.empty()) {
      refusal = code.str();
      detail = why.str();
    }
    return false;
  }
  bool charge(uint64_t amount = 1) {
    return refusal.empty() &&
           (work.charge(amount) ||
            fail("public-coin-limit", "report work exhausted"));
  }
  template <typename T> std::string text(const T &value) {
    if (!charge())
      return {};
    BoundedText stream;
    stream << value;
    auto result = stream.take();
    if (stream.exceeded() || result.size() > maxBytes - textualBytes) {
      fail("public-coin-limit", "report text exceeds its bound");
      return {};
    }
    textualBytes += result.size();
    return result;
  }
  json::Array types(TypeRange values) {
    json::Array result;
    for (Type type : values)
      result.push_back(text(type));
    return result;
  }
  unsigned operation(Operation *op) {
    auto found = operations.find(op);
    if (found == operations.end()) {
      fail("public-coin-module", "foreign operation in summary");
      return 0;
    }
    return found->second;
  }
  json::Object actual(Operation *op) {
    json::Array operands;
    for (Value operand : op->getOperands()) {
      if (!charge())
        break;
      if (auto formal = dyn_cast<BlockArgument>(operand)) {
        unsigned block = 0, region = 0;
        for (auto &candidate : formal.getOwner()->getParentOp()->getRegions()) {
          if (&candidate == formal.getOwner()->getParent())
            break;
          ++region;
        }
        for (auto &candidate : *formal.getOwner()->getParent()) {
          if (&candidate == formal.getOwner())
            break;
          ++block;
        }
        operands.push_back(
            json::Object{{"kind", "formal"},
                         {"owner", operation(formal.getOwner()->getParentOp())},
                         {"region", region},
                         {"block", block},
                         {"port", formal.getArgNumber()}});
      } else {
        auto result = cast<OpResult>(operand);
        operands.push_back(
            json::Object{{"kind", "result"},
                         {"operation", operation(result.getOwner())},
                         {"port", result.getResultNumber()}});
      }
    }
    json::Object record{{"operation", operation(op)},
                        {"kind", op->getName().getStringRef().str()},
                        {"attributes", text(op->getAttrDictionary())},
                        {"operand_types", types(op->getOperandTypes())},
                        {"operands", std::move(operands)},
                        {"outputs", types(op->getResultTypes())}};
    if (auto site = op->getAttrOfType<StringAttr>("site"))
      record["site"] = site.getValue().str();
    return record;
  }
  json::Value dependencies(const BitVector &bits) {
    if (bits.empty())
      return nullptr; // unavailable, distinct from an observed constant
    json::Array result;
    for (int bit : bits.set_bits()) {
      if (++dependencyCount > maxDependencies || !charge()) {
        fail("public-coin-limit", "serialized dependencies exceed their bound");
        break;
      }
      result.push_back(bit);
    }
    return result;
  }
  json::Array dependencies(ArrayRef<BitVector> values) {
    json::Array result;
    for (const auto &value : values)
      result.push_back(dependencies(value));
    return result;
  }
  json::Object origin(const Origin &value) {
    switch (value.kind) {
    case Origin::Kind::Unknown:
      return json::Object{{"kind", "unknown"}};
    case Origin::Kind::Formal:
      return json::Object{{"kind", "formal"}, {"port", value.port}};
    case Origin::Kind::Query: {
      json::Array path;
      for (Operation *op : value.path) {
        if (!charge())
          break;
        path.push_back(operation(op));
      }
      return json::Object{{"kind", "query"}, {"path", std::move(path)}};
    }
    }
    llvm_unreachable("closed origin kind");
  }
  json::Array origins(ArrayRef<Origin> values) {
    json::Array result;
    for (const auto &value : values)
      result.push_back(origin(value));
    return result;
  }
  json::Object transfer(const Pending &value) {
    StringRef input = value.input == Pending::Input::Any     ? "any"
                      : value.input == Pending::Input::Empty ? "empty"
                                                             : "formal";
    StringRef output = value.output == Pending::Output::Preserved ? "preserved"
                       : value.output == Pending::Output::Empty   ? "empty"
                                                                  : "query";
    json::Object result{{"input", input.str()}, {"output", output.str()}};
    if (value.input == Pending::Input::Formal)
      result["port"] = value.port;
    if (value.output == Pending::Output::Query)
      result["query"] = origin(value.query);
    return result;
  }
  unsigned numerical(func::FuncOp function,
                     const ExecutionObservationSummary *summary = nullptr) {
    if (auto found = numericalDefinitions.find(function);
        found != numericalDefinitions.end())
      return found->second;
    unsigned id = numericalRows.size();
    numericalDefinitions[function] = id;
    numericalRows.push_back(nullptr);
    if (!charge())
      return id;
    if (!summary) {
      auto checked = analysis.numerical(function, work);
      if (!checked) {
        fail(work.exhausted() ? "public-coin-limit" : "public-coin-dependence",
             toString(checked.takeError()));
        return id;
      }
      summary = *checked;
    }
    json::Array callees, primitives;
    for (auto child : summary->callees)
      callees.push_back(numerical(child));
    for (auto *op : summary->primitives) {
      if (!charge())
        break;
      auto row = actual(op);
      auto apply = cast<exec::ApplyOp>(op);
      auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
          apply, apply.getBindingAttr());
      if (!binding) {
        fail("public-coin-module", "missing numerical binding premise");
        break;
      }
      row["binding"] = actual(binding);
      primitives.push_back(std::move(row));
    }
    numericalRows[id] =
        json::Object{{"id", id},
                     {"declaration", function.getSymName().str()},
                     {"actual", actual(function)},
                     {"results", dependencies(summary->results)},
                     {"stops", dependencies(summary->stops)},
                     {"may_return", summary->mayReturn},
                     {"may_stop", summary->mayStop},
                     {"callees", std::move(callees)},
                     {"primitives", std::move(primitives)}};
    return id;
  }
  unsigned definition(const Summary &summary) {
    if (auto found = definitions.find(&summary); found != definitions.end())
      return found->second;
    unsigned id = definitionRows.size();
    definitions[&summary] = id;
    definitionRows.push_back(nullptr);
    if (!charge())
      return id;
    json::Array atoms, actions;
    for (const auto &atom : summary.atoms) {
      if (!charge())
        break;
      StringRef kind;
      using Kind = ProtocolObservationAtom::Kind;
      switch (atom.kind) {
      case Kind::Formal:
        kind = "formal";
        break;
      case Kind::Query:
        kind = "query";
        break;
      case Kind::Receive:
        kind = "receive";
        break;
      case Kind::CallResult:
        kind = "call_result";
        break;
      case Kind::CallStop:
        kind = "call_stop";
        break;
      case Kind::RepeatResult:
        kind = "repeat_result";
        break;
      case Kind::RepeatStop:
        kind = "repeat_stop";
        break;
      }
      json::Object row{{"kind", kind.str()}, {"port", atom.port}};
      if (atom.operation)
        row["operation"] = operation(atom.operation);
      atoms.push_back(std::move(row));
    }
    for (const auto &action : summary.actions) {
      if (!charge())
        break;
      auto row = actual(action.operation);
      row["inputs"] = dependencies(action.inputs);
      row["results"] = dependencies(action.results);
      row["input_origins"] = origins(action.inputOrigins);
      row["stops"] = dependencies(action.stops);
      row["may_stop"] = action.mayStop;
      row["delivered"] = origin(action.delivered);
      row["data_exchange"] = action.dataExchange;
      StringRef observation = "internal";
      if (action.service)
        observation = "query";
      else if (auto exchange = dyn_cast<pir::ExchangeOp>(action.operation)) {
        if (exchange.getReceiver() == summary.observer)
          observation = "receive";
        else if (exchange.getSender() == summary.observer)
          observation = action.dataExchange ? "data_transport" : "delivery";
      }
      row["observation"] = observation.str();
      if (action.service)
        row["service"] = *action.service;
      if (action.callee)
        row["callee"] = definition(*action.callee);
      if (auto loop = dyn_cast<pir::RepeatOp>(action.operation)) {
        row["carried"] = loop.getCarried();
        row["maximum"] = loop.getMaximum();
        row["transfer"] = "least-finite-may-dependence-including-zero";
      }
      if (action.numerical) {
        auto callee =
            action.operation->getAttrOfType<FlatSymbolRefAttr>("callee");
        auto function = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            action.operation, callee);
        if (!function) {
          fail("public-coin-module", "missing numerical call association");
          break;
        }
        row["numerical"] = numerical(function, action.numerical);
      }
      actions.push_back(std::move(row));
    }
    definitionRows[id] = json::Object{
        {"id", id},
        {"declaration",
         SymbolTable::getSymbolName(summary.declaration).getValue().str()},
        {"block_owner", operation(summary.block->getParentOp())},
        {"observer", summary.observer},
        {"formals", summary.formals},
        {"formal_types", types(summary.block->getArgumentTypes())},
        {"atoms", std::move(atoms)},
        {"actions", std::move(actions)},
        {"results", dependencies(summary.results)},
        {"result_origins", origins(summary.resultOrigins)},
        {"stops", dependencies(summary.stops)},
        {"services", dependencies(summary.services)},
        {"may_stop", summary.mayStop},
        {"pending", transfer(summary.pending)}};
    return id;
  }
  // Call contexts distinguish invocations without duplicating summaries.
  // A repeat adds an iteration-coordinate template, not an unrolled trace.
  bool occurrences(const Summary &summary, ArrayRef<std::string> path = {},
                   StringRef prefix = {}, ArrayRef<unsigned> coordinates = {},
                   ArrayRef<unsigned> context = {}) {
    if (path.size() + coordinates.size() > 64)
      return fail("public-coin-limit", "occurrence depth exceeded");
    for (const auto &action : summary.actions) {
      if (!charge())
        return false;
      auto *op = action.operation;
      auto site = op->getAttrOfType<StringAttr>("site");
      SmallVector<std::string> parts(path);
      std::string name;
      if (site) {
        name = prefix.empty() ? site.getValue().str()
                              : mathematical::expandedApplicationSite(
                                    prefix, site.getValue());
        if (name.size() > 4096 || !charge(name.size()))
          return fail("public-coin-limit", "expanded selector exceeds bound");
        parts.push_back(site.getValue().str());
      }
      if (action.callee) {
        SmallVector<unsigned> nested(context);
        nested.push_back(operation(op));
        if (isa<pir::RepeatOp>(op)) {
          SmallVector<unsigned> iterations(coordinates);
          iterations.push_back(operation(op));
          if (!occurrences(*action.callee, path, prefix, iterations, nested))
            return false;
        } else if (!occurrences(*action.callee, parts, name, coordinates,
                                nested))
          return false;
        continue;
      }
      auto occurrence = [&]() {
        json::Array calls, iteration, labels;
        for (unsigned id : context)
          calls.push_back(id);
        for (unsigned id : coordinates)
          iteration.push_back(id);
        for (const auto &part : parts)
          labels.push_back(part);
        return json::Object{{"definition", definitions.lookup(&summary)},
                            {"operation", operation(op)},
                            {"site", name},
                            {"path", std::move(labels)},
                            {"context", std::move(calls)},
                            {"iteration_coordinates", std::move(iteration)}};
      };
      if (auto query = dyn_cast<pir::QueryOp>(op); query && action.service) {
        if (pending || queries >= selected.size() ||
            selected[queries].first != name)
          return fail("public-coin-delivery", "query occurrence differs");
        auto row = occurrence();
        auto method = query.getMethod();
        StringRef law = method == "draw"      ? "uniform-field"
                        : method == "index"   ? "uniform-index"
                        : method == "indices" ? "product-uniform-indices"
                                              : "";
        if (law.empty())
          return fail("public-coin-service", "unsupported request law");
        json::Array staticArguments;
        for (Value input : query.getInputs()) {
          auto constant = input.getDefiningOp<data::IndexOp>();
          if (!constant || !protocol::uniformIndexBound(constant.getValue()))
            return fail("public-coin-service",
                        "nonstatic or empty request domain");
          staticArguments.push_back(constant.getValue());
        }
        row["request"] = json::Object{
            {"contract",
             cast<pir::ServiceReferenceType>(query.getReference().getType())
                 .getContract()
                 .str()},
            {"method", method.str()},
            {"law", law.str()},
            {"static_arguments", std::move(staticArguments)},
            {"operand_dependencies", dependencies(action.inputs)}};
        pending = queries++;
        draws.push_back(std::move(row));
      } else if (auto exchange = dyn_cast<pir::ExchangeOp>(op);
                 exchange && exchange.getSender() == summary.observer &&
                 !action.dataExchange) {
        if (!pending || selected[*pending].second != name)
          return fail("public-coin-delivery", "delivery occurrence differs");
        (*draws[*pending].getAsObject())["delivery"] = occurrence();
        pending.reset();
      }
    }
    return true;
  }

public:
  Graph(ModuleOp module, ProtocolObservationAnalysis &analysis,
        facts::Work &work,
        ArrayRef<std::pair<std::string, std::string>> selected)
      : module(module), analysis(analysis), work(work), selected(selected) {}
  Expected<json::Object> run(const Summary &root) {
    auto walk = module.walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (!charge())
        return WalkResult::interrupt();
      operations[op] = operations.size();
      return WalkResult::advance();
    });
    if (walk.wasInterrupted())
      return error(refusal, detail);
    unsigned rootId = definition(root);
    if (!refusal.empty())
      return error(refusal, detail);
    if (!occurrences(root))
      return error(refusal, detail);
    if (pending || queries != selected.size())
      return error("public-coin-delivery",
                   "unclosed or missing challenge family");
    json::Object result{{"root", rootId},
                        {"definitions", std::move(definitionRows)},
                        {"numerical", std::move(numericalRows)},
                        {"draws", std::move(draws)}};
    BoundedText stream;
    stream << json::Value(json::Object(result));
    if (!refusal.empty())
      return error(refusal, detail);
    if (stream.exceeded())
      return error("public-coin-limit", "report exceeds byte limit");
    return result;
  }
};
} // namespace
Expected<json::Object>
publicCoinGraph(ModuleOp module, ProtocolObservationAnalysis &analysis,
                const ProtocolObservationSummary &root, facts::Work &work,
                ArrayRef<std::pair<std::string, std::string>> selectedDraws) {
  return Graph(module, analysis, work, selectedDraws).run(root);
}
} // namespace zkc::detail
