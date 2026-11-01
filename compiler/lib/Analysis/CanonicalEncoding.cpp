#include "zkc/Analysis/CanonicalEncoding.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
#include <set>
using namespace llvm;
using namespace mlir;
namespace zkc {
struct CanonicalEncodingAnalysis::Impl {
  using Id = CanonicalEncodingAnalysis::Id;
  using Kind = CanonicalEncodingAnalysis::Kind;
  Operation *owner;
  SymbolTableCollection symbols;
  std::optional<protocol::SourceExecutionClosure> closure;
  Operation *closureOwner = nullptr;
  std::vector<Node> nodes;
  std::map<std::pair<Operation *, std::vector<Id>>, SmallVector<Id>> cache;
  std::set<Operation *> active;
  uint64_t remaining = 1000000;
  explicit Impl(Operation *owner) : owner(owner) {}
  Error unsupported(const Twine &detail) {
    return error("construction-binding-encoding", detail.str());
  }
  Error capacity() {
    remaining = 0;
    return error("construction-binding-capacity");
  }
  bool charge(uint64_t n = 1) {
    if (n > remaining) {
      remaining = 0;
      return false;
    }
    remaining -= n;
    return true;
  }
  Expected<Id> add(Node node) {
    if (nodes.size() >= 65536 || node.name.size() > 4096 ||
        !charge(1 + node.inputs.size() + node.name.size()))
      return capacity();
    nodes.push_back(std::move(node));
    return nodes.size() - 1;
  }
  Expected<Id> primitive(const protocol::SourceExecutionStep &step,
                         ArrayRef<Id> inputs) {
    auto op = cast<exec::ApplyOp>(step.operation);
    auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op->getAttrOfType<FlatSymbolRefAttr>("binding"));
    if (!binding || !binding.getImplementation().empty() ||
        step.outputs.size() != 1)
      return unsupported(
          "encoding primitive is not an installed single result");
    StringRef name = binding.getContract();
    Node result{Kind::Bytes,
                step.outputs[0].getType(),
                name.str(),
                {inputs.begin(), inputs.end()}};
    if (name == "index.constant") {
      auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
      if (!inputs.empty() || !parameters || parameters.size() != 1)
        return unsupported("integer constant parameters differ");
      auto constant = dyn_cast<IntegerAttr>(parameters[0]);
      if (!constant || constant.getValue().getActiveBits() > 64)
        return unsupported("integer constant is not a natural");
      result.kind = Kind::Integer;
      result.integer = constant.getValue().getZExtValue();
    } else if (name == "bytes.empty") {
      result.name.clear();
    } else if (name == "bytes.append") {
      const auto &left = nodes[inputs[0]], &right = nodes[inputs[1]];
      if (left.kind != Kind::Bytes || right.kind != Kind::Integer ||
          right.integer > 255 || left.name.size() >= 4096)
        return unsupported("literal byte construction is not constant");
      result.name = left.name + char(right.integer);
      result.inputs.clear();
    } else if (name == "bytes.concat") {
      if (nodes[inputs[0]].kind == Kind::Bytes &&
          nodes[inputs[1]].kind == Kind::Bytes) {
        result.name = nodes[inputs[0]].name + nodes[inputs[1]].name;
        result.inputs.clear();
      } else
        result.kind = Kind::Concat;
    } else if (name == "bytes.length")
      result.kind = Kind::Length;
    else if (name == "hash.keccak256" || name == "hash.sha256")
      result.kind = Kind::Hash;
    else if (name == "encoding.field_reduce_be" ||
             name == "encoding.field_reduce_le")
      result.kind = Kind::Reduce;
    else if (name == "encoding.field_be" || name == "encoding.field_le" ||
             name == "encoding.group_compressed" ||
             name == "encoding.index_uleb128")
      result.kind = Kind::Encode;
    else
      return unsupported("unrecognized encoding primitive: " + name);
    return add(std::move(result));
  }
  Expected<SmallVector<Id>> apply(func::FuncOp function, ArrayRef<Id> inputs,
                                  unsigned depth) {
    if (!charge(1 + inputs.size()) || depth > 64 || inputs.size() > 1024)
      return capacity();
    if (!isa_and_nonnull<ModuleOp>(owner) || !function ||
        !owner->isProperAncestor(function) || function.isExternal())
      return unsupported("helper is outside the immutable owner");
    auto key = std::make_pair(function.getOperation(), inputs.vec());
    if (auto prior = cache.find(key); prior != cache.end())
      return prior->second;
    if (!active.insert(function).second)
      return unsupported("cyclic helper closure");
    auto leave = scope_exit([&] { active.erase(function); });
    if (closureOwner && closureOwner != function->getParentOp())
      return unsupported("helper belongs to a different symbol-table owner");
    if (!closure) {
      auto read = protocol::readSourceExecutionClosure(function->getParentOp());
      if (!read)
        return read.takeError();
      closure = std::move(*read);
      closureOwner = function->getParentOp();
    }
    auto signature = protocol::scopedDataSignature(function);
    auto body = closure->bodies.find(function.getSymName().str());
    if (!signature || signature.getNumInputs() != inputs.size() ||
        body == closure->bodies.end())
      return unsupported("scoped helper signature differs");
    llvm::DenseMap<Value, Id> environment;
    for (auto [formal, actual] :
         zip(function.getArguments().drop_front(), inputs)) {
      if (actual >= nodes.size() || nodes[actual].type != formal.getType())
        return unsupported("actual helper input type differs");
      environment[formal] = actual;
    }
    for (const auto &step : body->second) {
      if (!charge(1 + step.inputs.size() + step.outputs.size()))
        return capacity();
      if (!step.regions.empty())
        return unsupported("encoding control requires a selected closed rule");
      SmallVector<Id> operands;
      for (auto value : step.inputs) {
        auto found = environment.find(value);
        if (found == environment.end())
          return unsupported("missing SSA association");
        operands.push_back(found->second);
      }
      if (isa<exec::ReturnOp, exec::CompleteOp>(step.operation)) {
        if (operands.size() != signature.getNumResults())
          return unsupported("encoding return signature differs");
        cache.emplace(std::move(key), operands);
        return operands;
      }
      SmallVector<Id> results;
      if (auto call = dyn_cast<func::CallOp>(step.operation)) {
        auto callee = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
        auto values = apply(callee, operands, depth + 1);
        if (!values)
          return values.takeError();
        results = std::move(*values);
      } else if (isa<exec::ApplyOp>(step.operation)) {
        auto result = primitive(step, operands);
        if (!result)
          return result.takeError();
        results.push_back(*result);
      } else
        return unsupported("unrecognized encoding operation");
      if (results.size() != step.outputs.size())
        return unsupported("encoding result signature differs");
      for (auto [value, id] : zip(step.outputs, results))
        environment[value] = id;
    }
    return unsupported("encoding helper has no continuing return");
  }
  bool flatten(Id id, SmallVectorImpl<Id> &parts, unsigned depth) {
    if (!charge() || depth > 64 || id >= nodes.size())
      return false;
    const auto &value = nodes[id];
    if (value.kind == Kind::Concat)
      return flatten(value.inputs[0], parts, depth + 1) &&
             flatten(value.inputs[1], parts, depth + 1);
    parts.push_back(id);
    return true;
  }
  Expected<Encoding> encoding(Id id, unsigned depth) {
    if (depth > 64 || !charge())
      return capacity();
    SmallVector<Id> parts;
    if (!flatten(id, parts, 0))
      return capacity();
    Encoding result;
    bool prefix = true;
    for (unsigned i = 0; i < parts.size(); ++i) {
      Id current = parts[i];
      const auto &part = nodes[current];
      if (part.kind == Kind::Bytes) {
        if (prefix) {
          if (result.tag.size() + part.name.size() > 4096)
            return capacity();
          result.tag += part.name;
        }
        continue;
      }
      prefix = false;
      if (part.kind == Kind::Hash) {
        auto inner = encoding(part.inputs.front(), depth + 1);
        if (!inner)
          return inner.takeError();
        append_range(result.inputs, inner->inputs);
      } else if (part.kind == Kind::Input && part.digestInput)
        result.inputs.push_back(current);
      else if (part.kind == Kind::Encode) {
        const auto &raw = nodes[part.inputs.front()];
        if (raw.kind == Kind::Input) {
          result.inputs.push_back(part.inputs.front());
        } else if (raw.kind == Kind::Integer)
          continue;
        else if (raw.kind == Kind::Length &&
                 part.name == "encoding.index_uleb128" &&
                 i + 1 < parts.size() && parts[i + 1] == raw.inputs.front() &&
                 nodes[parts[i + 1]].kind == Kind::Input) {
          result.inputs.push_back(parts[++i]);
        } else
          return unsupported("encoder does not cover an entire actual input");
      } else
        return unsupported("unframed or lossy encoding");
      if (!charge(result.inputs.size()))
        return capacity();
    }
    return result;
  }
};
CanonicalEncodingAnalysis::CanonicalEncodingAnalysis(Operation *owner)
    : impl(std::make_unique<Impl>(owner)) {}
CanonicalEncodingAnalysis::~CanonicalEncodingAnalysis() = default;
Expected<CanonicalEncodingAnalysis::Id>
CanonicalEncodingAnalysis::input(Type type, StringRef name, bool digest) {
  if (!type || name.empty())
    return impl->unsupported("encoding input has no type or identity");
  return impl->add({Kind::Input, type, name.str(), {}, 0, digest});
}
Expected<SmallVector<CanonicalEncodingAnalysis::Id>>
CanonicalEncodingAnalysis::apply(func::FuncOp function, ArrayRef<Id> inputs) {
  return impl->apply(function, inputs, 1);
}
Expected<CanonicalEncodingAnalysis::Encoding>
CanonicalEncodingAnalysis::encoding(Id id) {
  return impl->encoding(id, 1);
}
const CanonicalEncodingAnalysis::Node &
CanonicalEncodingAnalysis::node(Id id) const {
  return impl->nodes.at(id);
}
Expected<json::Value> CanonicalEncodingAnalysis::exportGraph() const {
  json::Array graph;
  for (const auto &node : impl->nodes) {
    auto type = exportLogicalTypeData(node.type);
    if (!type)
      return type.takeError();
    json::Array inputs;
    for (auto id : node.inputs)
      inputs.push_back(id);
    static constexpr StringLiteral kinds[] = {"input",  "integer", "bytes",
                                              "concat", "encode",  "length",
                                              "hash",   "reduce"};
    graph.push_back(json::Object{
        {"kind", kinds[unsigned(node.kind)]},
        {"type", std::move(*type)},
        {"name", node.kind == Kind::Bytes ? toHex(node.name) : node.name},
        {"inputs", std::move(inputs)},
        {"integer", node.integer},
        {"digest_input", node.digestInput}});
  }
  return json::Value(std::move(graph));
}
} // namespace zkc
