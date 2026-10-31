#include "OracleInspection.h"
#include "WrittenSourceIndex.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/BoundedStream.h"
using namespace llvm;
namespace zkc::language {
namespace {
using namespace detail;
class Instances {
  const ClosedEntry &entry;
  const WrittenIndex &written;
  Work &work;
  Expected<json::Value> term(const Type &type) {
    auto complexity =
        typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth);
    if (!complexity)
      return complexity.takeError();
    if (auto e = work.charge(*complexity))
      return std::move(e);
    return encodeStaticTerm(type);
  }
  Expected<json::Array> indices(ArrayRef<unsigned> values) {
    if (auto e = work.charge(values.size()))
      return std::move(e);
    json::Array result;
    for (auto value : values)
      result.push_back(value);
    return result;
  }
  json::Object span(Span value) const {
    return json::Object{
        {"module", entry.project().sources()[value.source.index].module},
        {"begin", value.begin},
        {"end", value.end}};
  }
  Expected<json::Value> shape(const DomainShape &shape) {
    if (auto e = work.charge(shape.inputs.size() + shape.nodes.size() + 1))
      return std::move(e);
    json::Array inputs, nodes;
    for (const auto &input : shape.inputs) {
      auto value = term(input);
      if (!value)
        return value.takeError();
      inputs.push_back(std::move(*value));
    }
    for (const auto &node : shape.nodes) {
      StringRef kind;
      using K = DomainBinding::Kind;
      switch (node.kind) {
      case K::Elements:
        kind = "elements";
        break;
      case K::Indices:
        kind = "indices";
        break;
      case K::Range:
        kind = "range";
        break;
      case K::Zip:
        kind = "zip";
        break;
      case K::Product:
        kind = "product";
        break;
      case K::MatrixRow:
        kind = "matrix_row";
        break;
      case K::MatrixColumn:
        kind = "matrix_column";
        break;
      case K::MatrixCoordinates:
        kind = "matrix_coordinates";
        break;
      case K::SourceArray:
        kind = "source_array";
        break;
      case K::Parameter:
      case K::Application:
        return failure("source.instances",
                       "domain argument is not a closed constructor graph");
      }
      if (node.parameter || node.factory || !node.arguments.empty() ||
          !node.argumentOrder.empty())
        return failure("source.instances",
                       "domain argument retains a source factory");
      auto item = term(node.item);
      if (!item)
        return item.takeError();
      if (auto e = work.charge(node.operands.size()))
        return std::move(e);
      json::Array operands;
      for (auto operand : node.operands)
        operands.push_back(operand.index);
      auto children = indices(node.children);
      if (!children)
        return children.takeError();
      nodes.push_back(json::Object{{"kind", kind.str()},
                                   {"item", std::move(*item)},
                                   {"operands", std::move(operands)},
                                   {"children", std::move(*children)},
                                   {"axis", node.axis}});
    }
    return json::Object{{"inputs", std::move(inputs)},
                        {"nodes", std::move(nodes)},
                        {"result", shape.result}};
  }

public:
  Instances(const ClosedEntry &entry, const WrittenIndex &written, Work &work)
      : entry(entry), written(written), work(work) {}
  Expected<json::Array> run() {
    json::Array result;
    for (const auto &decl : entry.declarations()) {
      if (auto e = work.charge(1))
        return std::move(e);
      if (!decl.origin)
        continue;
      const auto &source = entry.declarations()[decl.origin->index];
      if (source.parameters.size() != decl.staticArguments.size())
        return failure("source.instances",
                       "closed static argument count differs");
      json::Object origin;
      if (decl.scopedOrigin) {
        const auto &owner =
            entry.declarations()[decl.scopedOrigin->first.index];
        auto nodes = encodeWrittenAddresses(
            written.at(owner.span, {LexicalNode::Kind::Expression,
                                    decl.scopedOrigin->second}),
            work);
        if (!nodes)
          return nodes.takeError();
        if (auto e = work.charge(1 + owner.qualifiedName.size()))
          return std::move(e);
        origin = json::Object{{"kind", "scoped"},
                              {"owner", owner.qualifiedName},
                              {"source", span(source.span)},
                              {"nodes", std::move(*nodes)}};
      } else {
        auto candidates = encodeWrittenAddresses(written.at(source.span), work);
        if (!candidates)
          return candidates.takeError();
        if (auto e = work.charge(1 + source.qualifiedName.size()))
          return std::move(e);
        origin = json::Object{{"kind", "declaration"},
                              {"owner", source.qualifiedName},
                              {"generated", source.generated.has_value()},
                              {"source", span(source.span)},
                              {"candidates", std::move(*candidates)}};
      }
      json::Array statics, scoped, domains;
      for (unsigned i = 0; i < source.parameters.size(); ++i) {
        if (auto e = work.charge(1 + source.parameters[i].name.size()))
          return std::move(e);
        auto value = term(decl.staticArguments[i]);
        if (!value)
          return value.takeError();
        statics.push_back(
            json::Array{source.parameters[i].name, std::move(*value)});
      }
      for (auto argument : decl.scopedArguments) {
        const auto &selected = entry.declarations()[argument.index];
        if (auto e = work.charge(1 + selected.symbol.size()))
          return std::move(e);
        scoped.push_back(selected.symbol);
      }
      for (const auto &domain : decl.domainArguments) {
        if (!domain)
          return failure("source.instances", "missing closed domain argument");
        auto value = shape(*domain);
        if (!value)
          return value.takeError();
        domains.push_back(std::move(*value));
      }
      auto inputs = indices(decl.closureLayout.inputs);
      if (!inputs)
        return inputs.takeError();
      auto captures = indices(decl.closureLayout.captures);
      if (!captures)
        return captures.takeError();
      auto symbol = decl.relation ? formulaSymbol(decl) : decl.symbol;
      if (auto e = work.charge(1 + symbol.size()))
        return std::move(e);
      json::Object instance{
          {"symbol", std::move(symbol)},
          {"template", std::move(origin)},
          {"statics", std::move(statics)},
          {"scoped", std::move(scoped)},
          {"domains", std::move(domains)},
          {"layout", json::Object{{"inputs", std::move(*inputs)},
                                  {"captures", std::move(*captures)}}}};
      if (decl.oracleDefinition) {
        const auto &definition = *decl.oracleDefinition;
        if (auto e = work.charge(
                definition.predicates.size() + definition.sourceBounds.size() +
                definition.resultShape.size() +
                (decl.body ? decl.body->operations.size() : 0) + 1))
          return std::move(e);
        instance["oracle_definition"] =
            describeOracleDefinition(entry.declarations(), decl);
      }
      result.push_back(std::move(instance));
    }
    return result;
  }
};
} // namespace
Expected<std::string> inspectSourceInstances(const ClosedEntry &entry,
                                             const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  const auto &project = entry.project();
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations)
    return detail::failure("source.limit",
                           "checked project exceeds source instance limits");
  if (!project.storage->writtenSources)
    return detail::failure("source.syntax", "written source was not retained");
  detail::Work work{limits};
  auto written = detail::indexWrittenSource(
      project, *project.storage->writtenSources, work);
  if (!written)
    return written.takeError();
  auto instances = Instances(entry, *written, work).run();
  if (!instances)
    return instances.takeError();
  json::Value value =
      json::Object{{"format", "zkc.source-instances/0"},
                   {"capture", project.capture().identity()},
                   {"installation", project.installationIdentity()},
                   {"instances", std::move(*instances)}};
  std::string bytes;
  BoundedStream out(bytes, limits.apiInspectionBytes);
  out << value;
  if (out.overflow())
    return detail::failure("source.limit",
                           "source instance export byte limit exceeded");
  return bytes;
}
} // namespace zkc::language
