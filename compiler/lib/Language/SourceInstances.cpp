#include "OracleInspection.h"
#include "WrittenSourceIndex.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
using namespace llvm;
namespace zkc::language {
namespace {
using namespace detail;
class Instances {
  const ClosedEntry &entry;
  const WrittenIndex &written;
  Work &work;
  Expected<json::Value> term(const Type &type) {
    return encodeStaticTerm(
        type, work.limits, work.remaining(),
        [&](uint64_t amount) { return work.charge(amount); });
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
  Expected<json::Value> finiteShape(ArrayRef<Type> sourceInputs,
                                    ArrayRef<DescriptorBinding> sourceNodes,
                                    unsigned result) {
    if (auto e = work.charge(sourceInputs.size() + sourceNodes.size() + 1))
      return std::move(e);
    json::Array inputs, nodes;
    for (const auto &input : sourceInputs) {
      auto value = term(input);
      if (!value)
        return value.takeError();
      inputs.push_back(std::move(*value));
    }
    for (const auto &node : sourceNodes) {
      StringRef kind;
      using K = DescriptorBinding::Kind;
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
      case K::StructuralProduct:
      case K::Sequence:
      case K::ProductProjection:
      case K::SequenceProjection:
      case K::Append:
      case K::Concat:
      case K::Replace:
      case K::ForgetExtent:
      case K::CheckExtent:
      case K::Fold:
        return failure("source.instances",
                       "domain argument is not a closed constructor graph");
      }
      if (node.parameter || node.factory || !node.arguments.empty() ||
          !node.argumentOrder.empty())
        return failure("source.instances",
                       "domain argument retains a source factory");
      auto contract = term(descriptorType(node.contract));
      if (!contract)
        return contract.takeError();
      if (auto e = work.charge(node.operands.size()))
        return std::move(e);
      json::Array operands;
      for (auto operand : node.operands)
        operands.push_back(operand.index);
      json::Array children;
      if (auto e = work.charge(node.children.size()))
        return std::move(e);
      for (const auto &edge : node.children) {
        auto contract = term(descriptorType(edge.contract));
        if (!contract)
          return contract.takeError();
        children.push_back(json::Object{{"node", edge.node},
                                        {"contract", std::move(*contract)}});
      }
      nodes.push_back(json::Object{{"kind", kind.str()},
                                   {"contract", std::move(*contract)},
                                   {"operands", std::move(operands)},
                                   {"children", std::move(children)},
                                   {"axis", node.axis}});
    }
    return json::Object{{"inputs", std::move(inputs)},
                        {"nodes", std::move(nodes)},
                        {"result", result}};
  }
  Expected<json::Value> shape(const DescriptorShape &shape) {
    if (!shape.arena || shape.payload >= shape.arena->payloads.size())
      return failure("source.instances",
                     "descriptor formation arena is absent");
    const auto &arena = *shape.arena;
    const auto &selected = arena.payloads[shape.payload];
    if (finiteDescriptorItem(selected.contract))
      return finiteShape(shape.inputs, shape.nodes, shape.result);
    auto contract = term(descriptorType(selected.contract));
    auto leaves = finiteShape(shape.inputs, arena.leaves, UINT32_MAX);
    if (!contract)
      return contract.takeError();
    if (!leaves)
      return leaves.takeError();
    json::Array payloads, sequences, blocks;
    for (const auto &payload : arena.payloads) {
      if (auto e = work.charge(1))
        return std::move(e);
      auto contract = term(descriptorType(payload.contract));
      if (!contract)
        return contract.takeError();
      json::Object value{{"contract", std::move(*contract)}};
      if (const auto *leaf = std::get_if<unsigned>(&payload.value)) {
        value["kind"] = "finite";
        value["leaf"] = *leaf;
      } else if (const auto *product =
                     std::get_if<std::vector<unsigned>>(&payload.value)) {
        auto edges = indices(*product);
        if (!edges)
          return edges.takeError();
        value["kind"] = "product";
        value["elements"] = std::move(*edges);
      } else if (const auto *sequence = std::get_if<uint64_t>(&payload.value)) {
        value["kind"] = "sequence";
        value["root"] = *sequence == UINT32_MAX ? json::Value(nullptr)
                                                : json::Value(*sequence);
      } else
        return failure(
            "source.instances",
            "source residual cannot be exported as closed formation");
      payloads.push_back(std::move(value));
    }
    for (const auto &node : arena.sequences) {
      if (auto e = work.charge(1 + node.count))
        return std::move(e);
      json::Array elements;
      for (unsigned i = 0; i < node.count; ++i)
        elements.push_back(node.elements[i]);
      sequences.push_back(json::Object{
          {"length", node.length},
          {"height", node.height},
          {"left", node.count ? json::Value(nullptr) : json::Value(node.left)},
          {"right",
           node.count ? json::Value(nullptr) : json::Value(node.right)},
          {"elements", std::move(elements)}});
    }
    static constexpr StringLiteral kinds[] = {"parameter",
                                              "application",
                                              "elements",
                                              "indices",
                                              "range",
                                              "zip",
                                              "product",
                                              "matrix_row",
                                              "matrix_column",
                                              "matrix_coordinates",
                                              "source_array",
                                              "ordered_product",
                                              "sequence",
                                              "product_projection",
                                              "sequence_projection",
                                              "append",
                                              "concat",
                                              "replace",
                                              "forget_extent",
                                              "check_extent",
                                              "fold"};
    for (const auto &block : arena.blocks) {
      json::Array events;
      for (const auto &event : block) {
        if (auto e = work.charge(1 + 2 * event.authority.size()))
          return std::move(e);
        auto children = indices(event.children);
        if (!children)
          return children.takeError();
        if (unsigned(event.kind) >= std::size(kinds))
          return failure("source.instances",
                         "unknown formation occurrence kind");
        events.push_back(json::Object{
            {"kind", kinds[unsigned(event.kind)].str()},
            {"expression", event.expression ? json::Value(*event.expression)
                                            : json::Value(nullptr)},
            {"result", event.result},
            {"children", std::move(*children)},
            {"invocation", event.invocation ? json::Value(*event.invocation)
                                            : json::Value(nullptr)},
            {"authority", toHex(event.authority, true)}});
      }
      blocks.push_back(std::move(events));
    }
    auto &finite = *leaves->getAsObject();
    return json::Object{{"format", "zkc.descriptor-formation/0"},
                        {"contract", std::move(*contract)},
                        {"inputs", std::move(*finite.get("inputs"))},
                        {"leaves", std::move(*finite.get("nodes"))},
                        {"payloads", std::move(payloads)},
                        {"sequences", std::move(sequences)},
                        {"blocks", std::move(blocks)},
                        {"payload", shape.payload},
                        {"formation", shape.formation}};
  }
  Error oracleObligations(const Body &body, std::vector<unsigned> &path,
                          unsigned depth, json::Array &result) {
    if (depth > work.limits.expressionDepth)
      return failure("source.limit", "oracle obligation region depth exceeded");
    if (auto e = work.charge(1 + body.operations.size()))
      return e;
    for (unsigned i = 0; i < body.operations.size(); ++i) {
      const auto &operation = body.operations[i];
      path.push_back(i);
      if (const auto *call =
              std::get_if<OracleInstantiation>(&operation.action)) {
        const auto &definition = entry.declarations()[call->callee.index];
        const auto &plan = *definition.oracleDefinition;
        const auto &predicate = entry.declarations()[plan.admissibility.index];
        auto companions = oracleAdmissibilityCompanions(entry.declarations(),
                                                        definition, work);
        if (!companions)
          return companions.takeError();
        auto address = indices(path);
        if (!address)
          return address.takeError();
        auto receivers = indices(call->receivers);
        if (!receivers)
          return receivers.takeError();
        if (auto e =
                work.charge(call->operands.size() + operation.results.size() +
                            definition.symbol.size() + 1))
          return e;
        json::Array substitution, results;
        for (unsigned input = 0; input < call->operands.size(); ++input) {
          auto value = call->operands[input];
          auto type = term(body.values[value.index].type);
          if (!type)
            return type.takeError();
          substitution.push_back(json::Object{
              {"input", input},
              {"value", value.index},
              {"type", std::move(*type)},
              {"projection", input < plan.sourceCount ? "data" : "value"}});
        }
        for (auto value : operation.results)
          results.push_back(value.index);
        result.push_back(
            json::Object{{"path", std::move(*address)},
                         {"source", span(operation.span)},
                         {"site", operation.site ? json::Value(*operation.site)
                                                 : json::Value(nullptr)},
                         {"definition", definition.symbol},
                         {"admissibility", formulaSymbol(predicate)},
                         {"companions", std::move(*companions)},
                         {"substitution", std::move(substitution)},
                         {"holder", call->holder},
                         {"receivers", std::move(*receivers)},
                         {"results", std::move(results)},
                         {"status", "unresolved"}});
      }
      if (const auto *repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
        path.push_back(0);
        if (auto e =
                oracleObligations(*repeat->region, path, depth + 1, result))
          return e;
        path.pop_back();
      } else if (const auto *control =
                     std::get_if<Control>(&operation.action)) {
        for (unsigned region = 0; region < control->regions.size(); ++region) {
          path.push_back(region);
          if (auto e = oracleObligations(*control->regions[region], path,
                                         depth + 1, result))
            return e;
          path.pop_back();
        }
      }
      path.pop_back();
    }
    return Error::success();
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
        origin = json::Object{
            {"kind", "declaration"},
            {"owner", source.qualifiedName},
            {"generated", source.generated.has_value()},
            {"source",
             entry.project().sources()[source.span.source.index].origin ==
                     SourceOrigin::Installation
                 ? json::Value(nullptr)
                 : json::Value(span(source.span))},
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
      for (const auto &domain : decl.descriptorArguments) {
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
        auto definition =
            describeOracleDefinition(entry.declarations(), decl, work);
        if (!definition)
          return definition.takeError();
        instance["oracle_definition"] = std::move(*definition);
      }
      json::Array obligations;
      std::vector<unsigned> path;
      if (decl.body)
        if (auto e = oracleObligations(*decl.body, path, 1, obligations))
          return std::move(e);
      instance["oracle_obligations"] = std::move(obligations);
      result.push_back(std::move(instance));
    }
    return result;
  }
};
} // namespace
Expected<json::Value> sourceInstancesData(const ClosedEntry &entry,
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
  if (!jsonWithinByteLimit(value, limits.apiInspectionBytes))
    return detail::failure("source.limit",
                           "source instance export byte limit exceeded");
  ownJsonStrings(value);
  return value;
}
Expected<std::vector<json::Array>>
writtenSiteNodes(const CheckedProject &project, ArrayRef<EmittedSite> sites,
                 const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  if (!project.storage->writtenSources)
    return detail::failure("source.syntax", "written source was not retained");
  detail::Work work{limits};
  auto written = detail::indexWrittenSource(
      project, *project.storage->writtenSources, work);
  if (!written)
    return written.takeError();
  std::vector<json::Array> result;
  for (const auto &site : sites) {
    if (auto e = work.charge(1))
      return std::move(e);
    if (!site.expression) {
      result.emplace_back();
      continue;
    }
    auto nodes = detail::encodeWrittenAddresses(
        written->at(site.owner,
                    {detail::LexicalNode::Kind::Expression, *site.expression}),
        work);
    if (!nodes)
      return nodes.takeError();
    result.push_back(std::move(*nodes));
  }
  return result;
}
Expected<std::string> inspectSourceInstances(const ClosedEntry &entry,
                                             const Limits &limits) {
  auto value = sourceInstancesData(entry, limits);
  if (!value)
    return value.takeError();
  return printJson(*value);
}
} // namespace zkc::language
