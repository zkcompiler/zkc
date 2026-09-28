#include "zkc/Mathematical/Codec.h"
#include "zkc/Mathematical/Raw.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::mathematical::raw {
namespace {
class Writer {
  unsigned depth = 0;
  AdmissionBudget budget{EncodingLimits::nodes};
  size_t copiedBytes = 0;
  std::string failure;

  bool charge(size_t amount = 1) {
    if (!failure.empty())
      return false;
    if (auto exhausted = budget.consume(amount)) {
      consumeError(std::move(exhausted));
      failure = "math-resource-limit";
      return false;
    }
    return true;
  }
  struct Scope {
    Writer &writer;
    explicit Scope(Writer &writer) : writer(writer) { ++writer.depth; }
    ~Scope() { --writer.depth; }
    bool entered() {
      if (writer.depth > EncodingLimits::depth) {
        writer.failure = "math-resource-limit";
        return false;
      }
      return writer.charge();
    }
  };
  json::Value v(uint64_t input) { return input; }
  bool copyBytes(size_t amount) {
    if (amount > EncodingLimits::bytes - copiedBytes) {
      failure = "math-resource-limit";
      return false;
    }
    copiedBytes += amount;
    return true;
  }
  json::Value v(const std::string &input) {
    if (!copyBytes(input.size()) || !json::isUTF8(input)) {
      failure = "math-string";
      return "";
    }
    return input;
  }
  template <class Tag> json::Value v(Reference<Tag> input) {
    return input.index;
  }
  template <class T> json::Value v(const std::vector<T> &inputs) {
    json::Array result;
    if (inputs.size() >= EncodingLimits::children || !charge(inputs.size())) {
      failure = "math-resource-limit";
      return result;
    }
    for (const auto &input : inputs) {
      if (!failure.empty())
        break;
      result.push_back(v(input));
    }
    return result;
  }
  template <class... T> json::Value v(const std::variant<T...> &input) {
    return std::visit([&](const auto &item) { return v(item); }, input);
  }
  template <class T> json::Value v(const std::shared_ptr<const T> &input) {
    if (!input) {
      failure = "math-schema";
      return json::Array{};
    }
    return v(*input);
  }
  json::Value v(const json::Value &input) {
    // Attribute records are caller-owned values; check before making a copy.
    auto bounded = encodeValue(input);
    if (!bounded) {
      consumeError(bounded.takeError());
      failure = "math-attributes";
      return json::Array{};
    }
    if (!copyBytes(bounded->size()))
      return json::Array{};
    return input;
  }
  json::Value v(const Static &input) {
    Scope scope(*this);
    if (!scope.entered())
      return json::Array{};
    size_t arity = input.kind == Static::Kind::Pow2 ? 1 : 2;
    if (input.kind == Static::Kind::Literal ||
        input.kind == Static::Kind::Parameter)
      arity = 0;
    if (input.operands.size() != arity || (arity && input.value != 0)) {
      failure = "math-static-shape";
      return json::Array{};
    }
    switch (input.kind) {
    case Static::Kind::Literal:
      return json::Array{"literal", input.value};
    case Static::Kind::Parameter:
      return json::Array{"parameter", input.value};
    case Static::Kind::Add:
      return json::Array{"add", v(input.operands[0]), v(input.operands[1])};
    case Static::Kind::Multiply:
      return json::Array{"multiply", v(input.operands[0]),
                         v(input.operands[1])};
    case Static::Kind::Pow2:
      return json::Array{"pow2", v(input.operands[0])};
    }
    failure = "math-static-kind";
    return json::Array{};
  }
  json::Value v(const TypeUse &input) {
    return json::Object{{"type", v(input.type)}, {"statics", v(input.statics)}};
  }
  json::Value v(const NominalType &input) {
    return json::Array{"nominal", v(input.domain), v(input.name),
                       v(input.arguments)};
  }
  json::Value v(const ProductType &input) {
    return json::Array{"product", v(input.elements)};
  }
  json::Value v(const FinType &input) {
    return json::Array{"fin", v(input.count)};
  }
  json::Value v(const VectorType &input) {
    return json::Array{"vector", v(input.element), v(input.count)};
  }
  json::Value v(const PolynomialType &input) {
    if (input.convention != PolynomialType::Degree::Individual &&
        input.convention != PolynomialType::Degree::Total)
      failure = "math-schema";
    return json::Array{
        "polynomial", v(input.domain), v(input.arity), v(input.degree),
        input.convention == PolynomialType::Degree::Individual ? "individual"
                                                               : "total"};
  }
  json::Value v(const ResidualType &input) {
    return json::Array{"residual", v(input.domain), v(input.arity),
                       v(input.degree)};
  }
  json::Value v(const TypeTemplate &input) {
    return json::Object{{"statics", input.statics}, {"body", v(input.body)}};
  }
  json::Value v(const Identity &input) {
    return json::Object{{"name", v(input.name)},
                        {"version", v(input.version)},
                        {"digest", v(input.digest)}};
  }
  json::Value v(const Manifest &input) {
    return json::Object{{"domains", v(input.domains)},
                        {"operations", v(input.operations)},
                        {"wires", v(input.wires)},
                        {"services", v(input.services)},
                        {"laws", v(input.laws)}};
  }
  json::Value v(const CapabilityUse &input) {
    return json::Object{{"type", v(input.type)}, {"statics", v(input.statics)}};
  }
  json::Value v(const CapabilityType &input) {
    return json::Object{{"identity", v(input.identity)},
                        {"statics", input.statics},
                        {"arguments", v(input.arguments)},
                        {"result", v(input.result)}};
  }
  json::Value v(const CapabilityParameter &input) {
    return json::Object{{"signature", v(input.signature)},
                        {"roles", v(input.roles)}};
  }
  json::Value v(const Root &input) {
    return json::Object{{"signature", v(input.signature)},
                        {"roles", v(input.roles)}};
  }
  json::Value v(const std::pair<uint64_t, uint64_t> &input) {
    return json::Array{input.first, input.second};
  }
  json::Value v(const Operation &input) {
    if (input.purity != Operation::Purity::Total &&
        input.purity != Operation::Purity::Ordered)
      failure = "math-schema";
    return json::Object{{"identity", v(input.identity)},
                        {"statics", input.statics},
                        {"capabilities", v(input.capabilities)},
                        {"arguments", v(input.arguments)},
                        {"result", v(input.result)},
                        {"purity", input.purity == Operation::Purity::Total
                                       ? "total"
                                       : "ordered"},
                        {"distinct", v(input.distinct)}};
  }
  json::Value v(const Wire &input) {
    return json::Object{{"identity", v(input.identity)},
                        {"statics", input.statics},
                        {"type", v(input.type)}};
  }
  json::Value v(const Port &input) {
    return json::Object{{"roles", v(input.roles)}, {"type", v(input.type)}};
  }
  json::Value v(const PureOperation &input) {
    return json::Array{"operation", v(input.operation), v(input.statics),
                       v(input.attributes), v(input.arguments)};
  }
  json::Value v(const Tuple &input) {
    return json::Array{"tuple", v(input.elements)};
  }
  json::Value v(const Project &input) {
    return json::Array{"project", v(input.value), input.component};
  }
  json::Value v(const Map &input) {
    return json::Array{"map", v(input.count), v(input.body)};
  }
  json::Value v(const Fold &input) {
    return json::Array{"fold", v(input.count), v(input.initial), v(input.body)};
  }
  json::Value v(const Region &input) {
    Scope scope(*this);
    if (!scope.entered())
      return json::Array{};
    return json::Object{{"captures", v(input.captures)},
                        {"nodes", v(input.nodes)},
                        {"outputs", v(input.outputs)}};
  }
  json::Value v(const Relation &input) {
    return json::Object{{"statics", input.statics},
                        {"public", v(input.publicInputs)},
                        {"witness", v(input.witnessInputs)},
                        {"assumptions", v(input.assumptions)},
                        {"body", v(input.body)}};
  }
  json::Value v(const RelationBinding &input) {
    return json::Object{{"relation", v(input.relation)},
                        {"statics", v(input.statics)},
                        {"public", v(input.publicInputs)},
                        {"witness", v(input.witnessInputs)}};
  }
  json::Value v(const Pure &input) {
    return json::Array{"pure", v(input.region)};
  }
  json::Value v(const Local &input) {
    return json::Array{"local",
                       input.site,
                       v(input.owner),
                       v(input.operation),
                       v(input.statics),
                       v(input.attributes),
                       v(input.capabilities),
                       v(input.arguments)};
  }
  json::Value v(const Query &input) {
    return json::Array{"query", input.site, v(input.owner), v(input.capability),
                       v(input.arguments)};
  }
  json::Value v(const Guard &input) {
    return json::Array{"guard", input.site, v(input.owner), v(input.condition)};
  }
  json::Value v(const Message &input) {
    return json::Array{"message",        input.site,      v(input.wire),
                       v(input.statics), v(input.sender), v(input.receiver),
                       v(input.value)};
  }
  json::Value v(const Invoke &input) {
    return json::Array{"invoke",          input.site,     v(input.definition),
                       v(input.statics),  v(input.roles), v(input.capabilities),
                       v(input.arguments)};
  }
  json::Value v(const Repeat &input) {
    return json::Array{"repeat",         input.site,       v(input.count),
                       v(input.carried), v(input.initial), v(input.captures),
                       v(input.body)};
  }
  json::Value v(const Return &input) {
    return json::Array{"return", v(input.values)};
  }
  json::Value v(const Stop &input) {
    StringRef reason;
    switch (input.reason) {
    case StopReason::Reject:
      reason = "reject";
      break;
    case StopReason::Abort:
      reason = "abort";
      break;
    case StopReason::Exhausted:
      reason = "exhausted";
      break;
    case StopReason::Incomplete:
      reason = "incomplete";
      break;
    case StopReason::Refused:
      reason = "refused";
      break;
    default:
      failure = "math-schema";
    }
    return json::Array{"stop", input.site, v(input.owner), reason};
  }
  json::Value v(const Body &input) {
    Scope scope(*this);
    if (!scope.entered())
      return json::Array{};
    return json::Object{{"steps", v(input.steps)},
                        {"terminal", v(input.terminal)}};
  }
  json::Value v(const Definition &input) {
    return json::Object{{"statics", input.statics},
                        {"roles", input.roles},
                        {"capabilities", v(input.capabilities)},
                        {"arguments", v(input.arguments)},
                        {"results", v(input.results)},
                        {"relations", v(input.relations)},
                        {"body", v(input.body)}};
  }
  json::Value v(const Entry &input) {
    return json::Object{{"definition", v(input.definition)},
                        {"statics", v(input.statics)},
                        {"roles", v(input.roles)},
                        {"capabilities", v(input.capabilities)}};
  }
  json::Value v(const Module &input) {
    return json::Object{{"roles", v(input.roles)},
                        {"types", v(input.types)},
                        {"operations", v(input.operations)},
                        {"wires", v(input.wires)},
                        {"capabilityTypes", v(input.capabilityTypes)},
                        {"roots", v(input.roots)},
                        {"relations", v(input.relations)},
                        {"definitions", v(input.definitions)},
                        {"entry", v(input.entry)}};
  }

public:
  Expected<json::Value> write(const Subject &input) {
    json::Value result = json::Object{{"profile", "zkc.math.v1"},
                                      {"manifest", v(input.manifest)},
                                      {"module", v(input.module)}};
    if (!failure.empty())
      return error(failure);
    auto bounded = encodeValue(result);
    if (!bounded)
      return bounded.takeError();
    return result;
  }
};
} // namespace
Expected<json::Value> encode(const Subject &subject) {
  return Writer().write(subject);
}
} // namespace zkc::mathematical::raw
