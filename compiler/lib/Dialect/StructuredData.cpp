#include "zkc/Dialect/StructuredData.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Interfaces/CatalogType.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
Error refuse() { return error("structured-data"); }
InFlightDiagnostic silent(MLIRContext *context) {
  auto diagnostic = emitError(UnknownLoc::get(context));
  diagnostic.abandon();
  return diagnostic;
}
struct Budget {
  unsigned remaining = 200000;
  size_t bytes = 64 * 1024 * 1024;
  bool node(unsigned depth) {
    if (depth >= 64 || !remaining)
      return false;
    --remaining;
    return true;
  }
  bool text(StringRef text) {
    if (!json::isUTF8(text) || text.size() > bytes)
      return false;
    bytes -= text.size();
    return true;
  }
};
std::optional<uint64_t> natural(const json::Value &node) {
  auto text = node.getAsString();
  uint64_t value;
  if (!text || text->empty() || text->size() > 20 ||
      (text->size() > 1 && text->front() == '0') || !all_of(*text, isDigit) ||
      text->getAsInteger(10, value))
    return {};
  return value;
}
Expected<json::Value> exportTree(Attribute attr, Budget &budget,
                                 unsigned depth) {
  if (!attr || !budget.node(depth))
    return refuse();
  if (auto text = dyn_cast<StringAttr>(attr)) {
    if (!budget.text(text.getValue()))
      return refuse();
    return text.getValue().str();
  }
  if (auto flag = dyn_cast<BoolAttr>(attr))
    return flag.getValue();
  if (auto number = dyn_cast<IntegerAttr>(attr);
      number && number.getType().isUnsignedInteger(64))
    return number.getValue().getZExtValue();
  if (isa<UnitAttr>(attr))
    return nullptr;
  if (auto array = dyn_cast<ArrayAttr>(attr)) {
    json::Array values;
    for (auto item : array) {
      auto value = exportTree(item, budget, depth + 1);
      if (!value)
        return value.takeError();
      values.push_back(std::move(*value));
    }
    return values;
  }
  return refuse();
}
Expected<Attribute> importTree(MLIRContext *context, const json::Value &value,
                               Budget &budget, unsigned depth) {
  if (!context || !budget.node(depth))
    return refuse();
  if (auto text = value.getAsString()) {
    if (!budget.text(*text))
      return refuse();
    return StringAttr::get(context, *text);
  }
  if (auto flag = value.getAsBoolean())
    return BoolAttr::get(context, *flag);
  if (auto number = value.getAsUINT64())
    return IntegerAttr::get(
        IntegerType::get(context, 64, IntegerType::Unsigned), *number);
  if (value.kind() == json::Value::Null)
    return UnitAttr::get(context);
  if (auto array = value.getAsArray()) {
    SmallVector<Attribute> values;
    for (const auto &item : *array) {
      auto attr = importTree(context, item, budget, depth + 1);
      if (!attr)
        return attr.takeError();
      values.push_back(*attr);
    }
    return ArrayAttr::get(context, values);
  }
  return refuse();
}

struct TypeCodec {
  Budget budget;
  Expected<json::Value> encode(Type type, unsigned depth = 0) {
    if (!type || !budget.node(depth))
      return refuse();
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      if (!variant.getIdentity())
        return refuse();
      auto identity =
          exportTree(variant.getIdentity().getTerm(), budget, depth + 1);
      if (!identity)
        return identity.takeError();
      if (failed(data::IdentityAttr::verify(
              [&] { return silent(type.getContext()); },
              variant.getIdentity().getTerm())) ||
          variant.getAlternatives().empty() ||
          variant.getAlternatives().size() > 512)
        return refuse();
      json::Array alternatives;
      llvm::StringSet<> labels;
      for (auto arm : variant.getAlternatives()) {
        if (!arm || !budget.node(depth + 1) ||
            failed(data::AlternativeAttr::verify(
                [&] { return silent(type.getContext()); }, arm.getLabel(),
                arm.getPayload())) ||
            !budget.text(arm.getLabel().getValue()) ||
            !labels.insert(arm.getLabel().getValue()).second)
          return refuse();
        auto payload = encodeTypes(arm.getPayload(), depth + 2);
        if (!payload)
          return payload.takeError();
        alternatives.push_back(
            json::Array{arm.getLabel().getValue().str(), std::move(*payload)});
      }
      return json::Array{"variant", std::move(*identity),
                         std::move(alternatives)};
    }
    if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type)) {
      if (!budget.text(service.getContract()) ||
          protocol::randomServiceField(service.getContract()).empty())
        return refuse();
      return json::Array{"service", service.getContract().str()};
    }
    protocol_ir::OracleKindAttr oracle;
    std::optional<uint64_t> maximum;
    if (auto handle = dyn_cast<protocol_ir::OracleHandleType>(type))
      oracle = handle.getKind();
    if (auto sequence = dyn_cast<protocol_ir::OracleSequenceType>(type)) {
      oracle = sequence.getKind();
      maximum = sequence.getMaximum();
    }
    if (oracle) {
      if (!budget.text(oracle.getIdentity()) ||
          failed(protocol_ir::OracleKindAttr::verify(
              [&] { return silent(type.getContext()); }, oracle.getIdentity(),
              oracle.getArguments())))
        return refuse();
      auto arguments =
          encodeArguments(oracle.getArguments().getValue(), {}, depth + 1);
      if (!arguments)
        return arguments.takeError();
      if (maximum)
        return json::Array{"oracle_sequence", oracle.getIdentity().str(),
                           std::move(*arguments), std::to_string(*maximum)};
      return json::Array{"oracle", oracle.getIdentity().str(),
                         std::move(*arguments)};
    }
    auto interface = dyn_cast<CatalogTypeInterface>(type);
    auto application =
        interface ? interface.getCatalogApplication() : std::nullopt;
    auto declaration = application
                           ? protocol::typeDeclaration(application->constructor)
                           : nullptr;
    if (!declaration || !budget.text(application->constructor) ||
        failed(verifyLogicalTypeApplication(
            [&] { return silent(type.getContext()); }, type.getContext(),
            *application)))
      return refuse();
    auto arguments = encodeArguments(application->arguments,
                                     declaration->parameters, depth + 1);
    if (!arguments)
      return arguments.takeError();
    return json::Array{"apply", application->constructor.str(),
                       std::move(*arguments)};
  }
  Expected<json::Array> encodeTypes(TypeRange types, unsigned depth = 0) {
    json::Array result;
    for (auto type : types) {
      auto encoded = encode(type, depth);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    }
    return result;
  }
  Expected<json::Array>
  encodeArguments(ArrayRef<Attribute> arguments,
                  ArrayRef<protocol::StaticParameter> parameters,
                  unsigned depth) {
    if ((!parameters.empty() && parameters.size() != arguments.size()) ||
        arguments.size() > 1024)
      return refuse();
    json::Array result;
    for (auto [i, argument] : enumerate(arguments)) {
      if (!budget.node(depth))
        return refuse();
      if (auto type = dyn_cast<TypeAttr>(argument)) {
        if (!parameters.empty() &&
            parameters[i].kind != protocol::StaticKind::Type)
          return refuse();
        auto value = encode(type.getValue(), depth + 1);
        if (!value)
          return value.takeError();
        result.push_back(json::Array{"type", std::move(*value)});
      } else if (auto number = dyn_cast<IntegerAttr>(argument);
                 number && number.getType().isUnsignedInteger(64)) {
        if (!parameters.empty() &&
            parameters[i].kind != protocol::StaticKind::Nat)
          return refuse();
        result.push_back(json::Array{
            "nat", std::to_string(number.getValue().getZExtValue())});
      } else if (auto domain = dyn_cast<StringAttr>(argument);
                 domain && !parameters.empty() &&
                 parameters[i].kind == protocol::StaticKind::Domain) {
        if (!budget.text(domain.getValue()) || !budget.text(parameters[i].sort))
          return refuse();
        result.push_back(
            json::Array{"domain", parameters[i].sort, domain.getValue().str()});
      } else
        return refuse();
    }
    return result;
  }
  Expected<Type> decode(MLIRContext *context, const json::Value &value,
                        unsigned depth = 0) {
    if (!context || !budget.node(depth))
      return refuse();
    auto row = value.getAsArray();
    if (!row || row->empty() || !(*row)[0].getAsString())
      return refuse();
    auto tag = *(*row)[0].getAsString();
    auto emit = [&] { return silent(context); };
    if (tag == "service" && row->size() == 2) {
      auto contract = (*row)[1].getAsString();
      if (!contract || !budget.text(*contract) ||
          protocol::randomServiceField(*contract).empty() ||
          !context->getLoadedDialect<protocol_ir::ProtocolDialect>())
        return refuse();
      auto type = protocol_ir::ServiceReferenceType::get(context, *contract);
      if (!type)
        return refuse();
      return type;
    }
    if (tag == "variant" && row->size() == 3) {
      if (!context->getLoadedDialect<data::DataDialect>())
        return refuse();
      auto term = importTree(context, (*row)[1], budget, depth + 1);
      if (!term)
        return term.takeError();
      auto array = dyn_cast<ArrayAttr>(*term);
      auto arms = (*row)[2].getAsArray();
      if (!array || !arms || arms->empty() || arms->size() > 512)
        return refuse();
      auto identity = data::IdentityAttr::getChecked(emit, context, array);
      if (!identity)
        return refuse();
      SmallVector<data::AlternativeAttr> alternatives;
      for (const auto &item : *arms) {
        if (!budget.node(depth + 1))
          return refuse();
        auto arm = item.getAsArray();
        if (!arm || arm->size() != 2 || !(*arm)[0].getAsString() ||
            !budget.text(*(*arm)[0].getAsString()))
          return refuse();
        auto children = (*arm)[1].getAsArray();
        if (!children || children->size() > 512)
          return refuse();
        SmallVector<Type> payload;
        for (const auto &child : *children) {
          auto type = decode(context, child, depth + 2);
          if (!type)
            return type.takeError();
          payload.push_back(*type);
        }
        auto alternative = data::AlternativeAttr::getChecked(
            emit, context, StringAttr::get(context, *(*arm)[0].getAsString()),
            ArrayRef<Type>(payload));
        if (!alternative)
          return refuse();
        alternatives.push_back(alternative);
      }
      auto type = data::VariantType::getChecked(
          emit, context, identity,
          ArrayRef<data::AlternativeAttr>(alternatives));
      if (!type)
        return refuse();
      return type;
    }
    bool oracle = tag == "oracle" || tag == "oracle_sequence";
    if ((tag != "apply" && !oracle) ||
        row->size() != (tag == "oracle_sequence" ? 4u : 3u))
      return refuse();
    auto head = (*row)[1].getAsString();
    auto arguments = (*row)[2].getAsArray();
    if (!head || !budget.text(*head) || !arguments || arguments->size() > 16)
      return refuse();
    auto declaration = oracle ? nullptr : protocol::typeDeclaration(*head);
    if (!oracle &&
        (!declaration || declaration->parameters.size() != arguments->size()))
      return refuse();
    SmallVector<Attribute> attrs;
    for (auto [i, item] : enumerate(*arguments)) {
      if (!budget.node(depth + 1))
        return refuse();
      auto arg = item.getAsArray();
      if (!arg || arg->size() < 2 || !(*arg)[0].getAsString())
        return refuse();
      auto kind = *(*arg)[0].getAsString();
      if (kind == "type" && arg->size() == 2 &&
          (oracle ||
           declaration->parameters[i].kind == protocol::StaticKind::Type)) {
        auto type = decode(context, (*arg)[1], depth + 2);
        if (!type)
          return type.takeError();
        attrs.push_back(TypeAttr::get(*type));
      } else if (kind == "nat" && arg->size() == 2 &&
                 (oracle || declaration->parameters[i].kind ==
                                protocol::StaticKind::Nat)) {
        auto number = natural((*arg)[1]);
        if (!number)
          return refuse();
        attrs.push_back(IntegerAttr::get(
            IntegerType::get(context, 64, IntegerType::Unsigned), *number));
      } else if (!oracle && kind == "domain" && arg->size() == 3 &&
                 declaration->parameters[i].kind ==
                     protocol::StaticKind::Domain &&
                 (*arg)[1].getAsString() == declaration->parameters[i].sort &&
                 (*arg)[2].getAsString() &&
                 budget.text(*(*arg)[2].getAsString())) {
        attrs.push_back(StringAttr::get(context, *(*arg)[2].getAsString()));
      } else
        return refuse();
    }
    Type type;
    if (oracle) {
      if (!context->getLoadedDialect<protocol_ir::ProtocolDialect>())
        return refuse();
      auto kind = protocol_ir::OracleKindAttr::getChecked(
          emit, context, *head, ArrayAttr::get(context, attrs));
      if (!kind)
        return refuse();
      if (tag == "oracle_sequence") {
        auto maximum = natural((*row)[3]);
        if (!maximum)
          return refuse();
        type = protocol_ir::OracleSequenceType::getChecked(emit, context, kind,
                                                           *maximum);
      } else
        type = protocol_ir::OracleHandleType::getChecked(emit, context, kind);
    } else
      type = constructLogicalType(emit, context, {*head, attrs});
    if (!type)
      return refuse();
    return type;
  }
};

Expected<json::Value> parameterData(Attribute parameter) {
  if (auto number = dyn_cast<IntegerAttr>(parameter);
      number && number.getType().isUnsignedInteger(64))
    return json::Array{"natural",
                       std::to_string(number.getValue().getZExtValue())};
  if (auto literal = dyn_cast<algebra::FieldLiteralAttr>(parameter)) {
    auto value = algebra::encodeFieldLiteral(literal);
    if (!value)
      return value.takeError();
    return json::Array{"field_literal", literal.getField().getDomain().str(),
                       StringRef(*value).starts_with("0x") ? "bits" : "natural",
                       std::move(*value)};
  }
  if (auto asset = dyn_cast<runtime::AssetReferenceAttr>(parameter)) {
    auto digest = runtime::encodeAssetDigest(asset);
    if (!digest)
      return digest.takeError();
    return json::Array{"asset", asset.getFormat().str(), std::move(*digest)};
  }
  if (auto expression = dyn_cast<algebra::RingExpressionAttr>(parameter)) {
    auto value = algebra::exportRingExpression(expression);
    if (!value)
      return value.takeError();
    return json::Array{"expression", value->encode()};
  }
  if (auto origin = dyn_cast<runtime::NativeOriginAttr>(parameter)) {
    auto value = runtime::exportNativeOrigin(origin);
    if (!value)
      return value.takeError();
    json::Array path, event;
    for (const auto &step : value->path)
      path.push_back(json::Array{
          step.kind == protocol::NativeOriginStep::Kind::Apply ? "apply"
                                                               : "repeat",
          step.protocol, step.site});
    if (auto *query = std::get_if<protocol::NativeQueryOrigin>(&value->event))
      event = json::Array{
          "query",        query->protocol,
          query->site,    "input_" + std::to_string(query->serviceInput),
          query->service, query->method,
          query->owner};
    else if (auto *message =
                 std::get_if<protocol::NativeMessageOrigin>(&value->event))
      event =
          json::Array{"message",       message->protocol, message->site,
                      message->schema, message->sender,   message->receiver};
    else {
      auto &start = std::get<protocol::NativeStartOrigin>(value->event);
      event = json::Array{"start", start.protocol, start.site};
    }
    return json::Array{"origin", json::Array{"zkc.native-origin-template/0",
                                             value->entry, std::move(path),
                                             json::Array{}, std::move(event)}};
  }
  return refuse();
}
Expected<json::Value> semanticAttribute(Attribute attr, TypeCodec &codec,
                                        unsigned depth) {
  if (!attr || !codec.budget.node(depth))
    return refuse();
  if (auto text = dyn_cast<StringAttr>(attr)) {
    if (!codec.budget.text(text.getValue()))
      return refuse();
    return json::Array{"string", text.getValue().str()};
  }
  if (auto symbol = dyn_cast<SymbolRefAttr>(attr)) {
    json::Array parts;
    auto append = [&](StringRef text) {
      if (text.empty() || !codec.budget.text(text))
        return false;
      parts.push_back(text.str());
      return true;
    };
    if (!append(symbol.getRootReference().getValue()))
      return refuse();
    for (auto nested : symbol.getNestedReferences())
      if (!append(nested.getValue()))
        return refuse();
    return json::Array{"symbol", std::move(parts)};
  }
  if (auto flag = dyn_cast<BoolAttr>(attr))
    return json::Array{"bool", flag.getValue()};
  if (auto integer = dyn_cast<IntegerAttr>(attr)) {
    auto type = dyn_cast<IntegerType>(integer.getType());
    if (!type || !type.getWidth() || type.getWidth() > 4096)
      return refuse();
    return json::Array{"integer",
                       type.isSignless() ? "signless"
                       : type.isSigned() ? "signed"
                                         : "unsigned",
                       std::to_string(type.getWidth()),
                       toString(integer.getValue(), 10, type.isSigned())};
  }
  if (auto type = dyn_cast<TypeAttr>(attr)) {
    auto encoded = codec.encode(type.getValue(), depth + 1);
    if (!encoded)
      return encoded.takeError();
    return json::Array{"type", std::move(*encoded)};
  }
  if (auto array = dyn_cast<ArrayAttr>(attr)) {
    json::Array result;
    for (auto value : array) {
      auto encoded = semanticAttribute(value, codec, depth + 1);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    }
    return json::Array{"array", std::move(result)};
  }
  if (auto dictionary = dyn_cast<DictionaryAttr>(attr)) {
    json::Array result;
    for (auto item : dictionary) {
      if (!codec.budget.text(item.getName().getValue()))
        return refuse();
      auto encoded = semanticAttribute(item.getValue(), codec, depth + 1);
      if (!encoded)
        return encoded.takeError();
      result.push_back(
          json::Array{item.getName().getValue().str(), std::move(*encoded)});
    }
    return json::Array{"dictionary", std::move(result)};
  }
  auto parameter = parameterData(attr);
  if (!parameter)
    return parameter.takeError();
  return json::Array{"parameter", std::move(*parameter)};
}
} // namespace
Expected<json::Value> exportLogicalTypeData(Type type) {
  return TypeCodec{}.encode(type);
}
Expected<json::Array> exportLogicalTypesData(TypeRange types) {
  return TypeCodec{}.encodeTypes(types);
}
Expected<Type> importLogicalTypeData(MLIRContext *context,
                                     const json::Value &value) {
  return TypeCodec{}.decode(context, value);
}
Expected<SmallVector<Type>> importLogicalTypesData(MLIRContext *context,
                                                   const json::Array &values) {
  TypeCodec codec;
  SmallVector<Type> types;
  for (const auto &value : values) {
    auto type = codec.decode(context, value);
    if (!type)
      return type.takeError();
    types.push_back(*type);
  }
  return types;
}
Expected<json::Value> exportLogicalTypeInventory(TypeRange types) {
  if (types.size() > 4096)
    return refuse();
  auto rows = exportLogicalTypesData(types);
  if (!rows)
    return rows.takeError();
  // Exact structure is the interchange identity, even for roots from distinct
  // MLIR contexts. Native pointer uniqueness alone cannot enforce this rule.
  llvm::StringSet<> seen;
  for (const auto &row : *rows)
    if (!seen.insert(printJson(row)).second)
      return refuse();
  return json::Array{"zkc.logical-types/0", std::move(*rows)};
}
Expected<SmallVector<Type>>
importLogicalTypeInventory(MLIRContext *context, const json::Value &value) {
  const auto *record = value.getAsArray();
  if (!record || record->size() != 2 ||
      (*record)[0] != json::Value("zkc.logical-types/0"))
    return refuse();
  const auto *rows = (*record)[1].getAsArray();
  if (!rows || rows->size() > 4096)
    return refuse();
  auto types = importLogicalTypesData(context, *rows);
  if (!types)
    return types.takeError();
  llvm::DenseSet<Type> seen;
  for (Type type : *types)
    if (!seen.insert(type).second)
      return refuse();
  return std::move(*types);
}
Expected<json::Array> exportBindingData(runtime::BindingOp binding) {
  if (!binding)
    return refuse();
  auto emit = [&] { return silent(binding.getContext()); };
  auto native = readNativeBinding(emit, binding, false);
  if (failed(native))
    return refuse();
  const generic::Operation *declaration = nullptr;
  for (const auto &candidate : protocol::executableOperationContracts())
    if (candidate.name == binding.getContract())
      declaration = &candidate;
  if (!declaration)
    return refuse();
  SmallVector<protocol::StaticParameter> parameters;
  const auto &scope = declaration->signature.scope;
  for (auto [i, term] : enumerate(scope.terms))
    if (!term.parent && !term.arguments && !scope.constants.count(i)) {
      StringRef sort = scope.sorts[i];
      parameters.push_back({sort == "Type"  ? protocol::StaticKind::Type
                            : sort == "Nat" ? protocol::StaticKind::Nat
                                            : protocol::StaticKind::Domain,
                            sort == "Type" || sort == "Nat" ? "" : sort.str()});
    }
  TypeCodec codec;
  ArrayRef<Attribute> actuals = binding.getArguments().getValue();
  DenseBoolArrayAttr mask;
  if (declaration->numerical) {
    if (actuals.empty() ||
        !(mask = dyn_cast<DenseBoolArrayAttr>(actuals.back())))
      return refuse();
    actuals = actuals.drop_back();
  }
  if (actuals.size() != parameters.size())
    return refuse();
  auto arguments = codec.encodeArguments(actuals, parameters, 0);
  if (!arguments)
    return arguments.takeError();
  if (mask) {
    json::Array flags;
    for (bool flag : mask.asArrayRef())
      flags.push_back(flag);
    arguments->push_back(json::Array{"mask", std::move(flags)});
  }
  auto inputs = codec.encodeTypes(native->logicalType.getInputs());
  if (!inputs)
    return inputs.takeError();
  auto outputs = codec.encodeTypes(native->logicalType.getResults());
  if (!outputs)
    return outputs.takeError();
  return json::Array{binding.getContract().str(), std::move(*arguments),
                     binding.getImplementation().str(), std::move(*inputs),
                     std::move(*outputs)};
}
Error checkBindingData(runtime::BindingOp binding, const json::Value &value) {
  auto expected = exportBindingData(binding);
  if (!expected)
    return expected.takeError();
  return equalNaturalJson(json::Value(std::move(*expected)), value)
             ? Error::success()
             : refuse();
}
Expected<json::Array> exportInvocationParametersData(StringRef contract,
                                                     ArrayAttr arguments,
                                                     ArrayAttr parameters) {
  if (!arguments ||
      failed(verifyInvocationParameters(
          [&] { return silent(arguments.getContext()); }, contract, arguments,
          parameters, zkc::protocol::ParameterStage::Logical)))
    return refuse();
  json::Array result;
  for (auto parameter : parameters) {
    auto encoded = parameterData(parameter);
    if (!encoded)
      return encoded.takeError();
    result.push_back(std::move(*encoded));
  }
  return result;
}
Error checkInvocationParametersData(StringRef contract, ArrayAttr arguments,
                                    ArrayAttr parameters,
                                    const json::Value &value) {
  auto expected =
      exportInvocationParametersData(contract, arguments, parameters);
  if (!expected)
    return expected.takeError();
  return equalNaturalJson(json::Value(std::move(*expected)), value)
             ? Error::success()
             : refuse();
}
Expected<json::Value> exportSemanticAttributeData(Attribute attr) {
  TypeCodec codec;
  return semanticAttribute(attr, codec, 0);
}
Expected<ArrayAttr> importDeclarationData(MLIRContext *context,
                                          const json::Value &value) {
  if (!value.getAsArray())
    return refuse();
  Budget budget;
  auto attr = importTree(context, value, budget, 0);
  if (!attr)
    return attr.takeError();
  return cast<ArrayAttr>(*attr);
}
Expected<json::Value> exportDeclarationData(Attribute attr) {
  if (!attr || !isa<ArrayAttr>(attr))
    return refuse();
  Budget budget;
  return exportTree(attr, budget, 0);
}
} // namespace zkc
