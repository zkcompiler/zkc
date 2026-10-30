#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/Parameters.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
using protocol::ParameterValidator;
struct Profile {
  protocol::ParameterContract schema{ParameterValidator::None, 0, 0};
  algebra::FieldType field;
  DenseBoolArrayAttr mask;
};
InFlightDiagnostic silentDiagnostic(MLIRContext *context) {
  auto diagnostic = emitError(UnknownLoc::get(context));
  diagnostic.abandon();
  return diagnostic;
}
FailureOr<Profile> profile(llvm::function_ref<InFlightDiagnostic()> emit,
                           StringRef contract, ArrayAttr arguments) {
  if (!arguments) {
    (void)diagnostics::emit(emit(), "binding-signature");
    return failure();
  }
  auto *context = arguments.getContext();
  auto terms =
      resolveBindingTerms(emit, context, contract, arguments.getValue());
  if (failed(terms))
    return failure();
  Profile result;
  if (const auto *schema = protocol::parameterContract(contract))
    result.schema = *schema;
  auto fieldTerm = result.schema.fieldTerm;
  if (result.schema.validator == ParameterValidator::NumericalExpression) {
    for (const auto &declaration : protocol::executableOperationContracts())
      if (declaration.name == contract && declaration.numerical)
        fieldTerm = declaration.numerical->fieldTerm;
    result.mask =
        arguments.empty()
            ? DenseBoolArrayAttr{}
            : dyn_cast<DenseBoolArrayAttr>(arguments.getValue().back());
    if (!fieldTerm || !result.mask) {
      (void)diagnostics::emit(emit(), "numerical-body-signature");
      return failure();
    }
  }
  if (fieldTerm) {
    auto identity = *fieldTerm < terms->size()
                        ? dyn_cast<StringAttr>((*terms)[*fieldTerm])
                        : StringAttr{};
    if (!identity || !context->getLoadedDialect<algebra::AlgebraDialect>()) {
      (void)diagnostics::emit(emit(), "binding-static-identity");
      return failure();
    }
    result.field = algebra::FieldType::get(context, identity.getValue());
  }
  return result;
}
StringRef assetFormat(const Profile &profile) {
  return profile.schema.validator == ParameterValidator::MatrixIdentity
             ? "zkc.matrix/0"
             : profile.schema.assetFormat;
}
bool arity(const Profile &profile, size_t count) {
  return count >= profile.schema.minimum &&
         (!profile.schema.maximum || count <= *profile.schema.maximum);
}
LogicalResult verifyParameters(llvm::function_ref<InFlightDiagnostic()> emit,
                               StringRef contract, const Profile &profile,
                               ArrayAttr parameters, MLIRContext *context) {
  auto refuse = [&](StringRef code = "interactive-kernel-parameters") {
    return diagnostics::emit(emit(), code);
  };
  if (!parameters || parameters.getContext() != context ||
      !arity(profile, parameters.size()))
    return refuse();
  auto validator = profile.schema.validator;
  for (Attribute parameter : parameters) {
    if (!parameter || parameter.getContext() != context)
      return refuse();
    switch (validator) {
    case ParameterValidator::None:
      return refuse();
    case ParameterValidator::FieldLiteral:
    case ParameterValidator::FieldLiterals: {
      auto literal = dyn_cast<algebra::FieldLiteralAttr>(parameter);
      if (!literal || !profile.field || literal.getField() != profile.field)
        return refuse("interactive-constant");
      if (failed(algebra::FieldLiteralAttr::verify(emit, literal.getField(),
                                                   literal.getValue())))
        return failure();
      break;
    }
    case ParameterValidator::MatrixIdentity:
    case ParameterValidator::AssetIdentity: {
      auto asset = dyn_cast<runtime::AssetReferenceAttr>(parameter);
      if (!asset || asset.getFormat() != assetFormat(profile))
        return refuse();
      if (failed(runtime::AssetReferenceAttr::verify(emit, asset.getFormat(),
                                                     asset.getDigest())))
        return failure();
      break;
    }
    case ParameterValidator::NativeOrigin: {
      auto origin = dyn_cast<runtime::NativeOriginAttr>(parameter);
      if (!origin)
        return refuse("interactive-native-origin");
      if (failed(runtime::NativeOriginAttr::verify(
              emit, origin.getEntry(), origin.getPath(), origin.getEvent())))
        return failure();
      // The operation's declared role fixes the event kind and query method;
      // a suggestive operation spelling supplies no authority.
      const auto *roles = protocol::operationContracts(contract);
      if (!roles)
        return refuse("interactive-native-origin");
      if (roles->sampling) {
        auto query = dyn_cast<runtime::QueryOriginAttr>(origin.getEvent());
        StringRef method =
            roles->sampling->domain == protocol::SampleDomain::BoundedIndex
                ? "index"
                : "draw";
        if (!query || query.getMethod() != method)
          return refuse("interactive-native-origin");
      } else if (!roles->observation ||
                 !isa<runtime::MessageOriginAttr>(origin.getEvent()))
        return refuse("interactive-native-origin");
      break;
    }
    case ParameterValidator::NumericalExpression: {
      auto expression = dyn_cast<algebra::RingExpressionAttr>(parameter);
      if (!expression || !expression.getOutputs() ||
          expression.getInputs().size() != size_t(profile.mask.size()) ||
          expression.getOutputs().size() != 1)
        return refuse("numerical-body-signature");
      for (auto input : expression.getInputs())
        if (input != profile.field)
          return refuse("numerical-body-field");
      for (auto node : expression.getNodes())
        if (!node || node.getKind() == algebra::RingNodeKind::Embed ||
            (node.getKind() == algebra::RingNodeKind::Constant &&
             (!node.getLiteral() ||
              node.getLiteral().getField() != profile.field)))
          return refuse("numerical-body-field");
      auto size = algebra::ringExpressionByteSize(expression);
      if (!size) {
        consumeError(size.takeError());
        return refuse("numerical-body-signature");
      }
      if (*size > protocol::NumericalLimits::bodyBytes)
        return refuse("numerical-body-limit");
      break;
    }
    case ParameterValidator::Natural:
    case ParameterValidator::Extent:
    case ParameterValidator::MatrixShape:
    case ParameterValidator::MatrixVector:
    case ParameterValidator::GatherIndices:
    case ParameterValidator::ScatterIndices: {
      auto value = dyn_cast<IntegerAttr>(parameter);
      if (!value || !value.getType().isUnsignedInteger(64))
        return refuse();
      auto natural = value.getValue().getZExtValue();
      if (((validator == ParameterValidator::Extent ||
            validator == ParameterValidator::GatherIndices ||
            validator == ParameterValidator::MatrixVector) &&
           natural > 1048576) ||
          (validator == ParameterValidator::MatrixShape && natural > 65536))
        return refuse();
      break;
    }
    }
  }
  if (validator == ParameterValidator::MatrixVector &&
      cast<IntegerAttr>(parameters[2]).getValue().getZExtValue() > 1)
    return refuse();
  return success();
}
} // namespace
LogicalResult
verifyInvocationParameters(llvm::function_ref<InFlightDiagnostic()> emit,
                           StringRef contract, ArrayAttr arguments,
                           ArrayAttr parameters) {
  auto selected = profile(emit, contract, arguments);
  return failed(selected)
             ? failure()
             : verifyParameters(emit, contract, *selected, parameters,
                                arguments.getContext());
}
namespace protocol {
Expected<ArrayAttr>
decodeInvocationParameters(MLIRContext *context,
                           const BindingApplication &binding,
                           ArrayRef<std::string> parameters) {
  auto arguments = decodeBindingArguments(context, binding);
  if (!arguments)
    return arguments.takeError();
  return decodeInvocationParameters(binding.contract, *arguments, parameters);
}
Expected<std::vector<std::string>>
encodeInvocationParameters(exec::ApplyOp call) {
  auto binding = call && call.getBindingAttr()
                     ? SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                           call, call.getBindingAttr())
                     : runtime::BindingOp{};
  if (!binding)
    return zkc::error("binding-reference");
  return encodeInvocationParameters(binding.getContract(),
                                    binding.getArgumentsAttr(),
                                    call.getParametersAttr());
}
Expected<ArrayAttr>
decodeInvocationParameters(StringRef contract, ArrayAttr arguments,
                           ArrayRef<std::string> parameters) {
  if (!arguments)
    return zkc::error("binding-signature");
  auto *context = arguments.getContext();
  auto selected =
      profile([&] { return silentDiagnostic(context); }, contract, arguments);
  if (failed(selected) || !arity(*selected, parameters.size()))
    return zkc::error("interactive-kernel-parameters");
  SmallVector<Attribute> attributes;
  for (StringRef parameter : parameters) {
    switch (selected->schema.validator) {
    case ParameterValidator::None:
      return zkc::error("interactive-kernel-parameters");
    case ParameterValidator::FieldLiteral:
    case ParameterValidator::FieldLiterals: {
      auto literal = algebra::decodeFieldLiteral(selected->field, parameter);
      if (!literal)
        return literal.takeError();
      attributes.push_back(*literal);
      break;
    }
    case ParameterValidator::MatrixIdentity:
    case ParameterValidator::AssetIdentity: {
      auto asset = runtime::decodeAssetReference(
          context, assetFormat(*selected), parameter);
      if (!asset)
        return asset.takeError();
      attributes.push_back(*asset);
      break;
    }
    case ParameterValidator::NativeOrigin: {
      auto origin = decodeNativeOriginTemplate(parameter);
      if (!origin)
        return origin.takeError();
      auto attribute = runtime::importNativeOrigin(context, *origin);
      if (!attribute)
        return attribute.takeError();
      attributes.push_back(*attribute);
      break;
    }
    case ParameterValidator::NumericalExpression: {
      if (parameter.size() > NumericalLimits::bodyBytes)
        return zkc::error("numerical-body-limit");
      auto expression = ring::readExpressionText(parameter);
      if (!expression)
        return expression.takeError();
      if (printJson(expression->encode()) != parameter)
        return zkc::error("numerical-body-canonical");
      auto attribute = algebra::importRingExpression(context, *expression);
      if (!attribute)
        return attribute.takeError();
      attributes.push_back(*attribute);
      break;
    }
    case ParameterValidator::Natural:
    case ParameterValidator::Extent:
    case ParameterValidator::MatrixShape:
    case ParameterValidator::MatrixVector:
    case ParameterValidator::GatherIndices:
    case ParameterValidator::ScatterIndices: {
      uint64_t value;
      if (parameter.empty() ||
          (parameter.size() > 1 && parameter.front() == '0') ||
          !all_of(parameter, isDigit) || parameter.getAsInteger(10, value))
        return zkc::error("expected-natural");
      attributes.push_back(IntegerAttr::get(
          IntegerType::get(context, 64, IntegerType::Unsigned), value));
      break;
    }
    }
  }
  auto result = ArrayAttr::get(context, attributes);
  if (failed(verifyParameters([&] { return silentDiagnostic(context); },
                              contract, *selected, result, context)))
    return zkc::error("interactive-kernel-parameters");
  return result;
}
Expected<std::vector<std::string>>
encodeInvocationParameters(StringRef contract, ArrayAttr arguments,
                           ArrayAttr parameters) {
  if (!arguments ||
      failed(verifyInvocationParameters(
          [&] { return silentDiagnostic(arguments.getContext()); }, contract,
          arguments, parameters)))
    return zkc::error("interactive-kernel-parameters");
  std::vector<std::string> result;
  for (Attribute parameter : parameters) {
    if (auto natural = dyn_cast<IntegerAttr>(parameter))
      result.push_back(std::to_string(natural.getValue().getZExtValue()));
    else if (auto literal = dyn_cast<algebra::FieldLiteralAttr>(parameter)) {
      auto encoded = algebra::encodeFieldLiteral(literal);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    } else if (auto asset = dyn_cast<runtime::AssetReferenceAttr>(parameter)) {
      auto encoded = runtime::encodeAssetDigest(asset);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    } else if (auto expression =
                   dyn_cast<algebra::RingExpressionAttr>(parameter)) {
      auto encoded = algebra::encodeRingExpression(expression);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    } else if (auto origin = dyn_cast<runtime::NativeOriginAttr>(parameter)) {
      auto neutral = runtime::exportNativeOrigin(origin);
      if (!neutral)
        return neutral.takeError();
      auto encoded = encodeNativeOriginTemplate(*neutral);
      if (!encoded)
        return encoded.takeError();
      result.push_back(std::move(*encoded));
    } else
      return zkc::error("interactive-kernel-parameters");
  }
  return result;
}
bool invocationParametersMatch(StringRef contract, ArrayAttr arguments,
                               ArrayAttr parameters,
                               ArrayRef<std::string> expected) {
  auto decoded = decodeInvocationParameters(contract, arguments, expected);
  if (!decoded) {
    consumeError(decoded.takeError());
    return false;
  }
  return parameters == *decoded;
}
} // namespace protocol
} // namespace zkc
