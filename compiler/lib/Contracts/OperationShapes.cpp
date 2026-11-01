#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"

using namespace llvm;
namespace zkc::protocol {
Error checkParameters(const BindingApplication &binding,
                      ArrayRef<std::string> parameters, ParameterStage stage) {
  if (numericalContract(binding.contract)) {
    if (stage == ParameterStage::Logical)
      return checkNumericalParameters(binding, parameters);
    if (auto e = checkNumericalArguments(binding))
      return e;
    if (parameters.size() != 1)
      return error("interactive-kernel-parameters");
    auto plan = readNumericalPlan(parameters[0], binding.arguments[0],
                                  binding.arguments[1]);
    return plan ? Error::success() : plan.takeError();
  }
  std::string field;
  const auto *schema = parameterContract(binding.contract);
  if (schema && schema->fieldTerm) {
    const auto operations = executableOperationContracts();
    auto found = llvm::find_if(operations, [&](const auto &operation) {
      return operation.name == binding.contract;
    });
    if (found == operations.end())
      return error("binding-contract");
    auto terms =
        resolveStaticArguments(found->signature.scope, binding.arguments);
    if (!terms)
      return terms.takeError();
    if (*schema->fieldTerm >= terms->size())
      return error("binding-static-identity");
    field = (*terms)[*schema->fieldTerm];
  }
  return checkParameters(binding.contract, parameters, field);
}

StringRef fieldModulus(StringRef identity) {
  const auto *domain = installedDomains().domain(identity);
  return domain && domain->sort == "Field" ? StringRef(domain->modulus)
                                           : StringRef{};
}

unsigned fieldBitPatternWidth(StringRef identity) {
  // Closed presentations; see docs/spec/domains/values.md. The catalogue must
  // agree that the row is a field of characteristic two without PrimeField.
  static const struct {
    StringRef field;
    unsigned width;
  } binaryFields[] = {{"gf2-64.pentanomial-4-3-1", 64},
                      {"gf2-64.pentanomial-4-3-1.ext3-trinomial1", 192}};
  const auto &catalog = installedDomains();
  for (const auto &entry : binaryFields)
    if (entry.field == identity && fieldModulus(identity) == "2" &&
        !catalog.hasFact("PrimeField", {identity.str()}))
      return entry.width;
  return 0;
}

bool isBitPatternLiteral(StringRef text, unsigned width) {
  if (!text.consume_front("0x") || text.empty() || width % 4 ||
      text.size() > width / 4 || text.front() == '0' ||
      !all_of(text, [](char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
      }))
    return false;
  // Zero and one keep their natural spellings.
  return text.size() > 1 || text.front() >= '2';
}

namespace {
Error checkParametersImpl(StringRef key, llvm::ArrayRef<std::string> parameters,
                          StringRef field, bool genericField) {
  const auto *schema = parameterContract(key);
  const ParameterContract fallback{ParameterValidator::None, 0, 0};
  if (!schema)
    schema = &fallback;
  auto validator = schema->validator;
  if (parameters.size() < schema->minimum ||
      (schema->maximum && parameters.size() > *schema->maximum))
    return error("interactive-kernel-parameters");
  // A numerical body needs its complete closed [F,M] application. A
  // field-only or generic caller cannot establish positional agreement.
  if (validator == ParameterValidator::NumericalExpression)
    return error("numerical-body-signature");
  if (validator == ParameterValidator::MatrixIdentity ||
      validator == ParameterValidator::AssetIdentity) {
    StringRef digest = parameters.front();
    if (digest.size() != 64 || !all_of(digest, [](char c) {
          return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
        }))
      return error("interactive-kernel-parameters");
    return Error::success();
  }
  if (validator == ParameterValidator::NativeIndexBlock) {
    if (auto e = checkNativeOrigin(parameters.front(), "query", "indices"))
      return e;
    SmallVector<uint64_t> values;
    for (StringRef text : ArrayRef(parameters).drop_front()) {
      uint64_t value;
      if (text.empty() || (text.size() > 1 && text.front() == '0') ||
          !all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
          text.getAsInteger(10, value))
        return error("interactive-kernel-parameters");
      values.push_back(value);
    }
    auto n = values[0], q = values[1];
    if (!n || n > (uint64_t(1) << 63) || (n & (n - 1)) || !q || q > 1048576 ||
        (values.size() == 3 && values[2] > 64))
      return error("interactive-kernel-parameters");
    return Error::success();
  }
  if (validator == ParameterValidator::NativeOrigin) {
    if (key.ends_with(".challenge"))
      return checkNativeOrigin(parameters.front(), "query", "draw");
    if (key.ends_with(".index"))
      return checkNativeOrigin(parameters.front(), "query", "index");
    return checkNativeOrigin(parameters.front(), "message");
  }
  for (const auto &parameter : parameters) {
    StringRef n = parameter;
    auto code = (validator == ParameterValidator::FieldLiteral ||
                 validator == ParameterValidator::FieldLiterals)
                    ? "interactive-constant"
                : key == "curve.at" ? "interactive-index"
                                    : "interactive-kernel-parameters";
    // A binary field's constants other than zero and one are bit patterns.
    if ((validator == ParameterValidator::FieldLiteral ||
         validator == ParameterValidator::FieldLiterals) &&
        !genericField && n.starts_with("0x")) {
      if (!isBitPatternLiteral(n, fieldBitPatternWidth(field)))
        return error(code);
      continue;
    }
    if (n.empty() || !all_of(n, [](char c) { return c >= '0' && c <= '9'; }))
      return error("expected-natural");
    if (n.size() > 1 && n.front() == '0')
      return error("noncanonical-natural");
    if (validator == ParameterValidator::FieldLiteral ||
        validator == ParameterValidator::FieldLiterals) {
      if (genericField) {
        if (n != "0" && n != "1")
          return error(code);
        continue;
      }
      StringRef modulus = fieldModulus(field);
      if (modulus.empty() || n.size() > modulus.size() ||
          (n.size() == modulus.size() && n >= modulus))
        return error(code);
    } else {
      // Curve indices and vector sizes, positions and degrees share one
      // bound: no vector the runtimes provide is longer.
      uint64_t natural;
      if (n.getAsInteger(10, natural) ||
          ((validator == ParameterValidator::Extent ||
            validator == ParameterValidator::GatherIndices ||
            validator == ParameterValidator::MatrixVector) &&
           natural > 1048576) ||
          (validator == ParameterValidator::MatrixShape && natural > 65536))
        return error(code);
    }
  }
  if (validator == ParameterValidator::MatrixVector && parameters[2] != "0" &&
      parameters[2] != "1")
    return error("interactive-kernel-parameters");
  return Error::success();
}
} // namespace

Error checkParameters(StringRef key, ArrayRef<std::string> parameters,
                      StringRef field) {
  return checkParametersImpl(key, parameters, field, false);
}

Error checkGenericParameters(StringRef key, ArrayRef<std::string> parameters) {
  return checkParametersImpl(key, parameters, {}, true);
}
} // namespace zkc::protocol
