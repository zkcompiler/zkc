#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::protocol {
Error checkParameters(const BindingApplication &binding,
                      ArrayRef<std::string> parameters) {
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
  if (validator == ParameterValidator::MatrixIdentity) {
    StringRef digest = parameters.front();
    if (digest.size() != 64 || !all_of(digest, [](char c) {
          return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
        }))
      return error("interactive-kernel-parameters");
    return Error::success();
  }
  if (validator == ParameterValidator::NativeOrigin)
    return checkNativeOrigin(parameters.front(),
                             key.ends_with(".challenge") ? "query" : "message");
  for (const auto &parameter : parameters) {
    StringRef n = parameter;
    auto code = (validator == ParameterValidator::FieldLiteral ||
                 validator == ParameterValidator::FieldLiterals)
                    ? "interactive-constant"
                : key == "curve.at" ? "interactive-index"
                                    : "interactive-kernel-parameters";
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
