#include "mlir/IR/TypeRange.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/StringExtras.h"

using namespace mlir;
namespace zkc {
namespace {
struct SignatureFormation {
  llvm::function_ref<InFlightDiagnostic()> emit;
  MLIRContext *context;
  SmallVector<Attribute> terms;

  LogicalResult refuse(StringRef reason) {
    return diagnostics::emit(emit(), "binding-signature", reason);
  }
  LogicalResult checkStatic(Attribute value, StringRef sort) {
    if (!value || value.getContext() != context)
      return refuse("missing or foreign-context static value");
    if (sort == "Type") {
      auto type = dyn_cast<TypeAttr>(value);
      if (!type)
        return refuse("complete-Type static requires TypeAttr");
      return verifyLogicalType(emit, type.getValue());
    }
    if (sort == "Nat") {
      auto natural = dyn_cast<IntegerAttr>(value);
      if (!natural || !natural.getType().isUnsignedInteger(64) ||
          natural.getValue().getZExtValue() > 1048576)
        return refuse("static natural must be ui64 in 0..1048576");
      return success();
    }
    auto domain = dyn_cast<StringAttr>(value);
    if (!domain ||
        (sort == "Slot"
             ? !protocol::resourceUnitDomain(domain.getValue())
             : sort.empty() || protocol::installedDomains().identitySort(
                                   domain.getValue()) != sort))
      return refuse("static nominal identity has the wrong sort");
    return success();
  }
  Type application(StringRef constructor, ArrayRef<unsigned> arguments) {
    CatalogTypeApplication selected{constructor, {}};
    for (unsigned index : arguments) {
      if (index >= terms.size()) {
        (void)refuse("type argument is outside the formed scope");
        return {};
      }
      selected.arguments.push_back(terms[index]);
    }
    return constructLogicalType(emit, context, selected);
  }
  LogicalResult scope(const generic::Scope &scope,
                      ArrayRef<Attribute> arguments) {
    if (scope.terms.size() != scope.sorts.size() || scope.terms.size() > 1024 ||
        arguments.size() > 128)
      return refuse("invalid catalog scope or static arity");
    unsigned next = 0;
    for (auto [i, term] : llvm::enumerate(scope.terms)) {
      Attribute value;
      if (term.arguments) {
        if (term.parent || scope.constants.count(i) || scope.sorts[i] != "Type")
          return refuse("invalid catalog type application");
        auto type = application(term.name, *term.arguments);
        if (!type)
          return failure();
        value = TypeAttr::get(type);
      } else if (term.parent) {
        if (*term.parent >= i || scope.constants.count(i))
          return refuse("invalid catalog associated member");
        auto parent = dyn_cast<StringAttr>(terms[*term.parent]);
        auto identity =
            parent ? protocol::associatedIdentity(parent.getValue(), term.name)
                   : StringRef{};
        if (identity.empty())
          return refuse("associated identity is unavailable");
        value = StringAttr::get(context, identity);
      } else if (auto constant = scope.constants.find(i);
                 constant != scope.constants.end()) {
        // The neutral catalog admits only natural constants. This is immutable
        // declaration data, not a printed MLIR type or a caller's string value.
        StringRef literal = constant->second;
        uint64_t natural;
        if (scope.sorts[i] != "Nat" || literal.empty() ||
            (literal.size() > 1 && literal.front() == '0') ||
            !llvm::all_of(literal, llvm::isDigit) ||
            literal.getAsInteger(10, natural) || natural > 1048576)
          return refuse("invalid catalog natural constant");
        value = IntegerAttr::get(
            IntegerType::get(context, 64, IntegerType::Unsigned), natural);
      } else {
        if (next >= arguments.size())
          return refuse("missing static argument");
        value = arguments[next++];
      }
      if (failed(checkStatic(value, scope.sorts[i])))
        return failure();
      terms.push_back(value);
    }
    return next == arguments.size() ? success()
                                    : refuse("excess static arguments");
  }
  LogicalResult requirements(ArrayRef<requirements::Predicate> predicates) {
    for (const auto &predicate : predicates) {
      SmallVector<Attribute> arguments;
      for (unsigned index : predicate.arguments) {
        if (index >= terms.size())
          return refuse("requirement is outside the formed scope");
        arguments.push_back(terms[index]);
      }
      if (predicate.kind == requirements::Predicate::Kind::Equal) {
        if (arguments.size() != 2 || arguments[0] != arguments[1])
          return refuse("static equality requirement is unsatisfied");
        continue;
      }
      std::vector<std::string> identities;
      for (auto value : arguments) {
        auto identity = dyn_cast<StringAttr>(value);
        if (!identity)
          return refuse("no installed fact for this static argument kind");
        identities.push_back(identity.str());
      }
      if (!protocol::installedDomains().hasFact(predicate.relation, identities))
        return refuse("catalog capability requirement is unsatisfied");
    }
    return success();
  }
  const generic::Operation *binding(StringRef contract,
                                    ArrayRef<Attribute> arguments,
                                    DenseBoolArrayAttr &mask) {
    const generic::Operation *declaration = nullptr;
    for (const auto &candidate : protocol::executableOperationContracts())
      if (candidate.name == contract)
        declaration = &candidate;
    if (!context || !declaration) {
      (void)refuse("missing context or unknown catalog operation");
      return {};
    }
    ArrayRef<Attribute> roots = arguments;
    if (declaration->numerical) {
      if (arguments.empty() ||
          !(mask = dyn_cast_or_null<DenseBoolArrayAttr>(arguments.back())) ||
          mask.getContext() != context ||
          static_cast<size_t>(mask.size()) > protocol::NumericalLimits::slots) {
        (void)refuse("numerical family requires a bounded Boolean mask");
        return {};
      }
      roots = arguments.drop_back();
    }
    if (failed(scope(declaration->signature.scope, roots)) ||
        failed(requirements(declaration->signature.requirements)))
      return {};
    return declaration;
  }
  Type port(const generic::Type &port) {
    if (!port.term)
      return application(port.constructor, port.arguments);
    if (!port.constructor.empty() || !port.arguments.empty() ||
        *port.term >= terms.size()) {
      (void)refuse("invalid complete-Type port");
      return {};
    }
    auto selected = dyn_cast<TypeAttr>(terms[*port.term]);
    if (!selected) {
      (void)refuse("port term is not a complete Type");
      return {};
    }
    return selected.getValue();
  }
};
} // namespace

FailureOr<SmallVector<Attribute>>
resolveBindingTerms(llvm::function_ref<InFlightDiagnostic()> emit,
                    MLIRContext *context, StringRef contract,
                    ArrayRef<Attribute> arguments) {
  SignatureFormation formation{emit, context, {}};
  DenseBoolArrayAttr mask;
  if (!formation.binding(contract, arguments, mask))
    return failure();
  return std::move(formation.terms);
}

FunctionType
resolveLogicalSignature(llvm::function_ref<InFlightDiagnostic()> emit,
                        MLIRContext *context, StringRef contract,
                        ArrayRef<Attribute> arguments) {
  SignatureFormation formation{emit, context, {}};
  DenseBoolArrayAttr mask;
  auto *declaration = formation.binding(contract, arguments, mask);
  if (!declaration)
    return {};
  SmallVector<Type> inputs, outputs;
  if (declaration->numerical) {
    auto family = *declaration->numerical;
    auto row = formation.application("index", {});
    auto scalar = formation.application("field", {family.fieldTerm});
    auto vector = formation.application("vector", {family.fieldTerm});
    if (!row || !scalar || !vector)
      return {};
    inputs.push_back(row);
    for (bool mapped : mask.asArrayRef())
      inputs.push_back(mapped ? vector : scalar);
    outputs.push_back(family.result == generic::NumericalSignature::Result::Map
                          ? vector
                          : scalar);
  } else {
    auto append = [&](ArrayRef<generic::Type> ports,
                      SmallVectorImpl<Type> &out) {
      for (const auto &port : ports) {
        auto type = formation.port(port);
        if (!type)
          return failure();
        out.push_back(type);
      }
      return success();
    };
    if (failed(append(declaration->signature.inputs, inputs)) ||
        failed(append(declaration->signature.outputs, outputs)))
      return {};
  }
  return FunctionType::get(context, inputs, outputs);
}
} // namespace zkc
