#include "zkc/Dialect/Bindings.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {

namespace {
const generic::Operation *catalogOperation(StringRef contract) {
  for (const auto &operation : executableOperationContracts())
    if (operation.name == contract)
      return &operation;
  return nullptr;
}
FunctionType valueSignature(Operation *op) {
  auto attribute = op->getAttrOfType<TypeAttr>("function_type");
  auto type =
      attribute ? dyn_cast<FunctionType>(attribute.getValue()) : FunctionType{};
  if (!type || type.getNumInputs() == 0 ||
      !isa_and_nonnull<runtime::ScopeType>(type.getInput(0)) ||
      type.getNumResults() != 1)
    return {};
  auto outcome = dyn_cast_or_null<exec::OutcomeType>(type.getResult(0));
  return outcome ? FunctionType::get(op->getContext(),
                                     type.getInputs().drop_front(),
                                     outcome.getPayload())
                 : FunctionType{};
}
} // namespace

Expected<ArrayAttr> decodeBindingArguments(MLIRContext *context,
                                           const BindingApplication &binding) {
  auto *operation = catalogOperation(binding.contract);
  if (!context || !operation)
    return error("binding-contract");
  ArrayRef<std::string> values = binding.arguments;
  if (binding.contract == "table.relayout") {
    if (values.size() != 3)
      return error("binding-conversion");
    values = values.take_front(1);
  }
  SmallVector<Attribute> arguments;
  unsigned next = 0;
  for (auto [i, term] : enumerate(operation->signature.scope.terms)) {
    if (term.parent || term.arguments ||
        operation->signature.scope.constants.count(i))
      continue;
    if (next == values.size())
      return error("binding-static-arity");
    StringRef value = values[next++],
              sort = operation->signature.scope.sorts[i];
    if (!staticIdentityMatches(sort, value))
      return error("binding-static-identity");
    if (sort == "Type") {
      auto bound = parseBoundType(value, false);
      if (!bound)
        return bound.takeError();
      auto native = decodeBoundType(context, *bound);
      if (!native)
        return error("binding-type");
      arguments.push_back(TypeAttr::get(native));
    } else if (sort == "Nat") {
      uint64_t natural;
      if (value.getAsInteger(10, natural))
        return error("binding-static-identity");
      arguments.push_back(IntegerAttr::get(
          IntegerType::get(context, 64, IntegerType::Unsigned), natural));
    } else {
      arguments.push_back(StringAttr::get(context, value));
    }
  }
  if (operation->numerical) {
    if (next == values.size() || values[next].size() > NumericalLimits::slots)
      return error("binding-static-arity");
    SmallVector<bool> mask;
    for (char bit : values[next++]) {
      if (bit != '0' && bit != '1')
        return error("binding-static-identity");
      mask.push_back(bit == '1');
    }
    arguments.push_back(DenseBoolArrayAttr::get(context, mask));
  }
  if (next != values.size())
    return error("binding-static-arity");
  return ArrayAttr::get(context, arguments);
}

Expected<std::vector<std::string>> encodeBindingArguments(StringRef contract,
                                                          ArrayAttr arguments) {
  auto *operation = catalogOperation(contract);
  if (!operation || !arguments)
    return error("binding-contract");
  unsigned next = 0;
  std::vector<std::string> values;
  for (auto [i, term] : enumerate(operation->signature.scope.terms)) {
    if (term.parent || term.arguments ||
        operation->signature.scope.constants.count(i))
      continue;
    if (next == arguments.size())
      return error("binding-static-arity");
    auto value = arguments[next++];
    StringRef sort = operation->signature.scope.sorts[i];
    if (sort == "Type") {
      auto type = dyn_cast<TypeAttr>(value);
      if (!type)
        return error("binding-static-identity");
      auto bound = encodeBoundType(type.getValue(), false);
      if (!bound)
        return bound.takeError();
      values.push_back(bound->spelling());
    } else if (sort == "Nat") {
      auto natural = dyn_cast<IntegerAttr>(value);
      if (!natural || !natural.getType().isUnsignedInteger(64) ||
          natural.getValue().getZExtValue() > 1048576)
        return error("binding-static-identity");
      values.push_back(std::to_string(natural.getValue().getZExtValue()));
    } else {
      auto identity = dyn_cast<StringAttr>(value);
      if (!identity || !staticIdentityMatches(sort, identity.getValue()))
        return error("binding-static-identity");
      values.push_back(identity.getValue().str());
    }
  }
  if (operation->numerical) {
    if (next == arguments.size())
      return error("binding-static-arity");
    auto mask = dyn_cast<DenseBoolArrayAttr>(arguments[next++]);
    if (!mask || static_cast<size_t>(mask.size()) > NumericalLimits::slots)
      return error("binding-static-identity");
    std::string text;
    for (bool bit : mask.asArrayRef())
      text += bit ? '1' : '0';
    values.push_back(std::move(text));
  }
  if (next != arguments.size())
    return error("binding-static-arity");
  return values;
}

Expected<FunctionType> bindingSignature(MLIRContext *context,
                                        const BindingApplication &application,
                                        bool physical) {
  auto ports = resolveBinding(application, physical);
  if (!ports)
    return ports.takeError();
  SmallVector<Type> inputs, outputs;
  for (auto [source, target] : {std::make_pair(&ports->inputs, &inputs),
                                std::make_pair(&ports->outputs, &outputs)})
    for (const auto &bound : *source) {
      auto type = decodeBoundType(context, bound);
      if (!type)
        return error("binding-type");
      target->push_back(type);
    }
  return executableBindingSignature(
      FunctionType::get(context, inputs, outputs));
}
bool bindingMatches(runtime::BindingOp actual, const OperationBinding &expected,
                    bool physical) {
  if (!actual || !actual.getSymNameAttr() || !actual.getContractAttr() ||
      !actual.getImplementationAttr() ||
      actual->hasAttr("physical_arguments") ||
      actual.getSymName() != expected.name ||
      actual.getContract() != expected.application.contract ||
      actual.getImplementation() != expected.application.implementation)
    return false;
  auto arguments =
      decodeBindingArguments(actual.getContext(), expected.application);
  if (!arguments) {
    consumeError(arguments.takeError());
    return false;
  }
  auto signature =
      bindingSignature(actual.getContext(), expected.application, physical);
  if (!signature) {
    consumeError(signature.takeError());
    return false;
  }
  for (StringRef name : {"arg_attrs", "res_attrs"})
    if (auto attributes = actual->getAttr(name)) {
      auto dictionaries = dyn_cast<ArrayAttr>(attributes);
      size_t count = name == "arg_attrs" ? signature->getNumInputs()
                                         : signature->getNumResults();
      if (!dictionaries || dictionaries.size() != count ||
          any_of(dictionaries, [](Attribute value) {
            auto dictionary = dyn_cast<DictionaryAttr>(value);
            return !dictionary || !dictionary.empty();
          }))
        return false;
    }
  return actual.getArgumentsAttr() == *arguments &&
         actual->getAttr("function_type") == TypeAttr::get(*signature);
}
Expected<runtime::BindingOp> importBinding(OpBuilder &builder,
                                           Location location,
                                           const OperationBinding &binding,
                                           bool physical) {
  auto type =
      bindingSignature(builder.getContext(), binding.application, physical);
  if (!type)
    return type.takeError();
  auto arguments =
      decodeBindingArguments(builder.getContext(), binding.application);
  if (!arguments)
    return arguments.takeError();
  return runtime::BindingOp::create(
      builder, location, binding.name, binding.application.contract, *arguments,
      binding.application.implementation, *type, ArrayAttr{}, ArrayAttr{});
}

Expected<protocol::OperationBinding> readBinding(Operation *op) {
  if (!op)
    return error("binding-declaration-context");
  std::string code = "binding-signature", detail;
  ScopedDiagnosticHandler capture(op->getContext(), [&](Diagnostic &value) {
    if (detail.empty()) {
      auto refusals = diagnostics::refusals(value);
      if (!refusals.empty())
        code = refusals.front().code;
    }
    detail += value.str();
    return success();
  });
  auto native = readNativeBinding([&] { return op->emitOpError(); }, op);
  if (failed(native))
    return error(code, detail);
  auto declaration = native->declaration;
  auto type = native->valueType;
  bool physical = native->physical;
  auto arguments = encodeBindingArguments(declaration.getContract(),
                                          declaration.getArgumentsAttr());
  if (!arguments)
    return arguments.takeError();
  OperationBinding binding{declaration.getSymName().str(),
                           {declaration.getContract().str(),
                            std::move(*arguments),
                            declaration.getImplementation().str()}};
  // A byte publication cannot silently discard uninterpreted call annotations.
  for (StringRef name : {"arg_attrs", "res_attrs"})
    if (auto attributes = op->getAttrOfType<ArrayAttr>(name))
      for (Attribute value : attributes)
        if (!cast<DictionaryAttr>(value).empty())
          return error("binding-attributes");
  BoundOperation actual;
  for (auto [source, target] :
       {std::make_pair(type.getInputs(), &actual.inputs),
        std::make_pair(type.getResults(), &actual.outputs)})
    for (Type port : source) {
      auto encoded = encodeBoundType(port, physical);
      if (!encoded)
        return encoded.takeError();
      target->push_back(std::move(*encoded));
    }
  if (physical) {
    auto &application = binding.application;
    if (application.contract == "representation.convert") {
      if (actual.inputs.size() != 1 || actual.outputs.size() != 1)
        return error("binding-conversion");
      application.physicalArguments = {actual.inputs[0].spelling(),
                                       actual.outputs[0].spelling()};
    } else if (application.contract == "table.relayout") {
      if (actual.inputs.size() != 1 || actual.outputs.size() != 1)
        return error("binding-conversion");
      application.arguments.push_back(actual.inputs[0].representation);
      application.arguments.push_back(actual.outputs[0].representation);
    } else if (auto *descriptor = installedImplementations().find(
                   application.contract, application.implementation)) {
      using Family = ImplementationDescriptor::Family;
      if (descriptor->family == Family::Observation) {
        auto payload =
            operationContracts(application.contract)->observation->payloadInput;
        if (payload >= actual.inputs.size())
          return error("binding-signature");
        application.physicalArguments = {actual.inputs[payload].spelling()};
      } else if (descriptor->family != Family::Exact) {
        StringRef kind = descriptor->family == Family::Sequence ? "sequence"
                         : descriptor->family == Family::FieldArray
                             ? "field_array"
                             : "fixed_vector";
        for (const auto *ports : {&actual.inputs, &actual.outputs})
          for (const auto &port : *ports)
            if (application.physicalArguments.empty() && port.kind == kind)
              application.physicalArguments = {port.spelling()};
        if (application.physicalArguments.empty())
          return error("binding-representation");
      }
    }
  }
  if (auto error =
          checkBindingDeclaration(binding.name, binding.application, physical))
    return error;
  auto expected = resolveBinding(binding.application, physical);
  if (!expected)
    return expected.takeError();
  if (expected->inputs != actual.inputs || expected->outputs != actual.outputs)
    return error("binding-signature");
  return binding;
}

Expected<protocol::OperationBinding> operationBinding(Operation *user) {
  // Resolve in this lexical symbol table only. Compiler schedules use a
  // builtin module; executable profile admission owns its closed vocabulary.
  auto *root = SymbolTable::getNearestSymbolTable(user);
  auto reference = user->getAttrOfType<FlatSymbolRefAttr>("binding");
  if (!root || !reference)
    return error("binding-reference");
  return readBinding(SymbolTable::lookupSymbolIn(root, reference));
}

} // namespace zkc::protocol

namespace zkc {
namespace {
using Descriptor = protocol::ImplementationDescriptor;
using Family = Descriptor::Family;

std::optional<CatalogTypeApplication> applicationOf(Type type) {
  auto interface = dyn_cast_or_null<CatalogTypeInterface>(type);
  return interface ? interface.getCatalogApplication() : std::nullopt;
}
StringRef constructorOf(Type type) {
  if (isa<data::VariantType>(type))
    return "variant";
  auto application = applicationOf(type);
  return application ? application->constructor : StringRef{};
}
StringRef atomicDomain(Type type) {
  auto application = applicationOf(type);
  if (application && application->arguments.size() == 1)
    if (auto identity = dyn_cast<StringAttr>(application->arguments[0]))
      return identity.getValue();
  return {};
}

// Formation is mandatory before this profile query. Unlike local Copy, the
// closed message grammar covers every inactive variant arm and physical child.
bool messageType(Type type) {
  auto represented = dyn_cast<runtime::RepresentedType>(type);
  Type logical = logicalValueType(type);
  auto kind = constructorOf(logical);
  if (kind == "variant" || kind == "sequence") {
    if (represented)
      return all_of(represented.getChildren(), messageType);
    if (auto variant = dyn_cast<data::VariantType>(logical))
      return all_of(variant.getAlternatives(), [](auto arm) {
        return all_of(arm.getPayload(), messageType);
      });
    return messageType(
        cast<TypeAttr>(applicationOf(logical)->arguments[0]).getValue());
  }
  if (kind == "field_array") {
    auto application = applicationOf(logical);
    if (cast<StringAttr>(application->arguments[0]).getValue() !=
        "bls12-381.fr")
      return false;
    return !represented ||
           ((represented.getRepresentation() == "arkworks.field-array/0" ||
             represented.getRepresentation() == "blst/field-array") &&
            all_of(represented.getChildren(), messageType));
  }
  auto application = applicationOf(logical);
  if (!application || application->arguments.size() > 1 ||
      !protocol::nativeMessageAtom(kind, atomicDomain(logical)))
    return false;
  if (!represented)
    return true;
  StringRef representation = represented.getRepresentation();
  auto *ordinary = protocol::installedDomains().defaultRepresentation(
      kind, atomicDomain(logical));
  return (ordinary && ordinary->identity == representation) ||
         representation == "blst/fr" || representation == "blst/g1" ||
         representation == "blst/g2" ||
         representation == "halo2curves-axiom/bn254.fr" ||
         representation == "halo2curves-axiom/bn254.g1" ||
         representation == "halo2curves-axiom/bn254.g2";
}

LogicalResult callAttributes(llvm::function_ref<InFlightDiagnostic()> emit,
                             Operation *op, unsigned inputs, unsigned outputs) {
  for (auto [name, count] : {std::make_pair("arg_attrs", inputs),
                             std::make_pair("res_attrs", outputs)}) {
    auto attribute = op->getAttr(name);
    if (!attribute)
      continue;
    auto values = dyn_cast<ArrayAttr>(attribute);
    if (!values || values.size() != count ||
        !llvm::all_of(
            values, [](Attribute value) { return isa<DictionaryAttr>(value); }))
      return diagnostics::emit(
          emit(), "binding-attributes",
          "argument/result dictionaries must match the actual executable ABI");
  }
  return success();
}

struct Installation {
  llvm::function_ref<InFlightDiagnostic()> emit;

  LogicalResult refuse(StringRef code, StringRef reason) {
    return diagnostics::emit(emit(), code, reason);
  }
  LogicalResult provider(const Descriptor &entry, const generic::Scope &scope,
                         ArrayRef<Attribute> terms) {
    if (auto error = protocol::checkImplementationScope(entry, scope)) {
      consumeError(std::move(error));
      return refuse("binding-implementation", "invalid installed selector");
    }
    if (terms.size() != scope.sorts.size())
      return refuse("binding-implementation", "incomplete native scope");
    if (entry.compatibility == Descriptor::Compatibility::Independent)
      return success();
    auto selected = dyn_cast<StringAttr>(terms[entry.providerTerm]);
    if (!selected || (!entry.domains.empty() &&
                      !is_contained(entry.domains, selected.getValue())))
      return refuse("binding-implementation", "selected domain is unsupported");
    auto supports = [&](StringRef domain) {
      return protocol::implementationProviderSupports(entry.provider, domain);
    };
    if (entry.compatibility == Descriptor::Compatibility::Transcript) {
      auto suite = selected.getValue();
      StringRef field = protocol::associatedIdentity(suite, "ChallengeField");
      if (!supports(suite) || field.empty())
        return refuse("binding-implementation", "unsupported transcript suite");
      StringRef base = protocol::associatedIdentity(field, "BaseField");
      for (auto [index, term] : enumerate(terms)) {
        StringRef sort = scope.sorts[index];
        if (sort == "Type" || sort == "Nat" || sort == "Codec")
          continue;
        auto identity = cast<StringAttr>(term).getValue();
        if (identity == suite)
          continue;
        StringRef payloadField = identity;
        if (sort == "Group")
          payloadField = protocol::associatedIdentity(identity, "Scalar");
        else if (sort == "Commitment")
          payloadField = protocol::associatedIdentity(identity, "ValueField");
        if (payloadField != field && (base.empty() || payloadField != base))
          return refuse("binding-implementation",
                        "payload domain differs from the transcript field");
      }
      return success();
    }
    for (auto [index, term] : enumerate(terms)) {
      StringRef sort = scope.sorts[index];
      if (sort != "Type" && sort != "Nat" && sort != "Codec" &&
          !supports(cast<StringAttr>(term).getValue()))
        return refuse("binding-implementation",
                      "provider does not support every nominal domain");
    }
    return success();
  }

  FunctionType layouts(StringRef contract, const Descriptor &entry,
                       FunctionType logical, FunctionType actual, bool physical,
                       Type familyLayout) {
    // Logical pins in a polymorphic family constrain the provider but do not
    // select a layout. Exact pins must already have a realizable physical ABI.
    if (!physical && entry.family != Family::Exact)
      return logical;
    SmallVector<Type> inputs(logical.getInputs()),
        outputs(logical.getResults());
    Type container, selected = familyLayout, element;
    if (entry.family == Family::Sequence ||
        entry.family == Family::FieldArray ||
        entry.family == Family::FixedVector) {
      StringRef kind = entry.family == Family::Sequence     ? "sequence"
                       : entry.family == Family::FieldArray ? "field_array"
                                                            : "fixed_vector";
      for (auto [schema, ports] :
           {std::make_pair(logical.getInputs(),
                           actual ? actual.getInputs() : ArrayRef<Type>{}),
            std::make_pair(logical.getResults(),
                           actual ? actual.getResults() : ArrayRef<Type>{})})
        for (auto [index, value] : enumerate(schema))
          if (!container && constructorOf(value) == kind) {
            container = value;
            if (actual && !selected)
              selected = ports[index];
          }
      if (!selected && container) {
        if (!entry.denseLayout)
          selected = defaultPhysicalType(emit, container);
        else {
          auto app = applicationOf(container);
          Type child =
              entry.family == Family::FieldArray
                  ? constructLogicalType(emit, container.getContext(),
                                         {"field", {app->arguments[0]}})
                  : cast<TypeAttr>(app->arguments[0]).getValue();
          // The installation's finite pattern supplies a scalar layout;
          // native parent formation checks its exact domain and extent.
          for (const auto &layout : protocol::appliedTypeRepresentations()) {
            if (layout.constructor != kind ||
                layout.representation != entry.denseLayout->container ||
                layout.childType.kind != constructorOf(child) ||
                layout.childType.identity != atomicDomain(child))
              continue;
            auto scalar = runtime::RepresentedType::getChecked(
                emit, container.getContext(), child,
                llvm::StringRef(layout.childType.representation),
                ArrayRef<Type>{});
            if (!scalar)
              return {};
            selected = runtime::RepresentedType::getChecked(
                emit, container.getContext(), container,
                llvm::StringRef(entry.denseLayout->container),
                ArrayRef<Type>{scalar});
            if (selected)
              break;
          }
        }
      }
      auto represented = dyn_cast_or_null<runtime::RepresentedType>(selected);
      if (!represented || represented.getChildren().size() != 1 ||
          (entry.family != Family::Sequence &&
           (!entry.denseLayout ||
            represented.getRepresentation() != entry.denseLayout->container))) {
        (void)refuse("binding-representation",
                     "implementation requires its exact container layout");
        return {};
      }
      if (represented.getLogical() != container ||
          failed(verifyValueType(emit, selected))) {
        (void)refuse("binding-representation",
                     "complete container schema differs");
        return {};
      }
      element = represented.getChildren().front();
    }
    auto facets = protocol::operationContracts(contract);
    auto select = [&](Type value, bool output, unsigned index) -> Type {
      if (entry.family == Family::Observation && !output && facets &&
          facets->observation && index == facets->observation->payloadInput) {
        auto payload = familyLayout ? familyLayout
                       : actual     ? actual.getInput(index)
                                    : defaultPhysicalType(emit, value);
        if (!payload || logicalValueType(payload) != value ||
            failed(verifyValueType(emit, payload)) || !messageType(payload)) {
          (void)refuse("native-proof-wire-type",
                       "complete payload layout has no native message frame");
          return {};
        }
        return payload;
      }
      if (container) {
        if (value == container)
          return selected;
        bool elementPort =
            entry.family == Family::Sequence
                ? ((contract == "sequence.append" && !output && index == 1) ||
                   (contract == "sequence.at" && output && index == 0))
                : constructorOf(value) == "field";
        if (elementPort) {
          if (logicalValueType(element) == value)
            return element;
          (void)refuse("binding-representation", "element schema differs");
          return {};
        }
        if (entry.family != Family::Sequence &&
            constructorOf(value) == "vector")
          return runtime::RepresentedType::getChecked(
              emit, value.getContext(), value,
              llvm::StringRef(entry.denseLayout->vector), ArrayRef<Type>{});
      }
      return defaultPhysicalType(emit, value);
    };
    for (auto [ports, output] :
         {std::make_pair(&inputs, false), std::make_pair(&outputs, true)})
      for (auto [index, port] : enumerate(*ports)) {
        port = select(port, output, index);
        if (!port)
          return {};
      }
    // Overrides target exact atomic tuples. Indexed overrides cannot silently
    // miss; unindexed overrides replace all matching ports in either direction.
    for (const auto &rep : entry.representations) {
      auto replace = [&](Type &port) -> LogicalResult {
        auto logical = logicalValueType(port);
        auto application = applicationOf(logical);
        if (!application || application->constructor != rep.kind ||
            atomicDomain(logical) != rep.domain ||
            application->arguments.size() != 1)
          return refuse("binding-representation", "override tuple differs");
        port = runtime::RepresentedType::getChecked(
            emit, logical.getContext(), logical, llvm::StringRef(rep.identity),
            ArrayRef<Type>{});
        return success(bool(port));
      };
      if (rep.port) {
        auto &ports = rep.output ? outputs : inputs;
        if (*rep.port >= ports.size()) {
          (void)refuse("binding-representation", "override port is absent");
          return {};
        }
        if (failed(replace(ports[*rep.port])))
          return {};
      } else {
        for (auto *ports : {&inputs, &outputs})
          for (auto &port : *ports)
            if (constructorOf(logicalValueType(port)) == rep.kind &&
                atomicDomain(logicalValueType(port)) == rep.domain &&
                failed(replace(port)))
              return {};
      }
    }
    return physical ? FunctionType::get(logical.getContext(), inputs, outputs)
                    : logical;
  }
};
} // namespace

FailureOr<NativeBinding>
readNativeBinding(llvm::function_ref<InFlightDiagnostic()> emit, Operation *op,
                  std::optional<bool> physical) {
  return readNativeBinding(emit, op, physical,
                           protocol::installedImplementations());
}
namespace {
FailureOr<NativeBinding>
inspectNativeBindingSignature(llvm::function_ref<InFlightDiagnostic()> emit,
                              Operation *op,
                              std::optional<bool> requestedStage) {
  Installation check{emit};
  auto declaration = dyn_cast_or_null<runtime::BindingOp>(op);
  if (!declaration || !isa_and_nonnull<protocol_ir::ProtocolModuleOp, ModuleOp>(
                          op->getParentOp())) {
    (void)check.refuse("binding-declaration-context",
                       "expected module binding");
    return failure();
  }
  if (op->hasAttr("physical_arguments") || op->getNumOperands() ||
      op->getNumResults() || op->getNumRegions() || op->getNumSuccessors()) {
    (void)check.refuse("binding-declaration",
                       "expected a bodyless callable with physical choices "
                       "only in its represented ports");
    return failure();
  }
  auto name = declaration.getSymNameAttr();
  if (!name || name.getValue().empty() || name.getValue().size() > 256 ||
      !(llvm::isAlpha(name.getValue().front()) ||
        name.getValue().front() == '_') ||
      !all_of(name.getValue(), [](char c) {
        return llvm::isAlnum(c) || c == '_' || c == '.' || c == '-';
      })) {
    (void)check.refuse("binding-name", "invalid binding symbol");
    return failure();
  }
  auto actual = protocol::valueSignature(op);
  if (!actual || !declaration.getContractAttr() ||
      !declaration.getImplementationAttr() || !declaration.getArgumentsAttr()) {
    (void)check.refuse("binding-signature", "incomplete callable declaration");
    return failure();
  }
  for (StringRef key :
       {"sym_name", "contract", "arguments", "implementation", "function_type"})
    if (op->getAttr(key).getContext() != op->getContext()) {
      (void)check.refuse("binding-signature",
                         "declaration attributes cross MLIR contexts");
      return failure();
    }
  if (declaration.getFunctionType() != executableBindingSignature(actual)) {
    (void)check.refuse("binding-signature",
                       "scope and outcome must have the exact native ABI");
    return failure();
  }
  auto contract = declaration.getContract();
  auto arguments = declaration.getArguments().getValue();
  auto logical =
      resolveLogicalSignature(emit, op->getContext(), contract, arguments);
  if (!logical)
    return failure();
  if (actual.getNumInputs() != logical.getNumInputs() ||
      actual.getNumResults() != logical.getNumResults()) {
    (void)check.refuse("binding-signature", "callable value arity differs");
    return failure();
  }
  std::optional<bool> stage = requestedStage;
  if (auto root = dyn_cast<protocol_ir::ProtocolModuleOp>(op->getParentOp())) {
    if (!root.getProfileAttr()) {
      (void)check.refuse("binding-stage", "missing protocol profile");
      return failure();
    }
    bool enclosing = root.getProfile() == protocol_ir::Profile::Physical;
    if (stage && *stage != enclosing) {
      (void)check.refuse("binding-stage", "requested profile differs");
      return failure();
    }
    stage = enclosing;
  }
  for (auto [ports, schemas] :
       {std::make_pair(actual.getInputs(), logical.getInputs()),
        std::make_pair(actual.getResults(), logical.getResults())})
    for (auto [port, schema] : zip(ports, schemas)) {
      if (!port) {
        (void)check.refuse("binding-signature", "missing native value port");
        return failure();
      }
      bool represented = isa<runtime::RepresentedType>(port);
      if (stage && *stage != represented) {
        (void)check.refuse("binding-stage",
                           "value ports have a different stage");
        return failure();
      }
      stage = represented;
      if (failed(verifyValueType(emit, port)))
        return failure();
      if (logicalValueType(port) != schema) {
        (void)check.refuse("binding-signature", "exact logical port differs");
        return failure();
      }
    }
  bool physical = stage.value_or(false);
  auto implementation = declaration.getImplementation();
  if (physical && implementation.empty()) {
    (void)check.refuse("binding-stage",
                       "physical binding requires a selection");
    return failure();
  }
  if (failed(callAttributes(emit, op, actual.getNumInputs() + 1, 1)))
    return failure();
  return NativeBinding{declaration, logical, actual, physical};
}
} // namespace

FunctionType
readLogicalBindingSignature(llvm::function_ref<InFlightDiagnostic()> emit,
                            Operation *op) {
  auto inspected = inspectNativeBindingSignature(emit, op, false);
  return succeeded(inspected) ? inspected->logicalType : FunctionType{};
}

FailureOr<NativeBinding>
readNativeBinding(llvm::function_ref<InFlightDiagnostic()> emit, Operation *op,
                  std::optional<bool> requestedStage,
                  const protocol::ImplementationCatalog &catalog) {
  auto inspected = inspectNativeBindingSignature(emit, op, requestedStage);
  if (failed(inspected))
    return failure();
  auto declaration = inspected->declaration;
  auto arguments = declaration.getArguments().getValue();
  auto actual = inspected->valueType;
  bool physical = inspected->physical;
  NativeBindingApplication application{declaration.getContract().str(),
                                       {arguments.begin(), arguments.end()},
                                       declaration.getImplementation().str(),
                                       actual};
  auto expected = resolveInstalledSignature(emit, op->getContext(), application,
                                            physical, catalog);
  if (!expected)
    return failure();
  if (expected != actual) {
    (void)diagnostics::emit(
        emit(), "binding-signature",
        "actual complete layouts differ from the implementation");
    return failure();
  }
  return inspected;
}

FunctionType resolveInstalledSignature(
    llvm::function_ref<InFlightDiagnostic()> emit, MLIRContext *context,
    const NativeBindingApplication &application, bool physical,
    const protocol::ImplementationCatalog &catalog, Type familyLayout) {
  Installation check{emit};
  StringRef contract = application.contract,
            implementation = application.implementation;
  ArrayRef<Attribute> arguments = application.arguments;
  auto logical = resolveLogicalSignature(emit, context, contract, arguments);
  if (!logical)
    return {};
  auto actual = application.valueType;
  if (actual) {
    if (actual.getContext() != context ||
        actual.getNumInputs() != logical.getNumInputs() ||
        actual.getNumResults() != logical.getNumResults()) {
      (void)check.refuse("binding-signature",
                         "layout evidence has the wrong signature");
      return {};
    }
    for (auto [ports, schemas] :
         {std::make_pair(actual.getInputs(), logical.getInputs()),
          std::make_pair(actual.getResults(), logical.getResults())})
      for (auto [port, schema] : zip(ports, schemas)) {
        if (!port || port.getContext() != context ||
            failed(verifyValueType(emit, port)) ||
            isa<runtime::RepresentedType>(port) != physical ||
            logicalValueType(port) != schema) {
          (void)check.refuse("binding-signature",
                             "layout evidence differs from the logical port");
          return {};
        }
      }
  }
  if (physical && implementation.empty()) {
    (void)check.refuse("binding-stage",
                       "physical binding requires a selection");
    return {};
  }
  if (protocol::resourceUnitContract(contract)) {
    if (physical && !actual) {
      SmallVector<Type> inputs, outputs;
      for (auto [schemas, ports] :
           {std::make_pair(logical.getInputs(), &inputs),
            std::make_pair(logical.getResults(), &outputs)})
        for (Type schema : schemas) {
          auto port = defaultPhysicalType(emit, schema);
          if (!port)
            return {};
          ports->push_back(port);
        }
      actual = FunctionType::get(context, inputs, outputs);
    }
    if (!implementation.empty() &&
        implementation != ("logical/" + contract).str()) {
      (void)check.refuse("binding-implementation",
                         "unknown resource operation");
      return {};
    }
    return physical ? actual : logical;
  }
  if (contract == "representation.convert" || contract == "table.relayout") {
    if (!physical || !actual || actual.getNumInputs() != 1 ||
        actual.getNumResults() != 1 ||
        implementation != (contract == "table.relayout"
                               ? "arkworks/table.relayout"
                               : "native/representation.convert") ||
        actual.getInput(0) == actual.getResult(0)) {
      (void)check.refuse("binding-conversion", "invalid conversion selection");
      return {};
    }
    if (contract == "table.relayout")
      return physical ? actual : logical;
    auto schema = logical.getInput(0);
    StringRef kind = constructorOf(schema), domain = atomicDomain(schema),
              resident;
    if (kind == "field" || kind == "vector") {
      if (domain == "bls12-381.fr")
        resident = "blst/fr";
      if (domain == "bn254.fr")
        resident = "halo2curves-axiom/bn254.fr";
    } else if (kind == "group" || kind == "groups") {
      if (domain == "bls12-381.g1")
        resident = "blst/g1";
      if (domain == "bls12-381.g2")
        resident = "blst/g2";
      if (domain == "bn254.g1")
        resident = "halo2curves-axiom/bn254.g1";
      if (domain == "bn254.g2")
        resident = "halo2curves-axiom/bn254.g2";
    }
    auto ordinary = defaultPhysicalType(emit, schema);
    if (!ordinary)
      return {};
    Type from = actual.getInput(0), to = actual.getResult(0);
    if (resident.empty() ||
        !((from == ordinary &&
           cast<runtime::RepresentedType>(to).getRepresentation() ==
               resident) ||
          (to == ordinary &&
           cast<runtime::RepresentedType>(from).getRepresentation() ==
               resident))) {
      (void)check.refuse("binding-conversion",
                         "unsupported conversion endpoints");
      return {};
    }
    return physical ? actual : logical;
  }
  auto facets = protocol::operationContracts(contract);
  bool completePayload = false;
  const generic::Operation *operation = protocol::catalogOperation(contract);
  if (facets && facets->observation) {
    unsigned payload = facets->observation->payloadInput;
    completePayload = operation->signature.inputs[payload].term.has_value();
    if (completePayload && !messageType(logical.getInput(payload))) {
      (void)check.refuse("native-proof-wire-type",
                         "unsupported message schema");
      return {};
    }
  }
  if (implementation.empty())
    return physical ? actual : logical;
  const auto *descriptor = catalog.find(contract, implementation);
  if (!descriptor ||
      (completePayload && !descriptor->representations.empty())) {
    (void)check.refuse("binding-implementation",
                       "unknown or incompatible selection");
    return {};
  }
  auto terms = resolveBindingTerms(emit, context, contract, arguments);
  if (failed(terms) ||
      failed(check.provider(*descriptor, operation->signature.scope, *terms)))
    return {};
  return check.layouts(contract, *descriptor, logical, actual, physical,
                       familyLayout);
}

FailureOr<NativeBinding> lookupNativeBinding(Operation *user) {
  auto *root = SymbolTable::getNearestSymbolTable(user);
  auto reference = user->getAttrOfType<FlatSymbolRefAttr>("binding");
  if (!root || !reference) {
    diagnostics::emit(user->emitOpError(), "binding-reference",
                      "missing lexical binding reference");
    return failure();
  }
  return readNativeBinding([&] { return user->emitOpError(); },
                           SymbolTable::lookupSymbolIn(root, reference));
}

FunctionType executableBindingSignature(FunctionType values) {
  SmallVector<Type> inputs{runtime::ScopeType::get(values.getContext())};
  append_range(inputs, values.getInputs());
  auto outcome =
      exec::OutcomeType::get(values.getContext(), values.getResults());
  return FunctionType::get(values.getContext(), inputs, {outcome});
}
LogicalResult verifyCallAttributes(Operation *op, unsigned inputs,
                                   unsigned outputs) {
  return callAttributes([&] { return op->emitOpError(); }, op, inputs, outputs);
}
void runtime::BindingOp::build(OpBuilder &builder, OperationState &state,
                               StringRef name, StringRef contract,
                               ArrayAttr arguments, StringRef implementation) {
  state.addAttribute("sym_name", builder.getStringAttr(name));
  state.addAttribute("contract", builder.getStringAttr(contract));
  state.addAttribute("arguments", arguments);
  state.addAttribute("implementation", builder.getStringAttr(implementation));
  auto values = resolveLogicalSignature(
      [&] { return mlir::emitError(state.location); }, builder.getContext(),
      contract, arguments.getValue());
  if (values)
    state.addAttribute("function_type",
                       TypeAttr::get(executableBindingSignature(values)));
}
LogicalResult runtime::BindingOp::verify() {
  return success(succeeded(
      readNativeBinding([&] { return emitOpError(); }, getOperation())));
}
} // namespace zkc
