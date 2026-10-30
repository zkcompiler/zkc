#include "zkc/Dialect/Bindings.h"
#include "BindingTypeCache.h"
#include "mlir/IR/BuiltinDialect.h"
#include "mlir/IR/DialectInterface.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include <mutex>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {

namespace {
// Native types and the installed adapter set are immutable. Cache only a
// successful complete encode/parse/exact-native roundtrip, keyed by the actual
// type in its own context. Never cache source admission, mutable IR, failures,
// or context pointers in process-global storage. This interface owns no law.
class BindingTypeCache final : public DialectInterface::Base<BindingTypeCache> {
  std::mutex mutex;
  llvm::DenseMap<Type, BoundType> values;
  size_t bytes = 0;

public:
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(BindingTypeCache)
  explicit BindingTypeCache(Dialect *dialect) : Base(dialect) {}
  std::optional<BoundType> lookup(Type type) {
    std::lock_guard<std::mutex> lock(mutex);
    auto found = values.find(type);
    return found == values.end() ? std::nullopt
                                 : std::optional<BoundType>(found->second);
  }
  void remember(Type type, const BoundType &bound) {
    // Limit both entry count and retained serialized metadata. Clearing only
    // loses reuse; every miss executes the same complete checks below.
    constexpr size_t maxEntries = 4096, maxBytes = 4 * 1024 * 1024;
    size_t size = bound.spelling().size();
    if (size > maxBytes)
      return;
    std::lock_guard<std::mutex> lock(mutex);
    if (values.contains(type))
      return;
    if (values.size() == maxEntries || size > maxBytes - bytes) {
      values.clear();
      bytes = 0;
    }
    values.try_emplace(type, bound);
    bytes += size;
  }
};
BindingTypeCache *typeCache(Type type) {
  auto *builtin = type.getContext()->getLoadedDialect<BuiltinDialect>();
  return builtin ? builtin->getRegisteredInterface<BindingTypeCache>()
                 : nullptr;
}
} // namespace

void registerBindingTypeCache(DialectRegistry &registry) {
  registry.addExtension(+[](MLIRContext *, BuiltinDialect *builtin) {
    if (!builtin->getRegisteredInterface<BindingTypeCache>())
      builtin->addInterfaces<BindingTypeCache>();
  });
}

Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  if (!ctx)
    return {};
  auto checked = parseBoundType(t.spelling(), !t.representation.empty());
  if (!checked) {
    consumeError(checked.takeError());
    return {};
  }
  if (!(*checked == t))
    return {};
  const auto *adapter = type_adapters::findAdapter(t.kind);
  if (!adapter)
    return {};
  Type result = adapter->decode(ctx, t);
  if (!result)
    return {};
  if (t.representation.empty())
    return result;
  SmallVector<Type> children;
  if (t.physicalChildren)
    for (const auto &child : *t.physicalChildren) {
      auto decoded = decodeBoundType(ctx, child);
      if (!decoded)
        return {};
      children.push_back(decoded);
    }
  return type_adapters::loadedType<zkc::runtime::RepresentedType>(
      ctx, result, t.representation, children);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  if (!type)
    return error("binding-type");
  Type original = type;
  std::string rep;
  if (auto data = dyn_cast<zkc::runtime::RepresentedType>(type)) {
    if (!physical)
      return error("binding-physical-type-at-logical-stage");
    rep = data.getRepresentation().str();
    type = data.getLogical();
  } else if (physical)
    return error("binding-logical-type-at-physical-stage");
  auto *cache = typeCache(original);
  if (cache)
    if (auto found = cache->lookup(original))
      return *found;
  auto result = type_adapters::encodeLogicalType(type);
  if (!result)
    return result.takeError();
  if (physical) {
    std::vector<BoundType> children;
    for (auto child :
         cast<zkc::runtime::RepresentedType>(original).getChildren()) {
      auto encoded = encodeBoundType(child, true);
      if (!encoded)
        return encoded.takeError();
      children.push_back(std::move(*encoded));
    }
    result = physicalType(*result, rep, std::move(children));
    if (!result)
      return result.takeError();
  }
  auto checked = parseBoundType(result->spelling(), physical);
  if (!checked)
    return checked.takeError();
  // Compare the original carrier, including its exact physical wrapper.
  if (decodeBoundType(original.getContext(), *checked) != original)
    return error("binding-type-identity");
  if (cache)
    cache->remember(original, *checked);
  return checked;
}

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
      !isa<runtime::ScopeType>(type.getInput(0)) || type.getNumResults() != 1)
    return {};
  auto outcome = dyn_cast<exec::OutcomeType>(type.getResult(0));
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
  auto declaration = dyn_cast_or_null<runtime::BindingOp>(op);
  if (!declaration || !isa_and_nonnull<protocol_ir::ProtocolModuleOp, ModuleOp>(
                          op->getParentOp()))
    return error("binding-declaration-context");
  if (op->hasAttr("physical_arguments"))
    return error("binding-declaration");
  auto type = valueSignature(op);
  if (!type || !declaration.getSymNameAttr() ||
      !declaration.getContractAttr() || !declaration.getImplementationAttr())
    return error("binding-signature");
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
    if (auto attribute = op->getAttr(name)) {
      auto attributes = dyn_cast<ArrayAttr>(attribute);
      size_t count = name == "arg_attrs" ? type.getNumInputs() + 1 : 1;
      if (!attributes || attributes.size() != count ||
          any_of(attributes, [](Attribute value) {
            auto dictionary = dyn_cast<DictionaryAttr>(value);
            return !dictionary || !dictionary.empty();
          }))
        return error("binding-attributes");
    }
  std::optional<bool> stage;
  if (auto root = dyn_cast<protocol_ir::ProtocolModuleOp>(op->getParentOp()))
    stage = root.getProfileAttr() &&
            root.getProfile() == protocol_ir::Profile::Physical;
  for (TypeRange ports :
       {TypeRange(type.getInputs()), TypeRange(type.getResults())})
    for (Type port : ports) {
      bool represented = isa<runtime::RepresentedType>(port);
      if (stage && *stage != represented)
        return error("binding-stage");
      stage = represented;
    }
  bool physical = stage.value_or(false);
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
FunctionType executableBindingSignature(FunctionType values) {
  SmallVector<Type> inputs{runtime::ScopeType::get(values.getContext())};
  append_range(inputs, values.getInputs());
  auto outcome =
      exec::OutcomeType::get(values.getContext(), values.getResults());
  return FunctionType::get(values.getContext(), inputs, {outcome});
}
LogicalResult verifyCallAttributes(Operation *op, unsigned inputs,
                                   unsigned outputs) {
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
          op->emitOpError(), "binding-attributes",
          "argument/result dictionaries must match the actual executable ABI");
  }
  return success();
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
  auto refuse = [&](StringRef reason) {
    return diagnostics::emit(emitOpError(), "binding-signature", reason);
  };
  if ((*this)->hasAttr("physical_arguments"))
    return refuse("physical choices belong to actual represented ports");
  auto logical =
      resolveLogicalSignature([&] { return emitOpError(); }, getContext(),
                              getContract(), getArguments().getValue());
  if (!logical)
    return failure();
  auto actual = protocol::valueSignature(*this);
  if (!actual || actual.getNumInputs() != logical.getNumInputs() ||
      actual.getNumResults() != logical.getNumResults())
    return refuse("expected scope, exact value ports, and one outcome result");
  std::optional<bool> stage;
  for (auto [selected, expected] :
       {std::make_pair(actual.getInputs(), logical.getInputs()),
        std::make_pair(actual.getResults(), logical.getResults())})
    for (auto [port, value] : zip(selected, expected)) {
      auto represented = dyn_cast<runtime::RepresentedType>(port);
      if ((stage && *stage != bool(represented)) ||
          (represented ? represented.getLogical() : port) != value)
        return refuse(
            "actual value ports must have one stage and exact catalog erasure");
      stage = bool(represented);
    }
  if (protocol::authoringStage(getContract()) ==
          protocol::AuthoringStage::Physical &&
      !stage.value_or(false))
    return refuse("physical adapter cannot be declared with logical ports");
  if (auto root = dyn_cast_or_null<protocol_ir::ProtocolModuleOp>(
          (*this)->getParentOp()))
    if (stage && root.getProfileAttr() &&
        *stage != (root.getProfile() == protocol_ir::Profile::Physical))
      return refuse(
          "binding stage differs from the enclosing protocol profile");
  return verifyCallAttributes(*this, getFunctionType().getNumInputs(),
                              getFunctionType().getNumResults());
}
} // namespace zkc
