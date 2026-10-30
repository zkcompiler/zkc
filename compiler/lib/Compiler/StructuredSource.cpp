#include "zkc/Compiler/StructuredSource.h"
#include "ComponentContracts.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/AsmParser/AsmParserState.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SaveAndRestore.h"
#include "llvm/Support/SourceMgr.h"

using namespace llvm;
using namespace mlir;

namespace zkc::protocol {
namespace {
constexpr unsigned signatureLimit = 512;
constexpr unsigned instructionLimit = 4096;
constexpr unsigned depthLimit = 64;
constexpr uint64_t staticVisitLimit = 100000;
constexpr size_t effectiveSiteByteLimit = 4096;
constexpr uint64_t staticSiteByteLimit = 16 * 1024 * 1024;

/// Catalogue identities and random services a unit uses. Their rows are
/// exported with the unit, closed under associated members.
struct UsedIdentities {
  llvm::StringSet<> domains, services;
};

// This profile is deliberately smaller than the installed native catalogue.
// Catalogue resolution below still owns nominal arguments, full ordered ports,
// and parameters; membership alone never authorizes an execution.
bool primitiveContract(StringRef contract) {
  return llvm::is_contained(
      ArrayRef<StringRef>{"index.constant", "index.add", "index.sub",
                          "index.mul", "index.div", "index.mod", "index.equal",
                          "index.less", "vector.empty", "vector.length",
                          "vector.sum", "vector.split", "vector.append",
                          "vector.equal", "field.equal", "field.embed"},
      contract);
}

Expected<OperationBinding> primitiveBinding(Operation *op,
                                            UsedIdentities &used) {
  auto binding = readBinding(op);
  if (!binding)
    return binding.takeError();
  const auto &application = binding->application;
  if (!primitiveContract(application.contract) ||
      (StringRef(application.contract).starts_with("index.")
           ? !application.arguments.empty()
           : application.arguments.size() != 1 ||
                 installedDomains().identitySort(application.arguments[0]) !=
                     "Field"))
    return error("structured-source-binding");
  for (const auto &argument : application.arguments)
    used.domains.insert(argument);
  if (!application.implementation.empty())
    return error("structured-source-implementation");
  auto resolved = resolveLogicalBinding(application);
  if (!resolved)
    return resolved.takeError();
  return std::move(*binding);
}

Error attributes(Operation &op, ArrayRef<StringRef> allowed) {
  for (NamedAttribute attr : op.getAttrs()) {
    if (!llvm::is_contained(allowed, attr.getName().getValue()))
      return error("structured-source-attribute", attr.getName().getValue());
    // Protocol origin has a separate bounded tree validator; only its
    // template path can exceed the ordinary string limit.
    if (attr.getName() == "origin" && isa<protocol_ir::MathematicalOp>(op)) {
      auto origin = protocol_ir::readProtocolOrigin(attr.getValue());
      if (!origin)
        return origin.takeError();
      continue;
    }
    // This serialized declaration table has its own bounded, strict decoder
    // below. Its individual names still obey the ordinary string limit.
    if (attr.getName() == "source_declarations" &&
        isa<protocol_ir::ProtocolModuleOp>(op)) {
      auto text = dyn_cast<StringAttr>(attr.getValue());
      if (!text || !json::isUTF8(text.getValue()))
        return error("component-declaration");
      if (text.getValue().size() > 16 * 1024 * 1024)
        return error("structured-source-limit");
      continue;
    }
    bool valid = true, bounded = true;
    attr.getValue().walk([&](StringAttr string) {
      valid &= json::isUTF8(string.getValue());
      bounded &= string.getValue().size() <= 512;
    });
    // MLIR strings can contain arbitrary bytes. LLVM's JSON constructor
    // asserts or repairs invalid UTF-8; neither is a faithful source export.
    if (!valid)
      return error("structured-source-string");
    if (!bounded)
      return error("structured-source-limit");
  }
  return Error::success();
}

// Called only for the dialect-verified, bounded declaration contract layout.
json::Value contractValue(Attribute attr) {
  if (isa<UnitAttr>(attr))
    return nullptr;
  if (auto text = dyn_cast<StringAttr>(attr))
    return text.getValue();
  if (auto symbol = dyn_cast<FlatSymbolRefAttr>(attr))
    return symbol.getValue();
  if (auto index = dyn_cast<IntegerAttr>(attr))
    return index.getInt();
  json::Array values;
  for (Attribute value : cast<ArrayAttr>(attr))
    values.push_back(contractValue(value));
  return values;
}

// Field, vector and group sorts name catalogue identities admitted for those
// logical kinds; services name installed random services. The exported
// catalogue carries the rows of every identity used, so Lean resolves each
// sort against rows rather than against fixed spellings.
Expected<json::Value> encodeSort(Type type, UsedIdentities &used,
                                 unsigned depth);

// Keep the library identity and typed static arguments. Associated types are
// derived by each reader, rather than trusted from redundant exported fields.
Expected<json::Value> encodeOracleKind(protocol_ir::OracleKindAttr kind,
                                       UsedIdentities &used, unsigned depth) {
  if (depth >= depthLimit)
    return error("structured-source-limit");
  json::Array arguments;
  for (Attribute argument : kind.getArguments()) {
    if (auto type = dyn_cast<TypeAttr>(argument)) {
      auto encoded = encodeSort(type.getValue(), used, depth + 1);
      if (!encoded)
        return encoded.takeError();
      arguments.push_back(json::Array{"type", std::move(*encoded)});
    } else if (auto natural = dyn_cast<IntegerAttr>(argument);
               natural && natural.getType().isUnsignedInteger(64)) {
      arguments.push_back(json::Array{
          "nat", std::to_string(natural.getValue().getZExtValue())});
    } else {
      return error("structured-source-oracle-kind");
    }
  }
  return json::Array{kind.getIdentity(), std::move(arguments)};
}

json::Array oracleShapeValues(protocol_ir::OracleKindAttr kind,
                              DictionaryAttr values) {
  json::Array result;
  for (const auto &dimension : kind.getShapeDimensions())
    if (!dimension.extent)
      result.push_back(
          json::Array{dimension.name,
                      std::to_string(values.getAs<IntegerAttr>(dimension.name)
                                         .getValue()
                                         .getZExtValue())});
  return result;
}

Expected<json::Value> encodeSort(Type type, UsedIdentities &used,
                                 unsigned depth = 0) {
  if (depth >= depthLimit)
    return error("structured-source-type-depth");
  const auto &catalog = installedDomains();
  auto nominal = [&](StringRef kind, StringRef sort,
                     StringRef identity) -> Expected<json::Value> {
    if (catalog.identitySort(identity) != sort ||
        !catalog.admitsLogicalType(kind, identity))
      return error("structured-source-type");
    used.domains.insert(identity);
    return json::Array{kind, identity};
  };
  if (type.isSignlessInteger(1))
    return json::Array{"bool"};
  if (type.isUnsignedInteger(64))
    return json::Array{"index"};
  if (auto field = dyn_cast<algebra::FieldType>(type))
    return nominal("field", "Field", field.getDomain());
  if (auto vector = dyn_cast<algebra::FieldVectorType>(type))
    return nominal("vector", "Field", vector.getDomain());
  if (auto group = dyn_cast<algebra::GroupType>(type))
    return nominal("group", "Group", group.getDomain());
  if (auto groups = dyn_cast<algebra::GroupVectorType>(type))
    return nominal("groups", "Group", groups.getDomain());
  if (isa<algebra::IndicesType>(type))
    return json::Array{"indices"};
  if (auto handle = dyn_cast<protocol_ir::OracleHandleType>(type)) {
    auto encoded = encodeOracleKind(handle.getKind(), used, depth + 1);
    if (!encoded)
      return encoded.takeError();
    return json::Array{"oracle", std::move(*encoded)};
  }
  if (auto sequence = dyn_cast<protocol_ir::OracleSequenceType>(type)) {
    auto encoded = encodeOracleKind(sequence.getKind(), used, depth + 1);
    if (!encoded)
      return encoded.takeError();
    return json::Array{"oracle_sequence", std::move(*encoded),
                       std::to_string(sequence.getMaximum())};
  }
  if (auto sequence = dyn_cast<data::SequenceType>(type)) {
    auto element = encodeSort(sequence.getElementType(), used, depth + 1);
    if (!element)
      return element.takeError();
    return json::Array{"sequence", std::move(*element)};
  }
  if (auto product = dyn_cast<data::VariantType>(type)) {
    if (product.getAlternatives().size() != 1)
      return error("structured-source-product");
    auto constructor = product.getAlternatives().front();
    std::string identity =
        printJson(data::exportVariantIdentity(product.getIdentity()));
    auto label = constructor.getLabel().getValue();
    if (identity.size() > 512 || label.size() > 512 ||
        constructor.getPayload().size() > signatureLimit)
      return error("structured-source-limit");
    json::Array fields;
    for (auto type : constructor.getPayload()) {
      auto component = encodeSort(type, used, depth + 1);
      if (!component)
        return component.takeError();
      fields.push_back(std::move(*component));
    }
    return json::Array{"product", std::move(identity), label,
                       std::move(fields)};
  }
  if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type)) {
    if (depth)
      return error("structured-source-service");
    StringRef sampled = randomServiceField(service.getContract());
    if (sampled.empty())
      return error("structured-source-type");
    used.services.insert(service.getContract());
    used.domains.insert(sampled);
    return json::Array{"service", service.getContract()};
  }
  return error("structured-source-type");
}

Expected<json::Array> encodeSorts(TypeRange types, UsedIdentities &used,
                                  bool services = false) {
  if (types.size() > signatureLimit)
    return error("structured-source-limit");
  json::Array result;
  for (Type type : types) {
    if (!services && isa<protocol_ir::ServiceReferenceType>(type))
      return error("structured-source-service");
    auto encoded = encodeSort(type, used);
    if (!encoded)
      return encoded.takeError();
    result.push_back(std::move(*encoded));
  }
  return result;
}

// Rows of the used identities, closed under associated members, in catalogue
// order: ["nominal", identity, sort, [[member, identity]...], [capability...],
// modulus or null]. Services: ["service", contract, sampled field,
// [method...]], with "index" exactly where the sampled field has
// IndexRandomness.
Error collectStaticDomains(const json::Value &term, UsedIdentities &used) {
  // The shared origin reader has already checked shape and traversal limits.
  const auto &tree = *term.getAsArray();
  auto tag = *tree[0].getAsString();
  if (tag == "field" || tag == "group" || tag == "domain") {
    auto identity = *tree[tag == "domain" ? 2 : 1].getAsString();
    auto sort = tag == "domain"  ? *tree[1].getAsString()
                : tag == "field" ? StringRef("Field")
                                 : StringRef("Group");
    if (installedDomains().identitySort(identity) != sort)
      return error("structured-source-static-domain");
    used.domains.insert(identity);
  }
  if (tag == "array")
    return collectStaticDomains(tree[1], used);
  if (tag == "tuple" || tag == "nominal" || tag == "builtin" ||
      tag == "formal") {
    auto index = tag == "tuple" ? 1 : tag == "nominal" ? 3 : 2;
    for (const auto &argument : *tree[index].getAsArray())
      if (auto e = collectStaticDomains(argument, used))
        return e;
  }
  return Error::success();
}
json::Value catalogueSlot(const UsedIdentities &used) {
  const auto &catalog = installedDomains();
  llvm::StringSet<> closure;
  SmallVector<std::string> pending;
  for (const auto &identity : used.domains)
    pending.push_back(identity.getKey().str());
  while (!pending.empty()) {
    std::string identity = pending.pop_back_val();
    if (!closure.insert(identity).second)
      continue;
    if (const auto *domain = catalog.domain(identity))
      for (const auto &member : domain->associated)
        pending.push_back(member.identity);
  }
  json::Array nominals, services;
  for (const auto &domain : catalog.allDomains()) {
    if (!closure.contains(domain.identity))
      continue;
    json::Array members, capabilities;
    for (const auto &member : domain.associated)
      members.push_back(json::Array{member.member, member.identity});
    for (const auto &capability : domain.capabilities)
      capabilities.push_back(capability);
    nominals.push_back(json::Array{"nominal", domain.identity, domain.sort,
                                   std::move(members), std::move(capabilities),
                                   domain.modulus.empty()
                                       ? json::Value(nullptr)
                                       : json::Value(domain.modulus)});
  }
  for (const auto &service : randomServices) {
    if (!used.services.contains(service.contract))
      continue;
    json::Array methods{"draw"};
    if (serviceMethod(service.contract, "index"))
      methods.push_back("index");
    services.push_back(json::Array{"service", service.contract, service.field,
                                   std::move(methods)});
  }
  return json::Array{std::move(nominals), std::move(services)};
}

// Count lexical JSON arrays, rather than only native region nesting. A native
// region contributes several wire arrays. Strings are checked as UTF-8 bytes.
bool boundedWire(const json::Value &value, unsigned depth = 0) {
  if (auto string = value.getAsString())
    return string->size() <= 512;
  if (auto array = value.getAsArray()) {
    if (++depth > depthLimit)
      return false;
    return llvm::all_of(*array, [&](const json::Value &child) {
      return boundedWire(child, depth);
    });
  }
  return true;
}

// The protocol origin slot has its own typed tree budget and a longer template
// path. Keep every other slot under the ordinary lexical wire bounds.
bool boundedSourceWire(const json::Value &source) {
  const auto &slots = *source.getAsArray();
  for (unsigned slot = 0; slot < slots.size(); ++slot) {
    if (slot != 7) {
      if (!boundedWire(slots[slot], 1))
        return false;
      continue;
    }
    for (const auto &definition : *slots[slot].getAsArray()) {
      const auto &row = *definition.getAsArray();
      if (row.size() != 10 || row[0].getAsString() != "function" ||
          row[2].getAsString() != "protocol") {
        if (!boundedWire(definition, 2))
          return false;
        continue;
      }
      for (unsigned field = 0; field < row.size(); ++field)
        if (field != 8 && !boundedWire(row[field], 3))
          return false;
    }
  }
  return true;
}

FunctionType signature(Operation &op) {
  auto attr = op.getAttrOfType<TypeAttr>("function_type");
  auto type = attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
  if (auto function = dyn_cast<func::FuncOp>(op);
      function && isScopedExecutionFunction(function)) {
    if (!type || type.getNumInputs() == 0 || type.getNumResults() != 1)
      return {};
    auto outcome = dyn_cast<exec::OutcomeType>(type.getResult(0));
    if (!outcome || !isa<runtime::ScopeType>(type.getInput(0)))
      return {};
    return FunctionType::get(op.getContext(), type.getInputs().drop_front(),
                             outcome.getPayload());
  }
  return type;
}

StringRef kind(Operation &op) {
  if (isa<protocol_ir::MathematicalOp>(op))
    return "protocol";
  if (auto function = dyn_cast<func::FuncOp>(op))
    return isScopedExecutionFunction(function) ? "local" : "math";
  if (isa<data::DomainOp>(op))
    return "domain";
  if (isa<protocol_ir::OracleDefinitionOp>(op))
    return "oracle";
  return "";
}

Expected<StringRef> visibility(Operation &op) {
  auto attr = op.getAttrOfType<StringAttr>("sym_visibility");
  if (!attr)
    return StringRef("public");
  if (attr.getValue() != "public" && attr.getValue() != "private")
    return error("structured-source-visibility");
  return attr.getValue();
}

using RowPath = SmallVector<unsigned, 8>;
RowPath child(ArrayRef<unsigned> parent,
              std::initializer_list<unsigned> suffix) {
  RowPath result(parent);
  llvm::append_range(result, suffix);
  return result;
}

class Exporter {
  protocol_ir::ProtocolModuleOp unit;
  protocol_ir::MathematicalOp selected;
  SymbolTable symbols;
  ArrayAttr roles;
  Operation *definition = nullptr;
  llvm::StringSet<> sites;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> dependencies;
  unsigned instructions = 0;
  UsedIdentities used;
  SourceExecutionClosure execution;
  // Private declaration identities belong to this wire format, never native
  // admission. Multiple actual compute occurrences can name one declaration.
  std::vector<std::pair<std::string, Operation *>> computationOrigins;
  llvm::DenseMap<Operation *, std::string> computationNames;
  const AsmParserState &parser;
  const SourceMgr &sourceManager;
  std::vector<StructuredSourceAssociation> &associations;
  uint64_t associationBytes = 0;

  Error associate(ArrayRef<unsigned> row, Operation &op,
                  StructuredSourceDerivation derivation =
                      StructuredSourceDerivation::Direct) {
    // Bound retained storage before copying paths or operation names. Reused
    // closed regions have distinct emitted coordinates and spend work again.
    uint64_t size = sizeof(StructuredSourceAssociation) +
                    row.size() * sizeof(unsigned) +
                    op.getName().getStringRef().size();
    constexpr uint64_t limit = 16 * 1024 * 1024;
    if (size > limit - associationBytes)
      return error("structured-source-limit");
    associationBytes += size;
    std::optional<StructuredSourceTextRange> original;
    if (const auto *written = parser.getOpDef(&op)) {
      auto buffer =
          sourceManager.getMemoryBuffer(sourceManager.getMainFileID());
      const char *begin = buffer->getBufferStart();
      auto [line, column] = sourceManager.getLineAndColumn(written->loc.Start);
      original = StructuredSourceTextRange{
          unsigned(written->loc.Start.getPointer() - begin),
          unsigned(written->loc.End.getPointer() - begin), line, column};
    }
    associations.push_back({std::vector<unsigned>(row.begin(), row.end()),
                            op.getName().getStringRef().str(), derivation,
                            original});
    return Error::success();
  }

  Expected<json::Value> sort(Type type) { return encodeSort(type, used); }
  Expected<json::Array> sorts(TypeRange types, bool services = false) {
    return encodeSorts(types, used, services);
  }

  Expected<StringRef> reference(Operation &op, StringRef attribute,
                                ArrayRef<StringRef> allowedKinds,
                                bool optional = false) {
    if (optional && !op.hasAttr(attribute))
      return StringRef("");
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>(attribute);
    Operation *callee = ref ? symbols.lookup(ref.getValue()) : nullptr;
    if (!callee || callee == selected.getOperation() ||
        !llvm::is_contained(allowedKinds, kind(*callee)))
      return error("structured-source-reference");
    dependencies[definition].push_back(callee);
    return ref.getValue();
  }

  Expected<StringRef> site(Operation &op) {
    auto attr = op.getAttrOfType<StringAttr>(
        isa<func::CallOp>(op) ? "runtime.site" : "site");
    if (!attr || attr.getValue().empty() ||
        !sites.insert(attr.getValue()).second)
      return error("structured-source-site");
    return attr.getValue();
  }

  bool hasRole(StringRef role) const {
    return roles &&
           llvm::is_contained(roles, StringAttr::get(roles.getContext(), role));
  }

  json::Array names(ArrayAttr values) {
    json::Array result;
    for (Attribute value : values)
      result.push_back(cast<StringAttr>(value).getValue());
    return result;
  }

  Expected<json::Array> interface(protocol_ir::MathematicalOp function) {
    roles = function.getRoles();
    // Native verification owns uniqueness, nonempty scopes and port shape.
    if (roles.empty() || roles.size() > 16)
      return error("structured-source-role");
    json::Array inputs, outputs;
    for (Attribute scope : function.getInputRoles())
      inputs.push_back(names(cast<ArrayAttr>(scope)));
    for (Attribute scope : function.getOutputRoles())
      outputs.push_back(names(cast<ArrayAttr>(scope)));
    return json::Array{"protocol", names(roles), std::move(inputs),
                       std::move(outputs)};
  }

  Expected<json::Array> fold(Operation &op) {
    auto domain = reference(op, "domain", {"domain"});
    if (!domain)
      return domain.takeError();
    StringRef helperKind =
        isa<exec::FoldOp, exec::CollectOp>(op) ? "local" : "math";
    auto step =
        reference(op, isa<exec::CollectOp>(op) ? "body" : "step", {helperKind});
    if (!step)
      return step.takeError();
    auto predicate = reference(op, "predicate", {helperKind}, true);
    if (!predicate)
      return predicate.takeError();
    return json::Array{*domain, *step, *predicate};
  }

  Error indexComputations() {
    SymbolTableCollection tables;
    llvm::DenseMap<Operation *, std::string> helpers;
    unsigned next = 0;
    for (Operation *op : execution.computations) {
      auto call = dyn_cast<exec::ComputeOp>(op);
      Operation *helper =
          call ? call.resolveCallee(tables).getOperation() : nullptr;
      if (helper) {
        auto found = helpers.find(helper);
        if (found != helpers.end()) {
          computationNames.try_emplace(op, found->second);
          continue;
        }
      }
      std::string name;
      do {
        if (next == 4096)
          return error("structured-source-limit",
                       "private computation identities");
        name = (call ? "_mathematical_admission_" : "_finite_admission_") +
               std::to_string(next++);
      } while (symbols.lookup(name));
      if (helper)
        helpers.try_emplace(helper, name);
      computationNames.try_emplace(op, name);
      computationOrigins.emplace_back(std::move(name), op);
    }
    return Error::success();
  }
  Expected<StringRef> computationName(Operation &op) {
    auto found = computationNames.find(&op);
    if (found != computationNames.end())
      return StringRef(found->second);
    return error("structured-source-reference", "unassociated computation");
  }

  Expected<json::Value> scopedDescriptor(const SourceExecutionStep &step) {
    Operation &op = *step.operation;
    if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
      auto binding = primitiveBinding(symbols.lookup(apply.getBinding()), used);
      if (!binding)
        return binding.takeError();
      auto parameters = encodeInvocationParameters(apply);
      if (!parameters)
        return parameters.takeError();
      json::Array encoded;
      for (const auto &parameter : *parameters)
        encoded.push_back(parameter);
      return json::Array{"exec", apply->getName().getStringRef(), binding->name,
                         std::move(encoded)};
    }
    if (auto boolean = dyn_cast<exec::BooleanOp>(op))
      return json::Array{"bool.constant", boolean.getValue()};
    if (isa<func::CallOp>(op)) {
      auto target = reference(op, "callee", {"local"});
      if (!target)
        return target.takeError();
      return json::Array{"apply", target->str()};
    }
    if (isa<exec::ComputeOp, exec::FoldOp, exec::CollectOp>(op)) {
      // The exported apply names a derived declaration, whose own references
      // add an edge. Count that emitted graph, not just native direct calls.
      dependencies[definition].push_back(&op);
      SaveAndRestore<Operation *> derivedOwner(definition, &op);
      if (isa<exec::ComputeOp>(op)) {
        auto helper = reference(op, "callee", {"math"});
        if (!helper)
          return helper.takeError();
      } else {
        auto callbacks = fold(op);
        if (!callbacks)
          return callbacks.takeError();
      }
      auto target = computationName(op);
      if (!target)
        return target.takeError();
      // This key belongs to the transient view, not the MLIR context. The JSON
      // result outlives this Exporter and must own its bytes.
      return json::Array{"apply", target->str()};
    }
    if (isa<exec::TestOp>(op))
      return json::Array{"if"};
    if (isa<exec::RangeOp>(op))
      return json::Array{step.conditional ? "for_condition" : "for"};
    return error("structured-source-operation", op.getName().getStringRef());
  }

  // The CFG reader checks all scope acquisition, failure propagation, transfer
  // cleanup and branch edges. Export its checked association using the actual
  // SSA formals, not Program value names (which may identify aliased captures).
  Expected<json::Value> scopedBlock(func::FuncOp function,
                                    ArrayRef<unsigned> path,
                                    StringRef terminator,
                                    unsigned forwarded = 0,
                                    unsigned depth = 0) {
    if (depth > depthLimit)
      return error("structured-source-limit");
    auto found = execution.bodies.find(function.getSymName().str());
    if (found == execution.bodies.end() || found->second.empty())
      return error("structured-source-region");
    auto arguments = function.getArguments().drop_front();
    if (arguments.size() > signatureLimit || forwarded > arguments.size())
      return error("structured-source-limit");
    llvm::DenseMap<Value, unsigned> refs;
    for (auto [i, argument] : llvm::enumerate(arguments))
      refs[argument] = i;
    auto indices = [&](ValueRange values) -> Expected<json::Array> {
      json::Array result;
      for (Value value : values) {
        auto ref = refs.find(value);
        if (ref == refs.end())
          return error("structured-source-reference");
        if (ref->second > instructionLimit)
          return error("structured-source-limit");
        result.push_back(ref->second);
      }
      return result;
    };
    json::Array encoded;
    for (const SourceExecutionStep &step : found->second) {
      Operation &op = *step.operation;
      // Formation has checked the allowed attribute names. Apply the wire's
      // UTF-8 and size bounds to every actual attribute, including locations
      // represented by runtime.site and private computation references.
      SmallVector<StringRef> checkedAttributes;
      for (NamedAttribute attr : op.getAttrs())
        checkedAttributes.push_back(attr.getName().getValue());
      if (auto e = attributes(op, checkedAttributes))
        return std::move(e);
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        SmallVector<Value> values(step.inputs);
        // Scoped loops retain invariant captures in their parent. The formal
        // closed-region signature expresses that same transport explicitly.
        llvm::append_range(values, arguments.take_back(forwarded));
        auto result = indices(values);
        if (!result)
          return result.takeError();
        if (auto e = associate(child(path, {2}), op,
                               StructuredSourceDerivation::ScopedExecution))
          return std::move(e);
        return json::Array{"block", std::move(encoded),
                           json::Array{terminator, std::move(*result)}};
      }
      if (auto stop = dyn_cast<exec::RejectOp>(op)) {
        auto occurrence = site(op);
        if (!occurrence)
          return occurrence.takeError();
        if (auto e = associate(child(path, {2}), op,
                               StructuredSourceDerivation::ScopedExecution))
          return std::move(e);
        return json::Array{"block", std::move(encoded),
                           json::Array{"stop", stop.getReason(), *occurrence}};
      }
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto args = indices(step.inputs);
      if (!args)
        return args.takeError();
      auto inputs = sorts(ValueRange(step.inputs).getTypes());
      if (!inputs)
        return inputs.takeError();
      auto results = sorts(ValueRange(step.outputs).getTypes());
      if (!results)
        return results.takeError();
      auto desc = scopedDescriptor(step);
      if (!desc)
        return desc.takeError();
      auto occurrence = site(op);
      if (!occurrence)
        return occurrence.takeError();
      json::Array regions;
      auto row = child(path, {1, unsigned(encoded.size())});
      if (auto e =
              associate(row, op, StructuredSourceDerivation::ScopedExecution))
        return std::move(e);
      for (auto nested : step.regions) {
        auto regionPath = child(row, {3, unsigned(regions.size())});
        if (auto e = associate(regionPath, *nested,
                               StructuredSourceDerivation::ScopedExecution))
          return std::move(e);
        bool loop = isa<exec::RangeOp>(op);
        unsigned captures =
            loop ? step.inputs.size() - 2 - step.outputs.size() : 0;
        SmallVector<Type> outputs(signature(*nested).getResults());
        auto captureTypes = nested.getArgumentTypes().take_back(captures);
        llvm::append_range(outputs, captureTypes);
        auto in = sorts(nested.getArgumentTypes().drop_front());
        if (!in)
          return in.takeError();
        auto out = sorts(outputs);
        if (!out)
          return out.takeError();
        auto content = scopedBlock(nested, child(regionPath, {2}),
                                   step.conditional ? "condition" : "yield",
                                   captures, depth + 1);
        if (!content)
          return content.takeError();
        regions.push_back(
            json::Array{std::move(*in), std::move(*out), std::move(*content)});
      }
      encoded.push_back(json::Array{std::move(*desc), std::move(*args),
                                    std::move(*results), std::move(regions),
                                    *occurrence});
      for (auto &entry : refs)
        entry.second += step.outputs.size();
      for (auto [i, result] : llvm::enumerate(step.outputs))
        refs[result] = i;
    }
    return error("structured-source-region");
  }

  Expected<json::Value> descriptor(Operation &op, StringRef owner) {
    // Each branch checks exactly the attributes represented by its descriptor.
    // Inherent attributes and discardable attributes share this whitelist.
    auto field = [&]() {
      return cast<algebra::FieldType>(op.getOperand(0).getType()).getDomain();
    };
    if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
      // Native formation already checked nested active rosters and state
      // scopes.
      if (auto e = attributes(
              op, {"site", "carried", "maximum", "roles", "carried_roles"}))
        return std::move(e);
      if (owner != "protocol")
        return error("structured-source-operation");
      json::Array scopes;
      for (Attribute scope : repeat.getCarriedRoles())
        scopes.push_back(names(cast<ArrayAttr>(scope)));
      return json::Array{"protocol_repeat", repeat.getCarried(),
                         repeat.getMaximum(), names(repeat.getRoles()),
                         std::move(scopes)};
    }
    if (auto application = dyn_cast<protocol_ir::ApplyOp>(op)) {
      if (auto e = attributes(op, {"callee", "roles", "site"}))
        return std::move(e);
      auto callee =
          symbols.lookup<protocol_ir::MathematicalOp>(application.getCallee());
      if (owner != "protocol" || !callee || op.getNumRegions())
        return error("structured-source-reference");
      auto type = callee.getFunctionType();
      if (op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults() ||
          application.getRoles().size() != callee.getRoles().size())
        return error("structured-source-application");
      llvm::StringSet<> mapped;
      for (Attribute role : application.getRoles()) {
        auto name = cast<StringAttr>(role).getValue();
        if (!hasRole(name) || !mapped.insert(name).second)
          return error("structured-source-application");
      }
      if (!callee.getBody().front().getOps<protocol_ir::StatementOp>().empty())
        return error("structured-source-application");
      // Selection is an observation root, not a helper kind. A different,
      // acyclic protocol may invoke the selected statement-free protocol.
      dependencies[definition].push_back(callee);
      return json::Array{"protocol_apply", application.getCallee(),
                         names(application.getRoles())};
    }
    if (isa<data::IndexOp, data::EqualOp, data::LessOp, data::PowerOfTwoOp>(
            op)) {
      bool constant = isa<data::IndexOp>(op);
      if (owner != "protocol" && owner != "math" && owner != "oracle")
        return error("structured-source-operation");
      if (auto e = attributes(op, constant ? ArrayRef<StringRef>{"value"}
                                           : ArrayRef<StringRef>{}))
        return std::move(e);
      if (constant)
        return json::Array{"index.constant",
                           std::to_string(cast<data::IndexOp>(op).getValue())};
      return json::Array{isa<data::EqualOp>(op)  ? "index.equal"
                         : isa<data::LessOp>(op) ? "index.less"
                                                 : "index.power_of_two"};
    }
    if (auto restrict = dyn_cast<algebra::MultilinearRestrictPrefixOp>(op)) {
      if (owner != "protocol" && owner != "math" && owner != "oracle")
        return error("structured-source-operation");
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto domain = restrict.getResult().getType().getDomain();
      used.domains.insert(domain);
      return json::Array{"multilinear.restrict_prefix", domain};
    }
    if (auto dim = dyn_cast<data::DimOp>(op)) {
      if ((owner != "protocol" && owner != "math" && owner != "oracle") ||
          dim.getAxis() != 0 ||
          !isa<algebra::FieldVectorType>(dim.getInput().getType()))
        return error("structured-source-operation");
      if (auto e = attributes(op, {"axis"}))
        return std::move(e);
      auto domain =
          cast<algebra::FieldVectorType>(dim.getInput().getType()).getDomain();
      used.domains.insert(domain);
      return json::Array{"vector.length", domain};
    }
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      auto literal = algebra::encodeFieldLiteral(constant.getValue());
      if (!literal)
        return literal.takeError();
      return json::Array{"field.constant",
                         constant.getResult().getType().getDomain(),
                         std::move(*literal)};
    }
    StringRef fieldOpcode;
    if (isa<algebra::FieldAddOp>(op))
      fieldOpcode = "field.add";
    else if (isa<algebra::SubtractFieldOp>(op))
      fieldOpcode = "field.subtract";
    else if (isa<algebra::FieldMultiplyOp>(op))
      fieldOpcode = "field.multiply";
    else if (isa<algebra::FieldEqualOp>(op))
      fieldOpcode = "field.equal";
    if (!fieldOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      return json::Array{fieldOpcode, field()};
    }
    if (isa<algebra::GroupIdentityOp, algebra::GroupAddOp,
            algebra::GroupScaleOp, algebra::GroupEqualOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      bool identity = isa<algebra::GroupIdentityOp>(op);
      auto group = cast<algebra::GroupType>(
          identity ? op.getResult(0).getType() : op.getOperand(0).getType());
      StringRef opcode = identity                         ? "group.identity"
                         : isa<algebra::GroupAddOp>(op)   ? "group.add"
                         : isa<algebra::GroupEqualOp>(op) ? "group.equal"
                                                          : "group.scale";
      json::Array result{opcode, group.getDomain()};
      if (isa<algebra::GroupScaleOp>(op))
        result.push_back(
            cast<algebra::FieldType>(op.getOperand(1).getType()).getDomain());
      return result;
    }
    if (isa<protocol_ir::OracleSendOp, protocol_ir::OracleInputOp,
            protocol_ir::OracleComponentsOp, protocol_ir::OracleVirtualOp>(
            op)) {
      bool send = isa<protocol_ir::OracleSendOp>(op);
      bool input = isa<protocol_ir::OracleInputOp>(op);
      bool components = isa<protocol_ir::OracleComponentsOp>(op);
      bool virtualHandle = isa<protocol_ir::OracleVirtualOp>(op);
      if (owner != "protocol")
        return error("structured-source-operation");
      SmallVector<StringRef> allowed{send ? "sender" : "holder", "receivers"};
      if (send)
        allowed.push_back("site");
      if (send)
        allowed.push_back("shape_names");
      if (send || input)
        allowed.push_back("shape_bounds");
      if (virtualHandle)
        allowed.push_back("callee");
      if (auto e = attributes(op, allowed))
        return std::move(e);
      auto handle = cast<protocol_ir::OracleHandleType>(
          components ? op.getOperand(0).getType() : op.getResult(0).getType());
      auto encoded = encodeOracleKind(handle.getKind(), used, 0);
      if (!encoded)
        return encoded.takeError();
      json::Array descriptor{send         ? "oracle_send"
                             : input      ? "oracle_input"
                             : components ? "oracle_components"
                                          : "oracle_virtual"};
      if (virtualHandle) {
        auto callee = reference(op, "callee", {"oracle"});
        if (!callee)
          return callee.takeError();
        descriptor.push_back(*callee);
      }
      descriptor.push_back(
          op.getAttrOfType<StringAttr>(send ? "sender" : "holder").getValue());
      descriptor.push_back(names(op.getAttrOfType<ArrayAttr>("receivers")));
      descriptor.push_back(std::move(*encoded));
      if (send)
        descriptor.push_back(names(op.getAttrOfType<ArrayAttr>("shape_names")));
      if (send || input)
        descriptor.push_back(oracleShapeValues(
            handle.getKind(),
            op.getAttrOfType<DictionaryAttr>("shape_bounds")));
      return descriptor;
    }
    if (isa<protocol_ir::OracleQueryOp, protocol_ir::OracleContentsOp,
            protocol_ir::OracleShapeOp, protocol_ir::OracleForgetShapeOp>(op)) {
      bool query = isa<protocol_ir::OracleQueryOp>(op);
      bool contents = isa<protocol_ir::OracleContentsOp>(op);
      bool forget = isa<protocol_ir::OracleForgetShapeOp>(op);
      if (owner != "protocol" && !(owner == "oracle" && query))
        return error("structured-source-operation");
      if (auto e = attributes(op, query ? ArrayRef<StringRef>{"owner", "site"}
                                  : contents ? ArrayRef<StringRef>{"owner"}
                                  : forget ? ArrayRef<StringRef>{}
                                           : ArrayRef<StringRef>{"dimension"}))
        return std::move(e);
      auto handle =
          cast<protocol_ir::OracleHandleType>(op.getOperand(0).getType());
      auto encoded = encodeOracleKind(handle.getKind(), used, 0);
      if (!encoded)
        return encoded.takeError();
      json::Array descriptor{query      ? "oracle_query"
                             : contents ? "oracle_contents"
                             : forget   ? "oracle_forget_shape"
                                        : "oracle_shape"};
      if (query || contents) {
        auto role = op.getAttrOfType<StringAttr>("owner");
        descriptor.push_back(role ? json::Value(role.getValue())
                                  : json::Value(nullptr));
      }
      descriptor.push_back(std::move(*encoded));
      if (!query && !contents && !forget)
        descriptor.push_back(
            op.getAttrOfType<StringAttr>("dimension").getValue());
      if (forget) {
        auto target = encodeOracleKind(
            cast<protocol_ir::OracleHandleType>(op.getResult(0).getType())
                .getKind(),
            used, 0);
        if (!target)
          return target.takeError();
        descriptor.push_back(std::move(*target));
      }
      return descriptor;
    }
    if (isa<protocol_ir::OracleSequenceEmptyOp,
            protocol_ir::OracleSequenceAppendOp,
            protocol_ir::OracleSequenceAtOp,
            protocol_ir::OracleSequenceLengthOp>(op)) {
      bool empty = isa<protocol_ir::OracleSequenceEmptyOp>(op);
      bool append = isa<protocol_ir::OracleSequenceAppendOp>(op);
      bool at = isa<protocol_ir::OracleSequenceAtOp>(op);
      if (owner != "protocol")
        return error("structured-source-operation");
      if (auto e =
              attributes(op, append || at ? ArrayRef<StringRef>{"roles", "site"}
                                          : ArrayRef<StringRef>{}))
        return std::move(e);
      auto sequence = cast<protocol_ir::OracleSequenceType>(
          empty ? op.getResult(0).getType() : op.getOperand(0).getType());
      auto encoded = encodeOracleKind(sequence.getKind(), used, 0);
      if (!encoded)
        return encoded.takeError();
      json::Array descriptor{empty    ? "oracle_sequence_empty"
                             : append ? "oracle_sequence_append"
                             : at     ? "oracle_sequence_at"
                                      : "oracle_sequence_length",
                             std::move(*encoded),
                             std::to_string(sequence.getMaximum())};
      if (append || at)
        descriptor.push_back(names(op.getAttrOfType<ArrayAttr>("roles")));
      return descriptor;
    }
    if (auto assembly = dyn_cast<protocol_ir::AssembleRolesOp>(op)) {
      if (auto e = attributes(op, {"roles"}))
        return std::move(e);
      return json::Array{"assemble", names(assembly.getRoles())};
    }
    if (auto restrict = dyn_cast<protocol_ir::RestrictRolesOp>(op)) {
      if (auto e = attributes(op, {"roles"}))
        return std::move(e);
      return json::Array{"restrict", names(restrict.getRoles())};
    }
    if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
      if (auto e = attributes(op, {"sender", "receiver", "site"}))
        return std::move(e);
      return json::Array{"exchange", exchange.getSender(),
                         exchange.getReceiver()};
    }
    if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
      if (auto e = attributes(op, {"owner", "method", "site"}))
        return std::move(e);
      auto result = dyn_cast<algebra::FieldType>(op.getResult(0).getType());
      auto service = op.getNumOperands() == 1
                         ? dyn_cast<protocol_ir::ServiceReferenceType>(
                               op.getOperand(0).getType())
                         : protocol_ir::ServiceReferenceType();
      if (query.getMethod() != "draw" || !service || !result ||
          result.getDomain() != randomServiceField(service.getContract()))
        return error("structured-source-service");
      return json::Array{"draw", query.getOwner(), result.getDomain()};
    }
    if (auto statement = dyn_cast<protocol_ir::StatementOp>(op)) {
      if (auto e =
              attributes(op, {"relation", "selectors", "acceptance", "target"}))
        return std::move(e);
      return json::Array{"statement", statement.getRelation(),
                         names(statement.getSelectors()),
                         statement.getAcceptance(),
                         statement.getTargetAttr()
                             ? json::Value(statement.getTargetAttr().getValue())
                             : json::Value(nullptr)};
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      if (!constant.getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{"bool.constant",
                         cast<IntegerAttr>(constant.getValue()).getInt() != 0};
    }
    StringRef boolOpcode;
    if (isa<arith::AndIOp>(op))
      boolOpcode = "bool.and";
    else if (isa<arith::OrIOp>(op))
      boolOpcode = "bool.or";
    else if (isa<arith::XOrIOp>(op))
      boolOpcode = "bool.xor";
    if (!boolOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      if (!op.getResult(0).getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{boolOpcode};
    }
    if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
      if (auto e = attributes(op, {"predicate"}))
        return std::move(e);
      if (!compare.getLhs().getType().isSignlessInteger(1) ||
          (compare.getPredicate() != arith::CmpIPredicate::eq &&
           compare.getPredicate() != arith::CmpIPredicate::ne))
        return error("structured-source-operation");
      return json::Array{compare.getPredicate() == arith::CmpIPredicate::eq
                             ? "bool.equal"
                             : "bool.not_equal"};
    }
    if (isa<arith::SelectOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto type = sort(op.getResult(0).getType());
      if (!type)
        return type.takeError();
      return json::Array{"select", std::move(*type)};
    }
    if (auto make = dyn_cast<data::MakeOp>(op)) {
      if (auto e = attributes(op, {"alternative"}))
        return std::move(e);
      if (owner != "math" && owner != "protocol" && owner != "oracle")
        return error("structured-source-operation");
      return json::Array{"product.make", make.getAlternative()};
    }
    if (auto get = dyn_cast<data::GetOp>(op)) {
      if (auto e = attributes(op, {"index"}))
        return std::move(e);
      if (owner != "math" && owner != "protocol" && owner != "oracle")
        return error("structured-source-operation");
      return json::Array{"product.get", get.getIndex()};
    }
    if (isa<data::BoundedAtOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto vector =
          dyn_cast<algebra::FieldVectorType>(op.getOperand(0).getType());
      if (!vector)
        return error("structured-source-type");
      return json::Array{"bounded_at", vector.getDomain()};
    }
    if (isa<func::CallOp, protocol_ir::LocalCallOp>(op)) {
      bool math = isa<func::CallOp>(op);
      bool participant = !math;
      if (auto e = attributes(
              op, math ? ArrayRef<StringRef>{"callee"}
                       : ArrayRef<StringRef>{"callee", "site", "role"}))
        return std::move(e);
      if (math && owner != "math" && owner != "protocol" && owner != "oracle")
        return error("structured-source-reference");
      auto callee = reference(op, "callee",
                              math ? ArrayRef<StringRef>{"math"}
                                   : ArrayRef<StringRef>{"local"});
      if (!callee)
        return callee.takeError();
      auto *target = symbols.lookup(*callee);
      auto type = signature(*target);
      if (!type || op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults() ||
          (math && !cast<func::FuncOp>(target).isPrivate()))
        return error("structured-source-reference");
      if (participant) {
        auto ownerRole = op.getAttrOfType<StringAttr>("role");
        if (owner != "protocol" || !ownerRole || !hasRole(ownerRole.getValue()))
          return error("structured-source-role");
        return json::Array{"local_call", *callee, ownerRole.getValue()};
      }
      return json::Array{"call", *callee};
    }
    if (isa<algebra::FiniteFoldOp>(op)) {
      if (auto e = attributes(op, {"domain", "step", "predicate"}))
        return std::move(e);
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{"fold", std::move((*refs)[0]), std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    if (isa<protocol_ir::GuardOp>(op)) {
      if (auto e = attributes(op, {"site", "owner"}))
        return std::move(e);
      auto guardOwner = op.getAttrOfType<StringAttr>("owner");
      if (owner != "protocol" || !guardOwner || !hasRole(guardOwner.getValue()))
        return error("structured-source-role");
      return json::Array{"guard", guardOwner.getValue()};
    }
    return error("structured-source-operation", op.getName().getStringRef());
  }

  // A fresh context for every closed block is essential: two equal types (or
  // even two aliased actual arguments) still occupy distinct formal positions.
  Expected<json::Value> block(Region &region, ArrayRef<unsigned> path,
                              TypeRange outputs, StringRef owner,
                              StringRef terminator, unsigned depth = 0) {
    if (depth > depthLimit)
      return error("structured-source-limit");
    if (!llvm::hasSingleElement(region) || region.front().empty())
      return error("structured-source-region");
    Block &body = region.front();
    if (body.getNumArguments() > signatureLimit)
      return error("structured-source-limit");
    llvm::DenseMap<Value, unsigned> refs;
    for (auto [i, arg] : llvm::enumerate(body.getArguments()))
      refs[arg] = i;
    auto operands = [&](Operation &op) -> Expected<json::Array> {
      json::Array result;
      for (Value value : op.getOperands()) {
        auto found = refs.find(value);
        if (found == refs.end())
          return error("structured-source-reference");
        if (found->second > instructionLimit)
          return error("structured-source-limit");
        result.push_back(found->second);
      }
      return result;
    };
    json::Array encoded;
    for (Operation &op : body) {
      auto args = operands(op);
      if (!args)
        return args.takeError();
      if (&op == &body.back()) {
        bool valid = terminator == "return"
                         ? (owner == "math" ? isa<func::ReturnOp>(op)
                            : owner == "oracle"
                                ? isa<protocol_ir::OracleYieldOp>(op)
                                : isa<protocol_ir::MathematicalReturnOp>(op))
                         : owner == "protocol" && terminator == "yield" &&
                               isa<protocol_ir::ProtocolYieldOp>(op);
        if (!valid || op.getOperandTypes() != outputs)
          return error("structured-source-region");
        if (auto e = attributes(op, {}))
          return std::move(e);
        if (auto e = associate(child(path, {2}), op))
          return std::move(e);
        return json::Array{"block", std::move(encoded),
                           json::Array{terminator, std::move(*args)}};
      }
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto inputs = sorts(op.getOperandTypes(),
                          isa<protocol_ir::QueryOp, protocol_ir::ApplyOp,
                              protocol_ir::RepeatOp>(op));
      if (!inputs)
        return inputs.takeError();
      auto results = sorts(op.getResultTypes());
      if (!results)
        return results.takeError();
      auto desc = descriptor(op, owner);
      if (!desc)
        return desc.takeError();
      StringRef occurrence;
      if (op.hasAttr("site") ||
          isa<protocol_ir::ExchangeOp, protocol_ir::QueryOp,
              protocol_ir::GuardOp, protocol_ir::LocalCallOp,
              protocol_ir::RepeatOp>(op)) {
        auto checked = site(op);
        if (!checked)
          return checked.takeError();
        occurrence = *checked;
      }
      auto row = child(path, {1, unsigned(encoded.size())});
      if (auto e = associate(row, op))
        return std::move(e);
      json::Array regions;
      if (op.getNumRegions()) {
        if (!isa<protocol_ir::RepeatOp>(op) || op.getNumRegions() != 1)
          return error("structured-source-region");
        for (Region &nested : op.getRegions()) {
          if (!llvm::hasSingleElement(nested) || nested.front().empty())
            return error("structured-source-region");
          Block &inner = nested.front();
          // Count becomes the induction argument; state and immutable captures
          // retain their ordered types, without identifying their SSA values.
          SmallVector<Type> expectedInputs(op.getOperandTypes());
          SmallVector<Type> expectedOutputs(op.getResultTypes());
          if (inner.getArgumentTypes() != TypeRange(expectedInputs))
            return error("structured-source-region");
          auto in = sorts(expectedInputs, true);
          if (!in)
            return in.takeError();
          auto out = sorts(expectedOutputs);
          if (!out)
            return out.takeError();
          auto regionPath = child(row, {3, unsigned(regions.size())});
          if (auto e = associate(regionPath, op))
            return std::move(e);
          auto content = block(nested, child(regionPath, {2}), expectedOutputs,
                               owner, "yield", depth + 1);
          if (!content)
            return content.takeError();
          regions.push_back(json::Array{std::move(*in), std::move(*out),
                                        std::move(*content)});
        }
      }
      encoded.push_back(json::Array{std::move(*desc), std::move(*args),
                                    std::move(*results), std::move(regions),
                                    occurrence});
      // Prepend the complete result list once. Incremental single-result
      // insertion would reverse a multi-result operation's coordinates.
      for (auto &entry : refs)
        entry.second += op.getNumResults();
      for (auto [i, result] : llvm::enumerate(op.getResults()))
        refs[result] = i;
    }
    return error("structured-source-region");
  }

  Expected<json::Value> domain(data::DomainOp op, ArrayRef<unsigned> path) {
    if (auto e =
            attributes(*op, {"sym_name", "sym_visibility", "function_type"}))
      return std::move(e);
    if (op.getSymVisibility() != "private" ||
        !llvm::hasSingleElement(op.getBody()))
      return error("structured-source-domain");
    Block &body = op.getBody().front();
    if (body.empty() || !isa<data::DomainYieldOp>(body.back()))
      return error("structured-source-domain");
    auto input = [&](Value value) -> Expected<unsigned> {
      auto argument = dyn_cast<BlockArgument>(value);
      if (!argument || argument.getOwner() != &body)
        return error("structured-source-domain");
      return argument.getArgNumber();
    };
    llvm::DenseMap<Value, unsigned> refs;
    json::Array constructors;
    for (Operation &constructor : body.without_terminator()) {
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      if (constructor.getNumResults() != 1)
        return error("structured-source-domain");
      auto result =
          dyn_cast<data::DomainType>(constructor.getResult(0).getType());
      if (!result)
        return error("structured-source-domain");
      auto items = sorts(result.getItemTypes());
      if (!items)
        return items.takeError();
      json::Array desc;
      if (isa<data::DomainElementsOp, data::DomainIndicesOp>(constructor)) {
        bool indices = isa<data::DomainIndicesOp>(constructor);
        if (auto e =
                attributes(constructor, indices ? ArrayRef<StringRef>{"axis"}
                                                : ArrayRef<StringRef>{}))
          return std::move(e);
        auto arg = input(constructor.getOperand(0));
        if (!arg)
          return arg.takeError();
        if (!isa<algebra::FieldVectorType, data::SequenceType>(
                constructor.getOperand(0).getType()))
          return error("structured-source-domain");
        desc = json::Array{indices ? "indices" : "elements", *arg};
        if (indices) {
          if (cast<data::DomainIndicesOp>(constructor).getAxis() != 0)
            return error("structured-source-domain");
          desc.push_back(0);
        }
      } else if (isa<data::DomainRangeOp>(constructor)) {
        if (auto e = attributes(constructor, {}))
          return std::move(e);
        auto lower = input(constructor.getOperand(0));
        if (!lower)
          return lower.takeError();
        auto upper = input(constructor.getOperand(1));
        if (!upper)
          return upper.takeError();
        desc = json::Array{"range", *lower, *upper};
      } else if (isa<data::DomainZipOp, data::DomainProductOp>(constructor)) {
        if (auto e = attributes(constructor, {}))
          return std::move(e);
        json::Array operands;
        for (Value value : constructor.getOperands()) {
          auto found = refs.find(value);
          if (found == refs.end())
            return error("structured-source-domain");
          operands.push_back(found->second);
        }
        desc =
            json::Array{isa<data::DomainZipOp>(constructor) ? "zip" : "product",
                        std::move(operands)};
      } else {
        return error("structured-source-domain",
                     constructor.getName().getStringRef());
      }
      if (auto e = associate(child(path, {3, unsigned(constructors.size())}),
                             constructor))
        return std::move(e);
      constructors.push_back(std::move(desc));
      for (auto &entry : refs)
        ++entry.second;
      refs[constructor.getResult(0)] = 0;
    }
    Operation &yield = body.back();
    if (auto e = attributes(yield, {}))
      return std::move(e);
    if (auto e = associate(child(path, {4}), yield))
      return std::move(e);
    auto returned = refs.find(yield.getOperand(0));
    if (returned == refs.end())
      return error("structured-source-domain");
    auto inputs = sorts(signature(*op).getInputs());
    if (!inputs)
      return inputs.takeError();
    return json::Array{"domain", op.getSymName(), std::move(*inputs),
                       std::move(constructors), returned->second};
  }

  // Whole-unit bodies have already passed ordinary instruction admission and
  // cycle/depth checks. This memoized profile additionally constrains
  // every transitive instruction, including unused calls and discarded results.
  Error preparationProfiles() {
    llvm::DenseSet<Operation *> computationChecked;
    std::function<Error(Operation *)> check = [&](Operation *op) -> Error {
      if (computationChecked.contains(op))
        return Error::success();
      StringRef code = "structured-source-realization";
      auto helper = dyn_cast<func::FuncOp>(op);
      if (!helper || helper.isExternal() || !helper.isPrivate() ||
          helper->getParentOp() != unit.getOperation())
        return error(code, "private Math closure required");
      for (Operation &instruction : helper.getBody().front()) {
        if (auto call = dyn_cast<func::CallOp>(instruction)) {
          if (auto e = check(symbols.lookup(call.getCallee())))
            return e;
          continue;
        }
        if (isa<algebra::FiniteFoldOp>(instruction)) {
          // Ordinary formation discharges callback bounds at each call edge.
          // Both callbacks belong to admission even for an empty domain.
          for (StringRef attribute : {"step", "predicate"}) {
            auto reference =
                instruction.getAttrOfType<FlatSymbolRefAttr>(attribute);
            if (reference)
              if (auto e = check(symbols.lookup(reference.getValue())))
                return e;
          }
          continue;
        }
        bool allowed = isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
                           algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
                           func::ReturnOp>(instruction);
        allowed |=
            isa<algebra::MultilinearRestrictPrefixOp, algebra::FieldEqualOp,
                algebra::GroupIdentityOp, algebra::GroupAddOp,
                algebra::GroupScaleOp, algebra::GroupEqualOp, data::IndexOp,
                data::EqualOp, data::LessOp, data::PowerOfTwoOp, data::DimOp,
                data::MakeOp, data::GetOp, data::BoundedAtOp, arith::ConstantOp,
                arith::AndIOp, arith::OrIOp, arith::XOrIOp, arith::CmpIOp,
                arith::SelectOp>(instruction);
        if (!allowed || instruction.getNumRegions())
          return error(code, instruction.getName().getStringRef());
      }
      computationChecked.insert(op);
      return Error::success();
    };
    for (const auto &[name, origin] : computationOrigins)
      if (auto call = dyn_cast<exec::ComputeOp>(origin)) {
        auto *root = symbols.lookup(call.getCallee().getRootReference());
        if (!root)
          return error("structured-source-realization",
                       "sibling helper required");
        if (auto premises =
                root->getAttrOfType<ArrayAttr>("data.preconditions");
            premises && !premises.empty())
          return error("structured-source-realization", "root preconditions");
        if (auto e = check(root))
          return e;
      }
    return Error::success();
  }

  Expected<json::Value> computation(StringRef name, Operation &op) {
    if (++instructions > instructionLimit)
      return error("structured-source-limit");
    auto inputs = sorts(op.getOperands().drop_front().getTypes());
    if (!inputs)
      return inputs.takeError();
    auto outputs =
        sorts(cast<exec::OutcomeType>(op.getResult(0).getType()).getPayload());
    if (!outputs)
      return outputs.takeError();
    definition = &op;
    if (isa<exec::ComputeOp>(op)) {
      auto helper = reference(op, "callee", {"math"});
      if (!helper)
        return helper.takeError();
      return json::Array{"realize", name.str(), std::move(*inputs),
                         std::move(*outputs), *helper};
    }
    if (isa<exec::FoldOp, exec::CollectOp>(op)) {
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{isa<exec::CollectOp>(op) ? "collect" : "finite",
                         name.str(),
                         "private",
                         std::move(*inputs),
                         std::move(*outputs),
                         std::move((*refs)[0]),
                         std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    return error("structured-source-operation", op.getName().getStringRef());
  }

  Expected<json::Value> oracle(protocol_ir::OracleDefinitionOp op,
                               ArrayRef<unsigned> path) {
    if (auto e = attributes(*op, {"sym_name", "function_type", "kind",
                                  "admissibility", "shape_arguments",
                                  "shape_bounds"}))
      return std::move(e);
    auto inputs = sorts(op.getFunctionType().getInputs());
    if (!inputs)
      return inputs.takeError();
    auto encodedKind = encodeOracleKind(op.getKind(), used, 0);
    if (!encodedKind)
      return encodedKind.takeError();
    // Common admission checks the actual relation signature and every query,
    // including dormant declarations. Retain their source rather than their
    // expanded execution, with definition-local query labels and SSA positions.
    roles = {};
    auto body = block(op.getBody(), child(path, {7}),
                      op.getFunctionType().getResults(), "oracle", "return");
    if (!body)
      return body.takeError();
    return json::Array{"oracle",
                       op.getSymName(),
                       std::move(*inputs),
                       std::move(*encodedKind),
                       op.getAdmissibility(),
                       oracleShapeValues(op.getKind(), op.getShapeArguments()),
                       oracleShapeValues(op.getKind(), op.getShapeBounds()),
                       std::move(*body)};
  }

  Expected<json::Value> function(Operation &op, ArrayRef<unsigned> path) {
    StringRef owner = kind(op);
    auto scoped = dyn_cast<func::FuncOp>(op);
    if (scoped && !isScopedExecutionFunction(scoped))
      scoped = {};
    SmallVector<StringRef> allowed{"sym_name", "sym_visibility",
                                   "function_type"};
    if (owner == "math")
      allowed.push_back("data.preconditions");
    else if (owner == "local") {
      llvm::append_range(allowed,
                         ArrayRef<StringRef>{"runtime.origin", "no_inline",
                                             "data.preconditions"});
    } else if (owner == "protocol")
      llvm::append_range(allowed, ArrayRef<StringRef>{"roles", "input_roles",
                                                      "output_roles",
                                                      "contracts", "origin"});
    else
      return error("structured-source-operation", op.getName().getStringRef());
    if (auto e = attributes(op, allowed))
      return std::move(e);
    auto type = signature(op);
    if (!type)
      return error("structured-source-region");
    auto inputs = sorts(type.getInputs(), owner == "protocol");
    if (!inputs)
      return inputs.takeError();
    auto outputs = sorts(type.getResults());
    if (!outputs)
      return outputs.takeError();
    auto visible = visibility(op);
    if (!visible)
      return visible.takeError();
    StringRef name = SymbolTable::getSymbolName(&op).getValue();
    json::Array ports;
    roles = {};
    if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
      auto encoded = interface(protocol);
      if (!encoded)
        return encoded.takeError();
      ports = std::move(*encoded);
    }
    json::Array preconditions;
    if (op.hasAttr("data.preconditions")) {
      auto attrs = op.getAttrOfType<ArrayAttr>("data.preconditions");
      if (!attrs)
        return error("structured-source-precondition");
      if (attrs.size() > signatureLimit)
        return error("structured-source-limit");
      for (Attribute attr : attrs) {
        auto bound = dyn_cast<data::IndexBoundAttr>(attr);
        unsigned offset = scoped ? 1 : 0;
        if (!bound || bound.getAxis() != 0 || bound.getIndexArg() < offset ||
            bound.getContainerArg() < offset ||
            bound.getIndexArg() - offset >= type.getNumInputs() ||
            bound.getContainerArg() - offset >= type.getNumInputs() ||
            !type.getInput(bound.getIndexArg() - offset)
                 .isUnsignedInteger(64) ||
            !isa<algebra::FieldVectorType>(
                type.getInput(bound.getContainerArg() - offset)))
          return error("structured-source-precondition");
        preconditions.push_back(
            json::Array{"index_bound", bound.getIndexArg() - offset,
                        bound.getContainerArg() - offset, 0});
      }
    }
    json::Array origin;
    if (owner == "protocol") {
      auto value = protocol_ir::readProtocolOrigin(op.getAttr("origin"));
      if (!value)
        return value.takeError();
      origin = std::move(*value->getAsArray());
    }
    if (owner == "local") {
      auto attr = op.getAttrOfType<ArrayAttr>("runtime.origin");
      if (!attr || attr.size() != 2 || !isa<StringAttr>(attr[0]) ||
          !isa<ArrayAttr>(attr[1]))
        return error("structured-source-origin");
      json::Array bindings;
      for (Attribute component : cast<ArrayAttr>(attr[1])) {
        auto pair = dyn_cast<ArrayAttr>(component);
        if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
            !isa<StringAttr>(pair[1]))
          return error("structured-source-origin");
        bindings.push_back(json::Array{cast<StringAttr>(pair[0]).getValue(),
                                       cast<StringAttr>(pair[1]).getValue()});
      }
      origin.push_back(cast<StringAttr>(attr[0]).getValue());
      origin.push_back(std::move(bindings));
    }
    if (!scoped &&
        (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)) ||
         op.getRegion(0).front().getArgumentTypes() != type.getInputs()))
      return error("structured-source-region");
    auto body = scoped ? scopedBlock(scoped, child(path, {9}), "return")
                       : block(op.getRegion(0), child(path, {9}),
                               type.getResults(), owner, "return");
    if (!body)
      return body.takeError();
    return json::Array{"function",
                       name,
                       owner,
                       *visible,
                       std::move(*inputs),
                       std::move(*outputs),
                       std::move(ports),
                       std::move(preconditions),
                       std::move(origin),
                       std::move(*body)};
  }

  Error closure() {
    // Height is the longest reference path in edges; a leaf has height zero.
    // Memoize heights, not only colors: a shared helper encountered first on a
    // short path must still count its whole suffix on a later, longer path.
    llvm::DenseMap<Operation *, unsigned> heights;
    llvm::DenseSet<Operation *> active;
    std::function<Expected<unsigned>(Operation *, unsigned)> visit =
        [&](Operation *op, unsigned depth) -> Expected<unsigned> {
      if (depth > depthLimit)
        return error("structured-source-limit");
      if (auto found = heights.find(op); found != heights.end())
        return found->second;
      if (!active.insert(op).second)
        return error("structured-source-cycle");
      unsigned height = 0;
      for (Operation *callee : dependencies[op]) {
        auto nested = visit(callee, depth + 1);
        if (!nested)
          return nested.takeError();
        height = std::max(height, *nested + 1);
        if (height > depthLimit)
          return error("structured-source-limit");
      }
      active.erase(op);
      heights[op] = height;
      return height;
    };
    for (Operation &op : unit.getBody().front()) {
      auto checked = visit(&op, 0);
      if (!checked)
        return checked.takeError();
    }
    return Error::success();
  }

  Error effectiveSites() {
    // Native verification already checks its conservative application/Math
    // expansion budget. Independently check final protocol-site collisions,
    // without cloning syntax or entering the separate closed helper namespace.
    uint64_t visits = 0, bytes = 0;
    llvm::StringSet<> effective;
    std::function<Error(Block &, StringRef, unsigned, unsigned)> visit =
        [&](Block &body, StringRef prefix, unsigned applicationDepth,
            unsigned repeatDepth) -> Error {
      if (applicationDepth > depthLimit || repeatDepth > depthLimit)
        return error("structured-source-limit");
      for (Operation &op : body) {
        if (++visits > staticVisitLimit)
          return error("structured-source-limit");
        auto site = op.getAttrOfType<StringAttr>("site");
        if (!site)
          continue;
        StringRef leaf = site.getValue();
        auto length = std::to_string(prefix.size());
        size_t overhead =
            prefix.empty() ? 0 : 8 + length.size() + prefix.size();
        if (overhead > effectiveSiteByteLimit ||
            leaf.size() > effectiveSiteByteLimit - overhead)
          return error("structured-source-limit");
        size_t size = overhead + leaf.size();
        if (size > staticSiteByteLimit - bytes)
          return error("structured-source-limit");
        bytes += size;
        std::string rendered =
            prefix.empty()
                ? leaf.str()
                : "apply_" + length + "_" + prefix.str() + "_" + leaf.str();
        if (auto call = dyn_cast<protocol_ir::ApplyOp>(op)) {
          // Headers disappear, but their rendered labels advance the context
          // and count toward metadata work. Revisit each static occurrence.
          if (auto e = visit(
                  symbols.lookup<protocol_ir::MathematicalOp>(call.getCallee())
                      .getBody()
                      .front(),
                  rendered, applicationDepth + 1, repeatDepth))
            return e;
        } else if (!effective.insert(rendered).second) {
          return error("structured-source-site", "expanded protocol collision");
        }
        if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op))
          // A repeat header survives expansion. Its body has the same static
          // prefix and is visited once, even when maximum is zero.
          if (auto e = visit(repeat.getBody().front(), prefix, applicationDepth,
                             repeatDepth + 1))
            return e;
      }
      return Error::success();
    };
    for (auto function :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      effective.clear();
      if (auto e = visit(function.getBody().front(), {}, 1, 0))
        return e;
    }
    return Error::success();
  }

public:
  Exporter(protocol_ir::ProtocolModuleOp unit,
           protocol_ir::MathematicalOp selected, const AsmParserState &parser,
           const SourceMgr &sourceManager,
           std::vector<StructuredSourceAssociation> &associations)
      : unit(unit), selected(selected), symbols(unit), parser(parser),
        sourceManager(sourceManager), associations(associations) {}

  Expected<json::Value> run(StringRef bytes) {
    if (auto e = attributes(*unit, {"profile", "source_declarations"}))
      return std::move(e);
    auto admitted = readSourceExecutionClosure(unit);
    if (!admitted)
      return admitted.takeError();
    execution = std::move(*admitted);
    if (auto e = indexComputations())
      return std::move(e);
    json::Array domains, relations, bindings, definitions, contracts;
    llvm::StringSet<> symbolsSeen;
    for (Operation &op : unit.getBody().front()) {
      // MLIR permits an empty quoted symbol. The wire vocabulary uses the
      // empty string only for absent predicates and sites, never a declaration.
      if (auto name = op.getAttrOfType<StringAttr>("sym_name");
          !name || name.getValue().empty() ||
          !symbolsSeen.insert(name.getValue()).second)
        return error("structured-source-symbol");
      definition = &op;
      sites.clear();
      dependencies.try_emplace(&op);
      if (auto declaration = dyn_cast<data::DomainOp>(op)) {
        if (domains.size() == 128)
          return error("structured-source-limit");
        RowPath path{4, unsigned(domains.size())};
        if (auto e = associate(path, op))
          return std::move(e);
        auto encoded = domain(declaration, path);
        if (!encoded)
          return encoded.takeError();
        domains.push_back(std::move(*encoded));
      } else if (auto declaration = dyn_cast<relation::DeclareOp>(op)) {
        if (relations.size() == 128)
          return error("structured-source-limit");
        if (auto e = attributes(op, {"sym_name", "sym_visibility", "kind",
                                     "key", "revision", "static_arguments",
                                     "signature", "purposes", "formula"}))
          return std::move(e);
        auto visible = visibility(op);
        if (!visible)
          return visible.takeError();
        auto type = declaration.getSignature();
        auto inputs = sorts(type.getInputs());
        if (!inputs)
          return inputs.takeError();
        auto outputs = sorts(type.getResults());
        if (!outputs)
          return outputs.takeError();
        auto staticArguments =
            relation::readStaticArguments(declaration.getStaticArguments());
        if (!staticArguments)
          return staticArguments.takeError();
        for (const auto &argument : *staticArguments->getAsArray())
          if (auto e = collectStaticDomains(argument, used))
            return e;
        if (auto e = associate({5, unsigned(relations.size())}, op))
          return std::move(e);
        relations.push_back(json::Array{
            "relation", declaration.getSymName(), *visible,
            declaration.getKind(), declaration.getKey(),
            declaration.getRevision(), std::move(*staticArguments),
            std::move(*inputs), std::move(*outputs),
            names(declaration.getPurposes()),
            declaration.getFormulaAttr()
                ? json::Value(declaration.getFormulaAttr().getValue())
                : json::Value(nullptr)});
      } else if (isa<runtime::BindingOp>(op)) {
        if (bindings.size() == 128)
          return error("structured-source-limit");
        if (auto e = attributes(op, {"sym_name", "contract", "arguments",
                                     "implementation", "function_type"}))
          return std::move(e);
        auto binding = primitiveBinding(&op, used);
        if (!binding)
          return binding.takeError();
        if (auto e = associate({6, unsigned(bindings.size())}, op))
          return std::move(e);
        bindings.push_back(
            json::Array{"binding", binding->name, binding->application.contract,
                        names(op.getAttrOfType<ArrayAttr>("arguments")),
                        binding->application.implementation});
      } else {
        if (auto function = dyn_cast<func::FuncOp>(op);
            function && function->hasAttr("runtime.region"))
          continue; // Checked and consumed at each exact closed-region use.
        if (definitions.size() == 128)
          return error("structured-source-limit");
        RowPath path{7, unsigned(definitions.size())};
        if (auto e = associate(path, op))
          return std::move(e);
        auto declaration = dyn_cast<protocol_ir::OracleDefinitionOp>(op);
        auto encoded =
            declaration ? oracle(declaration, path) : function(op, path);
        if (!encoded)
          return encoded.takeError();
        definitions.push_back(std::move(*encoded));
        if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
          if (protocol.getContractsAttr() &&
              protocol.getContractsAttr().size() > signatureLimit)
            return error("structured-source-limit");
          if (auto e = associate({8, unsigned(contracts.size())}, op))
            return std::move(e);
          contracts.push_back(
              json::Array{protocol.getSymName(),
                          protocol.getContractsAttr()
                              ? contractValue(protocol.getContractsAttr())
                              : json::Value(json::Array{})});
        }
      }
    }
    for (const auto &[name, origin] : computationOrigins) {
      if (definitions.size() == 128 || !symbolsSeen.insert(name).second)
        return error("structured-source-limit");
      if (auto e = associate({7, unsigned(definitions.size())}, *origin,
                             StructuredSourceDerivation::Computation))
        return std::move(e);
      auto encoded = computation(name, *origin);
      if (!encoded)
        return encoded.takeError();
      definitions.push_back(std::move(*encoded));
    }
    if (auto e = closure())
      return std::move(e);
    if (auto e = preparationProfiles())
      return std::move(e);
    if (auto e = effectiveSites())
      return std::move(e);
    // Multi-role Math finite work needs separate partial-component semantics.
    // Follow only Math calls: owned Local finite work keeps its closed ABI.
    llvm::DenseSet<Operation *> checked;
    std::function<Error(Operation *)> scalarMath =
        [&](Operation *function) -> Error {
      if (!checked.insert(function).second)
        return Error::success();
      SmallVector<Operation *> operations;
      function->getRegion(0).walk<WalkOrder::PreOrder>(
          [&](Operation *op) { operations.push_back(op); });
      for (Operation *operation : operations) {
        Operation &op = *operation;
        if (isa<algebra::FiniteFoldOp, data::BoundedAtOp>(op))
          return error("structured-source-multirole-math");
        if (auto call = dyn_cast<func::CallOp>(op))
          if (auto e = scalarMath(symbols.lookup(call.getCallee())))
            return e;
      }
      return Error::success();
    };
    for (auto protocol :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>())
      if (protocol.getRoles().size() > 1)
        if (auto e = scalarMath(protocol))
          return std::move(e);
    json::Value declarations = json::Array{json::Array{}, json::Array{}};
    if (auto attr = unit->getAttr("source_declarations")) {
      auto text = dyn_cast<StringAttr>(attr);
      if (!text)
        return error("component-declaration");
      auto parsed = zkc::parseNaturalJson(text.getValue(), 16 * 1024 * 1024,
                                          256, "component-declaration",
                                          "structured-source-limit");
      if (!parsed)
        return parsed.takeError();
      auto rows = parsed->getAsArray();
      if (!rows || rows->size() != 2 || !(*rows)[0].getAsArray() ||
          !(*rows)[1].getAsArray())
        return error("component-declaration");
      if (auto e = language::checkComponentDeclarations(*parsed))
        return std::move(e);
      // These rows are emitted from the module's checked declaration context,
      // not reconstructed from an executable function or a printed symbol.
      for (unsigned table : {0, 1})
        for (unsigned i = 0; i < (*rows)[table].getAsArray()->size(); ++i)
          if (auto e = associate({10, table, i}, *unit))
            return std::move(e);
      declarations = std::move(*parsed);
    }
    auto digest = SHA256::hash(arrayRefFromStringRef(bytes));
    return json::Array{"zkc.structured-source/0",
                       "original",
                       "sha256:" + toHex(digest, true),
                       selected.getSymName(),
                       std::move(domains),
                       std::move(relations),
                       std::move(bindings),
                       std::move(definitions),
                       std::move(contracts),
                       catalogueSlot(used),
                       std::move(declarations)};
  }
};
} // namespace

Expected<StructuredSource>
exportStructuredSource(StringRef bytes, StringRef name, MLIRContext &context) {
  if (bytes.size() > 16 * 1024 * 1024 || !mlirNestingWithinLimit(bytes))
    return error("structured-source-limit");
  SourceMgr manager;
  manager.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(bytes, "original"),
                             SMLoc());
  AsmParserState parser;
  Block parsed;
  if (failed(parseAsmSourceFile(manager, &parsed, ParserConfig(&context, false),
                                &parser)))
    return error("structured-source-original");
  auto original =
      mlir::detail::constructContainerOpForParserIfNecessary<ModuleOp>(
          &parsed, &context, FileLineColLoc::get(&context, "original", 1, 1));
  if (!original || failed(verify(*original)))
    return error("structured-source-original");
  if (auto e = attributes(**original, {}))
    return std::move(e);
  if (!llvm::hasSingleElement(original->getBody()->getOperations()))
    return error("structured-source-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("structured-source-profile");
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(name);
  if (!selected)
    return error("structured-source-symbol");
  StructuredSource result;
  auto exported =
      Exporter(unit, selected, parser, manager, result.associations).run(bytes);
  if (!exported)
    return exported.takeError();
  if (!boundedSourceWire(*exported))
    return error("structured-source-limit");
  // Own framing and its byte budget together: callers emit these exact bytes.
  auto serialized = printJson(*exported) + '\n';
  if (serialized.size() > 1024 * 1024)
    return error("structured-source-limit");
  result.bytes = std::move(serialized);
  return result;
}
} // namespace zkc::protocol
