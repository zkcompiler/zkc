#include "OracleAnchorStorage.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include <limits>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
Expected<Type> product(MLIRContext *context, json::Value identity,
                       ArrayRef<Type> fields) {
  if (!context->getLoadedDialect<data::DataDialect>())
    return error("oracle-storage-type");
  auto nominal = data::importVariantIdentity(context, identity);
  if (!nominal || fields.size() > 128)
    return error("oracle-storage-type-limit");
  auto arm = data::AlternativeAttr::get(
      context, StringAttr::get(context, "Record"), fields);
  auto result =
      data::VariantType::getChecked(UnknownLoc::get(context), context, nominal,
                                    ArrayRef<data::AlternativeAttr>{arm});
  if (!result)
    return error("oracle-storage-type-limit");
  return Type(result);
}
struct Planner {
  pir::MathematicalOp program;
  SymbolTable &symbols;
  OracleStorageSelection select;
  OracleAnchorStorage result;
  unsigned remaining = 100000;
  Error role(OracleAnchorConstructor &constructor, StringRef owner,
             ArrayRef<OracleStorageField> payload) {
    OracleRoleStorage storage;
    storage.role = owner.str();
    auto *context = program.getContext();
    auto index = IntegerType::get(context, 64, IntegerType::Unsigned);
    // Instance ordinals identify storage, but cannot reconstruct coordinates
    // when nested trip counts vary. Keep each actual enclosing iteration.
    for (unsigned i = 1; i < constructor.path.size(); ++i)
      storage.fields.push_back({"iteration." + std::to_string(i - 1), index});
    for (const auto &shape : constructor.kind.getShapeDimensions())
      storage.fields.push_back({"shape." + shape.name, index});
    storage.fields.push_back({"query.leaves", index});
    append_range(storage.fields, payload);
    if (storage.fields.size() > remaining)
      return error("oracle-storage-limit");
    remaining -= storage.fields.size();
    json::Array path;
    for (unsigned step : constructor.path)
      path.push_back(std::to_string(step));
    SmallVector<Type> types;
    for (const auto &field : storage.fields)
      types.push_back(field.type);
    auto record =
        product(context,
                json::Array{"zkc.oracle.storage/0", toHex(result.entry, true),
                            std::move(path), toHex(owner, true)},
                types);
    if (!record)
      return record.takeError();
    storage.record = *record;
    storage.sequence =
        constructLogicalType([&] { return emitError(program.getLoc()); },
                             context, {"sequence", {TypeAttr::get(*record)}});
    if (!storage.sequence)
      return error("oracle-storage-type");
    constructor.roles.push_back(std::move(storage));
    return Error::success();
  }
  Error anchor(Operation *op, std::vector<unsigned> path, uint64_t maximum) {
    OracleAnchorConstructor constructor;
    constructor.path = std::move(path);
    if (auto site = op->getAttrOfType<StringAttr>("site"))
      constructor.site = site.getValue().str();
    constructor.maximumInstances = maximum;
    ArrayAttr receivers;
    SmallVector<OracleStorageField> holderFields, receiverFields;
    if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
      Value anchor = input.getAnchor();
      while (auto view = anchor.getDefiningOp<pir::RestrictRolesOp>()) {
        if (!remaining)
          return error("oracle-storage-limit");
        --remaining;
        anchor = view.getInput();
      }
      auto argument = dyn_cast<BlockArgument>(anchor);
      // Application expansion retains component rebindings. They preserve the
      // existing reference; only a root binding allocates an input constructor.
      if (!argument || argument.getOwner() != &program.getBody().front())
        return Error::success();
      // Sequence ports are internal references. Host ingress has no sequence
      // constructor or external graph representation in this profile.
      auto handle =
          dyn_cast<pir::OracleHandleType>(input.getHandle().getType());
      if (!handle)
        return error("oracle-common-interface");
      constructor.constructor = OracleAnchorConstructor::Kind::Input;
      constructor.kind = handle.getKind();
      constructor.holder = input.getHolder().str();
      receivers = input.getReceivers();
    } else if (auto send = dyn_cast<pir::OracleSendOp>(op)) {
      constructor.constructor = OracleAnchorConstructor::Kind::Send;
      constructor.kind = send.getHandle().getType().getKind();
      constructor.holder = send.getSender().str();
      receivers = send.getReceivers();
    } else {
      auto created = cast<pir::OracleVirtualOp>(op);
      constructor.constructor = OracleAnchorConstructor::Kind::Virtual;
      constructor.kind = created.getHandle().getType().getKind();
      constructor.holder = created.getHolder().str();
      constructor.declaration = created.getCallee().str();
      receivers = created.getReceivers();
      auto declaration =
          symbols.lookup<pir::OracleDefinitionOp>(created.getCallee());
      if (!declaration)
        return error("oracle-storage-source");
      unsigned sources = declaration.getNumSources();
      for (auto [i, input] : enumerate(created.getInputs())) {
        Type type = input.getType();
        if (i < sources) {
          auto reference =
              oracleReferenceType(cast<pir::OracleHandleType>(type).getKind());
          if (!reference)
            return reference.takeError();
          type = *reference;
        }
        holderFields.push_back(
            {(i < sources ? "source." : "parameter.") + std::to_string(i),
             type});
      }
      receiverFields = holderFields;
    }
    for (Attribute receiver : receivers)
      constructor.receivers.push_back(
          cast<StringAttr>(receiver).getValue().str());
    if (constructor.constructor != OracleAnchorConstructor::Kind::Virtual) {
      auto scheme = select(constructor);
      if (!scheme)
        return scheme.takeError();
      constructor.scheme = *scheme;
      Type data = constructor.kind.getDataType();
      holderFields.push_back({"data", data});
      if (scheme->empty())
        receiverFields.push_back({"data", data});
      else {
        auto *context = program.getContext();
        auto signature = resolveLogicalSignature(
            [&] { return emitError(program.getLoc()); }, context,
            "oracle.commit", {StringAttr::get(context, *scheme)});
        if (!signature || signature.getNumInputs() != 2 ||
            signature.getNumResults() != 2 || signature.getInput(0) != data)
          return error("oracle-storage-scheme");
        Type root = signature.getResult(0);
        Type state = signature.getResult(1);
        holderFields.push_back({"opening_state", state});
        receiverFields.push_back({"root", root});
      }
    }
    if (auto e = role(constructor, constructor.holder, holderFields))
      return e;
    for (const auto &receiver : constructor.receivers)
      if (auto e = role(constructor, receiver, receiverFields))
        return e;
    result.constructors.push_back(std::move(constructor));
    return Error::success();
  }
  Error block(Block &body, std::vector<unsigned> path, uint64_t multiplicity,
              unsigned depth) {
    if (!depth)
      return error("oracle-storage-limit");
    for (auto [i, op] : enumerate(body)) {
      if (!remaining)
        return error("oracle-storage-limit");
      --remaining;
      auto location = path;
      location.push_back(i);
      if (isa<pir::ApplyOp>(op))
        return error("oracle-storage-preparation");
      if (isa<pir::OracleInputOp, pir::OracleSendOp, pir::OracleVirtualOp>(op))
        if (auto e = anchor(&op, location, multiplicity))
          return e;
      if (auto repeat = dyn_cast<pir::RepeatOp>(op)) {
        uint64_t bound = repeat.getMaximum();
        if (bound &&
            multiplicity > std::numeric_limits<uint64_t>::max() / bound)
          return error("oracle-storage-capacity");
        if (auto e = block(repeat.getBody().front(), std::move(location),
                           multiplicity * bound, depth - 1))
          return e;
      }
    }
    return Error::success();
  }
};
} // namespace
Expected<Type> oracleReferenceType(pir::OracleKindAttr kind) {
  if (!kind ||
      failed(pir::OracleKindAttr::verify(
          [&]() { return emitError(UnknownLoc::get(kind.getContext())); },
          kind.getIdentity(), kind.getArguments())))
    return error("oracle-storage-kind");
  if (!kind.getContext()->getLoadedDialect<data::DataDialect>())
    return error("oracle-storage-type");
  // The reference's /0 nominal identity contains canonical interchange type
  // strings. Encode only at this identity boundary; never decode the carrier
  // to derive its native fields or oracle associations. Unserializable kinds
  // cannot be published under this existing reference schema.
  auto data = encodeBoundType(kind.getDataType(), false);
  if (!data)
    return data.takeError();
  auto query = encodeBoundType(kind.getQueryType(), false);
  if (!query)
    return query.takeError();
  auto answer = encodeBoundType(kind.getAnswerType(), false);
  if (!answer)
    return answer.takeError();
  auto index = IntegerType::get(kind.getContext(), 64, IntegerType::Unsigned);
  return product(kind.getContext(),
                 json::Array{"zkc.oracle.reference/0", kind.getIdentity(),
                             data->spelling(), query->spelling(),
                             answer->spelling()},
                 {index, index});
}
Expected<OracleAnchorStorage>
planOracleAnchorStorage(ModuleOp prepared, StringRef entry,
                        OracleStorageSelection select) {
  if (!select || !prepared || failed(zkc::admitStage(prepared)) ||
      !hasSingleElement(prepared.getBody()->getOperations()))
    return error("oracle-storage-source");
  auto module = dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  if (!module || module.getProfile() != pir::Profile::Protocol)
    return error("oracle-storage-source");
  SymbolTable symbols(module);
  auto program = symbols.lookup<pir::MathematicalOp>(entry);
  if (!program)
    return error("oracle-storage-entry");
  Planner planner{program, symbols, select, {entry.str(), {}}};
  if (auto e = planner.block(program.getBody().front(), {}, 1, 64))
    return std::move(e);
  // Charge expanded native structure across every role, including repeated
  // uniqued layouts. Canonical byte size belongs to reference/publication
  // boundaries; it is not a premise for forming a persistent native store.
  SmallVector<Type> stores;
  for (const auto &constructor : planner.result.constructors)
    for (const auto &role : constructor.roles)
      stores.push_back(role.sequence);
  if (failed(verifyLogicalTypes([&] { return emitError(program.getLoc()); },
                                stores)))
    return error("oracle-storage-limit");
  return std::move(planner.result);
}
} // namespace zkc::protocol
