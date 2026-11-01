#include "zkc/Target/Evm/Layout.h"
#include "mlir/IR/BuiltinTypes.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::evm {
struct NativeLayouts::Storage {
  MLIRContext &context;
  llvm::DenseMap<Type, std::unique_ptr<ValueLayout>> values;
  llvm::DenseMap<Type, std::unique_ptr<FieldLayout>> fields;
  explicit Storage(MLIRContext &context) : context(context) {}
};
NativeLayouts::NativeLayouts(MLIRContext &context)
    : storage(std::make_unique<Storage>(context)) {}
NativeLayouts::~NativeLayouts() = default;

namespace {
bool formed(Type type, LogicalTypePermissions &permissions) {
  return succeeded(verifyLogicalType(
      [&] {
        auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
        diagnostic.abandon();
        return diagnostic;
      },
      type, &permissions));
}
Expected<APInt> primeModulus(StringRef domain) {
  const auto &catalog = protocol::installedDomains();
  auto *fact = catalog.domain(domain);
  APInt number;
  if (!fact || !catalog.hasFact("PrimeField", {domain.str()}) ||
      StringRef(fact->modulus).getAsInteger(10, number) ||
      number.getActiveBits() > 256 || number.ult(2))
    return zkc::error("evm.field", "requires an exact installed prime modulus");
  return number.zextOrTrunc(256);
}
} // namespace

Expected<const FieldLayout *> NativeLayouts::field(algebra::FieldType type) {
  if (!type || type.getContext() != &storage->context)
    return zkc::error("evm.field", "field belongs to another context");
  if (auto found = storage->fields.find(type); found != storage->fields.end())
    return found->second.get();
  LogicalTypePermissions permissions;
  if (!formed(type, permissions) || !permissions.copy || !permissions.drop)
    return zkc::error("evm.field", "requires a formed Copy/Drop field");
  auto result = std::make_unique<FieldLayout>();
  result->type = result->base = type;
  const auto &catalog = protocol::installedDomains();
  if (catalog.hasFact("PrimeField", {type.getDomain().str()})) {
    auto modulus = primeModulus(type.getDomain());
    if (!modulus)
      return modulus.takeError();
    result->modulus = *modulus;
  } else {
    auto *extension = protocol::plonky3Field(type.getDomain());
    if (!extension || extension->degree < 2 || extension->degree > 8 ||
        !catalog.hasFact("ExtensionField", {type.getDomain().str()}) ||
        catalog.associatedIdentity(type.getDomain(), "BaseField") !=
            extension->base)
      return zkc::error("evm.field",
                        "requires installed ascending-binomial facts");
    auto modulus = primeModulus(extension->base);
    if (!modulus)
      return modulus.takeError();
    APInt declared;
    if (extension->modulus.getAsInteger(10, declared) ||
        declared.getActiveBits() > 256 ||
        declared.zextOrTrunc(256) != *modulus || !extension->nonresidue ||
        modulus->ule(extension->nonresidue))
      return zkc::error("evm.field", "inconsistent installed extension facts");
    result->base = algebra::FieldType::get(&storage->context, extension->base);
    result->modulus = *modulus;
    result->degree = extension->degree;
    result->beta = APInt(256, extension->nonresidue);
  }
  auto *descriptor = result.get();
  storage->fields[type] = std::move(result);
  return descriptor;
}

Expected<const ValueLayout *> NativeLayouts::get(Type type) {
  if (!type || type.getContext() != &storage->context)
    return zkc::error("evm.layout", "type belongs to another context");
  if (auto found = storage->values.find(type); found != storage->values.end())
    return found->second.get();
  LogicalTypePermissions permissions;
  if (!formed(type, permissions) || !permissions.copy || !permissions.drop)
    return zkc::error("evm.layout", "requires complete logical Copy/Drop data");
  auto result = std::make_unique<ValueLayout>();
  result->logical = type;
  auto i64 = IntegerType::get(&storage->context, 64);
  using Kind = ValueLayout::Kind;
  using Cells = CollectionLayout::Storage;
  if (type.isInteger(1)) {
    result->kind = Kind::Boolean;
    result->lanes.push_back(IntegerType::get(&storage->context, 1));
  } else if (auto index = dyn_cast<IntegerType>(type);
             index && index.isUnsigned() && index.getWidth() == 64) {
    result->kind = Kind::Index;
    result->lanes.push_back(i64);
  } else if (auto scalar = dyn_cast<algebra::FieldType>(type)) {
    auto facts = field(scalar);
    if (!facts)
      return facts.takeError();
    result->kind = Kind::Field;
    result->lanes.push_back(
        IntegerType::get(&storage->context, (*facts)->degree == 1 ? 256 : 64));
  } else if (isa<algebra::FieldVectorType, algebra::FieldArrayType>(type)) {
    StringRef domain = isa<algebra::FieldVectorType>(type)
                           ? cast<algebra::FieldVectorType>(type).getDomain()
                           : cast<algebra::FieldArrayType>(type).getDomain();
    auto element = algebra::FieldType::get(&storage->context, domain);
    auto facts = field(element);
    if (!facts)
      return facts.takeError();
    result->kind = isa<algebra::FieldVectorType>(type) ? Kind::FieldVector
                                                       : Kind::FieldArray;
    result->lanes.append({i64, i64});
    result->collection = CollectionLayout{element, Cells::FieldCoefficients,
                                          (*facts)->coefficientBytes()};
  } else if (isa<algebra::IndicesType>(type)) {
    result->kind = Kind::Indices;
    result->lanes.append({i64, i64});
    result->collection = CollectionLayout{
        IntegerType::get(&storage->context, 64, IntegerType::Unsigned),
        Cells::LaneCells, 32};
  } else if (isa<data::BytesType>(type)) {
    result->kind = Kind::Bytes;
    result->lanes.append({i64, i64});
    result->collection = CollectionLayout{{}, Cells::PackedBytes, 1};
  } else if (isa<data::SequenceType, algebra::FixedVectorType>(type)) {
    Type element = isa<data::SequenceType>(type)
                       ? cast<data::SequenceType>(type).getElementType()
                       : cast<algebra::FixedVectorType>(type).getElementType();
    auto child = get(element);
    if (!child)
      return child.takeError();
    result->kind =
        isa<data::SequenceType>(type) ? Kind::Sequence : Kind::FixedVector;
    result->lanes.append({i64, i64});
    result->collection =
        CollectionLayout{element, Cells::LaneCells, (*child)->laneCellBytes()};
  } else if (auto object = dyn_cast<commitment::VectorObjectType>(type)) {
    if (object.getKind() != "commitment" && object.getKind() != "proof")
      return zkc::error("evm.layout",
                        "requires an installed immutable root/path envelope");
    result->kind = object.getKind() == "commitment" ? Kind::Root : Kind::Path;
    result->lanes.append({i64, i64});
  } else if (auto variant = dyn_cast<data::VariantType>(type)) {
    for (auto alternative : variant.getAlternatives())
      for (Type child : alternative.getPayload()) {
        auto layout = get(child);
        if (!layout)
          return layout.takeError();
      }
    result->kind = Kind::Variant;
    result->lanes.push_back(i64);
  } else {
    return zkc::error("evm.layout",
                      "no local EVM representation for this native type");
  }
  auto *descriptor = result.get();
  storage->values[type] = std::move(result);
  return descriptor;
}
Expected<SignatureLayout> NativeLayouts::signature(TypeRange types) {
  SignatureLayout result;
  for (Type type : types) {
    auto layout = get(type);
    if (!layout)
      return layout.takeError();
    result.values.push_back(
        {unsigned(result.lanes.size()), unsigned((*layout)->lanes.size())});
    append_range(result.lanes, (*layout)->lanes);
  }
  return result;
}
Expected<SignatureLayout> NativeLayouts::payload(data::VariantType type,
                                                 uint32_t alternative) {
  auto complete = get(type);
  if (!complete)
    return complete.takeError();
  if (alternative >= type.getAlternatives().size())
    return zkc::error("evm.layout", "variant alternative is out of range");
  return signature(type.getAlternatives()[alternative].getPayload());
}
} // namespace zkc::evm
