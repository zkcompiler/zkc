// Link this fixture with TypeAdapters/Registry.cpp, MLIRIR, ZkcContracts and
// ZkcSupport. It owns an explicit test installation; do not link the shipped
// Installed.cpp.
#include "support/NativeCases.h"
#include "zkc/Dialect/TypeAdapters/Support.h"

using namespace mlir;
using namespace zkc::protocol;
using namespace zkc::protocol::type_adapters;
using namespace zkc::test;

namespace {
// A test-only view of an ordinary tensor lets the actual Type/Nat helper run
// against an isolated registry without importing the production IR
// installation.
class AppliedTensor : public RankedTensorType {
public:
  using RankedTensorType::RankedTensorType;
  Type element() const { return getElementType(); }
  uint64_t length() const { return getDimSize(0); }
};
using Applied = TypeNatAdapter<AppliedTensor, &AppliedTensor::element,
                               &AppliedTensor::length>;
Type noDecode(MLIRContext *, const BoundType &) { return {}; }
std::optional<BoundType> boolean(Type type, llvm::StringRef constructor) {
  if (type.isSignlessInteger(1))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
std::optional<BoundType> index(Type type, llvm::StringRef constructor) {
  if (type.isUnsignedInteger(64))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
std::optional<BoundType> float32(Type type, llvm::StringRef constructor) {
  if (type.isF32())
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
std::optional<BoundType> never(Type, llvm::StringRef) { return std::nullopt; }
} // namespace

namespace zkc::protocol::type_adapters {
llvm::ArrayRef<llvm::ArrayRef<TypeAdapter>> installedAdapters() {
  static constexpr TypeAdapter first[] = {
      {"bool", noDecode, boolean},
      {"index", noDecode, index},
      {"fixed_vector", noDecode, Applied::encode},
      {"duplicate", noDecode, float32}};
  static constexpr TypeAdapter second[] = {{"other_bool", noDecode, boolean},
                                           {"duplicate", noDecode, never}};
  static const llvm::ArrayRef<TypeAdapter> tables[] = {first, second};
  return tables;
}
} // namespace zkc::protocol::type_adapters

int main() {
  MLIRContext context;
  Cases cases;
  auto booleanType = IntegerType::get(&context, 1);
  cases.run("custom/custom ambiguity refuses",
            [&] { refuses(encodeLogicalType(booleanType), "binding-type"); });
  cases.run("nested custom/custom ambiguity refuses", [&] {
    auto nested = RankedTensorType::get({4}, booleanType);
    require(!Applied::encode(nested, "fixed_vector"),
            "nested helper selected the first custom match");
    refuses(encodeLogicalType(nested), "binding-type");
  });
  cases.run("unique nested encoding retains Type and Nat", [&] {
    auto element = IntegerType::get(&context, 64, IntegerType::Unsigned);
    auto nested = RankedTensorType::get({4}, element);
    BoundType expected{"fixed_vector",
                       {},
                       {},
                       {TypeArgument::typeArgument({"index", {}, {}}),
                        TypeArgument::naturalArgument(4)}};
    require(take(encodeLogicalType(nested)) == expected,
            "unique nested translation changed structure");
  });
  cases.run("duplicate registration invalidates unique native match", [&] {
    require(!findAdapter("duplicate"),
            "duplicate constructor acquired an owner");
    refuses(encodeLogicalType(Float32Type::get(&context)), "binding-type");
  });
  return cases.result();
}
