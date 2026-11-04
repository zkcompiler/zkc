#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Contracts/NativePolicy.h"
#include "llvm/Support/Error.h"
using namespace llvm;
namespace zkc::protocol {
StringRef oracleTableCollectionConstructor(StringRef rowConstructor) {
  if (rowConstructor == "field")
    return "vector";
  if (rowConstructor == "group")
    return "groups";
  if (rowConstructor == "index")
    return "indices";
  return "sequence";
}
Expected<OracleKindSignature>
oracleKindSignature(StringRef identity, ArrayRef<TypeArgument> arguments) {
  auto refuse = [](const Twine &message) {
    return createStringError(inconvertibleErrorCode(), message);
  };
  if (identity != "table")
    return refuse("unsupported oracle kind: " + identity);
  if ((arguments.size() != 1 && arguments.size() != 2) ||
      arguments[0].kind != TypeArgument::Kind::Type || !arguments[0].type)
    return refuse("oracle table needs a row type and optional static rows");
  if (arguments.size() == 2 && arguments[1].kind != TypeArgument::Kind::Nat)
    return refuse("oracle table static rows must be a natural");
  const auto &row = *arguments[0].type;
  if (auto e = checkBoundType(row, false))
    return e;
  auto policy = nativeTypePolicy(row);
  if (!policy || !policy->total || !policy->shared || policy->affine)
    return refuse("oracle table rows require canonical total data");
  auto constructor = oracleTableCollectionConstructor(row.kind);
  BoundType data =
      constructor == "sequence"
          ? BoundType{"sequence", {}, {}, {TypeArgument::typeArgument(row)}}
          : BoundType{constructor.str(), row.identity, {}};
  if (auto e = checkBoundType(data, false))
    return e;
  return OracleKindSignature{
      std::move(data),
      {"index", {}, {}},
      row,
      {{"rows", arguments.size() == 2
                    ? std::optional<uint64_t>(arguments[1].natural)
                    : std::nullopt}}};
}
} // namespace zkc::protocol
