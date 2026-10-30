#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Contracts/NativePolicy.h"
#include "llvm/Support/Error.h"
#include <functional>
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
  // SDK callers can construct descriptors directly. Bound the structure and
  // check pointers before recursive policy or spelling routines inspect it.
  unsigned remaining = 200000;
  std::function<bool(const BoundType &, unsigned)> logical =
      [&](const BoundType &type, unsigned depth) {
        if (!remaining || depth > 64 || !type.representation.empty() ||
            type.physicalChildren)
          return false;
        --remaining;
        for (const auto &argument : type.arguments)
          if (argument.kind == TypeArgument::Kind::Type &&
              (!argument.type || !logical(*argument.type, depth + 1)))
            return false;
        return true;
      };
  if (!logical(row, 0))
    return refuse(
        "oracle table row is malformed, physical or exceeds type bounds");
  auto policy = nativeTypePolicy(row);
  if (!policy || !policy->total || !policy->shared || policy->affine)
    return refuse("oracle table rows require canonical total data");
  auto canonical = parseBoundType(row.spelling(), false);
  if (!canonical)
    return canonical.takeError();
  if (!(*canonical == row))
    return refuse("oracle table rows require canonical logical data");
  auto constructor = oracleTableCollectionConstructor(row.kind);
  BoundType data =
      constructor == "sequence"
          ? BoundType{"sequence", {}, {}, {TypeArgument::typeArgument(row)}}
          : BoundType{constructor.str(), row.identity, {}};
  // The associated collection must fit the complete logical type grammar.
  auto collection = parseBoundType(data.spelling(), false);
  if (!collection)
    return collection.takeError();
  return OracleKindSignature{
      std::move(*collection),
      {"index", {}, {}},
      std::move(*canonical),
      {{"rows", arguments.size() == 2
                    ? std::optional<uint64_t>(arguments[1].natural)
                    : std::nullopt}}};
}
} // namespace zkc::protocol
