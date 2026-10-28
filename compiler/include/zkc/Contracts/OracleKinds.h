#ifndef ZKC_CONTRACTS_ORACLEKINDS_H
#define ZKC_CONTRACTS_ORACLEKINDS_H
#include "zkc/Contracts/Bindings.h"
#include <optional>
#include <vector>

namespace zkc::protocol {
/// Logical associations of an admitted library kind. These are ordinary data
/// types; the kind itself is not a native value or a commitment scheme.
struct OracleShapeDimension {
  std::string name;
  std::optional<uint64_t> extent;
};
struct OracleKindSignature {
  BoundType data, query, answer;
  std::vector<OracleShapeDimension> shape;
  std::optional<uint64_t> staticShape(llvm::StringRef name) const {
    for (const auto &dimension : shape)
      if (dimension.name == name)
        return dimension.extent;
    return std::nullopt;
  }
};
/// Check closed, typed kind arguments without depending on an IR or source
/// representation. Frontend closure and IR formation share this definition.
llvm::Expected<OracleKindSignature>
oracleKindSignature(llvm::StringRef identity,
                    llvm::ArrayRef<TypeArgument> arguments);
} // namespace zkc::protocol
#endif
