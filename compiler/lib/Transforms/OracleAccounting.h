#ifndef ZKC_TRANSFORMS_ORACLEACCOUNTING_H
#define ZKC_TRANSFORMS_ORACLEACCOUNTING_H

#include "OracleAnchorStorage.h"
#include "OracleNativeCommon.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/JSON.h"
#include <algorithm>

namespace zkc::protocol {
// A private cancellation signal bridges value-returning native/type builder
// callbacks to Error/Expected boundaries. Catch only this signal; allocation
// failures and unrelated exceptions retain their ordinary behavior.
inline mlir::Type requireOracleReferenceType(protocol_ir::OracleKindAttr kind,
                                             OracleNativeWork &work) {
  auto reference = oracleReferenceTypeWithWork(kind, work);
  if (!reference && work.exhausted) {
    llvm::consumeError(reference.takeError());
    throw OracleAccountingLimit{};
  }
  return llvm::cantFail(std::move(reference));
}
inline llvm::Error normalizeOracleAccountingError(llvm::Error failure,
                                                  OracleNativeWork &work) {
  if (!failure || !work.exhausted)
    return failure;
  return llvm::handleErrors(std::move(failure),
                            [](const Refusal &refusal) -> llvm::Error {
                              if (refusal.code == "common-control-capacity")
                                return error(refusal.code, refusal.detail);
                              return error("oracle-common-limit");
                            });
}
template <class F>
llvm::Error oracleVerificationWithWork(OracleNativeWork &work, F &&check) {
  try {
    zkc::detail::NativeTypeWorkScope types(work.types, [&](uint64_t amount) {
      if (!work.charge(amount))
        throw OracleAccountingLimit{};
    });
    if (!work.charge(0))
      return error("oracle-common-limit");
    auto failure = check();
    if (failure)
      return normalizeOracleAccountingError(std::move(failure), work);
    return work.exhausted ? error("oracle-common-limit")
                          : llvm::Error::success();
  } catch (const OracleAccountingLimit &) {
    return error("oracle-common-limit");
  }
}
template <class F>
auto oracleExpectedWithWork(OracleNativeWork &work, F &&emit)
    -> decltype(emit()) {
  using Result = decltype(emit());
  try {
    zkc::detail::NativeTypeWorkScope types(work.types, [&](uint64_t amount) {
      if (!work.charge(amount))
        throw OracleAccountingLimit{};
    });
    if (!work.charge(0))
      return Result(error("oracle-common-limit"));
    auto result = emit();
    if (work.exhausted) {
      if (!result)
        return Result(normalizeOracleAccountingError(result.takeError(), work));
      return Result(error("oracle-common-limit"));
    }
    return result;
  } catch (const OracleAccountingLimit &) {
    return Result(error("oracle-common-limit"));
  }
}

// Descriptor conversion expands shared native subtrees at every occurrence.
// Reserve that expansion before the codec verifies or allocates any output.
// The interned-storage preflight deliberately has different (DAG) semantics.
// Eight units cover the visit, carrier verification, tags and output slots;
// text is scanned/copied separately. The codec retains its own depth/size caps.
template <class Value>
bool reserveOracleDescriptor(Value value, OracleNativeWork &work,
                             unsigned depth = 0) {
  if (!value || !work.charge(8 * uint64_t(depth + 1)))
    return false;
  // Logical codec depth is at most 64; a logical node may include native
  // alternative/type/identity wrappers. Public subjects additionally passed
  // the native 64-level preflight. Leave the codec's refusal distinction
  // intact.
  if (depth >= 256)
    return true;
  if (!chargeOracleNativeImmediate(work, value))
    return false;
  if constexpr (std::is_same_v<Value, mlir::Attribute>) {
    if (auto text = mlir::dyn_cast<mlir::StringAttr>(value))
      if (!work.chargeProduct(2, text.getValue().size()))
        return false;
  }
  bool good = true;
  value.walkImmediateSubElements(
      [&](mlir::Attribute child) {
        if (good)
          good = reserveOracleDescriptor(child, work, depth + 1);
      },
      [&](mlir::Type child) {
        if (good)
          good = reserveOracleDescriptor(child, work, depth + 1);
      });
  return good;
}

// Reserve recursive JSON import/verification before its allocations. Unlike
// native storage, JSON is a tree: each repeated descriptor is charged again.
inline bool reserveOracleJson(const llvm::json::Value &value,
                              OracleNativeWork &work, unsigned depth = 0) {
  if (!work.charge(8 * uint64_t(depth + 1)))
    return false;
  if (depth >= 64)
    return true;
  if (auto text = value.getAsString())
    return work.chargeProduct(2, text->size());
  if (auto array = value.getAsArray()) {
    for (const auto &child : *array)
      if (!reserveOracleJson(child, work, depth + 1))
        return false;
  } else if (auto object = value.getAsObject()) {
    for (const auto &field : *object)
      if (!work.charge(8 + llvm::StringRef(field.first).size()) ||
          !reserveOracleJson(field.second, work, depth + 1))
        return false;
  }
  return true;
}

// The result borrows unescaped wire strings. Its only production consumer
// completes the raw record check before the caller's text expires.
llvm::Expected<llvm::json::Value>
parseOracleRecordWithWork(llvm::StringRef text, OracleNativeWork &work);

inline llvm::Expected<bool>
equalOracleRecordWithWork(const llvm::json::Value &left,
                          const llvm::json::Value &right,
                          OracleNativeWork &work) {
  using namespace llvm;
  if (!work.charge())
    return error("oracle-common-limit");
  if (left.kind() != right.kind())
    return false;
  if (auto text = left.getAsString()) {
    auto other = *right.getAsString();
    if (!work.charge(std::min(text->size(), other.size())))
      return error("oracle-common-limit");
    return *text == other;
  }
  if (auto array = left.getAsArray()) {
    const auto &other = *right.getAsArray();
    if (array->size() != other.size())
      return false;
    for (auto [a, b] : zip(*array, other)) {
      auto equal = equalOracleRecordWithWork(a, b, work);
      if (!equal || !*equal)
        return equal;
    }
    return true;
  }
  if (auto object = left.getAsObject()) {
    const auto &other = *right.getAsObject();
    if (object->size() != other.size())
      return false;
    for (const auto &field : *object) {
      if (!work.charge(1 + StringRef(field.first).size()))
        return error("oracle-common-limit");
      const auto *node = other.get(field.first);
      if (!node)
        return false;
      auto equal = equalOracleRecordWithWork(field.second, *node, work);
      if (!equal || !*equal)
        return equal;
    }
    return true;
  }
  return equalNaturalJson(left, right); // Constant-size exact natural/scalar.
}
} // namespace zkc::protocol
#endif
