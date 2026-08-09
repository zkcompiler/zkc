//===- KappaView.h - reading the construction profile -----------*- C++ -*-===//
// The construction profile κ is a free-form dictionary with a closed
// axis set (SealBattery zkc-E225). Several judgments read the same
// facts from it — the sponge name, the iv, and per-class codecs — and
// FS pricing derives the same vocabulary keys from them. One spelling
// here keeps every consumer's reading identical;
// a wrong-typed axis reads as absent (checkKappa already named the
// type error at the container).
//===----------------------------------------------------------------------===//
#ifndef ZKC_DIALECT_PIR_KAPPAVIEW_H
#define ZKC_DIALECT_PIR_KAPPAVIEW_H

#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

#include <optional>

namespace zkc {
namespace pir {

inline llvm::StringRef
kappaStringAxis(std::optional<mlir::DictionaryAttr> kappa,
                llvm::StringRef axis) {
  if (!kappa)
    return {};
  auto entry = kappa->getNamed(axis);
  auto value = entry ? mlir::dyn_cast<mlir::StringAttr>(entry->getValue())
                     : mlir::StringAttr();
  return value ? value.getValue() : llvm::StringRef();
}

inline llvm::StringRef
kappaSpongeName(std::optional<mlir::DictionaryAttr> kappa) {
  return kappaStringAxis(kappa, "sponge");
}

inline llvm::StringRef kappaIv(std::optional<mlir::DictionaryAttr> kappa) {
  return kappaStringAxis(kappa, "iv");
}

/// The codec a payload class routes through (empty when unmapped or
/// wrong-typed). Challenge producers retain their semantic payload class, so
/// squeeze consumers select the codec for that event's class rather than a
/// distinguished global challenge class.
inline llvm::StringRef
kappaCodecName(std::optional<mlir::DictionaryAttr> kappa,
               llvm::StringRef payloadClass) {
  if (!kappa)
    return {};
  auto codecsEntry = kappa->getNamed("codecs");
  auto dict = codecsEntry
                  ? mlir::dyn_cast<mlir::DictionaryAttr>(codecsEntry->getValue())
                  : mlir::DictionaryAttr();
  if (!dict)
    return {};
  auto entry = dict.getNamed(payloadClass);
  auto value = entry ? mlir::dyn_cast<mlir::StringAttr>(entry->getValue())
                     : mlir::StringAttr();
  return value ? value.getValue() : llvm::StringRef();
}

/// Every codec name kappa consumes, sorted and deduplicated (several
/// payload classes may route through one codec). These are the
/// entries whose registry content the artifact pins unconditionally
/// (docs/spec/kernel.md §8): a codec's decode width is transcript bytes and
/// proof ABI, so the content is identity-bearing whether or not any
/// FS hop prices it. Consumption therefore follows pinning. Wrong-typed
/// entries read as absent (checkKappa already named the type error at the
/// container).
inline llvm::SmallVector<llvm::StringRef, 4>
kappaConsumedCodecNames(std::optional<mlir::DictionaryAttr> kappa) {
  llvm::SmallVector<llvm::StringRef, 4> names;
  if (!kappa)
    return names;
  auto codecsEntry = kappa->getNamed("codecs");
  auto dict =
      codecsEntry
          ? mlir::dyn_cast<mlir::DictionaryAttr>(codecsEntry->getValue())
          : mlir::DictionaryAttr();
  if (!dict)
    return names;
  for (mlir::NamedAttribute named : dict)
    if (auto value = mlir::dyn_cast<mlir::StringAttr>(named.getValue()))
      if (!value.getValue().empty())
        names.push_back(value.getValue());
  llvm::sort(names);
  names.erase(llvm::unique(names), names.end());
  return names;
}

} // namespace pir
} // namespace zkc

#endif // ZKC_DIALECT_PIR_KAPPAVIEW_H
