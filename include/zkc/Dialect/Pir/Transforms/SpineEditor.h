//===- SpineEditor.h - spine editing utilities ------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_TRANSFORMS_SPINEEDITOR_H
#define ZKC_DIALECT_PIR_TRANSFORMS_SPINEEDITOR_H

#include "zkc/Dialect/Pir/PirOps.h"

#include <string>

namespace zkc {
namespace pir {

/// Editing utilities over one OPEN protocol's spine (transforms never
/// touch sealed material — the rewrite fence stands; the edited
/// result is judged by a fresh seal). The utilities keep the token
/// thread spliced: the thread is the carrier's ≤, and a transform that
/// broke it would author an unverifiable body, not a different protocol.
class SpineEditor {
public:
  explicit SpineEditor(ProtocolOp protocol)
      : body(protocol.getBody().front()) {}

  /// Erases one token-threading spine event, splicing the thread
  /// around it. The event's value handle must already be unused.
  void eraseEvent(mlir::Operation *event);

  /// Deterministic content-derived name component: the first
  /// `hexChars` hex digits of an anchor reference (`sha256:<hex>`),
  /// so synthesized labels and domains are functions of content,
  /// never of visitation order.
  static std::string contentTag(llvm::StringRef anchorRef,
                                unsigned hexChars);

  mlir::Block &body;
};

} // namespace pir
} // namespace zkc

#endif // ZKC_DIALECT_PIR_TRANSFORMS_SPINEEDITOR_H
