//===- SpineEditor.cpp - spine editing utilities ----------------*- C++ -*-===//
#include "zkc/Dialect/Pir/Transforms/SpineEditor.h"

using namespace mlir;
using namespace zkc::pir;

void SpineEditor::eraseEvent(Operation *event) {
  auto member = cast<ProtocolMemberOpInterface>(event);
  Value in = member.getThreadIn();
  Value out = member.getThreadOut();
  assert(in && out && "eraseEvent takes a token-threading event");
  out.replaceAllUsesWith(in);
  event->erase();
}

std::string SpineEditor::contentTag(llvm::StringRef anchorRef,
                                    unsigned hexChars) {
  anchorRef.consume_front("sha256:");
  return anchorRef.take_front(hexChars).str();
}
