#include "zkc/Protocol/Admission.h"
#include "../Syntax/Lexer.h"
#include "Admission.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
namespace zkc::frontend {
Error checkSourceContent(const source::Content &content,
                         const source::Node **failureLocation) {
  if (failureLocation)
    *failureLocation = nullptr;
  if (auto e = source::checkStructure(content))
    return e;
  if (const auto *module = std::get_if<source::Module>(&content)) {
    if (module->isLibrary()) {
      auto closed = generic::elaborateLibrary(*module, failureLocation);
      return closed ? Error::success() : closed.takeError();
    }
    return protocol::admit(content, false, failureLocation);
  }
  if (std::holds_alternative<source::Participants>(content))
    return protocol::admit(content, false, failureLocation);
  const auto &construction = std::get<source::Construction>(content);
  StringRef acceptance = construction.acceptance;
  if (acceptance.empty() ||
      (acceptance.size() > 1 && acceptance.front() == '0') ||
      !all_of(acceptance, [](char c) { return isDigit(c); })) {
    if (failureLocation)
      *failureLocation = &construction;
    return zkc::error("source-shape");
  }
  return Error::success();
}

Error checkProtocolDocument(const source::Document &document) {
  const source::Node *failure = nullptr;
  if (auto e = checkSourceContent(document.root(), &failure)) {
    auto span = document.span(failure);
    auto file = span ? span->file : 0;
    return diagnostic(document.text(file), document.filename(file),
                      span ? span->offset : 0, toString(std::move(e)),
                      "source admission failed");
  }
  return Error::success();
}

} // namespace zkc::frontend
