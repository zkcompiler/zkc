#ifndef ZKC_COMPILER_INSPECTION_H
#define ZKC_COMPILER_INSPECTION_H

#include "zkc/Source/Document.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace zkc::frontend {
class Analysis;
}
namespace zkc {
/// One checked inspection path for textual and programmatic source clients.
/// Pass the retained analysis for a multi-file project. Without it, the
/// optional elaborated-call report re-analyzes only the document's root
/// spelling.
llvm::Expected<llvm::json::Value>
inspectSource(const source::Document &, const frontend::Analysis * = nullptr);
llvm::Error sourceDiagnostic(const source::Document &, llvm::Error,
                             const source::Node *record = nullptr);
} // namespace zkc

#endif
