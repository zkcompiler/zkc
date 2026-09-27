#ifndef ZKC_FRONTEND_PROTOCOL_H
#define ZKC_FRONTEND_PROTOCOL_H

#include "zkc/Source/Document.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace zkc::frontend {
class Analysis;
class Input;
/// Parse and elaborate authoring syntax into explicit common source. Omitted
/// static arguments are reconstructed before common admission; success is not
/// a claim that capability or resource obligations have been discharged.
/// JSON and explicit carrier text are read directly as common source; neither
/// representation creates an authored Analysis.
llvm::Expected<source::Document>
parseProtocolDocument(llvm::StringRef text,
                      llvm::StringRef filename = "<stdin>");
llvm::Expected<source::Document> parseProtocolDocument(const Input &);

/// Check complete text syntax without name resolution, type elaboration, or
/// admission. This is the editing/formatting boundary.
llvm::Error checkProtocolSyntax(llvm::StringRef text,
                                llvm::StringRef filename = "<stdin>");
/// Inspect authored syntax or the decoded records of an explicit common input.
llvm::Expected<llvm::json::Value>
inspectProtocolSyntax(llvm::StringRef text,
                      llvm::StringRef filename = "<stdin>");

/// Reconstruct source-linked call decisions for inspection. This is diagnostic
/// metadata, never part of the common source or an artifact identity. Common
/// inputs have no authored call decisions and return an empty array.
llvm::Expected<llvm::json::Array>
inspectProtocolElaboration(llvm::StringRef text, llvm::StringRef filename);
llvm::Expected<llvm::json::Array> inspectProtocolElaboration(const Analysis &);

/// Check through the common source owners, with source-linked diagnostics.
llvm::Error checkProtocolDocument(const source::Document &);
/// Print an admitted common module or a structurally valid descriptor. This is
/// a representation conversion, not participant construction or lowering.
llvm::Expected<std::string> printProtocol(const source::Content &content);
/// Format text without discarding comments, or convert JSON to readable text.
/// Formatting preserves token values, including explicit source identifiers.
/// Syntactically complete text need not pass admission; incomplete syntax is an
/// error. JSON-to-text retains printProtocol's admitted-only module contract.
llvm::Expected<std::string>
formatProtocol(llvm::StringRef text, llvm::StringRef filename = "<stdin>");
} // namespace zkc::frontend

#endif
