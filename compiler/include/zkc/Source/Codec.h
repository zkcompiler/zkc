#ifndef ZKC_SOURCE_CODEC_H
#define ZKC_SOURCE_CODEC_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <map>

namespace zkc::source {

/// Coordinates belong only to this interchange encoding, not compiler nodes
/// or persistent identity. Optional maps serve diagnostics and inspection.
using Path = std::vector<size_t>;
using SourceMap = std::map<Path, Span>;
using RecordMap = std::map<Path, const Node *>;

/// Decode structure, preserving declaration order and unresolved names. This
/// does not resolve symbols, infer types, admit execution or verify security.
/// Reject malformed records and resource exhaustion at this boundary.
/// On failure, optionally return the enclosing record's diagnostic span.
llvm::Expected<Content> decode(const llvm::json::Value &,
                               const SourceMap &locations = {},
                               std::optional<Span> *failure = nullptr);

/// The positional format remains only an interchange with independent readers
/// and exact-source identity. Metadata is omitted from the serialized value.
/// Precondition: checkStructure succeeded for the unchanged enclosing content
/// (including when encoding one of its GenericFunction records). Encoding is
/// not an admission API. Broken relation invariants terminate with an internal
/// diagnostic in release builds too; fallible callers use checkStructure first.
/// On that domain, decode(encode(x)) preserves authored
/// fields except diagnostic locations. Checked relation-generated functions and
/// bindings are derived from the retained immutable asset/view declarations;
/// decoding reconstructs them in canonical generated order. The resource budget
/// is compact encoded bytes, not sizeof the owning C++ model.
llvm::json::Value encode(const Content &, RecordMap *records = nullptr);
llvm::json::Value encode(const Module &, RecordMap *records = nullptr);
llvm::json::Value encode(const Participants &, RecordMap *records = nullptr);
llvm::json::Value encode(const Construction &, RecordMap *records = nullptr);
llvm::json::Value encode(const GenericFunction &, RecordMap *records = nullptr);

/// Structural/resource checks for non-text authors. Semantic checks remain in
/// the protocol/generic owners; callers cannot bypass limits with a builder.
llvm::Error checkStructure(const Content &);
llvm::Error checkStructure(const Module &);
llvm::Error checkStructure(const Participants &);
llvm::Error checkStructure(const Construction &);

} // namespace zkc::source
#endif
