#ifndef ZKC_FRONTEND_DEPENDENCIES_H
#define ZKC_FRONTEND_DEPENDENCIES_H
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Relation/Authoring.h"
namespace zkc::frontend {
/// Capture explicit roots and their declared modules/assets. Logical modules
/// use root-relative paths (a::b -> a/b.pir); assets use the declaring file's
/// parent. All child paths must remain under their canonical library root.
/// File IDs enumerate library/source order, with the application first.
llvm::Expected<ProjectInput>
captureProject(Input application, llvm::ArrayRef<Input> libraryRoots = {});

/// Pure shared relation decoder. The caller supplies the declaration's name
/// and location after decoding; this function never reads a file.
llvm::Expected<source::RelationDeclaration>
decodeRelationAsset(llvm::StringRef family, llvm::StringRef bytes);

/// Explicit bounded loading boundary. Callback returns owned bytes and must
/// honor the requested maximum. Parsing/formatting never invoke this API.
using AssetResolver = llvm::function_ref<llvm::Expected<std::string>(
    llvm::StringRef path, size_t maximumBytes)>;
llvm::Expected<source::Document> loadProtocolDocument(llvm::StringRef text,
                                                      llvm::StringRef filename,
                                                      AssetResolver resolver);
/// Constrained filesystem resolver rooted at the source file's parent
/// directory. Relative regular files only; canonical containment rejects
/// symlink escapes. A source with no file has no directory to resolve against.
llvm::Expected<source::Document> loadProtocolFile(const Input &source);
} // namespace zkc::frontend
#endif
