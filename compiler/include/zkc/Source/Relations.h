#ifndef ZKC_SOURCE_RELATIONS_H
#define ZKC_SOURCE_RELATIONS_H

#include "zkc/Relation/AIR.h"
#include "zkc/Relation/Matrices.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/RelationLowering.h"
#include <map>

namespace zkc::relation {
struct DependencyLimits {
  static constexpr size_t count = 64;
  static constexpr size_t bytes = 128 * 1024 * 1024;
  static constexpr size_t snapshotBytes = bytes + 1024 * 1024;
};
llvm::Expected<llvm::json::Value>
readSnapshotJSON(llvm::StringRef,
                 size_t maximumBytes = DependencyLimits::snapshotBytes);
/// Decode captured relation bytes without filesystem or frontend dependencies.
/// The caller supplies the declaration name and location after decoding.
llvm::Expected<source::RelationDeclaration> decodeAsset(llvm::StringRef family,
                                                        llvm::StringRef bytes);
/// Canonical content identity, including nominal field and exact ordered
/// layout.
std::string identity(const source::RelationDeclaration &);
llvm::Expected<source::Module>
lowerAIRArithmetic(const AIR &, llvm::StringRef prefix, uint32_t height);
llvm::Expected<source::Module> generateView(const source::Module &,
                                            const source::RelationView &);
/// Append typed generated declarations. Refuse every collision before mutation.
llvm::Error materializeViews(source::Module &);
/// Verify exact generated signatures/bodies/bindings, then remove generated
/// portions for source serialization/accounting. Never infers trust from names.
llvm::Expected<source::Module> authoredSource(const source::Module &);
llvm::json::Value encodeDeclarations(const source::Module &);
llvm::Error decodeDeclarations(const llvm::json::Value &, source::Module &);
/// A relation captured as a static association also enters type identities
/// (as the canonical compact descriptor text inside a local variant nominal).
/// Only the declaration table rebuilds view code, so every relation named in a
/// type identity of the snapshot's protocol must be one of the table's own.
llvm::Error checkEmbeddedRelations(const llvm::json::Value &protocol,
                                   const source::Module &);
llvm::Expected<std::map<std::string, std::pair<std::string, std::string>>>
associations(const source::Module &);
/// Verify generated views, then explicitly lower their immutable ownership
/// records to ordinary arithmetic. Function origins and data checks survive.
/// This is a native compiler transformation, not an independent adequacy proof.
llvm::Expected<source::Module> materializeRelations(const source::Module &);
} // namespace zkc::relation
#endif
