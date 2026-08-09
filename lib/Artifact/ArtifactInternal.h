//===- ArtifactInternal.h - internal PIR artifact access -------*- C++ -*-===//
#ifndef ZKC_LIB_ARTIFACT_ARTIFACTINTERNAL_H
#define ZKC_LIB_ARTIFACT_ARTIFACTINTERNAL_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/IR/OwningOpRef.h"
#include "zkc/Artifact/Artifact.h"

#include <memory>
#include <utility>

namespace zkc::artifact::detail {

/// An independent raw copy used by representation-specific consumers. Its
/// context is retained with the module, so the clone remains valid after the
/// admitted source capability is destroyed. The artifact-owned context keeps
/// the sealed-pattern guard: consumers read this root or reopen an editable
/// `pir.protocol` sibling before applying rewrite patterns.
class MutablePirArtifact {
public:
  MutablePirArtifact(MutablePirArtifact &&) = default;
  MutablePirArtifact &operator=(MutablePirArtifact &&) = delete;

  mlir::ModuleOp module() const { return *module_; }
  pir::SealedOp sealed() const;

private:
  MutablePirArtifact(std::shared_ptr<mlir::MLIRContext> context,
                     mlir::OwningOpRef<mlir::ModuleOp> module)
      : context_(std::move(context)), module_(std::move(module)) {}

  std::shared_ptr<mlir::MLIRContext> context_;
  mlir::OwningOpRef<mlir::ModuleOp> module_;

  friend class ArtifactAccess;
};

/// Internal representation access. A clone is raw input for a read or reopen
/// operation; it carries no admitted authority. Any direct mutation of the
/// independent copy cannot change its source capability.
class ArtifactAccess {
public:
  static MutablePirArtifact cloneForReopen(const AdmittedPirArtifact &artifact);
};

} // namespace zkc::artifact::detail

#endif // ZKC_LIB_ARTIFACT_ARTIFACTINTERNAL_H
