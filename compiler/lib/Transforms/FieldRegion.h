#ifndef ZKC_TRANSFORMS_FIELD_REGION_H
#define ZKC_TRANSFORMS_FIELD_REGION_H

#include "LaneRealization.h"

namespace zkc::mathematical {
/// Borrowed, fully admitted source slice used only during construction.
struct FieldRegionSource {
  mlir::Block &body;
  const llvm::DenseMap<mlir::Value, LaneInput> &bindings;
  const llvm::DenseSet<mlir::Value> &live;
  llvm::ArrayRef<mlir::Value> terms;
  llvm::ArrayRef<LaneInput> slots;
  MathematicalIdentity combine;
};
void registerFieldRegionDialects(mlir::DialectRegistry &);
/// A private implementation region. Its index argument is an abstract common
/// extent, not a cast of the source's checked u64 indices. Rank-zero operands
/// denote scalar broadcasts and rank-one operands denote admitted columns.
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
createFieldRegion(const FieldRegionSource &, mlir::Type field);

/// Independently read the actual region, including all unused operations and
/// inputs. Only the declared parallel identity/broadcast indexing is admitted.
/// Destination contents, outer captures and target attributes are not premises.
llvm::Expected<ring::Expression> readFieldRegion(mlir::ModuleOp,
                                                 llvm::StringRef field,
                                                 llvm::ArrayRef<bool> lanes);
llvm::Error compareFieldExpressions(const ring::Expression &source,
                                    const ring::Expression &candidate);
llvm::Expected<ring::Expression> checkFieldRegion(const LaneFormula &);
} // namespace zkc::mathematical
#endif
