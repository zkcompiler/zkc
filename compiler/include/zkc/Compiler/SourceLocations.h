#ifndef ZKC_COMPILER_SOURCELOCATIONS_H
#define ZKC_COMPILER_SOURCELOCATIONS_H

#include "mlir/IR/Location.h"
#include "zkc/Source/Document.h"

namespace zkc {
/// Diagnostic provenance carried directly by typed source nodes. No tree
/// correspondence is inferred. The document snapshot keeps spelling alive.
class SourceLocations {
  source::Document document;
  mlir::MLIRContext *context;
  mlir::Location fallback;

public:
  SourceLocations(const source::Document &, mlir::MLIRContext &);
  mlir::Location operator()(const source::Node &) const;
};
} // namespace zkc

#endif
