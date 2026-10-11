#ifndef ZKC_TRANSFORMS_NESTEDCONTRACTIONVERIFICATION_H
#define ZKC_TRANSFORMS_NESTEDCONTRACTIONVERIFICATION_H
#include "AlgorithmSupport.h"
namespace zkc::nested {
mlir::LogicalResult checkFiniteCollections(
    mlir::ModuleOp source, mlir::ModuleOp candidate,
    const protocol::detail::AlgorithmExpansionRecord &input,
    protocol::detail::AlgorithmExpansionRecord &expected,
    protocol::detail::AlgorithmExpansionRecord *output = nullptr);
} // namespace zkc::nested
#endif
