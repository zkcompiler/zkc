//===- Passes.h - Protocol IR passes ----------------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_TRANSFORMS_PASSES_H
#define ZKC_DIALECT_PIR_TRANSFORMS_PASSES_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"

namespace zkc {
namespace pir {

#define GEN_PASS_DECL
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

#define GEN_PASS_REGISTRATION
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

} // namespace pir
} // namespace zkc

#endif // ZKC_DIALECT_PIR_TRANSFORMS_PASSES_H
