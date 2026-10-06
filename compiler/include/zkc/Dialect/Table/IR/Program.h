#ifndef ZKC_DIALECT_TABLE_IR_PROGRAM_H
#define ZKC_DIALECT_TABLE_IR_PROGRAM_H
#include "zkc/Interfaces/SourceLibrary.h"
namespace zkc {
/// Resolve the library belonging to a checked finite-table context.
llvm::Expected<const SourceLibraryInterface *>
resolveProgramLibrary(mlir::Operation *);
namespace table {
struct ProgramContext {
  llvm::SmallVector<mlir::Type> inputs;
  mlir::Type result;
  const SourceLibraryInterface *library;
};
llvm::Expected<ProgramContext> readProgramContext(const llvm::json::Value &,
                                                  mlir::Builder &);
/// Read and validate the complete program body after MLIR local invariants.
/// The finite-table model has its own recursive JSON expression vocabulary.
llvm::Expected<llvm::json::Value> readProgramBody(mlir::Operation *);
} // namespace table
} // namespace zkc
#endif
