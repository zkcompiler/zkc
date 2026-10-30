#ifndef ZKC_TRANSLATION_ENTRY_NATIVE_H
#define ZKC_TRANSLATION_ENTRY_NATIVE_H
#include "zkc/Translation/Entry.h"
namespace zkc::language::entry_detail {
struct Calculation {
  NumericalFragment fragment;
  std::vector<ValueId> inputs;
};
/// Extract exactly one checked source action with its ordered distinct
/// captures. Native emission and source-side comparison share only this source
/// operation; the emitted numerical module is independently checked against it.
llvm::Expected<Calculation> extractCalculation(const Declaration &owner,
                                               const Body &body,
                                               const Operation &source,
                                               unsigned ordinal);
struct NativeHost {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  std::vector<NumericalFragment> calculations;
};
llvm::Expected<NativeHost> emitNativeHost(const ClosedEntry &,
                                          mlir::MLIRContext &, const Limits &);
llvm::Expected<llvm::json::Array> reconstructNativeHost(mlir::ModuleOp,
                                                        const Limits &);
} // namespace zkc::language::entry_detail
#endif
