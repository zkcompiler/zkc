#ifndef ZKC_TRANSLATION_ENTRY_H
#define ZKC_TRANSLATION_ENTRY_H
#include "zkc/Language/Layout.h"
#include "zkc/Translation/Language.h"
#include "llvm/Support/JSON.h"
namespace zkc::language {
struct NumericalFragment {
  std::string id;
  Declaration definition;
};
struct HostPlan {
  llvm::json::Array functions, signatures;
  std::vector<NumericalFragment> calculations;
};
struct HostAnalysis {
  std::vector<NumericalFragment> calculations;
  llvm::json::Array functions;
  Correspondence correspondence;
};
/// Compare independent source and SSA views and retain checked compilation
/// inputs.
llvm::Expected<HostAnalysis>
analyzeHostOriginal(const ClosedEntry &, mlir::ModuleOp, const Limits & = {});
std::string entryDeploymentId(HostInvocation::Kind, llvm::StringRef target,
                              llvm::ArrayRef<Type> arguments);
llvm::json::Value encodeEntrySchema(const Layout &);
llvm::Expected<HostPlan> planHost(const ClosedEntry &, const Limits & = {});
llvm::Expected<std::string>
emitHostOriginal(const ClosedEntry &, mlir::MLIRContext &, const Limits & = {});
llvm::Expected<Correspondence>
compareHostOriginal(const ClosedEntry &, mlir::ModuleOp, const Limits & = {});
llvm::Expected<std::vector<Declaration>>
numericalDefinitions(const ClosedEntry &, const Declaration &);
llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
buildNumericalOriginal(const ClosedEntry &, const Declaration &,
                       mlir::MLIRContext &, const Limits & = {});
llvm::Expected<Correspondence> compareNumericalOriginal(const ClosedEntry &,
                                                        const Declaration &,
                                                        mlir::ModuleOp,
                                                        const Limits & = {});
/// Source-independent reconstruction of Host functions from actual SSA.
llvm::Expected<llvm::json::Array> readHostFunctions(mlir::ModuleOp,
                                                    const Limits & = {});
} // namespace zkc::language
#endif
