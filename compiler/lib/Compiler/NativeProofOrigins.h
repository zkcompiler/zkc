#ifndef ZKC_LIB_COMPILER_NATIVE_PROOF_ORIGINS_H
#define ZKC_LIB_COMPILER_NATIVE_PROOF_ORIGINS_H
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OwningOpRef.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/Error.h"
#include <string>
#include <variant>
#include <vector>
namespace zkc::mathematical {
class RealizedProtocol;
}
namespace zkc::detail {
// Structural boundaries and oracle provenance are not encodable wire events.
struct NativeRepeatOrigin {};
struct NativeBranchOrigin {};
struct NativeOracleOrigin {};
struct NativeSourceOrigin {
  std::string protocol, site;
  std::variant<protocol::NativeQueryOrigin, protocol::NativeMessageOrigin,
               protocol::NativeStartOrigin, NativeRepeatOrigin,
               NativeBranchOrigin, NativeOracleOrigin>
      event;
  std::vector<protocol::NativeOriginStep> steps;
};
// Project only actual wire events to the shared typed byte boundary.
llvm::Expected<protocol::NativeOriginTemplate>
exportNativeSourceOrigin(llvm::StringRef entry, const NativeSourceOrigin &);
// The exact independent candidate inspected by the origin producer. Owning the
// snapshot grants no admission authority; mutation invalidates its origins.
// The caller keeps the MLIR context alive for the snapshot's entire lifetime.
struct RealizedNativeOrigins {
  mlir::OwningOpRef<mlir::ModuleOp> candidate;
  llvm::StringMap<NativeSourceOrigin> origins;
};
// The record is read only through its immutable checked owner. Generated
// occurrences acquire source associations, never authority from helper names.
// Return the candidate and its origins only after every origin check succeeds.
llvm::Expected<RealizedNativeOrigins>
realizedNativeOrigins(const mathematical::RealizedProtocol &,
                      llvm::StringRef entry,
                      const llvm::StringMap<NativeSourceOrigin> &authored);
} // namespace zkc::detail
#endif
