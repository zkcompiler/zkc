#ifndef ZKC_COMPILER_APPLICATIONMAP_H
#define ZKC_COMPILER_APPLICATIONMAP_H

#include "mlir/IR/MLIRContext.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <string>

namespace zkc::protocol {
/// Propose an untrusted zkc.application-map/0 for these exact MLIR artifacts.
/// Both artifacts must admit the complete structured-source profile and select
/// entry. Supports application/helper expansion with retained shared helpers
/// and port role restrictions. Unsupported rewrites refuse; diagnostic
/// locations never authorize an association. No frontend provenance is
/// inferred.
llvm::Expected<std::string>
produceApplicationMap(llvm::StringRef originalBytes,
                      llvm::StringRef candidateBytes, llvm::StringRef entry,
                      mlir::MLIRContext &context);

/// Independently admit both actual artifacts, check the complete map and check
/// native preparation value correspondence. This reader does not run expansion
/// or reproduce the producer's map. Success establishes only the bounded
/// original-to-prepared structured boundary, not arbitrary relocation, source
/// elaboration, participant projection or executable-byte correspondence.
llvm::Error checkApplicationMap(llvm::StringRef originalBytes,
                                llvm::StringRef candidateBytes,
                                llvm::StringRef entry, llvm::StringRef mapBytes,
                                mlir::MLIRContext &context);
} // namespace zkc::protocol
#endif
