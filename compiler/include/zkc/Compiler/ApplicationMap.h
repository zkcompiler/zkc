#ifndef ZKC_COMPILER_APPLICATIONMAP_H
#define ZKC_COMPILER_APPLICATIONMAP_H

#include "mlir/IR/MLIRContext.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <optional>
#include <string>

namespace zkc::language {
class CheckedOriginal;
}
namespace zkc::protocol {
/// A supplied `zkc.source-correspondence/0` for written links: its exact bytes
/// and, when the caller holds it, the checked original it was exported from.
struct CorrespondenceInput {
  llvm::StringRef bytes;
  const language::CheckedOriginal *checked = nullptr;
};
/// How far the written links of a checked map can be trusted. `Absent`: no
/// correspondence. `Conditional`: links follow the supplied bytes only.
/// `Checked`: the checked original's own export is those bytes, so the links
/// are authoritative navigation; they are never source-correspondence
/// evidence.
enum class WrittenStatus { Absent, Conditional, Checked };

/// Propose an untrusted zkc.application-map/0 for these exact MLIR artifacts.
/// Both artifacts must admit the complete structured-source profile and select
/// entry. Supports application/helper expansion with retained shared helpers
/// and port role restrictions. Unsupported rewrites refuse; diagnostic
/// locations never authorize an association. With a supplied correspondence,
/// each application's written link comes from its occurrence; nothing is
/// inferred from spans or symbol spellings.
llvm::Expected<std::string>
produceApplicationMap(llvm::StringRef originalBytes,
                      llvm::StringRef candidateBytes, llvm::StringRef entry,
                      mlir::MLIRContext &context,
                      std::optional<CorrespondenceInput> correspondence = {});

/// Independently admit both actual artifacts, check the complete map and check
/// native preparation value correspondence. This reader does not run expansion
/// or reproduce the producer's map. Success establishes only the bounded
/// original-to-prepared structured boundary, not arbitrary relocation, source
/// elaboration, participant projection or executable-byte correspondence. A
/// supplied correspondence is read strictly; written links are rederived
/// from it and the returned status says whether they are authoritative.
llvm::Expected<WrittenStatus>
checkApplicationMap(llvm::StringRef originalBytes,
                    llvm::StringRef candidateBytes, llvm::StringRef entry,
                    llvm::StringRef mapBytes, mlir::MLIRContext &context,
                    std::optional<CorrespondenceInput> correspondence = {});
} // namespace zkc::protocol
#endif
