#ifndef ZKC_COMPILER_STRUCTUREDSOURCE_H
#define ZKC_COMPILER_STRUCTUREDSOURCE_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/Error.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::protocol {
/// An address follows array indices in the exact exported snapshot. A row can
/// be emitted more than once from the same original operation (closed regions)
/// or derived from an operation (computation declarations).
enum class StructuredSourceDerivation { Direct, ScopedExecution, Computation };
struct StructuredSourceTextRange {
  /// UTF-8 byte offsets of the original operation name, exclusive at the end.
  unsigned begin, end;
  /// One-based line and column in the supplied original, not its loc attribute.
  unsigned line, column;
};
struct StructuredSourceAssociation {
  std::vector<unsigned> row;
  std::string operation;
  StructuredSourceDerivation derivation;
  /// Absent for a parser-inserted operation without a written definition.
  std::optional<StructuredSourceTextRange> original;
};
struct StructuredSource {
  /// Complete bounded JSON file, including its trailing newline.
  std::string bytes;
  /// Proposals produced with the rows, outside the admitted snapshot and its
  /// identity. They neither authorize admission nor prove denotation.
  std::vector<StructuredSourceAssociation> associations;
};
/// Preparation materializes nested occurrence paths up to 4096 UTF-8 bytes.
/// This profile changes only site bounds; all other admission and export limits
/// remain identical. Selecting it is not evidence that preparation is correct.
enum class StructuredSourceProfile { Original, Prepared };
/// Verify the whole supplied original, then export the bounded structured
/// profile without preparation, projection or helper expansion. Associations
/// address the actual rows of this export, including reconstructed regions.
/// The digest binds the supplied bytes; it is not a correspondence proof.
llvm::Expected<StructuredSource> exportStructuredSource(
    llvm::StringRef originalBytes, llvm::StringRef symbol,
    mlir::MLIRContext &context,
    StructuredSourceProfile profile = StructuredSourceProfile::Original);
} // namespace zkc::protocol
#endif
