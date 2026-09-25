#ifndef ZKC_PROTOCOL_INSTANTIATION_H
#define ZKC_PROTOCOL_INSTANTIATION_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace zkc::generic {

/// Check all original definitions and configurations through the existing
/// requirements/inference engine, then instantiate demanded definitions.
/// The closed module retains logical origins independently from generated code
/// symbols. Unused partial configurations emit no executable body. Failure
/// nodes borrow the immutable original input, including failures while
/// admitting generated specializations.
llvm::Expected<source::Module>
elaborateLibrary(const source::Module &,
                 const source::Node **failureLocation = nullptr);

/// Prepare the same closed source while retaining each demanded configuration's
/// name. Construction uses these names as source locations; code sharing must
/// not replace them with generated callable names. Failure nodes borrow the
/// original input, which remains authoritative including unused declarations.
llvm::Expected<source::Module>
prepareLibrary(const source::Module &,
               const source::Node **failureLocation = nullptr);

/// Report checked requirements, resolved configurations, demanded
/// specializations and closed source. No implementation search is performed or
/// implied. Failure nodes borrow the original input.
llvm::Expected<llvm::json::Value>
inspectLibrary(const source::Module &,
               const source::Node **failureLocation = nullptr);

} // namespace zkc::generic

#endif
