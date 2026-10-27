#ifndef ZKC_COMPILER_SOURCECORRESPONDENCE_H
#define ZKC_COMPILER_SOURCECORRESPONDENCE_H
#include "zkc/Compiler/Language.h"

namespace zkc::language {
/// Written syntax and bounded source/row proposals for this exact checked
/// protocol original. The structured unit and its row associations are emitted
/// together. No proposal grants admission or proves source correspondence.
llvm::Expected<std::string> exportSourceCorrespondence(const CheckedOriginal &,
                                                       const Limits & = {});
/// Compare a publication with the retained checked original's canonical export.
/// This is an integrity check, not the independent source-correspondence proof.
llvm::Error checkSourceCorrespondenceExport(const CheckedOriginal &,
                                            llvm::StringRef,
                                            const Limits & = {});
} // namespace zkc::language
#endif
