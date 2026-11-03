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
/// The completeness invariant of a correspondence document. Every domain row
/// and every function or oracle definition row of its snapshot is the symbol
/// of exactly one closed instance or generated definition; every realize,
/// finite, collect and map row has its computation association. Generated
/// symbols are unique, as are their purpose, part and origins, and each
/// origin names a definition of the snapshot. Every occurrence names a
/// definition of the snapshot and a site of that definition.
llvm::Error checkCorrespondenceInventory(const llvm::json::Value &);
} // namespace zkc::language
#endif
