#ifndef ZKC_FRONTEND_CARRIER_READER_H
#define ZKC_FRONTEND_CARRIER_READER_H

#include "zkc/Source/Model.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace zkc::frontend::carrier {
/// Decode exact common records, without authored resolution or elaboration.
/// The caller must apply common checking/admission before using these records.
llvm::Expected<source::Content> readCarrier(llvm::StringRef text,
                                            llvm::StringRef filename);
} // namespace zkc::frontend::carrier

#endif
