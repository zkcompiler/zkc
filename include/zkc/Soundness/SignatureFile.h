//===- SignatureFile.h - Reading a signature ------------------*- C++ -*-===//
//
// The signature is data, and this is the only way it enters the process.
//
// Reading is fail-closed in the ordinary registry sense (docs/spec/carrier.md
// §7): a wrong envelope, an unsupported version, an unknown field at any
// depth, a duplicate key, or an enumeration spelling this build does not
// implement refuses rather than being skipped.  A machine-decider kind is the
// sharpest case — a signature may only name deciders the binary actually
// implements, so the trusted computing base cannot be widened by editing a
// file.
//
// A declaration's own revision is not written in the file; it is the
// declaration's content digest, and the reader computes it
// (SignatureEncoding.h).  A binding names its rule by identifier and the
// reader resolves the exact revision inside the same signature, so a binding
// can never be pinned to a stale digest.  References that leave the file —
// a reduction contract's digest, a path transition's revision — are written
// out, because those are the pins that mean something.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SIGNATUREFILE_H
#define ZKC_SOUNDNESS_SIGNATUREFILE_H

#include "zkc/Soundness/Signature.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace zkc::soundness {

/// Parse and freeze one signature document.
llvm::Expected<Signature> parseSignature(llvm::StringRef json,
                                         llvm::StringRef sourceName);

/// Read a signature file from disk and parse it.
llvm::Expected<Signature> loadSignatureFromFile(llvm::StringRef path);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SIGNATUREFILE_H
