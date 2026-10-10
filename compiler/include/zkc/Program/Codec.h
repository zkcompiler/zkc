#ifndef ZKC_PROGRAM_CODEC_H
#define ZKC_PROGRAM_CODEC_H
#include "zkc/Program/Model.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
namespace zkc::program {
/// Raw and compact-encoded participant program ceiling. Structural and
/// executable admission retain their independent count and depth limits.
inline constexpr size_t artifactByteLimit = 4 * 1024 * 1024;
inline constexpr size_t artifactNodeLimit = 400000;
/// Parse under the Program byte ceiling, then decode the current carrier.
llvm::Expected<Participants> parse(llvm::StringRef);
/// Read only zkc.program/0 physical programs. Structural decoding does not
/// replace semantic admission.
llvm::Expected<Participants> decode(const llvm::json::Value &);
/// Precondition: checkStructure has succeeded for this unchanged program.
/// Physical-only, preserving the zkc.program/0 carrier and declaration order.
llvm::json::Value encode(const Participants &);
llvm::Error checkStructure(const Participants &);
} // namespace zkc::program
#endif
