//===- ExecutionProfile.cpp - profile selection by name ---------*- C++ -*-===//
// The one selection vocabulary: every driver resolves a profile name
// here, so the set of selectable supplier sets cannot drift between
// tools and the unknown-name refusal has one spelling.
//===----------------------------------------------------------------------===//

#include "zkc/Interpreter/ExecutionProfile.h"

#include "llvm/ADT/Twine.h"

namespace zkc {
namespace interpreter {

llvm::Expected<const ExecutionProfile &> selectProfile(llvm::StringRef name) {
  if (name == "toy")
    return toyProfile();
  if (name == "plonky3")
    return plonky3Profile();
  if (name == "toy-cheat")
    return toyCheatProfile();
  return llvm::createStringError(llvm::Twine("unknown execution profile '") +
                                 name + "'");
}

} // namespace interpreter
} // namespace zkc
