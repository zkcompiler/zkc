#ifndef ZKC_LIB_COMPILER_LANGUAGE_PACKAGE_READER_H
#define ZKC_LIB_COMPILER_LANGUAGE_PACKAGE_READER_H
#include "zkc/Compiler/LanguageInterface.h"
namespace zkc::language::detail {
/// Decoded package shape and captured interface; artifact admission is
/// separate.
struct PackagedEntry {
  LanguageInterface interface;
  std::string artifact;
};
llvm::Expected<PackagedEntry> readPackagedEntry(llvm::StringRef,
                                                const Limits &);
} // namespace zkc::language::detail
#endif
