#ifndef ZKC_LANGUAGE_BUILTINS_H
#define ZKC_LANGUAGE_BUILTINS_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Language/Types.h"
namespace zkc::language {
/// Library-facing native data types. Constructor formation is catalog-owned;
/// source nominals and managed service roots cannot be erased through this API.
bool isNativeData(const Type &);
bool isDomainSort(llvm::StringRef);
/// Resolve a catalog association, retaining a symbolic projection when needed.
llvm::Expected<Type> domainMember(const Type &, llvm::StringRef member);
llvm::Expected<std::string> kernelArgument(const Type &, llvm::StringRef sort);
/// Formal values are eliminated before execution and have no native data codec.
llvm::Expected<Type> formalType(llvm::StringRef, llvm::ArrayRef<Type>);
llvm::Expected<Type> builtinType(llvm::StringRef, llvm::ArrayRef<Type>);
llvm::Expected<protocol::BoundType> builtinLayout(const Type &);
/// Encode the explicitly supplied roots using the installed contract's kinds.
llvm::Expected<std::vector<std::string>>
kernelArguments(llvm::StringRef contract, llvm::ArrayRef<Type>);
} // namespace zkc::language
#endif
