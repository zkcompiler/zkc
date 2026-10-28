#ifndef ZKC_LANGUAGE_WRITTENSOURCE_H
#define ZKC_LANGUAGE_WRITTENSOURCE_H
#include "Internal.h"
namespace zkc::language::detail {
/// Parser records before generated declarations, inferred contracts and names
/// enter the mutable checking tree. They never authorize an elaboration.
struct WrittenSources {
  std::vector<SyntaxDeclaration> modules;
};
llvm::Expected<std::shared_ptr<WrittenSources>>
retainWrittenHeaders(llvm::ArrayRef<SyntaxDeclaration>, Work &);
llvm::Error retainWrittenBodies(WrittenSources &,
                                llvm::ArrayRef<SyntaxDeclaration *>, Work &);
} // namespace zkc::language::detail
#endif
