#ifndef ZKC_FRONTEND_SYNTAX_CAPTURES_H
#define ZKC_FRONTEND_SYNTAX_CAPTURES_H
#include "Tree.h"
namespace zkc::frontend::syntax {
/// Infer the lexical free places of an isolated region in first-use order.
/// This chooses bindings only. Type, role and affine legality remain checker
/// obligations; no communication, cloning or loop state is synthesized.
void inferCaptures(syntax::Module &);
bool hasLexicalTraversals(const syntax::Body &);
} // namespace zkc::frontend::syntax
#endif
