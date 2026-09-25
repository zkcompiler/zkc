#ifndef ZKC_FRONTEND_SEMANTICS_CAPTURES_H
#define ZKC_FRONTEND_SEMANTICS_CAPTURES_H
#include "../Syntax/Tree.h"
namespace zkc::frontend::semantics {
/// Infer the lexical free places of an isolated region in first-use order.
/// This chooses bindings only. Type, role and affine legality remain checker
/// obligations; no communication, cloning or loop state is synthesized.
void inferCaptures(syntax::Module &);
bool hasLexicalTraversals(const syntax::Body &);
} // namespace zkc::frontend::semantics
#endif
