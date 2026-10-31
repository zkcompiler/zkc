#ifndef ZKC_LANGUAGE_ORACLEDEFINITIONS_H
#define ZKC_LANGUAGE_ORACLEDEFINITIONS_H
#include "Semantics.h"
namespace zkc::language::detail {
struct SyntaxDeclaration;
bool checkOraclePredicateReferences(Semantics &, const Declaration &,
                                    const SyntaxDeclaration &,
                                    unsigned sourceCount);
std::shared_ptr<OracleDefinition>
closeOracleDefinition(Semantics &, const OracleDefinition &,
                      const Substitution &, Span);
bool checkOracleDefinition(Semantics &, llvm::ArrayRef<Declaration>,
                           const Declaration &);
/// Compare metadata under the explicit closed static substitution.
bool checkOracleMetadataSubstitution(Semantics &, const Declaration &original,
                                     const Declaration &closed,
                                     const Substitution &,
                                     llvm::ArrayRef<Declaration>);
/// Recheck the explicit query ABI and actual answer dependencies.
bool checkOracleQueryBody(Semantics &, llvm::ArrayRef<Declaration>,
                          const Declaration &, const Body &);
} // namespace zkc::language::detail
#endif
