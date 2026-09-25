#ifndef ZKC_RELATION_LOWERING_H
#define ZKC_RELATION_LOWERING_H

#include "zkc/Relation/R1CS.h"
#include "zkc/Source/Model.h"

namespace zkc::relation {

enum class Staging { Specialized, PublicMatrices };

/// Shared grammar for relation aliases and generated-function prefixes.
bool isValidSymbol(llvm::StringRef);

/// Core rank-one interfaces, independent of any multilinear/QAP consumer.
/// Products and Residuals have exactly the relation's ordered row count.
llvm::Expected<source::Module>
lowerRankOneR1CS(const R1CS &, llvm::StringRef prefix,
                 Staging staging = Staging::Specialized);

/// Build local computations for the multilinear R1CS consumer.
/// Field identity is fixed by the relation; physical implementations remain
/// selectable. No proof, witness generator, participant or transcript is hidden
/// in these functions. Products, row contraction and matrix evaluation use
/// sparse gather/multiply/scatter operations, never a dense matrix expansion.
///
/// Rows and columns pad independently to Boolean cubes (minimum size two).
/// Binding coordinate/check functions cover ONE and each public coordinate.
/// A protocol must invoke authenticated openings at those points; calling a
/// local predicate on prover-provided values does not establish binding.
/// PublicMatrices keeps coefficients in immutable, verifier-owned public input
/// values. Before each matrix use, the functions require exact canonical
/// content identity as well as dimensions. A matrix of the same shape with
/// different coefficients cannot be substituted. Transcript/public-input
/// authentication remains the consuming protocol's separate responsibility.
llvm::Expected<source::Module>
lowerMultilinearR1CS(const R1CS &, llvm::StringRef prefix,
                     Staging staging = Staging::Specialized);

/// Three canonical COO matrix payloads, with independently padded dimensions.
/// Each is [rows, columns, [[row, column, coefficient], ...]] using strings.
llvm::json::Value matrixValues(const R1CS &, bool padded = true);

} // namespace zkc::relation

#endif
