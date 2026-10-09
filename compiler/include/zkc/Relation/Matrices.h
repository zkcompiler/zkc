#ifndef ZKC_RELATION_MATRICES_H
#define ZKC_RELATION_MATRICES_H

#include "zkc/Relation/R1CS.h"

namespace zkc::relation {
/// Three canonical COO payloads [rows, columns, [[row, column, coefficient]]]
/// using strings. Padding rounds each dimension to a Boolean cube, minimum two.
llvm::json::Value matrixValues(const R1CS &, bool padded = true);
/// SHA256 of compact ["zkc.matrix/1", field, matrixValues(relation)[index]].
/// The caller supplies a matrix index in [0, 3).
std::string matrixIdentity(const R1CS &, unsigned index, bool padded = true);
} // namespace zkc::relation

#endif
