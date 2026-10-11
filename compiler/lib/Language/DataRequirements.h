#ifndef ZKC_LANGUAGE_DATAREQUIREMENTS_H
#define ZKC_LANGUAGE_DATAREQUIREMENTS_H
#include "Semantics.h"
namespace zkc::language::detail {
/// The source view of existing native collection types. This does not form a
/// type, infer an extent, or grant a runtime bound.
enum class CollectionElementKind { None, Parameter, Index };
/// Constructor-only classification also works before element variables solve.
CollectionElementKind collectionElementKind(const Type &head, size_t arguments);
std::optional<Type> collectionElement(const Type &, bool matrix = false);
bool collectionAxis(const Type &, unsigned);
std::optional<std::vector<DataPrecondition>>
mapDataPreconditions(Semantics &, llvm::ArrayRef<DataPrecondition>,
                     llvm::ArrayRef<unsigned> inputAliases);
} // namespace zkc::language::detail
#endif
