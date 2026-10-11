#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using FieldAdapter = DomainAdapter<zkc::algebra::FieldType>;
using FieldVectorAdapter = DomainAdapter<zkc::algebra::FieldVectorType>;
using FieldMatrixAdapter = DomainAdapter<zkc::algebra::FieldMatrixType>;
using IndicesAdapter = NullaryAdapter<zkc::algebra::IndicesType>;
using FieldArrayAdapter =
    DomainNatAdapter<zkc::algebra::FieldArrayType,
                     &zkc::algebra::FieldArrayType::getDomain,
                     &zkc::algebra::FieldArrayType::getLength>;
using FixedVectorAdapter =
    TypeNatAdapter<zkc::algebra::FixedVectorType,
                   &zkc::algebra::FixedVectorType::getElementType,
                   &zkc::algebra::FixedVectorType::getLength>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Algebra.inc"
