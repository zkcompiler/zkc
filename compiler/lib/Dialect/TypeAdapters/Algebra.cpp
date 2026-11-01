#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using FieldAdapter = DomainAdapter<zkc::algebra::FieldType>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Algebra.inc"
