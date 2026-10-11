#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using GroupAdapter = DomainAdapter<zkc::algebra::GroupType>;
using GroupVectorAdapter = DomainAdapter<zkc::algebra::GroupVectorType>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Curve.inc"
