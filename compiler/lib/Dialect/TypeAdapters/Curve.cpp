#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using GroupAdapter = DomainAdapter<zkc::algebra::GroupType>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Curve.inc"
