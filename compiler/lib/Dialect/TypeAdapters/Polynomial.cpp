#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using PolynomialAdapter = DomainAdapter<UnivariateType>;
using TableAdapter = DomainAdapter<MultilinearType>;
using PointAdapter = DomainAdapter<PointType>;
using RoundAdapter = DomainAdapter<QuadraticType>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Polynomial.inc"
