#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

namespace zkc::protocol::type_adapters {
namespace {
using PolynomialAdapter = DomainAdapter<zkc::poly::UnivariateType>;
using TableAdapter = DomainAdapter<zkc::poly::MultilinearType>;
using PointAdapter = DomainAdapter<zkc::poly::PointType>;
using RoundAdapter = DomainAdapter<zkc::poly::QuadraticType>;
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Polynomial.inc"
