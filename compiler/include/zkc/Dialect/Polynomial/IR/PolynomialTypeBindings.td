// Native binding decisions owned by Polynomial.
include "zkc/Dialect/TypeBindings.td"
def PolynomialTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "polynomialAdapters">;
def PolynomialNativeBinding : ZKC_DirectBinding<TypePolynomial, Univariate, "PolynomialAdapter", PolynomialTypeAdapters>;
def TableNativeBinding : ZKC_DirectBinding<TypeTable, Multilinear, "TableAdapter", PolynomialTypeAdapters>;
def PointNativeBinding : ZKC_DirectBinding<TypePoint, Point, "PointAdapter", PolynomialTypeAdapters>;
def RoundNativeBinding : ZKC_DirectBinding<TypeRound, Quadratic, "RoundAdapter", PolynomialTypeAdapters>;
