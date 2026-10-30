// Native binding decisions owned by Polynomial.
include "zkc/Dialect/TypeBindings.td"
def PolynomialTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "polynomialAdapters">;
def PolynomialNativeBinding : ZKC_DirectBinding<CatalogType_polynomial, Univariate, "PolynomialAdapter", PolynomialTypeAdapters>;
def TableNativeBinding : ZKC_DirectBinding<CatalogType_table, Multilinear, "TableAdapter", PolynomialTypeAdapters>;
def PointNativeBinding : ZKC_DirectBinding<CatalogType_point, Point, "PointAdapter", PolynomialTypeAdapters>;
def RoundNativeBinding : ZKC_DirectBinding<CatalogType_round, Quadratic, "RoundAdapter", PolynomialTypeAdapters>;
