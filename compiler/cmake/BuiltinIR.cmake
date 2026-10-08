# Core build facts only: dialect namespace | C++ owner | type generation.
# Both contribution admission and TableGen generation consume these records.
set(zkc_builtin_dialects
  "protocol|Protocol|types"
  "local|Local|types"
  "data|Data|types"
  "crypto|Crypto|none"
  "algebra|Algebra|types"
  "poly|Polynomial|types"
  "plan|Plan|types"
  "pcs|PCS|types"
  "oracle|Oracle|types"
  "relation|Relation|none"
)

# Type-binding owner record | generated output stem. Owners need not be dialects.
set(zkc_builtin_type_adapters
  "CoreTypeAdapters|Core"
  "AlgebraTypeAdapters|Algebra"
  "PolynomialTypeAdapters|Polynomial"
  "CurveTypeAdapters|Curve"
  "CommitmentTypeAdapters|Commitment"
  "ResourceTypeAdapters|Resources")
