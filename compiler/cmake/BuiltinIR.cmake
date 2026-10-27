# Core build facts only: dialect namespace | C++ owner | type generation.
# Both contribution admission and TableGen generation consume these records.
set(zkc_builtin_dialects
  "protocol|Protocol|types"
  "local|Local|none"
  "exec|Exec|types"
  "runtime|Runtime|types"
  "data|Data|types"
  "crypto|Crypto|types"
  "algebra|Algebra|types"
  "poly|Polynomial|types"
  "commitment|Commitment|types"
  "relation|Relation|none"
)

# Type-binding owner record | generated output stem. Owners need not be dialects.
set(zkc_builtin_type_adapters
  "CoreTypeAdapters|Core"
  "RuntimeTypeAdapters|Runtime"
  "AlgebraTypeAdapters|Algebra"
  "PolynomialTypeAdapters|Polynomial"
  "CurveTypeAdapters|Curve"
  "CommitmentTypeAdapters|Commitment"
  "ResourceTypeAdapters|Resources")
