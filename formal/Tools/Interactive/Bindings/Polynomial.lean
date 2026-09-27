import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Polynomial

private def alternatives (contract : String) : List String :=
  if ["poly.product_sum", "poly.product_round", "poly.boundary", "poly.round_evaluate",
      "poly.fold", "poly.evaluate", "poly.empty_point", "poly.append_point"].contains contract then
    ["arkworks-msb/" ++ contract] else []

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let field ← Support.scalarArgument binding
  if numericalContract binding.contract then
    ensure (field == bn254Fr || field == koalaBear || field == koalaBearExt8) "binding-two-adic-field"
  if binding.contract == "poly.even_odd_fold" then
    ensure ((← scalarModulus field) > 2) "binding-requirement"
  let msb := binding.implementation == "arkworks-msb/" ++ binding.contract
  let representation := fun (_ : Bool) (_ : Nat) (ty : ValueType) =>
    if msb && ty.kind == "table" then "arkworks.mle-msb/1" else ty.defaultRepresentation
  Support.realize physical binding (Support.signature shape field) (Support.scalarBackend field)
    (if field == fr then alternatives binding.contract else []) representation

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "poly.coefficient_count" ["polynomial"] ["index"] resolve,
    Operation.ofShape "poly.coset_evaluate" ["polynomial", "field", "index"] ["vector"] resolve,
    Operation.ofShape "poly.coset_interpolate" ["vector", "field"] ["polynomial"] resolve,
    Operation.ofShape "poly.domain_point" ["field", "index", "index"] ["field"] resolve,
    Operation.ofShape "poly.domain_root" ["index"] ["field"] resolve,
    Operation.ofShape "poly.domain_points" ["field", "index"] ["vector"] resolve,
    Operation.ofShape "poly.even_odd_fold" ["vector", "field", "field"] ["vector"] resolve,
    Operation.ofShape "poly.divide_opening" ["polynomial", "field", "field"] ["polynomial"] resolve,
    Operation.ofShape "poly.opening_quotient" ["vector", "field", "field", "field"] ["vector"] resolve,
    Operation.ofShape "poly.equality_weights" ["point"] ["vector"] resolve,
    Operation.ofShape "poly.from_coefficients" ["vector"] ["polynomial"] resolve,
    Operation.ofShape "poly.coefficients" ["polynomial"] ["vector"] resolve,
    Operation.ofShape "poly.degree_check" ["polynomial"] ["bool"] resolve,
    Operation.ofShape "poly.univariate_evaluate" ["polynomial", "field"] ["field"] resolve,
    Operation.ofShape "poly.univariate_boundary" ["polynomial"] ["field"] resolve,
    Operation.ofShape "poly.product_sum" ["table", "table"] ["field"] resolve,
    Operation.ofShape "poly.product_round" ["table", "table"] ["round"] resolve,
    Operation.ofShape "poly.boundary" ["round"] ["field"] resolve,
    Operation.ofShape "poly.round_evaluate" ["round", "field"] ["field"] resolve,
    Operation.ofShape "poly.fold" ["table", "field"] ["table"] resolve,
    Operation.ofShape "poly.evaluate" ["table", "point"] ["field"] resolve,
    Operation.ofShape "poly.empty_point" [] ["point"] resolve,
    Operation.ofShape "poly.append_point" ["point", "field"] ["point"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract ++ alternatives contract)

end Tools.Interactive.Bindings.Polynomial
