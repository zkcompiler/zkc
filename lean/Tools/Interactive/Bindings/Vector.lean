import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Vector

private def alternatives (contract : String) : List String :=
    (if ["vector.from_table", "vector.to_table"].contains contract then
      ["arkworks-msb/" ++ contract] else []) ++
    (if ["vector.mul", "vector.dot"].contains contract then
      ["arkworks-diagonal/" ++ contract] else []) ++
    (if contract == "vector.dot" then ["arkworks-pairwise/vector.dot"] else [])

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let field ← Support.scalarArgument binding
  let logical := Support.signature shape field
  let logical ← if binding.contract == "vector.embed" then do
      let base ← associatedIdentity field "BaseField"
      pure { logical with inputs := [ValueType.mk "vector" base] }
    else pure logical
  let msb := binding.implementation == "arkworks-msb/" ++ binding.contract
  let diagonal := binding.implementation == "arkworks-diagonal/" ++ binding.contract
  let representation := fun output i (ty : ValueType) =>
    if diagonal && ((output && i == 0 && binding.contract == "vector.mul") ||
        (!output && i == 1 && binding.contract == "vector.dot")) then "arkworks.fr-diagonal/0"
    else if msb && ty.kind == "table" then "arkworks.mle-msb/0"
    else ty.defaultRepresentation
  Support.realize physical binding logical (Support.scalarBackend field)
    (if field == fr then alternatives binding.contract else []) representation

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "vector.slice" ["vector", "index", "index"] ["vector"] resolve,
    Operation.ofShape "vector.get" ["vector", "index"] ["field"] resolve,
    Operation.ofShape "vector.length" ["vector"] ["index"] resolve,
    Operation.ofShape "vector.rotate" ["vector", "index"] ["vector"] resolve,
    Operation.ofShape "vector.interleave" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.prefix_product" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.prefix_sum" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.inverse" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.embed" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.fill" ["field", "index"] ["vector"] resolve,
    Operation.ofShape "vector.geometric" ["field", "index"] ["vector"] resolve,
    Operation.ofShape "vector.constant" [] ["vector"] resolve,
    Operation.ofShape "vector.empty" [] ["vector"] resolve,
    Operation.ofShape "vector.append" ["vector", "field"] ["vector"] resolve,
    Operation.ofShape "vector.splat" ["field"] ["vector"] resolve,
    Operation.ofShape "vector.powers" ["field"] ["vector"] resolve,
    Operation.ofShape "vector.equal" ["vector", "vector"] ["bool"] resolve,
    Operation.ofShape "vector.add" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.sub" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.mul" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.concat" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.kronecker" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.matvec" ["vector", "vector"] ["vector"] resolve,
    Operation.ofShape "vector.scale" ["vector", "field"] ["vector"] resolve,
    Operation.ofShape "vector.sum" ["vector"] ["field"] resolve,
    Operation.ofShape "vector.at" ["vector"] ["field"] resolve,
    Operation.ofShape "vector.dot" ["vector", "vector"] ["field"] resolve,
    Operation.ofShape "vector.split" ["vector"] ["vector", "vector"] resolve,
    Operation.ofShape "vector.length_check" ["vector"] ["bool"] resolve,
    Operation.ofShape "vector.scatter_sum" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.gather" ["vector"] ["vector"] resolve,
    Operation.ofShape "vector.from_point" ["point"] ["vector"] resolve,
    Operation.ofShape "vector.to_point" ["vector"] ["point"] resolve,
    Operation.ofShape "vector.from_table" ["table"] ["vector"] resolve,
    Operation.ofShape "vector.to_table" ["vector"] ["table"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract ++ alternatives contract)

end Tools.Interactive.Bindings.Vector
