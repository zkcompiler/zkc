import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.FixedVector

private def resolve (physical : Bool) (binding : Declaration) (_shape : Support.Shape) : Result Signature := do
  let [field, length] := binding.arguments | throw "binding-static-arity"
  ensure (scalarDomain field) "binding-static-arguments"
  let n ← Logical.natural length
  ensure ((!physical && binding.implementation.isEmpty) ||
    (field == koalaBear && binding.implementation == "plonky3/" ++ binding.contract)) "binding-implementation"
  let fixed := ValueType.ofLogical (.application "fixed_vector" [.type (.atom "field" field), .natural n])
  let vector := ValueType.mk "vector" field
  let scalar := ValueType.mk "field" field
  let logical : Signature := match binding.contract with
    | "fixed_vector.from_vector" => ⟨[vector], [fixed]⟩
    | "fixed_vector.to_vector" => ⟨[fixed], [vector]⟩
    | _ => ⟨[fixed, fixed], [scalar]⟩
  let select := fun (ty : ValueType) => do
    let selected := if physical then {ty with representation := ty.defaultRepresentation} else ty
    ensure (selected.valid physical) "binding-representation"
    return selected
  return ⟨← logical.inputs.mapM select, ← logical.outputs.mapM select⟩

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "fixed_vector.from_vector" ["vector"] ["fixed_vector"] resolve,
    Operation.ofShape "fixed_vector.to_vector" ["fixed_vector"] ["vector"] resolve,
    Operation.ofShape "fixed_vector.dot" ["fixed_vector", "fixed_vector"] ["field"] resolve]⟩
  (fun contract => Support.implementations ["plonky3"] contract)

end Tools.Interactive.Bindings.FixedVector
