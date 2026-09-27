import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Field

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let field ← Support.scalarArgument binding
  let logical := Support.signature shape field
  let logical ← if binding.contract == "field.embed" then do
      let base ← associatedIdentity field "BaseField"
      pure { logical with inputs := [ValueType.mk "field" base] }
    else pure logical
  Support.realize physical binding logical (Support.scalarBackend field)

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "field.from_index" ["index"] ["field"] resolve,
    Operation.ofShape "field.constant" [] ["field"] resolve,
    Operation.ofShape "field.add" ["field", "field"] ["field"] resolve,
    Operation.ofShape "field.mul" ["field", "field"] ["field"] resolve,
    Operation.ofShape "field.sub" ["field", "field"] ["field"] resolve,
    Operation.ofShape "field.neg" ["field"] ["field"] resolve,
    Operation.ofShape "field.inverse" ["field"] ["field"] resolve,
    Operation.ofShape "field.embed" ["field"] ["field"] resolve,
    Operation.ofShape "field.equal" ["field", "field"] ["bool"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract)

end Tools.Interactive.Bindings.Field
