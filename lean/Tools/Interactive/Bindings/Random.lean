import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Random

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let field ← Support.scalarArgument binding
  if binding.contract == "random.index" then ensure (field == koalaBearExt8) "binding-index-randomness"
  Support.realize physical binding (Support.signature shape field) (Support.scalarBackend field)

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "random.vector" ["rng"] ["vector", "rng"] resolve,
    Operation.ofShape "random.index" ["rng", "index"] ["index", "rng"] resolve,
    Operation.ofShape "random.draw" ["rng"] ["field", "rng"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract)

end Tools.Interactive.Bindings.Random
