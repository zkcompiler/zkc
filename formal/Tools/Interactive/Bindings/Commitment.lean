import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Commitment

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  ensure (binding.arguments == [pcs]) "binding-static-arguments"
  Support.realize physical binding (Support.signature shape) "arkworks/"

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "pcs.commit" ["prover_key", "table"] ["commitment", "opening_state"] resolve,
    Operation.ofShape "pcs.open" ["opening_state", "point"] ["field", "proof"] resolve,
    Operation.ofShape "pcs.check" ["verifier_key", "commitment", "point", "field", "proof"] ["bool"] resolve,
    Operation.ofShape "pcs.equal" ["commitment", "commitment"] ["bool"] resolve]⟩
  (fun contract => Support.implementations ["arkworks"] contract)

end Tools.Interactive.Bindings.Commitment
