import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Oracle

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let (inputs, outputs) := shape
  let [scheme] := binding.arguments | throw "binding-static-arity"
  ensure (rowDomain scheme &&
    ((!physical && binding.implementation.isEmpty) ||
      binding.implementation == "plonky3/" ++ binding.contract)) "binding-static-arguments"
  let field ← associatedIdentity scheme "ValueField"
  let make := fun kind =>
    let identity := if domainIndependent kind then "" else if kind == "vector" then field else scheme
    ValueType.mk kind identity (if physical then defaultRepresentation kind identity else "")
  return ⟨inputs.map make, outputs.map make⟩

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "oracle.commit" ["vector", "index"] ["commitment", "opening_state"] resolve,
    Operation.ofShape "oracle.open" ["opening_state", "index"] ["vector", "proof"] resolve,
    Operation.ofShape "oracle.check" ["commitment", "index", "index", "index", "vector", "proof"] ["bool"] resolve,
    Operation.ofShape "commitments.empty" [] ["commitments"] resolve,
    Operation.ofShape "commitments.append" ["commitments", "commitment"] ["commitments"] resolve,
    Operation.ofShape "commitments.at" ["commitments", "index"] ["commitment"] resolve,
    Operation.ofShape "commitments.length" ["commitments"] ["index"] resolve,
    Operation.ofShape "opening_states.empty" [] ["opening_states"] resolve,
    Operation.ofShape "opening_states.append" ["opening_states", "opening_state"] ["opening_states"] resolve,
    Operation.ofShape "opening_states.at" ["opening_states", "index"] ["opening_state"] resolve,
    Operation.ofShape "opening_states.length" ["opening_states"] ["index"] resolve]⟩
  (fun contract => Support.implementations ["plonky3"] contract)

end Tools.Interactive.Bindings.Oracle
