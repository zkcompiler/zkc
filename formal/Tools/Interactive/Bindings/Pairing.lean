import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Pairing

private def resolve (physical : Bool) (binding : Declaration) (_shape : Support.Shape) : Result Signature := do
  ensure (binding.arguments == [bn254Fr]) "binding-static-arguments"
  ensure ((!physical && binding.implementation.isEmpty) ||
    binding.implementation == "arkworks/" ++ binding.contract) "binding-implementation"
  let make := fun kind identity => ValueType.mk kind identity
    (if physical then defaultRepresentation kind identity else "")
  if binding.contract == "pairing.apply" then
    return ⟨[make "group" bn254G1, make "group" bn254G2], [make "group" bn254GT]⟩
  return ⟨[make "groups" bn254G1, make "groups" bn254G2], [make "bool" ""]⟩

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "pairing.apply" ["group", "group"] ["group"] resolve,
    Operation.ofShape "pairing.check" ["groups", "groups"] ["bool"] resolve]⟩
  (fun contract => Support.implementations ["arkworks"] contract)

end Tools.Interactive.Bindings.Pairing
