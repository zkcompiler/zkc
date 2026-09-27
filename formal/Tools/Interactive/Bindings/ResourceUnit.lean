import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.ResourceUnit

private def resolve (physical : Bool) (binding : Declaration) : Result Signature := do
  let [domain] := binding.arguments | throw "binding-resource-unit-domain"
  ensure (resourceUnitDomain domain) "binding-resource-unit-domain"
  ensure ((!physical && binding.implementation.isEmpty) || binding.implementation == "logical/" ++ binding.contract) "binding-implementation"
  let ty := ValueType.mk "resource_unit" domain (if physical then "logical.resource_unit/1" else "")
  return ⟨if binding.contract == "resource_unit.create" then [] else [ty],
    if binding.contract == "resource_unit.consume" then [] else [ty]⟩

/-- These bindings historically have no generic shape entry. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨["resource_unit.create", "resource_unit.pass", "resource_unit.consume"].map
    (fun contract => ⟨contract, none, resolve, []⟩)⟩
  (fun contract => Support.implementations ["logical"] contract)

end Tools.Interactive.Bindings.ResourceUnit
