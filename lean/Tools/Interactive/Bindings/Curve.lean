import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Curve

private def alternatives (contract : String) : List String :=
  (if ["curve.scale_each", "curve.msm"].contains contract then
    ["dalek-diagonal/" ++ contract] else []) ++
  (if contract == "curve.msm" then ["dalek-vartime/curve.msm"] else [])

private def resolve (physical : Bool) (binding : Declaration) (shape : Support.Shape) : Result Signature := do
  let (field, group) ← if binding.contract == "curve.response" then do
      pure (← Support.scalarArgument binding, g1)
    else do
      let [group] := binding.arguments | throw "binding-static-arity"
      ensure (groupDomain group) "binding-static-arguments"
      pure (← associatedIdentity group "Scalar", group)
  let diagonal := binding.implementation == "dalek-diagonal/" ++ binding.contract
  -- Mathematical binding only. Public-operand leakage admission is host-owned.
  let representation := fun output i (ty : ValueType) =>
    if diagonal && ((output && i == 0 && binding.contract == "curve.scale_each") ||
        (!output && i == 1 && binding.contract == "curve.msm")) then "dalek.ristretto-diagonal/0"
    else ty.defaultRepresentation
  Support.realize physical binding (Support.signature shape field group) (Support.scalarBackend field)
    (if group == ristrettoGroup then alternatives binding.contract else []) representation

/-- Independently authored installed contracts for this domain. -/
def contribution : Contribution :=
  Contribution.withImplementations
  ⟨[
    Operation.ofShape "curve.neg" ["group"] ["group"] resolve,
    Operation.ofShape "curve.nonidentity" ["group"] ["bool"] resolve,
    Operation.ofShape "curve.msm" ["vector", "groups"] ["group"] resolve,
    Operation.ofShape "curve.scale_each" ["vector", "groups"] ["groups"] resolve,
    Operation.ofShape "curve.vector_add" ["groups", "groups"] ["groups"] resolve,
    Operation.ofShape "curve.concat" ["groups", "groups"] ["groups"] resolve,
    Operation.ofShape "curve.vector_scale" ["groups", "field"] ["groups"] resolve,
    Operation.ofShape "curve.split" ["groups"] ["groups", "groups"] resolve,
    Operation.ofShape "curve.generator" [] ["group"] resolve,
    Operation.ofShape "curve.add" ["group", "group"] ["group"] resolve,
    Operation.ofShape "curve.scale" ["group", "field"] ["group"] resolve,
    Operation.ofShape "curve.equal" ["group", "group"] ["bool"] resolve,
    Operation.ofShape "curve.empty" [] ["groups"] resolve,
    Operation.ofShape "curve.append" ["groups", "group"] ["groups"] resolve,
    Operation.ofShape "curve.at" ["groups"] ["group"] resolve,
    Operation.ofShape "curve.get" ["groups", "index"] ["group"] resolve,
    Operation.ofShape "curve.length" ["groups"] ["index"] resolve,
    Operation.ofShape "curve.commit" ["groups", "nonce"] ["groups", "nonce"] resolve,
    Operation.ofShape "curve.response" ["field", "field", "nonce"] ["field"] resolve]⟩
  (fun contract => Support.implementations ["arkworks", "dalek", "plonky3"] contract ++ alternatives contract)

end Tools.Interactive.Bindings.Curve
