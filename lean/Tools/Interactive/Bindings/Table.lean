import Tools.Interactive.Bindings.Support

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Table

private def resolve (physical : Bool) (binding : Declaration) : Result Signature := do
  ensure physical "binding-adapter-at-logical-stage"
  ensure (binding.implementation == "arkworks/table.relayout") "binding-implementation"
  let [field, sourceRepresentation, targetRepresentation] := binding.arguments | throw "binding-static-arity"
  let a := ValueType.mk "table" field sourceRepresentation
  let b := ValueType.mk "table" field targetRepresentation
  ensure (a.valid true && b.valid true && sourceRepresentation != targetRepresentation) "binding-adapter-type"
  return ⟨[a], [b]⟩

/-- Physical representation adapters have no logical/generic shape entry. -/
def contribution : Contribution :=
  Contribution.withImplementations ⟨[⟨"table.relayout", none, resolve, []⟩]⟩
  (fun contract => Support.implementations ["arkworks"] contract)

end Tools.Interactive.Bindings.Table
