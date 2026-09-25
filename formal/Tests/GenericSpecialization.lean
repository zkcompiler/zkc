import Tools.Interactive.Specialization

set_option autoImplicit false

namespace Tests.GenericSpecialization
open Tools.Interactive

private def definition : Generic.Definition :=
  ⟨"Check", [], [], [("allowed", ⟨"bool", none⟩)], [⟨"bool", none⟩],
   [⟨"first", "control.require", [], [], ["allowed"], [], false⟩,
    ⟨"second", "control.require", [], [], ["allowed"], [], false⟩], ["allowed"], []⟩

private def selected (reserved : List Name) : Result (Explicit.Function × List OperationBinding) := do
  Generic.specialize ⟨"Checked", "Check", [], []⟩ (← Generic.checkDefinition definition) reserved

private def names (reserved : List Name) : Option (List Name) :=
  (selected reserved).toOption.map fun (_, bindings) => bindings.map OperationBinding.name

example : names [] = some ["reference_binding_0", "reference_binding_1"] := by native_decide
example : names ["reference_binding_0", "reference_binding_2", "reference_binding_0"] =
    some ["reference_binding_1", "reference_binding_3"] := by native_decide
example : names ((List.range 512).map fun i => s!"reference_binding_{i}") =
    some ["reference_binding_512", "reference_binding_513"] := by native_decide

-- Fresh names change references, not source sites, attributes, operands or order.
example : ((selected ["reference_binding_0", "reference_binding_2"]).toOption.map
    fun (function, _) => function.code.body) == some (some [
      .op "first" "reference_binding_1" [] ["allowed"] [],
      .op "second" "reference_binding_3" [] ["allowed"] [], .ret ["allowed"]]) := by native_decide

end Tests.GenericSpecialization
