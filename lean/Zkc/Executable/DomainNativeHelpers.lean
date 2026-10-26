module

public import Zkc.Executable.DomainNativeScope

@[expose] public section

/-! Helper signature readback from actual checked declarations. Signature
checking is independent of whether invocation returns or stops. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem helperShapes_fold (definitions : List Structured.CheckedDefinition)
    (table : Structured.Meanings F G) :
    (definitions.foldl (Structured.Evaluation.extendMeanings Structured.SiteObservations.closed) table).map
      (·.helper) = definitions.reverse.map (·.helper) ++ table.map (·.helper) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
      rw [List.foldl_cons, ih]
      simp only [Structured.Evaluation.extendMeanings, List.map_cons, List.reverse_cons,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]

theorem nativeHelperSignatures_table (program : Structured.Program) :
    (Domain.helperTable (Structured.ringModel F G) program).map (·.helper) =
      nativeHelperSignatures program := by
  rw [Uniform.DomainAdapter.helperTable_eq, helperShapes_fold]
  simp [nativeHelperSignatures]

theorem nativeHelperSignature (program : Structured.Program) (name : String)
    {helper : Structured.Helper}
    (checked : (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper)
    (entry : Structured.HelperDefinition (Structured.assignment F G) Structured.closedInterface)
    (found : (Domain.helperTable (Structured.ringModel F G) program).find?
      (fun found => found.helper.name == name) = some entry) : entry.helper = helper := by
  have mapped := congrArg (Option.map (·.helper)) found
  change Option.map (·.helper) (List.find?
    ((fun found : Structured.Helper => found.name == name) ∘ (·.helper))
    (Domain.helperTable (Structured.ringModel F G) program)) = some entry.helper at mapped
  rw [← List.find?_map, nativeHelperSignatures_table program, checked] at mapped
  exact (Option.some.inj mapped).symm

/-- Structural checking supplies the canonical helper metadata even if the
helper always stops. Native Prepared is used separately for execution/cost. -/
theorem nativeHelper_call (program : Structured.Program) (name : String)
    {helper : Structured.Helper}
    (checked : (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper)
    (eligible : helper.outputs.all dataType = true)
    {values : List (Value F G)} {encoded : Environment F G}
    (embedded : Uniform.DomainAdapter.embedValues values = some encoded) :
    Domain.callHelper (Structured.ringModel F G) program name (helper.outputs.map ValueSort.data) encoded =
      Uniform.DomainAdapter.embedOutcome
        (Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name values) := by
  apply Uniform.DomainAdapter.callHelper_checked_signature
  · intro entry found
    rw [nativeHelperSignature program name checked entry found]
    exact ⟨rfl, eligible⟩
  · exact embedded

end Zkc.Executable.DomainVM
