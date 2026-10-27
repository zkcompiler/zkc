module

public import Zkc.Executable.DomainNativeBodyScopes
public import Zkc.Executable.DomainNativeReceive
public import Zkc.Executable.DomainNativeHelperCosts
public import Zkc.Executable.DomainNativeEntry

@[expose] public section
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem Erases.of_read {suite : String} {key : Origin → Origin} {initial : History F G}
    {env : Environment F G} {scalar : List (Value F G)} (erases : Erases suite key initial env scalar)
    {references : List Nat} {values : List (Value F G)}
    (read : Construction.read scalar references = some values) :
    ∃ nominal, Domain.read env references = some nominal ∧ Erases suite key initial nominal values := by
  have commute := (erases.read references).trans read
  cases found : Domain.read env references with
  | none => simp [found] at commute
  | some nominal => exact ⟨nominal, rfl, by simpa only [Erases, found, Option.bind_some] using commute⟩

theorem nativeHelper_results (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (name : String) (references : List Nat) (declared : List ValueSort)
    (checked : checkNativeItem program context (.helper ⟨.call name, references, declared, []⟩) scope = some final) :
    ∃ helper, (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper ∧
      references.map (scope.slots[·]?) = helper.inputs.map (some ∘ NativeSlot.data) ∧
      helper.inputs.all dataType = true ∧ helper.outputs.all dataType = true ∧
      declared = helper.outputs.map ValueSort.data ∧
      final = scope.append (helper.outputs.map NativeSlot.data) false := by
  change (nativeResults program context scope (.call name) references).bind _ = some final at checked
  simp only [nativeResults] at checked
  split at checked
  · rename_i helper found
    split at checked
    · rename_i facts
      obtain ⟨operands, inputs, outputs⟩ := facts
      simp only [Option.bind] at checked
      split at checked
      · rename_i declaredEq
        cases checked
        exact ⟨helper, found, operands, inputs, outputs, by simpa [List.map_map, Function.comp_def, NativeSlot.sort] using declaredEq.symm, rfl⟩
      · cases checked
    · cases checked
  · cases checked

theorem native_receive_results (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (site schema peer : String) (ty : Structured.Ty)
    (checked : checkNativeItem program context (.step ⟨.receive site schema peer ty, [], [.data ty], []⟩ 1) scope = some final) :
    site = schema ∧ (scalarType ty).isSome = true ∧ final = scope.append [.data ty] false := by
  obtain ⟨slots, advances, checked, declared, finalEq⟩ := checkNativeStep_results program context scope final _ _ _ 1 checked
  simp only [nativeResults] at checked
  split at checked
  · rename_i facts
    cases checked
    exact ⟨facts.1, facts.2, finalEq⟩
  · cases checked

end Zkc.Executable.DomainVM
