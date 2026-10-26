module

public import Zkc.Executable.DomainNativeCodeScope

@[expose] public section

/-! Calculation and helper boundaries through the actual constructed step.
The operand inverse below is derived from checked nominal slots and partial
readback; it does not assert a mathematical relation between input numbers. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem NativeScope.Holds.readData {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) {suite : String} {key : Origin → Origin} {initial : History F G}
    {scalar : List (Value F G)} (erases : Erases suite key initial env scalar)
    {references : List Nat} {types : List Structured.Ty}
    (checked : references.map (scope.slots[·]?) = types.map (some ∘ NativeSlot.data))
    {arguments : List (Value F G)} (read : Construction.read scalar references = some arguments) :
    ∃ nominal, Domain.read env references = some nominal ∧
      DomainAdapter.embedValues arguments = some nominal := by
  have slots : references.map (scope.slots[·]?) = (types.map NativeSlot.data).map some := by
    simpa only [List.map_map] using checked
  obtain ⟨nominal, found, sorted⟩ := holds.read slots
  refine ⟨nominal, found, ?_⟩
  have erased : Erases suite key initial nominal arguments := by
    have mapped := erases.read references
    rw [found, Option.bind_some, read] at mapped
    exact mapped
  apply erased.dataEmbedding
  intro value member actual transcript
  have schema := NativeScope.Holds.schema (scope := ⟨types.map NativeSlot.data, 0⟩) sorted
  have memberSort : value.sort ∈ (types.map NativeSlot.data).map NativeSlot.sort :=
    schema ▸ List.mem_map_of_mem member
  simp only [List.map_map, Function.comp_def, NativeSlot.sort] at memberSort
  obtain ⟨ty, _, equation⟩ := List.mem_map.mp memberSort
  rw [transcript] at equation
  cases equation

variable {m : Type → Type} [Monad m]

theorem helper_returns_embeds (program : Structured.Program) (name : String)
    (helper : Structured.Helper)
    (checked : (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper)
    (eligible : helper.outputs.all dataType = true)
    (arguments results : List (Value F G))
    (returned : Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name arguments =
      .returned results) :
    ∃ nominal, DomainAdapter.embedValues results = some nominal ∧
      nominal.map Domain.Value.sort = helper.outputs.map ValueSort.data := by
  unfold Construction.callHelper at returned
  cases found : (Domain.helperTable (Structured.ringModel F G) program).find?
      (fun entry => entry.helper.name == name) with
  | none => simp [found] at returned
  | some entry =>
    simp only [found] at returned
    have signature := nativeHelperSignature program name checked entry found
    cases decoded : decodeValues entry.helper.inputs arguments with
    | none => simp [decoded] at returned
    | some values =>
      simp only [decoded] at returned
      cases computed : Construction.closedOutcome (entry.invoke values) with
      | stopped => simp [computed] at returned
      | returned values =>
        simp only [computed, PIR.Outcome.returned.injEq] at returned
        subst results
        have outputsData : entry.helper.outputs.all dataType = true := by simpa [signature] using eligible
        obtain ⟨nominal, embedded, sorted⟩ := encodeValues_embeds values outputsData
        exact ⟨nominal, embedded, by simpa [signature] using sorted⟩

/-- Exact CPS calculation law. Every failure is retained, and no instruction
interpreter is used between the native scalar calculation and Domain.step. -/
theorem step_calculate_native {R : Type} (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (calculation : Calculation) (references : List Nat)
    (env nominal : Environment F G) (arguments : List (Value F G))
    (read : Domain.read env references = some nominal)
    (embedded : DomainAdapter.embedValues arguments = some nominal)
    (eligible : calculation.op.results.all dataType = true)
    (proof : Proof F G) (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.calculate calculation, references, calculation.op.results.map ValueSort.data, []⟩ env) proof next =
      match Construction.calculate calculation arguments with
      | .stopped reason => pure (.stopped reason, proof)
      | .returned results =>
          match DomainAdapter.embedValues results with
          | none => pure (.stopped .refused, proof)
          | some values => next (env ++ values) proof := by
  rw [Domain.Correspondence.calculation]
  simp only [Domain.View.calculation, read, DomainAdapter.calculate_embed calculation eligible embedded]
  cases computed : Construction.calculate calculation arguments with
  | stopped reason => rfl
  | returned results =>
      obtain ⟨values, mapped, schema⟩ := calculate_returns_embeds calculation eligible computed
      have sorted : Domain.sortsMatch (calculation.op.results.map ValueSort.data) values = true := by
        simp only [Domain.sortsMatch, schema, beq_self_eq_true]
      simp only [DomainAdapter.embedOutcome, mapped, Domain.View.append, sorted, ite_true,
        DomainAdapter.runK]

/-- Structural helper metadata applies to stopped helpers as well as returned
helpers. This reduction keeps the partial result embedding explicit. -/
theorem step_helper_native {R : Type} (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (name : String) (helper : Structured.Helper)
    (checked : (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper)
    (references : List Nat) (env nominal : Environment F G) (arguments : List (Value F G))
    (read : Domain.read env references = some nominal)
    (embedded : DomainAdapter.embedValues arguments = some nominal)
    (eligible : helper.outputs.all dataType = true)
    (proof : Proof F G) (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.call name, references, helper.outputs.map ValueSort.data, []⟩ env) proof next =
      match DomainAdapter.embedOutcome
          (Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name arguments) with
      | .stopped reason => pure (.stopped reason, proof)
      | .returned results =>
          if Domain.sortsMatch (helper.outputs.map ValueSort.data) results then
            next (env ++ results) proof else pure (.stopped .refused, proof) := by
  rw [Domain.Correspondence.helper]
  simp only [Domain.View.helper, read,
    nativeHelper_call program name checked eligible embedded]
  cases DomainAdapter.embedOutcome
    (Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name arguments) with
  | stopped => rfl
  | returned results =>
      simp only [Domain.View.append]
      split <;> rfl

end Zkc.Executable.DomainVM
