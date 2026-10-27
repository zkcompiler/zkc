module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawReading
public import ZkcSecurity.Realizations.Sumcheck.OriginalRawTerminal
public import ZkcSecurity.FiatShamir.CostComposition

@[expose] public section

/-! Full original raw-table roots, with their actual refusal branches. The
presentation retains the optional Boolean and the complete construction state.
No honest-input policy restricts this meaning or any adversarial reply. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent

variable {F G : Type} [Field F] [DecidableEq F]

abbrev Result := Values (Component (assignment F G)) [.boolean] × ConstructionState (F := F) (G := G)
abbrev acceptance := @OriginalSecurity.acceptance

noncomputable def sourceRoot (maximum : Nat) (context : Realizations.Sumcheck.Original.Context)
    (raw : List F) (scalar : F) (count : Nat) :
    PIR.Process (ZkcExamples.Structured.OriginalSumcheckLibrary.signature (F := F) (G := G))
      (Values (Component (assignment F G)) [.boolean]) :=
  if count ≤ maximum then
    (run context (List.range count) ⟨[], scalar⟩).bind fun final => terminal raw final.point final.scalar
  else .halt .refused

noncomputable def root (maximum : Nat) (schedule : Nominal.Schedule "bls12-381.fr")
    (raw : List F) (scalar : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) :
    PIR.Process (NominalField.signature F "bls12-381.fr") (Result (F := F) (G := G)) :=
  if count ≤ maximum then
    (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count) ⟨[], scalar, construction.history⟩).bind
      fun final => (terminal raw final.point final.scalar).bind
        fun result => .done (result, { construction with history := final.history })
  else .halt .refused

theorem terminal_bridge (routing : Zkc.Construction.Original.Routing)
    (raw point : List F) (scalar : F) (construction : ConstructionState (F := F) (G := G)) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr")
      (fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing (terminal raw point scalar) construction)
      ((terminal raw point scalar).bind fun result => .done (result, construction)) := by
  unfold terminal
  split
  · split
    · split
      · exact .done _ _ ⟨rfl, rfl⟩
      · exact .halt _ .exhausted
    · exact .done _ _ ⟨rfl, rfl⟩
  · exact .halt _ .exhausted

/-- The complete source root reads nominally for every raw table and count.
All terminal branches and the full original return survive this bridge. -/
theorem root_bridge (routing : Zkc.Construction.Original.Routing)
    (context : Realizations.Sumcheck.Original.Context) (schedule : Nominal.Schedule "bls12-381.fr")
    (maximum : Nat) (raw : List F) (scalar : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G))
    (routes : OriginalSecurity.Routes routing context schedule construction.frames) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr")
      (fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing (sourceRoot maximum context raw scalar count) construction)
      (root maximum schedule raw scalar count construction) := by
  unfold sourceRoot root
  by_cases bound : count ≤ maximum
  · rw [ite_eq_left bound, ite_eq_left bound, Zkc.Construction.Original.fold_bind]
    have continued := (run_bridge routing context schedule (List.range count) ⟨[], scalar⟩ construction routes).bind
      (fun result => Zkc.Construction.Original.fold routing (terminal raw result.1.point result.1.scalar) result.2)
      (fun result => (terminal raw result.1.point result.1.scalar).bind
        fun value => .done (value, result.2))
      (PostNext := fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames) (by
        intro reached result preserved
        have tail := terminal_bridge routing raw result.1.point result.1.scalar result.2
        rw [preserved.1] at tail
        exact tail.weaken (fun reached result holds => ⟨holds.1, holds.2.trans preserved.2⟩))
    simpa only [presentedRun, nominal, unpack, PIR.Process.bind_assoc, PIR.Process.bind] using continued
  · rw [ite_eq_right bound, ite_eq_right bound]
    exact .halt _ .refused

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
