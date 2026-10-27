module

public import ZkcSecurity.Realizations.Gkr.CanonicalVerifier
public import ZkcSecurity.Realizations.Gkr.CanonicalRoutes
public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrentExecution

@[expose] public section

/-! Readback of the actual current source pair. The producer computes the proof;
its complete nominal execution and the actual validator share the same history
and exact source-selected challenge coordinates. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalReadback
open Zkc Source Structured Construction
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open ZkcSecurity.FiatShamir HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev ValuesResult := Values (Component (assignment F G)) [.boolean]
abbrev Result := ValuesResult (F := F) (G := G) × Original.State (uniformCarriers F G)

def producer (encoding : CircuitEncoding F) (outputs : List F) (handle : Nat)
    (service : Option Nat) (history : Domain.History (uniformCarriers F G)) :=
  Original.participant (ringModel F G) GkrSourceViews.program
    { routing handle with mode := .producer } 0 (currentInputs encoding outputs service) ⟨[], history⟩

def validator (encoding : CircuitEncoding F) (outputs : List F) (handle : Nat)
    (history : Domain.History (uniformCarriers F G)) :=
  Original.participant (ringModel F G) GkrSourceViews.program
    (routing handle) 1 (currentInputs encoding outputs (some handle)) ⟨[], history⟩

/-- The shared postcondition retains both full source returns, exact history,
and empty final occurrence stacks. -/
def Post (left right : Result (F := F) (G := G)) : Prop :=
  ∃ history, left = (.cons none .nil, ⟨[], history⟩) ∧
    right = (.cons (some true) .nil, ⟨[], history⟩)

theorem actual (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (correct : encoding.Outputs outputs)
    (handle : Nat) (service : Option Nat) (history : Domain.History (uniformCarriers F G)) :
    Readback Post (producer encoding outputs handle service history)
      (validator encoding outputs handle history) := by
  have pair := HonestProducerCurrentExecution.pair (G := G) (routing handle)
    _ rfl handle encoding outputs admitted correct service ⟨[], history⟩
    (fun index => CanonicalRoutes.output handle index)
    (fun index => CanonicalRoutes.layer handle index)
  unfold producer validator Original.participant
  have snapshot : { routing handle with snapshot := GkrSourceViews.program.snapshot } = routing handle := by rfl
  have producerSnapshot : { { routing handle with mode := .producer } with
      snapshot := GkrSourceViews.program.snapshot } = { routing handle with mode := .producer } := by rfl
  rw [snapshot, producerSnapshot, CanonicalVerifier.reads encoding outputs admitted handle,
    Original.fold_bind]
  have aligned := pair.bind (Final := Post) (fun left => .done left)
    (fun right => .done (.cons right.1 .nil, right.2)) (by
      rintro left right ⟨finalHistory, rfl, rfl⟩
      exact .done ⟨finalHistory, rfl, rfl⟩)
  have validatorMode : { routing handle with mode := .validator } = routing handle := by rfl
  simpa only [PIR.Process.bind_done, ArtifactBinding.fold_done, validatorMode] using aligned

end ZkcSecurity.Realizations.Gkr.CanonicalReadback
