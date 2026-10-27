module

public import ZkcSecurity.Realizations.Sumcheck.OriginalHonestLoop

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalHonest
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck
open SumcheckVerifierBodies TableComponent

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev ReduceResult := Values (Component (assignment F G)) reduceOutputs × SourceState (F := F) (G := G)

def ReducePost (raw : List F) (count : Nat)
    (left right : ReduceResult (F := F) (G := G)) : Prop :=
  ∃ final : MathState F 0,
    final.original = raw ∧ final.point.length = count ∧ final.scalar = final.entries.sum ∧
    ∃ reached,
    left = (reduceReturnValues (producerValues final), ⟨[], reached⟩) ∧
    right = (reduceReturnValues (verifierValues final), ⟨[], reached⟩)

/-- The shared exact source reference also named by source soundness. The
producer prelude, both original repeat admissions, all iterations and the full
return permutation are proved here. Root-specific code supplies only routes. -/
theorem reduce (payload : UnitPayload) (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (maximum : Nat) (producerRouting validatorRouting : Original.Routing) (context : ProtocolContext)
    (separate : context.roles 0 ≠ context.roles 1) (handle : Nat)
    (routes : Routes producerRouting validatorRouting context handle)
    (raw : List F) (count : Nat) (shape : PrimitiveLibrary.HasShape raw count 1)
    (bounded : raw.length < indexLimit) (admitted : count ≤ maximum)
    (history : Domain.History (uniformCarriers F G)) :
    Readback (ReducePost raw count)
      (Original.fold producerRouting
        (OriginalSecurity.SourceFamily.sourceReference payload maximum context (context.roles 0) []
          (.cons (some raw) (.cons (some count) (.cons (some 1)
            (.cons none (.cons (some count) (.cons none .nil))))))) ⟨[], history⟩)
      (Original.fold validatorRouting
        (OriginalSecurity.SourceFamily.sourceReference payload maximum context (context.roles 1) []
          (.cons none (.cons none (.cons none
            (.cons (some raw.sum) (.cons (some count) (.cons (some handle) .nil))))))) ⟨[], history⟩) := by
  dsimp only [OriginalSecurity.SourceFamily.sourceReference]
  have countBound : count < indexLimit := lt_trans shape.2.1 (by decide +kernel)
  rw [OriginalProducer.source_reduce payload bodies maximum context (Ne.symm separate) []
    raw count count countBound countBound (Nat.le_refl _) none]
  rw [OriginalSumcheckLibrary.reduce_verifier payload
    ⟨bodies.empty, bodies.append, bodies.width, bodies.variables, bodies.values⟩
    maximum context separate [] (some raw.sum) (some count) (some handle)]
  simp only [Original.fold_bind]
  rw [Original.fold_repeat, Original.fold_repeat]
  have producerActive : ((repeatSpec maximum).roles.map context.roles).contains (context.roles 0) = true := by
    simp []
  have validatorActive : ((repeatSpec maximum).roles.map context.roles).contains (context.roles 1) = true := by
    simp []
  dsimp only at producerActive validatorActive
  simp only [producerActive, validatorActive, admitted, ↓reduceIte,
    SumcheckProverLaws.mask_embedP _ _ rfl maximum,
    SumcheckVerifierLaws.mask_embedV _ _ rfl maximum]
  rw [List.range_eq_range']
  let initial : MathState F (0 + count) :=
    PrefixState.initial raw (0 + count) raw.sum () (by simpa using shape.length)
  have initialShape : PrimitiveLibrary.HasShape initial.entries (0 + count) 1 := by
    simpa only [initial, PrefixState.initial_entries, Nat.zero_add] using shape
  have rounds := loop payload bodies maximum producerRouting validatorRouting context separate handle
    routes (n := 0) count 0 initial initialShape bounded rfl history
  have initialP : producerValues (G := G) initial = SumcheckProverLaws.embedP (raw, count, 1, []) := by
    simp [producerValues, initial, PrefixState.initial, PrefixState.entries,
      Zkc.Polynomial.Multilinear.restrictPrefixValues_nil]
  have initialV : verifierValues (G := G) initial = SumcheckVerifierLaws.embedV (some [], some raw.sum) := rfl
  rw [initialP, initialV] at rounds
  apply rounds.bind
  intro left right returned
  obtain ⟨final, original, length, honestFinal, reached, rfl, rfl⟩ := returned
  exact .done ⟨final, original, by simpa only [initial, PrefixState.initial, List.length_nil,
    Nat.zero_add] using length, honestFinal, reached, rfl, rfl⟩

end ZkcSecurity.Realizations.Sumcheck.OriginalHonest
