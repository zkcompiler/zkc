module

public import ZkcSecurity.Realizations.Sumcheck.OriginalHonest

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalHonest
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck
open SumcheckVerifierBodies TableComponent

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def iteration (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext)
    (routing : Original.Routing) (self : Nat) (handle : Option Nat)
    (source : RoundResult (F := F) (G := G)) (index : Nat) :=
  Original.fold routing
    (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) context self
      (.cons handle .nil) (OriginalSumcheckLibrary.round payload context self)
      source.1 index Occurrence.iterations "s15") source.2

structure Routes (producerRouting validatorRouting : Original.Routing)
    (context : ProtocolContext) (handle : Nat) where
  origins : Nat → ArtifactBinding.Origins
  producer : ∀ index, OriginalProducer.Routes producerRouting context
    [⟨qualifyProtocolSite context.applicationPrefix "s15", index⟩] (origins index)
  validator : ∀ index, ArtifactBinding.Routes validatorRouting context
    [⟨qualifyProtocolSite context.applicationPrefix "s15", index⟩] handle (origins index)

/-- Actual repeat entry, role masks and matching leave surround the callback.
The common return history is passed through the original closing boundary. -/
theorem step (payload : UnitPayload) (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (maximum : Nat) (producerRouting validatorRouting : Original.Routing) (context : ProtocolContext)
    (separate : context.roles 0 ≠ context.roles 1) (handle index : Nat)
    (routes : Routes producerRouting validatorRouting context handle)
    {n : Nat} (state : MathState F (n + 1))
    (shape : PrimitiveLibrary.HasShape state.entries (n + 1) 1)
    (bounded : state.entries.length < indexLimit) (honest : state.scalar = state.entries.sum)
    (history : Domain.History (uniformCarriers F G)) :
    Readback (fun left right => ∃ challenge reached,
      left = (producerValues (state.advance (endpoints state) challenge), ⟨[], reached⟩) ∧
      right = (verifierValues (state.advance (endpoints state) challenge), ⟨[], reached⟩))
      (iteration payload maximum context producerRouting (context.roles 0) none
        (producerValues state, ⟨[], history⟩) index)
      (iteration payload maximum context validatorRouting (context.roles 1) (some handle)
        (verifierValues state, ⟨[], history⟩) index) := by
  unfold iteration
  simp only [Repeat.stepOn, producerValues, verifierValues,
    SumcheckProverLaws.mask_embedP _ _ rfl maximum,
    SumcheckVerifierLaws.mask_embedV _ _ rfl maximum,
    Original.fold_bind, Original.fold_within, List.nil_append, PIR.Process.bind_assoc]
  apply (round payload bodies producerRouting validatorRouting context separate index handle
    (routes.origins index) state shape bounded honest
    ⟨[⟨qualifyProtocolSite context.applicationPrefix "s15", index⟩], history⟩
    (routes.producer index) (routes.validator index)).bind
  intro left right returned
  obtain ⟨challenge, reached, rfl, rfl⟩ := returned
  simp only [Original.fold, PIR.Process.interpretState,
    List.getLast?_singleton, ↓reduceIte, List.dropLast_singleton,
    PIR.Process.bind, producerValues, verifierValues,
    SumcheckProverLaws.mask_embedP _ _ rfl maximum,
    SumcheckVerifierLaws.mask_embedV _ _ rfl maximum]
  exact .done ⟨challenge, reached, rfl, rfl⟩

def LoopPost {n remaining : Nat} (initial : MathState F remaining)
    (count : Nat) (left right : RoundResult (F := F) (G := G)) : Prop :=
  ∃ final : MathState F n,
    final.original = initial.original ∧ final.point.length = initial.point.length + count ∧
    final.scalar = final.entries.sum ∧ ∃ reached,
    left = (producerValues final, ⟨[], reached⟩) ∧
    right = (verifierValues final, ⟨[], reached⟩)

/-- All original rounds compose, at arbitrary reached indices and with the
full optional carried state. The scalar invariant follows from library math
for every typed challenge, including the zero-trip case. -/
theorem loop (payload : UnitPayload) (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (maximum : Nat) (producerRouting validatorRouting : Original.Routing) (context : ProtocolContext)
    (separate : context.roles 0 ≠ context.roles 1) (handle : Nat)
    (routes : Routes producerRouting validatorRouting context handle)
    {n : Nat} (count start : Nat) (state : MathState F (n + count))
    (shape : PrimitiveLibrary.HasShape state.entries (n + count) 1)
    (bounded : state.entries.length < indexLimit) (honest : state.scalar = state.entries.sum)
    (history : Domain.History (uniformCarriers F G)) :
    Readback (LoopPost (n := n) state count)
      (Finite.fold (iteration payload maximum context producerRouting (context.roles 0) none)
        (List.range' start count) (producerValues state, ⟨[], history⟩))
      (Finite.fold (iteration payload maximum context validatorRouting (context.roles 1) (some handle))
        (List.range' start count) (verifierValues state, ⟨[], history⟩)) := by
  induction count generalizing start history with
  | zero => exact .done ⟨state, rfl, by simp, honest, history, rfl, rfl⟩
  | succ count ih =>
    simp only [List.range'_succ, Finite.fold]
    apply (step payload bodies maximum producerRouting validatorRouting context separate handle start
      routes state shape bounded honest history).bind
    intro left right returned
    obtain ⟨challenge, reached, rfl, rfl⟩ := returned
    let next := state.advance (endpoints state) challenge
    have nextShape : PrimitiveLibrary.HasShape next.entries (n + count) 1 := by
      simpa only [next, PrefixState.advance_entries, Nat.add_sub_cancel] using
        MapFirstLaws.restrict_shape state.entries (n + count + 1) 1 challenge shape (by omega)
    have nextBound : next.entries.length < indexLimit := by
      rw [show next.entries = _ from state.advance_entries (endpoints state) challenge]
      exact MapFirstLaws.restrict_length_bound state.entries challenge bounded
    apply (ih (start + 1) next nextShape nextBound (advance_honest state challenge) reached).mono
    intro finalLeft finalRight returned
    obtain ⟨final, original, length, honestFinal, finalHistory, leftEq, rightEq⟩ := returned
    refine ⟨final, original, ?_, honestFinal, finalHistory, leftEq, rightEq⟩
    simpa only [next, PrefixState.advance_point, List.length_append, List.length_singleton,
      Nat.add_assoc, Nat.add_comm 1 count] using length

end ZkcSecurity.Realizations.Sumcheck.OriginalHonest
