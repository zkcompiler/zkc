module

public import ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerReduce
public import ZkcSecurity.Realizations.Sumcheck.OriginalSecurity
public import ZkcSecurity.FiatShamir.OriginalReadback

@[expose] public section

/-! Honest readback of the shared original library. The original producer
computes the actual half sums; the original validator checks their boundary
and uses the identical nominal query. Both directions use Original.layout and
TableReference, also used by the original-source soundness proof. -/
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

abbrev MathState (F : Type) [Field F] := PrefixState F Unit
abbrev SourceState := Zkc.Construction.Original.State (uniformCarriers F G)
abbrev RoundResult := Values (Component (assignment F G)) repeatState × SourceState (F := F) (G := G)

def producerValues {n : Nat} (state : MathState F n) :=
  SumcheckProverLaws.embedP (G := G) (state.entries, n, 1, state.point)

def verifierValues {n : Nat} (state : MathState F n) :=
  SumcheckVerifierLaws.embedV (G := G) (some state.point, some state.scalar)

def endpoints {n : Nat} (state : MathState F n) : F × F :=
  ((state.entries.take (state.entries.length / 2)).sum,
    (state.entries.drop (state.entries.length / 2)).sum)

omit [DecidableEq F] in
/-- The same decoded reference and restriction law as soundness prove the
actual producer expression is honest after every field reply. -/
theorem advance_honest {n : Nat} (state : MathState F (n + 1)) (challenge : F) :
    (state.advance (endpoints state) challenge).scalar =
      (state.advance (endpoints state) challenge).entries.sum := by
  let layout := Realizations.Sumcheck.Original.layout (F := F) (G := Unit) (Frame := Unit)
  let context : Realizations.Sumcheck.Original.Context := ⟨{}, 0⟩
  have message := layout.honest_endpoints state
  have evaluated := (TableReference.laws (F := F)).evaluation_eq (layout.table state) challenge trivial
  rw [← layout.restrict context state (endpoints state) challenge,
    layout.total] at evaluated
  rw [← TableReference.honest_polynomial, ← message, Message.endpointPolynomial_eval] at evaluated
  exact evaluated

/-- Exact source round return: all six optional slots, common reached history
and the original occurrence stack, for every typed query reply. -/
theorem round (payload : UnitPayload) (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (producerRouting validatorRouting : Original.Routing) (context : ProtocolContext)
    (separate : context.roles 0 ≠ context.roles 1)
    (index handle : Nat) (origins : ArtifactBinding.Origins)
    {n : Nat} (state : MathState F (n + 1))
    (shape : PrimitiveLibrary.HasShape state.entries (n + 1) 1)
    (bounded : state.entries.length < indexLimit)
    (honest : state.scalar = state.entries.sum)
    (construction : SourceState (F := F) (G := G))
    (producerRoutes : OriginalProducer.Routes producerRouting context construction.frames origins)
    (validatorRoutes : ArtifactBinding.Routes validatorRouting context construction.frames handle origins) :
    Readback (fun left right => ∃ challenge history,
      left = (producerValues (state.advance (endpoints state) challenge),
        ⟨construction.frames, history⟩) ∧
      right = (verifierValues (state.advance (endpoints state) challenge),
        ⟨construction.frames, history⟩))
      (Original.fold producerRouting
        (OriginalSumcheckLibrary.round payload context (context.roles 0)
          (.cons (some index) ((producerValues state).append (.cons none .nil)))) construction)
      (Original.fold validatorRouting
        (OriginalSumcheckLibrary.round payload context (context.roles 1)
          (.cons (some index) ((verifierValues state).append (.cons (some handle) .nil)))) construction) := by
  dsimp only [producerValues, verifierValues]
  rw [OriginalProducer.original_round payload bodies producerRouting context (Ne.symm separate)
    index none origins state.entries (n + 1) 1 state.point shape bounded (by omega)
    construction producerRoutes]
  rw [ArtifactBinding.original_round payload
    ⟨bodies.empty, bodies.append, bodies.width, bodies.variables, bodies.values⟩
    validatorRouting context separate index handle origins state.point state.scalar construction validatorRoutes]
  have boundary : state.scalar = (endpoints state).1 + (endpoints state).2 := by
    change state.scalar = (state.entries.take (state.entries.length / 2)).sum +
      (state.entries.drop (state.entries.length / 2)).sum
    rw [honest, ← List.sum_append, List.take_append_drop]
  unfold OriginalProducer.producer ArtifactBinding.verifier
  dsimp only
  refine Readback.sendReceive (carriers := uniformCarriers F G) (ty := .field "bls12-381.fr")
    _ _ _ _ _ _ (.field "bls12-381.fr" (endpoints state).1) (endpoints state).1
    (by simp [Domain.Payload.value]) ?_
  apply Readback.observeLeft
  apply Readback.observeRight
  refine Readback.sendReceive (carriers := uniformCarriers F G) (ty := .field "bls12-381.fr")
    _ _ _ _ _ _ (.field "bls12-381.fr" (endpoints state).2) (endpoints state).2
    (by simp [Domain.Payload.value]) ?_
  apply Readback.observeLeft
  apply Readback.observeRight
  simp only [show state.scalar = _ from boundary, ite_true, Original.queryField,
    producerRoutes.request, ↓reduceDIte, PIR.Process.bind]
  apply Readback.query _ _ (DomainReduction.drawRequest_of_request producerRoutes.request)
  intro reply
  apply Readback.observeLeft
  apply Readback.observeRight
  apply Readback.done
  let challenge : F := by simpa only [Domain.Raw, producerRoutes.request, Request.draw] using reply
  refine ⟨challenge, construction.history ++
    [.message origins.low (.field "bls12-381.fr" (endpoints state).1),
     .message origins.high (.field "bls12-381.fr" (endpoints state).2)] ++
    [.challenge origins.draw] ++ [.message origins.delivery (.field "bls12-381.fr" challenge)], ?_, ?_⟩
  · simp only [PrefixState.advance_entries, PrefixState.advance_point,
      Nat.add_sub_cancel, challenge]
    rfl
  · rfl

end ZkcSecurity.Realizations.Sumcheck.OriginalHonest
