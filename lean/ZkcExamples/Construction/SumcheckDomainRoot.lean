module

public import ZkcExamples.Construction.SumcheckDomainLoop
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section
/-! A total all-reply connection for the actual retained Sumcheck participant. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
attribute [local irreducible] reduce roundState
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def frame (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim), .data (.index rounds),
    .transcript SumcheckProof.context.suite history]

def terminal (values : List F) (state : RoundState F G) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G)) :=
  let result (decision : Bool) := PIR.Process.done
    [.data (.boolean decision), .transcript SumcheckProof.context.suite state.history]
  if state.point.length < indexLimit then
    if state.point.length < 64 then
      if values.length < indexLimit then
        result (Zkc.Protocols.Sumcheck.Multilinear.check (n := 0 + state.point.length) values
          (Zkc.Polynomial.Quadratic.point state.point.length
            (Zkc.Polynomial.coordinates state.point.length state.point) Fin.elim0) state.scalar)
      else .halt .exhausted
    else result false
  else .halt .exhausted

def rootProcess (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (uniformCarriers F G)) :=
  if rounds ≤ 2 then
    (reduce (List.range rounds) [] claim history).bind (terminal values)
  else .halt .refused

def rootProjection (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (uniformCarriers F G)) :=
  ((Domain.participant (ringModel F G) SumcheckProof.program SumcheckProof.context SumcheckProof.participant
      (frame values claim rounds history)).bind fun result => .done result.values).interpret
    Original.forgetCheckpoints

theorem root_projection (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    rootProjection values claim rounds history = rootProcess values claim rounds history := by
  unfold rootProjection
  rw [← artifact_identity, participant_eq]
  simp only [view, body, bodyStep0, bodyStep1, bodyStep2, bodyStep3, bodyStep4]
  normalize_artifact_operations [pending_helper (F := F) (G := G), openClaim_helper (F := F) (G := G), atPrefix_helper (F := F) (G := G), context_suite]
    unfolding [inputSorts, outputSorts, returned, frame, PIR.Process.interpret,
      Original.forgetCheckpoints, Structured.Ty.isHandle, Bool.not_false, Bool.not_true]
  by_cases bounded : rounds ≤ 2
  all_goals normalize_artifact_operations [bounded, context_suite]
    unfolding [Domain.View.loop, rootProcess, PIR.Process.interpret, Original.forgetCheckpoints]
  simp only [PIR.Process.interpret_bind]
  have loopEq := loop_projection (.data (.vector "bls12-381.fr" values))
    (.data (.field "bls12-381.fr" claim)) (.data (.index rounds))
    (.transcript SumcheckProof.context.suite history) (.data (.vector "bls12-381.fr" []))
    (.data (.field "bls12-381.fr" claim)) (.data (.vector "bls12-381.fr" []))
    (.data (.field "bls12-381.fr" claim)) (List.range rounds) [] claim history
  simp only [round_results, carried, context_suite] at loopEq
  rw [loopEq]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  congr 1
  funext state
  cases state with
  | mk point scalar suffix =>
      normalize_artifact_operations [atPrefix_helper (F := F) (G := G), check_helper (F := F) (G := G), context_suite]
        unfolding [RoundState.values, carried, terminal, PIR.Process.interpret,
          Original.forgetCheckpoints, List.append_assoc]
      split_ifs <;> normalize_artifact_operations [context_suite]
        unfolding [PIR.Process.interpret, Original.forgetCheckpoints]

end ZkcExamples.Construction.SumcheckDomainConnection
