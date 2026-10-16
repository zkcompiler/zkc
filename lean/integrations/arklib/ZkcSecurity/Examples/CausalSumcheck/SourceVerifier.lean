module

public import ZkcSecurity.Examples.CausalSumcheck.Iteration
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckReduceVerifier
public import Zkc.Polynomial.Coordinates
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

namespace ZkcSecurity.Examples.CausalSumcheck.SourceVerifier

open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.Examples.CausalSumcheck.Iteration
open scoped ENNReal

variable {F G S E : Type} [Field F] [DecidableEq F]

/-- Length is part of the terminal predicate even for malformed short points. -/
private theorem rawTerminal_iff_coordinates {n : Nat} (raw : List F)
    (table : Table F n) (decoded : ofList? n raw = some table)
    (point : List F) (claim : F) :
    Causal.rawTerminal n raw point claim ↔
      point.length = n ∧ extension n table (coordinates n point) = claim := by
  rw [Causal.rawTerminal_eq_table raw table decoded]
  constructor
  · rintro ⟨values, rfl, evaluation⟩
    exact ⟨List.length_ofFn, by simpa only [coordinates_ofFn] using evaluation⟩
  · rintro ⟨length, evaluation⟩
    exact ⟨coordinates n point, ofFn_coordinates point length, evaluation⟩

omit [Field F] [DecidableEq F] in
private theorem decoded_count_two_representable {n : Nat} (raw : List F)
    (table : Table F n) (decoded : ofList? n raw = some table)
    (admitted : n ≤ 2) : raw.length < indexLimit := by
  rw [ofList?_length raw table decoded]
  have size : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) admitted
  exact lt_of_le_of_lt size (by decide : 2 ^ 2 < indexLimit)

/-- This is a final value conversion; prior stopped records survive unchanged. -/
private theorem observation_bind_done {I : PIR.Signature} {A B : Type}
    (handler : PIR.MonadHandler ProbComp I S E) (process : PIR.Proc I A)
    (convert : A → B) (predicate : B → Prop) (s : S) :
    (do
      let e ← (process.bind (fun a => .done (convert a))).runM handler s
      pure (returnedSatisfies predicate e)) = (do
      let e ← process.runM handler s
      pure (returnedSatisfies (fun a => predicate (convert a)) e)) := by
  simp only [PIR.runM_bind, bind_assoc]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> simp [PIR.Execution.followM, PIR.Proc.runM, returnedSatisfies]

/-- The source terminal's actual Boolean output, after its checked equation. -/
abbrev checkedResult (n : Nat) (table : Table F n) (pc : List F × F) :
    Values (Component (assignment F G)) [.boolean] :=
  .cons (some (decide (pc.1.length = n ∧ extension n table (coordinates n pc.1) = pc.2))) .nil

/-- The observer reads V's two original outputs; Reduction has no Boolean checker. -/
def residualObservation (remaining n : Nat) (table : Table F (remaining + n))
    (outputs : Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs) :
    Prop :=
  match outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here))) with
  | some point, some claim => Causal.residualTerminal remaining n table point claim
  | _, _ => False

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact process equation, retaining all interactions, stops and final output
conversion. Its subject includes admission of the exported complete snapshot. -/
theorem source_present (n : Nat) (admitted : n ≤ 2) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (handle : Nat) :
    SumcheckSourceViews.imported.program.participant F G 1
      (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n) (some handle)) =
      (PIR.repeatN n (SumcheckVerifierLaws.roundPresent SumcheckSourceVerifier.childContext handle)
        ([], claim)).bind (fun pc => .done (checkedResult n table pc)) := by
  change SumcheckSourceViews.program.participant F G 1 _ = _
  rw [SumcheckSourceVerifier.verifier_checked n admitted rawV (some claim) (some handle)
    table decoded (decoded_count_two_representable rawV table decoded admitted)]
  rw [SumcheckVerifierLaws.repeat_present SumcheckSourceVerifier.childContext handle n ([], claim)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl

/-- The actual returned-present-true event equals the shared process terminal
observation. This equation needs no provider premise and keeps stops false. -/
theorem source_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (n : Nat) (admitted : n ≤ 2) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (handle : Nat) (s : S) :
    (do
      let e ← (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))).runM handler s
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        SumcheckSourceVerifier.childContext handle) ([], claim)).runM handler s
      pure (Causal.accepts (Causal.rawTerminal n rawV) e)) := by
  change (do
    let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) [.boolean]) handler
      (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))) s
    pure (returnedSatisfies
      (fun outputs : Values (Component (assignment F G)) [.boolean] =>
        outputs.get .here = some true) e)) = _
  rw [source_present n admitted rawV table decoded claim handle, observation_bind_done]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> simp [returnedSatisfies, Causal.accepts, checkedResult, Values.get,
      rawTerminal_iff_coordinates rawV table decoded]

/-- Full imported Sumcheck returned-true bound for arbitrary receive/send
behavior and all initial states. The concrete service discharges freshness and
routing; the source's actual checker and count admission are internal. -/
theorem source_returned_true_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (rawV : List F)
    (table : Table F n) (decoded : ofList? n rawV = some table)
    (claim : F) (falseClaim : claim ≠ rawV.sum) (handle : Nat) (s : S) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle]
              before after) s
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  by_cases admitted : n ≤ 2
  · rw [source_observation _ n admitted rawV table decoded claim handle s]
    exact repeat_uniform_publicTable_soundness network before after
      SumcheckSourceVerifier.childContext handle n rawV table decoded claim falseClaim s
  · change mass (do
      let e ← PIR.Proc.runM (A := Values (Component (assignment F G)) [.boolean])
        (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle]
          before after)
        (SumcheckSourceViews.program.participant F G 1
          (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n)
            (some handle))) s
      pure (returnedSatisfies
        (fun outputs : Values (Component (assignment F G)) [.boolean] =>
          outputs.get .here = some true) e)) ≤ _
    rw [SumcheckSourceVerifier.verifier_excess (some rawV) (some claim) n (some handle)
      (Nat.lt_of_not_ge admitted)]
    simp [PIR.Proc.runM, returnedSatisfies]

/-- Original Reduction root output selection after the shared source process.
Prover inputs are arbitrary; no association to the external table is imposed. -/
theorem reduction_present (xs : Option (List F)) (dimension : Option Nat)
    (n : Nat) (admitted : n ≤ 4) (claim : F) (handle : Nat) :
    SumcheckReduceViews.imported.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n) (some handle)) =
      (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0,1]) handle) ([], claim)).bind
          (fun pc => .done (SumcheckReduceVerifier.reduceRootResults (some pc.1, some pc.2))) := by
  change SumcheckReduceViews.program.participant F G 1 _ = _
  rw [SumcheckReduceVerifier.verifier_optional]
  simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
  rw [SumcheckVerifierLaws.repeat_present _ handle n ([], claim)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]
  rfl

/-- Exact observation of the complete Reduction root, without a Boolean checker. -/
theorem reduction_observation
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (xs : Option (List F)) (dimension : Option Nat)
    (remaining n : Nat) (admitted : n ≤ 4) (table : Table F (remaining+n))
    (claim : F) (handle : Nat) (s : S) :
    (do
      let e ← (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))).runM handler s
      pure (returnedSatisfies (residualObservation remaining n table) e)) = (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent
        (ProtocolContext.enter {} "s3" [0,1]) handle) ([], claim)).runM handler s
      pure (Causal.accepts (Causal.residualTerminal remaining n table) e)) := by
  change (do
    let e ← PIR.Proc.runM
      (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs) handler
      (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))) s
    pure (returnedSatisfies (residualObservation remaining n table) e)) = _
  rw [reduction_present xs dimension n admitted claim handle, observation_bind_done]
  apply bind_congr
  intro e
  cases e with
  | mk outcome state events =>
    cases outcome <;> rfl

/-- Full imported Reduction residual bound against an external original table.
This root returns a reduced relation, not an acceptance Boolean. -/
theorem reduction_residual_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (xs : Option (List F)) (dimension : Option Nat)
    (remaining n : Nat) (table : Table F (remaining+n))
    (claim : F) (falseClaim : claim ≠ booleanSum table) (handle : Nat) (s : S) :
    mass (do
      let e ← (SumcheckReduceViews.imported.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
          (some handle))).runM
            (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0,1]) handle]
              before after) s
      pure (returnedSatisfies (residualObservation remaining n table) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  by_cases admitted : n ≤ 4
  · rw [reduction_observation _ xs dimension remaining n admitted table claim handle s]
    exact repeat_uniform_residual_soundness network before after
      (ProtocolContext.enter {} "s3" [0,1]) handle remaining n table claim falseClaim s
  · change mass (do
      let e ← PIR.Proc.runM
        (A := Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs)
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s3" [0,1]) handle]
          before after)
        (SumcheckReduceViews.program.participant F G 1
          (SumcheckReduceVerifier.reduceRootInputs xs dimension (some claim) (some n)
            (some handle))) s
      pure (returnedSatisfies (residualObservation remaining n table) e)) ≤ _
    rw [SumcheckReduceVerifier.verifier_excess xs dimension (some claim) n
      (Nat.lt_of_not_ge admitted) (some handle)]
    simp [PIR.Proc.runM, returnedSatisfies]

end ZkcSecurity.Examples.CausalSumcheck.SourceVerifier
