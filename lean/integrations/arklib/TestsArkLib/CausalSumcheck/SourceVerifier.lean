import ZkcArkLib.Examples.CausalSumcheck.Iteration
import Mathlib.Algebra.Field.ZMod
import ZkcArkLib.Examples.CausalSumcheck.SourceVerifier

/-! Non-vacuity controls on the complete admitted Source and Reduction roots. -/
namespace TestsSecurity.CausalSumcheck.SourceVerifier

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.SumcheckVerifierLaws
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F : Type}

private theorem different_sites (context : ProtocolContext) :
    highSite context ≠ lowSite context := by
  unfold highSite lowSite qualifyProtocolSite
  cases context.applicationPrefix <;> simp

/-- The scalar state is the next HIGH reply. Delivery supplies the next state.
The old query branch returns zero and is replaced by the concrete service. -/
def network [Zero F] (context : ProtocolContext) (update : F → F → F) :
    PIR.MonadHandler ProbComp (participantInterface F Unit) F Unit
  | .receive (.field _) site peer, s =>
      if peer ≠ context.roles 0 then pure ⟨.stopped .refused, s, []⟩
      else if site = lowSite context then pure ⟨.returned 0, s, []⟩
      else if site = highSite context then pure ⟨.returned s, s, []⟩
      else pure ⟨.stopped .refused, s, []⟩
  | .receive .., s => pure ⟨.stopped .refused, s, []⟩
  | .send (ty := .field _) site peer r, s =>
      if site = deliverySite context ∧ peer = context.roles 0 then
        pure ⟨.returned (), update r s, []⟩
      else pure ⟨.stopped .refused, s, []⟩
  | .send .., s => pure ⟨.stopped .refused, s, []⟩
  | .query _ _ (.cons _ .nil), s => pure ⟨.returned (0 : F), s, []⟩

def handler [Zero F] [SampleableType F] (context : ProtocolContext) (handle : Nat)
    (update : F → F → F) :=
  withUniformQueries (network context update) [queryKey context handle]
    (fun _ => noOp) (fun _ _ => noOp)

/-- The actual receive route also checks the mapped sender, before any update. -/
theorem wrong_receive_peer [Zero F] [SampleableType F]
    (context : ProtocolContext) (handle : Nat) (update : F → F → F) (s : F) :
    handler context handle update
      (.receive (.field "bls12-381.fr") (lowSite context) (context.roles 0 + 1)) s =
        pure ⟨.stopped .refused, s, []⟩ := by
  simp [handler, network]

/-- Delivery to a different peer retains the refusal and the original state. -/
theorem wrong_send_peer [Zero F] [SampleableType F]
    (context : ProtocolContext) (handle : Nat) (update : F → F → F) (r s : F) :
    handler context handle update
      (.send (ty := .field "bls12-381.fr") (deliverySite context) (context.roles 0 + 1) r) s =
        pure ⟨.stopped .refused, s, []⟩ := by
  simp [handler, network]

/-- A receive label cannot silently substitute for the actual delivery label. -/
theorem wrong_delivery_site [Zero F] [SampleableType F]
    (context : ProtocolContext) (handle : Nat) (update : F → F → F) (r s : F) :
    handler context handle update
      (.send (ty := .field "bls12-381.fr") (lowSite context) (context.roles 0) r) s =
        pure ⟨.stopped .refused, s, []⟩ := by
  have different : lowSite context ≠ deliverySite context := by
    unfold lowSite deliverySite qualifyProtocolSite
    cases context.applicationPrefix <;> simp
  simp [handler, network, different]

private theorem query_handler [Zero F] [SampleableType F]
    (context : ProtocolContext) (handle : Nat) (update : F → F → F) (s : F) :
    withUniformQueries (network context update) [queryKey context handle]
        (fun _ => noOp) (fun _ _ => noOp)
        (.query (challengeSite context) "bls12-381.fr" (.cons handle .nil)) s =
      freshQuery (F := F) noOp (fun _ => noOp) s := by
  have law := withUniformQueries_queryKey (network context update)
    (fun _ => noOp) (fun _ _ => noOp) context handle s
  rw [participantActions_runM (F := F) (G := Unit)] at law
  exact law

section Processes
variable [Field F] [DecidableEq F] [SampleableType F]

set_option backward.isDefEq.respectTransparency false in
theorem round_exact (context : ProtocolContext) (handle : Nat)
    (update : F → F → F) (point : List F) (s : F) :
    (roundPresent (G := Unit) context handle (point, s)).runM
        (handler context handle update) s = (do
      let r ← ($ᵗ F)
      pure ⟨.returned (point ++ [r], r*s), update r s, []⟩) := by
  simp [roundPresent, PIR.Process.runM, query_handler, handler, network,
    different_sites context, freshQuery, noOp, result, PIR.Execution.followM]

theorem adaptive_two (context : ProtocolContext) (handle : Nat) :
    (PIR.repeatN 2 (roundPresent (G := Unit) context handle) ([], (1 : F))).runM
        (handler context handle (fun r _ => r)) 1 = (do
      let r1 ← ($ᵗ F)
      let r2 ← ($ᵗ F)
      pure ⟨.returned ([r1,r2], r1*r2), r2, []⟩) := by
  rw [PIR.repeatN, PIR.runM_bind, round_exact]
  simp only [bind_assoc, pure_bind, PIR.Execution.followM, List.nil_append, mul_one]
  apply bind_congr
  intro r1
  rw [PIR.repeatN, PIR.runM_bind, round_exact]
  simp [PIR.repeatN, PIR.Process.runM, PIR.Execution.followM, mul_comm]

theorem zero_two (context : ProtocolContext) (handle : Nat) :
    (PIR.repeatN 2 (roundPresent (G := Unit) context handle) ([], (0 : F))).runM
        (handler context handle (fun _ _ => 0)) 0 = (do
      let r1 ← ($ᵗ F)
      let r2 ← ($ᵗ F)
      pure ⟨.returned ([r1,r2], 0), 0, []⟩) := by
  rw [PIR.repeatN, PIR.runM_bind, round_exact]
  simp only [bind_assoc, pure_bind, PIR.Execution.followM, List.nil_append, mul_zero]
  apply bind_congr
  intro r1
  rw [PIR.repeatN, PIR.runM_bind, round_exact]
  simp [PIR.repeatN, PIR.Process.runM, PIR.Execution.followM]


omit [DecidableEq F] in
private theorem refused_query (context : ProtocolContext) (handle : Nat)
    (update : F → F → F) (s : F) :
    withUniformQueries (network context update) [queryKey context (handle+1)]
        (fun _ => noOp) (fun _ _ => noOp)
        (.query (challengeSite context) "bls12-381.fr" (.cons handle .nil)) s =
      pure ⟨.stopped .refused, s, []⟩ := by
  have law := withUniformQueries_unconfigured (network context update)
    [queryKey context (handle+1)] (fun _ => noOp) (fun _ _ => noOp)
    (challengeSite context) "bls12-381.fr" handle (by simp [queryKey]) s
  rw [participantActions_runM (F := F) (G := Unit)] at law
  exact law

theorem wrong_handle (context : ProtocolContext) (handle n : Nat)
    (update : F → F → F) (point : List F) (s : F) :
    (PIR.repeatN (n+1) (roundPresent (G := Unit) context handle) (point,s)).runM
        (withUniformQueries (network context update) [queryKey context (handle+1)]
          (fun _ => noOp) (fun _ _ => noOp)) s = pure ⟨.stopped .refused, s, []⟩ := by
  simp [PIR.repeatN, roundPresent, PIR.Process.bind, PIR.Process.runM,
    refused_query, network, different_sites context, PIR.Execution.followM]

end Processes


abbrev F5 := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem zero_table_decodes :
    ofList? 2 ([0,0,0,0] : List F5) = some (fun _ => 0) := by decide

theorem zero_table_observation (a b value : F5) :
    Causal.rawTerminal 2 [0,0,0,0] [a,b] value ↔ value = 0 := by
  rw [Causal.rawTerminal_eq_table _ _ zero_table_decodes]
  change Causal.tableTerminal (fun _ => (0 : F5)) (List.ofFn ![a,b]) value ↔ _
  rw [Causal.tableTerminal_ofFn]
  simp [extension, eq_comm]

theorem adaptive_positive_mass (context : ProtocolContext) (handle : Nat) :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (G := Unit) context handle) ([], (1 : F5))).runM
        (handler context handle (fun r _ => r)) 1
      pure (Causal.accepts (Causal.rawTerminal 2 [0,0,0,0]) e)) = 9/25 := by
  rw [adaptive_two]
  simp only [bind_assoc, pure_bind, Causal.accepts, zero_table_observation]
  change Pr{let a ← ($ᵗ F5); let b ← ($ᵗ F5)}[a*b=0] = _
  rw [← SampleableType.prEvent_uniformSample_prod (fun p : F5 × F5 => p.1*p.2=0),
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun p : F5 × F5 => p.1*p.2=0)).card = 9 := by decide
  rw [count]
  norm_num [F5]

theorem true_claim_mass (context : ProtocolContext) (handle : Nat) :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (G := Unit) context handle) ([], (0 : F5))).runM
        (handler context handle (fun _ _ => 0)) 0
      pure (Causal.accepts (Causal.rawTerminal 2 [0,0,0,0]) e)) = 1 := by
  rw [zero_two]
  simp [Causal.accepts, zero_table_observation, mass]



/-- An external three-variable zero table leaves one variable after two draws. -/
theorem zero_residual_observation (a b value : F5) :
    Causal.residualTerminal 1 2 (fun _ => 0) [a,b] value ↔ value = 0 := by
  rw [Causal.residualTerminal_eq_marginal]
  change Causal.tableTerminal (fun _ => (0 : F5)) (List.ofFn ![a,b]) value ↔ _
  rw [Causal.tableTerminal_ofFn]
  simp [extension, eq_comm]

theorem residual_positive_mass (context : ProtocolContext) (handle : Nat) :
    mass (do
      let e ← (PIR.repeatN 2 (roundPresent (G := Unit) context handle) ([], (1 : F5))).runM
        (handler context handle (fun r _ => r)) 1
      pure (Causal.accepts (Causal.residualTerminal 1 2 (fun _ => 0)) e)) = 9/25 := by
  rw [adaptive_two]
  simp only [bind_assoc, pure_bind, Causal.accepts, zero_residual_observation]
  change Pr{let a ← ($ᵗ F5); let b ← ($ᵗ F5)}[a*b=0] = _
  rw [← SampleableType.prEvent_uniformSample_prod (fun p : F5 × F5 => p.1*p.2=0),
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun p : F5 × F5 => p.1*p.2=0)).card = 9 := by decide
  rw [count]
  norm_num [F5]

open ZkcExamples.Structured
open ZkcSecurity.Examples.CausalSumcheck.SourceVerifier

/-- The positive-mass control starts with a false V claim. -/
theorem initial_claim_false : (1 : F5) ≠ ([0,0,0,0] : List F5).sum := by decide

/-- Actual admitted root, real child route and original raw-V Boolean checker. -/
theorem source_false_positive (handle : Nat) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F5 Unit 1
        (SumcheckSourceVerifier.sourceRootInputs (some [0,0,0,0]) (some 1)
          (some 2) (some handle))).runM
        (handler SumcheckSourceVerifier.childContext handle (fun r _ => r)) 1
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = 9/25 := by
  rw [source_observation _ 2 (by decide) _ _ zero_table_decodes]
  exact adaptive_positive_mass SumcheckSourceVerifier.childContext handle

/-- True claim and actual checker return true with probability one. -/
theorem source_true_claim (handle : Nat) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F5 Unit 1
        (SumcheckSourceVerifier.sourceRootInputs (some [0,0,0,0]) (some 0)
          (some 2) (some handle))).runM
        (handler SumcheckSourceVerifier.childContext handle (fun _ _ => 0)) 0
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = 1 := by
  rw [source_observation _ 2 (by decide) _ _ zero_table_decodes]
  exact true_claim_mass SumcheckSourceVerifier.childContext handle

/-- A wrong installed handle reaches the actual query and retains its refusal. -/
theorem source_wrong_handle_record (handle : Nat) :
    (SumcheckSourceViews.imported.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0,0,0,0]) (some 1)
        (some 2) (some handle))).runM
      (handler SumcheckSourceVerifier.childContext (handle+1) (fun r _ => r)) 1 =
        pure ⟨.stopped .refused, 1, []⟩ := by
  change PIR.Process.runM (A := Values (Component (assignment F5 Unit)) [.boolean])
    (handler SumcheckSourceVerifier.childContext (handle+1) (fun r _ => r))
    (SumcheckSourceViews.imported.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0,0,0,0]) (some 1)
        (some 2) (some handle))) 1 =
      pure ⟨.stopped .refused, 1, []⟩
  rw [source_present 2 (by decide) _ _ zero_table_decodes, PIR.runM_bind]
  simp only [handler]
  rw [wrong_handle SumcheckSourceVerifier.childContext handle 1]
  simp [PIR.Execution.followM]

theorem source_wrong_handle_mass (handle : Nat) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F5 Unit 1
        (SumcheckSourceVerifier.sourceRootInputs (some [0,0,0,0]) (some 1)
          (some 2) (some handle))).runM
        (handler SumcheckSourceVerifier.childContext (handle+1) (fun r _ => r)) 1
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = 0 := by
  rw [source_wrong_handle_record]
  simp [returnedSatisfies]

/-- With zero rounds the original checker rejects a false constant claim. -/
theorem source_zero_false_record (handle : Nat) :
    (SumcheckSourceViews.imported.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
        (some 0) (some handle))).runM
      (handler SumcheckSourceVerifier.childContext handle (fun r _ => r)) 1 =
        pure ⟨.returned (.cons (some false) .nil), 1, []⟩ := by
  change PIR.Process.runM (A := Values (Component (assignment F5 Unit)) [.boolean])
    (handler SumcheckSourceVerifier.childContext handle (fun r _ => r))
    (SumcheckSourceViews.imported.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
        (some 0) (some handle))) 1 =
      pure ⟨.returned (.cons (some false) .nil), 1, []⟩
  rw [source_present 0 (by decide) [0] (fun _ => 0) (by decide)]
  simp [PIR.repeatN, PIR.Process.bind, PIR.Process.runM, checkedResult, extension]

theorem source_zero_false_mass (handle : Nat) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F5 Unit 1
        (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
          (some 0) (some handle))).runM
        (handler SumcheckSourceVerifier.childContext handle (fun r _ => r)) 1
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = 0 := by
  rw [source_zero_false_record]
  change mass (pure ((some false : Option Bool) = some true)) = 0
  simp


/-- Real Reduction root, arbitrary P inputs, and an external original table.
The event observes residual truth; it is not a checker acceptance event. -/
theorem reduction_residual_positive (xs : Option (List F5)) (dimension : Option Nat)
    (handle : Nat) :
    mass (do
      let e ← (SumcheckReduceViews.imported.program.participant F5 Unit 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some 1)
          (some 2) (some handle))).runM
        (handler (ProtocolContext.enter {} "s3" [0,1]) handle (fun r _ => r)) 1
      pure (returnedSatisfies (residualObservation 1 2 (fun _ => 0)) e)) = 9/25 := by
  rw [reduction_observation _ xs dimension 1 2 (by decide)]
  exact residual_positive_mass (ProtocolContext.enter {} "s3" [0,1]) handle


/-- Padding coordinates is insufficient: a short point is not terminal truth. -/
theorem short_point_not_terminal : ¬ Causal.rawTerminal 2 ([0,0,0,0] : List F5) [] 0 := by
  rw [Causal.rawTerminal_eq_table _ _ zero_table_decodes]
  rintro ⟨point, chronology, _⟩
  have length := congrArg List.length chronology
  simp at length

/-- The external original table in the residual control also starts false. -/
theorem residual_initial_claim_false :
    (1 : F5) ≠ booleanSum (fun _ : Fin (1+2) → Bool => (0 : F5)) := by decide

/-- Runtime count admission refuses before querying, even for malformed rawV. -/
theorem source_excess_record (handle : Nat) (initial : F5) :
    (SumcheckSourceViews.imported.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
        (some 3) (some handle))).runM
      (handler SumcheckSourceVerifier.childContext handle (fun r _ => r)) initial =
        pure ⟨.stopped .refused, initial, []⟩ := by
  change PIR.Process.runM (A := Values (Component (assignment F5 Unit)) [.boolean])
    (handler SumcheckSourceVerifier.childContext handle (fun r _ => r))
    (SumcheckSourceViews.program.participant F5 Unit 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
        (some 3) (some handle))) initial = pure ⟨.stopped .refused, initial, []⟩
  rw [SumcheckSourceVerifier.verifier_excess _ _ _ _ (by decide)]
  rfl

/-- Reduction's own maximum four is independent of the other root's maximum. -/
theorem reduction_excess_record (xs : Option (List F5)) (dimension : Option Nat)
    (handle : Nat) (initial : F5) :
    (SumcheckReduceViews.imported.program.participant F5 Unit 1
      (SumcheckReduceVerifier.reduceRootInputs xs dimension (some 1)
        (some 5) (some handle))).runM
      (handler (ProtocolContext.enter {} "s3" [0,1]) handle (fun r _ => r)) initial =
        pure ⟨.stopped .refused, initial, []⟩ := by
  change PIR.Process.runM
    (A := Values (Component (assignment F5 Unit)) SumcheckReduceBodies.runSignature.outputs)
    (handler (ProtocolContext.enter {} "s3" [0,1]) handle (fun r _ => r))
    (SumcheckReduceViews.program.participant F5 Unit 1
      (SumcheckReduceVerifier.reduceRootInputs xs dimension (some 1)
        (some 5) (some handle))) initial = pure ⟨.stopped .refused, initial, []⟩
  rw [SumcheckReduceVerifier.verifier_excess _ _ _ _ (by decide)]
  rfl

/-- Excess Source counts have zero returned-true mass, without normalization. -/
theorem source_excess_mass (handle : Nat) (initial : F5) :
    mass (do
      let e ← (SumcheckSourceViews.imported.program.participant F5 Unit 1
        (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1)
          (some 3) (some handle))).runM
        (handler SumcheckSourceVerifier.childContext handle (fun r _ => r)) initial
      pure (returnedSatisfies (fun outputs => outputs.get .here = some true) e)) = 0 := by
  rw [source_excess_record]
  simp [returnedSatisfies]

/-- Excess Reduction counts have zero residual-observation mass for every table. -/
theorem reduction_excess_mass (xs : Option (List F5)) (dimension : Option Nat)
    (remaining : Nat) (table : Table F5 (remaining + 5)) (handle : Nat) (initial : F5) :
    mass (do
      let e ← (SumcheckReduceViews.imported.program.participant F5 Unit 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension (some 1)
          (some 5) (some handle))).runM
        (handler (ProtocolContext.enter {} "s3" [0,1]) handle (fun r _ => r)) initial
      pure (returnedSatisfies (residualObservation remaining 5 table) e)) = 0 := by
  rw [reduction_excess_record]
  simp [returnedSatisfies]

end TestsSecurity.CausalSumcheck.SourceVerifier
