module

public import ZkcSecurity.Examples.CausalSumcheck.UniformService
public import ZkcArkLib.Sumcheck.Multilinear.Causal
public import ZkcExamples.Structured.SumcheckVerifierProcess

@[expose] public section

namespace ZkcSecurity.Examples.CausalSumcheck.Iteration

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear
open ZkcSecurity.VCVio.Execution
open ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcExamples.Structured

variable {F G S E : Type} [Field F] [DecidableEq F]

/-- The first actual scalar receive at the immutable child context. -/
abbrev lowAction (context : ProtocolContext) : (participantInterface F G).Op :=
  .receive (.field "bls12-381.fr")
    (SumcheckVerifierLaws.lowSite context) (context.roles 0)

/-- HIGH is a separate action and receives the state returned by LOW. -/
abbrev highAction (context : ProtocolContext) : (participantInterface F G).Op :=
  .receive (.field "bls12-381.fr")
    (SumcheckVerifierLaws.highSite context) (context.roles 0)

abbrev sendAction (context : ProtocolContext) (r : F) : (participantInterface F G).Op :=
  .send (ty := .field "bls12-381.fr")
    (SumcheckVerifierLaws.deliverySite context) (context.roles 0) r

/-- Construct the existing causal strategy from the actual ordered network
actions. The source append/interpolation view determines the next point/claim.
This factory introduces no process evaluator or new strategy carrier. -/
def strategyOf (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle : Nat) :
    (n : Nat) → List F → F → Causal.Strategy F S E n
  | 0, _, _ => noOp
  | n + 1, point, _ =>
      mapPhase (fun lo => (lo,
        mapPhase (fun hi => (hi, {
          beforeDraw := before (queryKey context handle)
          publicAbort := noOp
          afterDraw := after (queryKey context handle)
          deliver := fun r => mapPhase
            (fun _ => strategyOf handler before after context handle n
              (point ++ [r]) (evaluate (lo, hi) r))
            ((participantActions F G (sendAction context r)).runM handler)
          advance := fun _ => noOp }))
          ((participantActions F G (highAction context)).runM handler)))
        ((participantActions F G (lowAction context)).runM handler)

/-- Normalize the existing causal execution to its real phases. Both receive
records, callbacks and the actual send record survive, including every stop.
The guard is evaluated before the service callbacks and designated draw. -/
theorem strategyOf_run_succ [SampleableType F]
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle n : Nat) (point : List F) (claim : F) (s : S) :
    Causal.run (n + 1) claim point
      (strategyOf handler before after context handle (n + 1) point claim) s = (do
        let low ← (participantActions F G (lowAction context)).runM handler s
        low.followM fun lo s => do
          let high ← (participantActions F G (highAction context)).runM handler s
          high.followM fun hi s =>
            if boundary (lo, hi) = claim then do
              let query ← freshQuery (before (queryKey context handle))
                (after (queryKey context handle)) s
              query.followM fun r s => do
                let sent ← (participantActions F G (sendAction context r)).runM handler s
                sent.followM fun _ s => Causal.run n (evaluate (lo, hi) r) (point ++ [r])
                  (strategyOf handler before after context handle n
                    (point ++ [r]) (evaluate (lo, hi) r)) s
            else pure ⟨.stopped .reject, s, []⟩) := by
  simp only [Causal.run, Causal.prepare, strategyOf, mapPhase, bind_assoc,
    PIR.followM_assoc, pure_bind, follow_result]
  apply bind_congr
  intro low
  congr 1
  funext lo s
  apply bind_congr
  intro high
  congr 1
  funext hi s
  by_cases guard : boundary (lo, hi) = claim
  · simp [guard, freshQuery, bind_assoc, PIR.followM_assoc, noOp, mapPhase]
  · simp [guard, noOp, result, Causal.stopped, PIR.Execution.followM]

/-- Distribution transport over the source owner's shared present-state process.
The only provider premise is the local query law at every state. -/
theorem repeat_distribution_of_queryLaw [SampleableType F]
    (handler : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle : Nat)
    (queryLaw : ∀ s, SameDist
      ((participantActions F G (.query (queryKey context handle).1
        (queryKey context handle).2.1 (.cons handle .nil))).runM handler s)
      (freshQuery (F := F) (before (queryKey context handle))
        (after (queryKey context handle)) s))
    (n : Nat) (point : List F) (claim : F) (s : S) :
    SameDist
      ((PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        (point, claim)).runM handler s)
      (Causal.run n claim point
        (strategyOf handler before after context handle n point claim) s) := by
  induction n generalizing point claim s with
  | zero =>
    simp only [PIR.repeatN, PIR.Proc.runM, Causal.run, strategyOf, noOp,
      pure_bind, follow_result]
    exact SameDist.refl _
  | succ n ih =>
    rw [PIR.repeatN, strategyOf_run_succ]
    simp only [participantActions_runM (F := F) (G := G)]
    simp only [SumcheckVerifierLaws.roundPresent, PIR.Proc.bind, PIR.Proc.runM]
    refine SameDist.follow_congr (SameDist.refl (handler (lowAction context) s))
      (fun _ _ => True) _ _
      (by intro e he a returned; trivial) ?_
    intro lo s _
    refine SameDist.follow_congr (SameDist.refl (handler (highAction context) s))
      (fun _ _ => True) _ _
      (by intro e he a returned; trivial) ?_
    intro hi s _
    by_cases guard : claim = lo + hi
    · have pairGuard : boundary (lo, hi) = claim := guard.symm
      simp only [guard, pairGuard, ite_true, PIR.Proc.bind, PIR.Proc.runM]
      have localLaw := queryLaw s
      rw [participantActions_runM (F := F) (G := G)] at localLaw
      refine SameDist.follow_congr (A := F) localLaw (fun _ _ => True) _ _
        (by intro e he a returned; trivial) ?_
      intro r s _
      refine SameDist.follow_congr (SameDist.refl (handler (sendAction context r) s))
        (fun _ _ => True) _ _
        (by intro e he a returned; trivial) ?_
      intro acknowledgment s _
      exact ih (point ++ [r]) (evaluate (lo, hi) r) s
    · have pairGuard : ¬ boundary (lo, hi) = claim := fun same => guard same.symm
      simp only [guard, pairGuard, ite_false, PIR.Proc.bind, PIR.Proc.runM]
      exact SameDist.refl _

theorem repeat_uniform_distribution [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (ports : List Key) (before : Key → Phase S E Unit)
    (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle : Nat)
    (configured : queryKey context handle ∈ ports)
    (n : Nat) (point : List F) (claim : F) (s : S) :
    let handler := withUniformQueries network ports before after
    SameDist
      ((PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        (point, claim)).runM handler s)
      (Causal.run n claim point
        (strategyOf handler before after context handle n point claim) s) := by
  apply repeat_distribution_of_queryLaw
  intro s
  exact congrArg _ (withUniformQueries_query network ports before after
    (queryKey context handle).1 (queryKey context handle).2.1 handle configured s)

open Zkc.Polynomial.Multilinear
open scoped ENNReal

/-- The shared present-state process with a concrete service satisfies the raw
public-table observation bound. Actual source root/checker association is a
separate consumer of this theorem. -/
theorem repeat_uniform_publicTable_soundness [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle n : Nat) (raw : List F) (table : Table F n)
    (decoded : ofList? n raw = some table) (claim : F) (falseClaim : claim ≠ raw.sum)
    (s : S) :
    let handler := withUniformQueries network [queryKey context handle] before after
    mass (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        ([], claim)).runM handler s
      pure (Causal.accepts (Causal.rawTerminal n raw) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  dsimp only
  let handler := withUniformQueries network [queryKey context handle] before after
  have same := repeat_uniform_distribution network [queryKey context handle]
    before after context handle (by simp) n [] claim s
  have observed := same.bind_left (fun e => pure (Causal.accepts (Causal.rawTerminal n raw) e))
  have equality := congrArg (fun measure => measure {True}) observed
  calc
    _ = mass (Causal.phaseGame n claim []
        (strategyOf handler before after context handle n [] claim) s
        (Causal.rawTerminal n raw)) := equality
    _ ≤ _ := Causal.phase_publicTable_soundness raw table decoded claim _ s falseClaim

/-- Observe the residual relation against an external original table. The
shared reduction process has no Boolean terminal checker. -/
theorem repeat_uniform_residual_soundness [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (context : ProtocolContext) (handle remaining n : Nat)
    (table : Table F (remaining + n)) (claim : F)
    (falseClaim : claim ≠ booleanSum table) (s : S) :
    let handler := withUniformQueries network [queryKey context handle] before after
    mass (do
      let e ← (PIR.repeatN n (SumcheckVerifierLaws.roundPresent context handle)
        ([], claim)).runM handler s
      pure (Causal.accepts (Causal.residualTerminal remaining n table) e)) ≤
        (n : ENNReal) / Fintype.card F := by
  dsimp only
  let handler := withUniformQueries network [queryKey context handle] before after
  have same := repeat_uniform_distribution network [queryKey context handle]
    before after context handle (by simp) n [] claim s
  have observed := same.bind_left
    (fun e => pure (Causal.accepts (Causal.residualTerminal remaining n table) e))
  have equality := congrArg (fun measure => measure {True}) observed
  calc
    _ = mass (Causal.phaseGame n claim []
        (strategyOf handler before after context handle n [] claim) s
        (Causal.residualTerminal remaining n table)) := equality
    _ ≤ _ := Causal.residual_phase_soundness table claim _ s falseClaim

end ZkcSecurity.Examples.CausalSumcheck.Iteration
