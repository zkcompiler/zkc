module

public import ZkcArkLibExamples.CausalSumcheck.Operations

@[expose] public section


namespace ZkcSecurity.Examples.CausalSumcheck

open OracleComp OracleSpec
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F G S E A B : Type} {I : PIR.Signature}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (sites : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)
  (h : PIR.MonadHandler ProbComp I S E) (names : Sites)
  (before : Phase S E Unit) (after : F → Phase S E Unit)
  (advance terminal : Message F → F → PIR.Process I Unit)

/-- All non-query local operations are extracted using the actual interpreter.
    These phases describe joint execution; trusted Process work is not a P action. -/
def phaseTail (pair : Message F) : AfterPair F S E (Strategy F S E 0) where
  beforeDraw := fun s => do
    let marked ← (sites.mark names.query).runM h s
    marked.followM fun _ s => before s
  publicAbort := noOp
  afterDraw := after
  deliver := fun r => mapPhase (fun _ => (terminal pair r).runM h)
    (((sites.mark names.delivery).bind fun _ => actions (sendAction names.delivery r)).runM h)
  advance := fun r => (advance pair r).runM h

def phaseStrategy : Strategy F S E 1 :=
  mapPhase (fun lo => (lo,
    mapPhase (fun hi => (hi, phaseTail sites actions h names before after advance terminal (lo, hi)))
      ((actions (lowAction names.high)).runM h)))
    (((sites.mark names.round).bind fun _ => actions (lowAction names.low)).runM h)

set_option backward.isDefEq.respectTransparency false in
/-- The only non-definitional operational premise is local to the one query.
    Receives, send, marks, trusted advance and terminal work retain their exact
    handlers. No equality or inequality of entire games appears as a premise. -/
theorem one_round_execution [SampleableType F]
    (tables : Evaluation.ComponentTables F G I) (service : Nat) (claim : F) (s : S)
    (queryLaw : ∀ s, (actions (queryAction names.query service)).runM h s =
      freshQuery before after s) :
    (scalarRound sites actions tables names service claim advance terminal).runM h s =
      run 1 claim [] (phaseStrategy sites actions h names before after advance terminal) s := by
  rw [scalarRound_eq]
  simp only [PIR.runM_bind]
  simp only [run, prepare, phaseStrategy, mapPhase, bind_assoc, PIR.followM_assoc,
    follow_result, pure_bind, PIR.runM_bind, bind_assoc, PIR.followM_assoc]
  apply bind_congr
  intro marked
  apply congrArg (PIR.Execution.followM marked)
  funext u s
  simp only [PIR.runM_bind]
  apply bind_congr
  intro low
  apply congrArg (PIR.Execution.followM low)
  funext lo s
  simp only [PIR.runM_bind]
  apply bind_congr
  intro high
  apply congrArg (PIR.Execution.followM high)
  funext hi s
  by_cases passed : boundary (lo, hi) = claim
  · simp only [ite_eq_left passed, phaseTail, mapPhase,
      PIR.runM_bind, bind_assoc, PIR.followM_assoc, follow_result, pure_bind]
    simp only [runM_bind_function, queryLaw, freshQuery, bind_assoc]
    apply bind_congr; intro queryMark
    apply congrArg (PIR.Execution.followM queryMark)
    funext u s
    apply bind_congr; intro ready
    dsimp only [services] at *
    rw [PIR.followM_assoc]
    apply congrArg (PIR.Execution.followM ready)
    funext u s
    rw [bind_assoc]
    apply bind_congr; intro r
    rw [bind_assoc]
    apply bind_congr; intro queried
    rw [PIR.followM_assoc]
    simp only [pure_bind, follow_result]
    rfl
  · simp [passed, phaseTail, noOp, result, stopped, PIR.Process.runM, PIR.Execution.followM]

def acceptanceOf (process : PIR.Process I (List F × F)) (s : S)
    (observation : List F → F → Prop) : ProbComp Prop := do
  let e ← process.runM h s
  pure (accepts observation e)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The curried Sumcheck observation is the generic returned-value observation. -/
theorem acceptanceOf_eq (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Process I (List F × F)) (s : S) (terminal : List F → F → Prop) :
    acceptanceOf h p s terminal = acceptance h p s (fun pc => terminal pc.1 pc.2) := by
  unfold acceptanceOf acceptance
  apply bind_congr
  intro e
  cases e with | mk out state events => cases out <;> rfl

theorem one_round_acceptance_eq [SampleableType F]
    (tables : Evaluation.ComponentTables F G I) (service : Nat) (claim : F) (s : S)
    (queryLaw : ∀ s, (actions (queryAction names.query service)).runM h s =
      freshQuery before after s) (observation : List F → F → Prop) :
    acceptanceOf h (scalarRound sites actions tables names service claim advance terminal) s observation =
      phaseGame 1 claim [] (phaseStrategy sites actions h names before after advance terminal) s observation := by
  unfold acceptanceOf phaseGame
  rw [one_round_execution sites actions h names before after advance terminal tables service claim s queryLaw]

theorem one_round_domination [SampleableType F]
    (tables : Evaluation.ComponentTables F G I) (service : Nat) (claim : F) (s : S)
    (queryLaw : ∀ s, (actions (queryAction names.query service)).runM h s =
      freshQuery before after s) (observation : List F → F → Prop) :
    mass (acceptanceOf h (scalarRound sites actions tables names service claim advance terminal) s observation) ≤
      mass (endpointGame 1 claim []
        (complete 1 claim (phaseStrategy sites actions h names before after advance terminal) s) observation) := by
  rw [one_round_acceptance_eq sites actions h names before after advance terminal tables service claim s queryLaw]
  exact domination 1 claim [] _ s observation

theorem one_round_soundness [Fintype F] [SampleableType F]
    (tables : Evaluation.ComponentTables F G I) (service : Nat) (claim : F) (s : S)
    (queryLaw : ∀ s, (actions (queryAction names.query service)).runM h s =
      freshQuery before after s) (table : Table F 1) (falseClaim : claim ≠ booleanSum table) :
    mass (acceptanceOf h (scalarRound sites actions tables names service claim advance terminal)
      s (tableTerminal table)) ≤ (1 : ENNReal) / Fintype.card F := by
  rw [one_round_acceptance_eq sites actions h names before after advance terminal tables service claim s queryLaw]
  simpa only [Nat.cast_one] using phase_soundness table claim
    (phaseStrategy sites actions h names before after advance terminal) s falseClaim

theorem one_round_publicTable_soundness [Fintype F] [SampleableType F]
    (tables : Evaluation.ComponentTables F G I) (service : Nat) (claim : F) (s : S)
    (queryLaw : ∀ s, (actions (queryAction names.query service)).runM h s =
      freshQuery before after s) (values : List F) (table : Table F 1)
    (decoded : ofList? 1 values = some table) (falseClaim : claim ≠ values.sum) :
    mass (acceptanceOf h (scalarRound sites actions tables names service claim advance terminal)
      s (rawTerminal 1 values)) ≤ (1 : ENNReal) / Fintype.card F := by
  rw [one_round_acceptance_eq sites actions h names before after advance terminal tables service claim s queryLaw]
  simpa only [Nat.cast_one] using phase_publicTable_soundness values table decoded claim
    (phaseStrategy sites actions h names before after advance terminal) s falseClaim

end ZkcSecurity.Examples.CausalSumcheck
