module

public import ZkcSecurity.Examples.CausalSumcheck.DistributionalRound

@[expose] public section


namespace ZkcSecurity.Examples.CausalSumcheck

open OracleComp OracleSpec
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear
open scoped ENNReal

variable {F G S E : Type} {I : PIR.Signature}

def attachTerminal (p : PIR.Proc I (List F × F))
    (work : List F → F → PIR.Proc I Unit) : PIR.Proc I (List F × F) :=
  p.bind fun pc => (work pc.1 pc.2).bind fun _ => .done pc

def checkedGame (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Proc I (List F × F))
    (checker : List F → F → PIR.Proc I Bool) (s : S) : ProbComp Prop := do
  let e ← (p.bind fun pc => checker pc.1 pc.2).runM h s
  pure (e.outcome = .returned true)

/-- A LOCAL trusted checker equation, including its stopping/capacity work,
    composes through any existing Proc prefix. No whole-game premise. -/
theorem checkedGame_eq (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Proc I (List F × F)) (work : List F → F → PIR.Proc I Unit)
    (checker : List F → F → PIR.Proc I Bool) (value : List F → F → Bool) (s : S)
    (checkLaw : ∀ point claim s, (checker point claim).runM h s = (do
      let e ← (work point claim).runM h s
      e.followM fun _ s => pure (result (value point claim) s))) :
    checkedGame h p checker s =
      acceptanceOf h (attachTerminal p work) s (fun point claim => value point claim = true) := by
  simpa only [checkedGame, checked, acceptanceOf_eq, attachTerminal, attachWork] using
    checked_eq h p (fun pc => work pc.1 pc.2) (fun pc => checker pc.1 pc.2)
    (fun pc => value pc.1 pc.2) s (fun pc s => checkLaw pc.1 pc.2 s)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
/-- Moving terminal work out of the finite structured fragment is a Proc bind
    equation; all masks, marks, actions, states and stops keep their order. -/
theorem scalarRound_attach (sites : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (names : Sites) (service : Nat) (claim : F)
    (advance : Message F → F → PIR.Proc I Unit) (work : List F → F → PIR.Proc I Unit) :
    attachTerminal (scalarRound sites actions tables names service claim advance (fun _ _ => .done ())) work =
      scalarRound sites actions tables names service claim advance
        (fun pair r => work [r] (evaluate pair r)) := by
  simp only [attachTerminal, scalarRound_eq, PIR.Proc.bind_assoc]
  congr 1; funext u; congr 1; funext lo; congr 1; funext hi
  split <;> simp [PIR.Proc.bind, PIR.Proc.bind_assoc]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Curried specialization of the reusable conservative-checker law. -/
theorem checkedGame_le (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Proc I (List F × F)) (work : List F → F → PIR.Proc I Unit)
    (checker : List F → F → PIR.Proc I Bool) (value : List F → F → Bool) (s : S)
    (checkLaw : ∀ point claim s, (checker point claim).runM h s = (do
      let e ← (work point claim).runM h s
      e.followM fun _ s => pure (result (value point claim) s)))
    (terminal : List F → F → Prop)
    (mathematics : ∀ point claim, value point claim = true → terminal point claim) :
    mass (checkedGame h p checker s) ≤ mass (acceptanceOf h (attachTerminal p work) s terminal) := by
  simpa only [checkedGame, checked, acceptanceOf_eq, attachTerminal, attachWork] using
    checked_le h p (fun pc => work pc.1 pc.2) (fun pc => checker pc.1 pc.2)
    (fun pc => value pc.1 pc.2) s (fun pc s => checkLaw pc.1 pc.2 s)
    (fun pc => terminal pc.1 pc.2) (fun pc => mathematics pc.1 pc.2)

variable (sites : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)
  (h : PIR.MonadHandler ProbComp I S E) (names : Sites)
  (advance : Message F → F → PIR.Proc I Unit)
  (work : List F → F → PIR.Proc I Unit)
  (before : Phase S E Unit) (after : F → Phase S E Unit)

theorem calculatedRound_attach (service : Nat) (claim : F) :
    attachTerminal (calculatedRound sites actions names service claim advance
      (fun _ _ => .done ())) work =
    calculatedRound sites actions names service claim advance work := by
  rw [calculatedRound_eq, scalarRound_attach, calculatedRound_eq]

theorem checked_calculatedRound_soundness [Fintype F] [SampleableType F]
    (service : Nat) (claim : F) (s : S) (invariant : Message F → S → Prop)
    (reachable : Reaches ((queryPrefix sites actions names claim).runM h s) invariant)
    (queryLaw : ∀ pair s, invariant pair s → SameDist
      ((actions (queryAction names.query service)).runM h s) (freshQuery (F := F) before after s))
    (checker : List F → F → PIR.Proc I Bool) (value : List F → F → Bool)
    (checkLaw : ∀ point claim s, (checker point claim).runM h s = (do
      let e ← (work point claim).runM h s
      e.followM fun _ s => pure (result (value point claim) s)))
    (table : Table F 1)
    (mathematics : ∀ point claim, value point claim = true → tableTerminal table point claim)
    (falseClaim : claim ≠ booleanSum table) :
    mass (checkedGame h
      (calculatedRound sites actions names service claim advance (fun _ _ => .done ())) checker s) ≤
      (1 : ENNReal) / Fintype.card F := by
  apply (checkedGame_le h _ work checker value s checkLaw _ mathematics).trans
  rw [calculatedRound_attach]
  exact calculatedRound_soundness sites actions h names advance work before after
    service claim s invariant reachable queryLaw table falseClaim

theorem calculatedRound_publicTable_soundness [Fintype F] [SampleableType F]
    (service : Nat) (claim : F) (s : S) (invariant : Message F → S → Prop)
    (reachable : Reaches ((queryPrefix sites actions names claim).runM h s) invariant)
    (queryLaw : ∀ pair s, invariant pair s → SameDist
      ((actions (queryAction names.query service)).runM h s) (freshQuery (F := F) before after s))
    (values : List F) (table : Table F 1) (decoded : ofList? 1 values = some table)
    (falseClaim : claim ≠ values.sum) :
    mass (acceptanceOf h (calculatedRound sites actions names service claim advance work)
      s (rawTerminal 1 values)) ≤ (1 : ENNReal) / Fintype.card F := by
  rw [rawTerminal_eq_table values table decoded]
  apply calculatedRound_soundness sites actions h names advance work before after
    service claim s invariant reachable queryLaw table
  rwa [booleanSum_ofList? values table decoded]


end ZkcSecurity.Examples.CausalSumcheck
