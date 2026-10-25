module

public import ZkcArkLib.Examples.CausalSumcheck.CalculatedRound

@[expose] public section

namespace ZkcSecurity.Examples.CausalSumcheck
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open OracleComp OracleSpec Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear
open MeasureTheory
open scoped ENNReal

variable {F G S E : Type} {I : PIR.Signature}
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (sites : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)
  (h : PIR.MonadHandler ProbComp I S E) (names : Sites)

/-- The cut is after the guard and query mark. This is a Process subexpression;
calculatedRound_cut proves its relation to the typed canonical fragment. -/
def queryPrefix (claim : F) : PIR.Process I (Message F) :=
  (sites.mark names.round).bind fun _ =>
  (actions (lowAction names.low)).bind fun lo =>
  (actions (lowAction names.high)).bind fun hi =>
  if boundary (lo, hi) = claim then
    (sites.mark names.query).bind fun _ => .done (lo, hi)
  else .halt .reject

def querySuffix (advance : Message F → F → PIR.Process I Unit)
    (terminal : List F → F → PIR.Process I Unit) (pair : Message F) (r : F) :
    PIR.Process I (List F × F) :=
  (sites.mark names.delivery).bind fun _ =>
  (actions (sendAction names.delivery r)).bind fun _ =>
  (advance pair r).bind fun _ =>
  (calculatedUpdate sites actions [] pair r).bind fun pc =>
  (terminal pc.1 pc.2).bind fun _ => .done pc

variable (advance : Message F → F → PIR.Process I Unit)
  (terminal : List F → F → PIR.Process I Unit)

set_option backward.isDefEq.respectTransparency false in
theorem calculatedRound_cut (service : Nat) (claim : F) :
    calculatedRound sites actions names service claim advance terminal =
      (queryPrefix sites actions names claim).bind fun pair =>
      (actions (queryAction names.query service)).bind fun r =>
      querySuffix sites actions names advance terminal pair r := by
  rw [calculatedRound_eq, scalarRound_eq]
  simp only [queryPrefix, querySuffix, calculatedUpdate_eq, List.nil_append,
    PIR.Process.bind_assoc, PIR.Process.bind]
  congr 1; funext u; congr 1; funext lo; congr 1; funext hi
  split <;> simp only [PIR.Process.bind_assoc, PIR.Process.bind]

variable (before : Phase S E Unit) (after : F → Phase S E Unit)

set_option backward.isDefEq.respectTransparency false in
/-- Independent of any handler query law: expose the existing phase runner at
exactly the same cut. Fresh uniform sampling is explicit on this side. -/
theorem phase_at_cut [SampleableType F] (claim : F) (s : S) :
    run 1 claim [] (phaseStrategy sites actions h names before after advance
      (fun pair r => terminal [r] (evaluate pair r))) s =
    (do let e ← (queryPrefix sites actions names claim).runM h s
        e.followM fun pair s => do
          let q ← freshQuery (F := F) before after s
          q.followM fun r s => (querySuffix sites actions names advance terminal pair r).runM h s) := by
  simp only [queryPrefix, querySuffix, calculatedUpdate_eq, List.nil_append,
    PIR.Process.bind, PIR.runM_bind, run, prepare, phaseStrategy, mapPhase,
    bind_assoc, PIR.followM_assoc, follow_result, pure_bind]
  apply bind_congr; intro marked
  apply congrArg (PIR.Execution.followM marked)
  funext u s
  apply bind_congr; intro low
  apply congrArg (PIR.Execution.followM low)
  funext lo s
  apply bind_congr; intro high
  apply congrArg (PIR.Execution.followM high)
  funext hi s
  by_cases passed : boundary (lo, hi) = claim
  · simp only [ite_eq_left passed, phaseTail, freshQuery, mapPhase,
      PIR.runM_bind, runM_bind_function, bind_assoc, PIR.followM_assoc,
      follow_result, pure_bind, PIR.Process.runM]
    have returned (pair : Message F) (s : S)
        (k : Message F → S → ProbComp (PIR.Execution S E (List F × F))) :
        (⟨.returned pair, s, []⟩ : PIR.Execution S E (Message F)).followM k = k pair s :=
      follow_result pair s k
    simp only [returned]
    rfl
  · simp [passed, phaseTail, noOp, result, stopped, PIR.Process.runM, PIR.Execution.followM]

/-- Full execution distribution equality from local query equality on reachable
states. The prefix itself supplies residual states and ordered observations. -/
theorem calculatedRound_distribution [SampleableType F]
    (service : Nat) (claim : F) (s : S) (invariant : Message F → S → Prop)
    (reachable : Reaches ((queryPrefix sites actions names claim).runM h s) invariant)
    (queryLaw : ∀ pair s, invariant pair s → SameDist
      ((actions (queryAction names.query service)).runM h s) (freshQuery (F := F) before after s)) :
    SameDist ((calculatedRound sites actions names service claim advance terminal).runM h s)
      (run 1 claim [] (phaseStrategy sites actions h names before after advance
        (fun pair r => terminal [r] (evaluate pair r))) s) := by
  rw [calculatedRound_cut, PIR.runM_bind, phase_at_cut]
  simp only [runM_bind_function]
  exact replace_follow_prefix _ invariant
    (fun _ => (actions (queryAction names.query service)).runM h)
    (fun _ => freshQuery (F := F) before after)
    (fun pair r => (querySuffix sites actions names advance terminal pair r).runM h)
    reachable queryLaw

theorem calculatedRound_soundness [Fintype F] [SampleableType F]
    (service : Nat) (claim : F) (s : S) (invariant : Message F → S → Prop)
    (reachable : Reaches ((queryPrefix sites actions names claim).runM h s) invariant)
    (queryLaw : ∀ pair s, invariant pair s → SameDist
      ((actions (queryAction names.query service)).runM h s) (freshQuery (F := F) before after s))
    (table : Table F 1) (falseClaim : claim ≠ booleanSum table) :
    mass (acceptanceOf h (calculatedRound sites actions names service claim advance terminal)
      s (tableTerminal table)) ≤ (1 : ENNReal) / Fintype.card F := by
  have same := calculatedRound_distribution sites actions h names advance terminal before after
    service claim s invariant reachable queryLaw
  have observed := same.bind_left (fun e => pure (accepts (tableTerminal table) e))
  unfold mass acceptanceOf
  rw [observed]
  simpa only [Nat.cast_one, mass, phaseGame] using phase_soundness table claim
    (phaseStrategy sites actions h names before after advance
      (fun pair r => terminal [r] (evaluate pair r))) s falseClaim

end ZkcSecurity.Examples.CausalSumcheck
