import Zkc.Protocols.CapturedPrograms.Selection
import ZkcArkLib.LocalProver.Observation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.CapturedPrograms
open Zkc.Protocols.CapturedPrograms Zkc.Source.Availability
variable {F : Type} [CommRing F] [DecidableEq F]
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver

def actual {D : Type} (embed : D → F) (draw : Boundary F → ProbComp D)
    (x : Issued F) : ProbComp (Option Unit) :=
  ZkcArkLib.LocalProver.actual embed draw x.code.causal x.inputs

theorem issued_actual_agreement {D : Type} (embed : D → F) (draw : Boundary F → ProbComp D)
    (scope : List Nat) (s t : Env F) (p : Tree) (h : Agree scope s t) :
    (issue scope s p).map (actual embed draw) =
      (issue scope t p).map (actual embed draw) := by rw [issue_agreement scope s t p h]

/-- The selected source feeds the observer/verifier projection. -/
theorem issued_observer {D : Type} (embed : D → F) (draw : Boundary F → ProbComp D)
    (x : Issued F) :
    observeVerdict embed <$> joint draw x.code.causal x.inputs = actual embed draw x :=
  observer_transport embed draw x.code.causal x.inputs

/-- Exact conditional provider law at a reachable selected commit; this is NOT privacy. -/
theorem issued_conditional {D : Type} (draw : Boundary F → ProbComp D) (x : Issued F)
    (b : Boundary F) (hb : Reaches x.code.causal (initial x.inputs) (.committed b)) (d : D) :
    Pr[= (.committed b,some d) | joint draw x.code.causal x.inputs] /
      Pr[= .committed b | pre x.code.causal (initial x.inputs)] = Pr[= d | draw b] :=
  conditional_draw draw x.code.causal x.inputs b hb d

end ZkcArkLib.CapturedPrograms

namespace ZkcArkLib.CapturedPrograms
open Zkc.Protocols.CapturedPrograms Zkc.Source.Availability
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver
/-- Property-specific cap stays a common provider contract and a false-claim premise. -/
theorem issued_acceptance_cap {F D : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (draw : Boundary F → ProbComp D)
    (x : Issued F) (ε : ℝ≥0∞)
    (cap : ∀ b, Reaches x.code.causal (initial x.inputs) (.committed b) →
      ∀ d, Pr[= d | draw b] ≤ ε)
    (false_claim : ∀ b, Reaches x.code.causal (initial x.inputs) (.committed b) → b.claim ≠ 2) :
    Pr[= some () | actual embed draw x] ≤ 2 * ε :=
  source_bound embed inj draw x.code.causal x.inputs ε cap false_claim
end ZkcArkLib.CapturedPrograms

namespace ZkcArkLib.CapturedPrograms
open Zkc.Protocols.CapturedPrograms Zkc.Source.Availability
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver
variable {F D : Type} [CommRing F] [DecidableEq F]
/-- Refusal is a defined non-accepting experiment outcome. -/
def experiment (scope : List Nat) (s : Env F) (p : Tree)
    (embed : D → F) (draw : Boundary F → ProbComp D) : ProbComp (Option Unit) :=
  match issue scope s p with
  | none => pure none
  | some x => actual embed draw x

theorem experiment_agreement (scope : List Nat) (s t : Env F) (p : Tree)
    (h : Agree scope s t) (embed : D → F) (draw : Boundary F → ProbComp D) :
    experiment scope s p embed draw = experiment scope t p embed draw := by
  simp only [experiment,issue_agreement scope s t p h]

theorem experiment_of_issue (scope : List Nat) (s : Env F) (p : Tree)
    (x : Issued F) (h : issue scope s p = some x)
    (embed : D → F) (draw : Boundary F → ProbComp D) :
    observeVerdict embed <$> joint draw x.code.causal x.inputs =
      experiment scope s p embed draw := by
  simpa [experiment,h] using issued_observer embed draw x
end ZkcArkLib.CapturedPrograms

namespace ZkcArkLib.CapturedPrograms
open Zkc.Protocols.CapturedPrograms Zkc.Source.Availability
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver
/-- Bound on the actual CHECK-ISSUE-EXECUTE operation, with refusal included. -/
theorem experiment_bound {F D : Type} [Field F] [DecidableEq F] [Fintype D]
    (scope : List Nat) (s : Env F) (p : Tree)
    (embed : D → F) (inj : Function.Injective embed) (draw : Boundary F → ProbComp D)
    (ε : ℝ≥0∞)
    (cap : ∀ x, issue scope s p = some x → ∀ b,
      Reaches x.code.causal (initial x.inputs) (.committed b) → ∀ d, Pr[= d | draw b] ≤ ε)
    (false_claim : ∀ x, issue scope s p = some x → ∀ b,
      Reaches x.code.causal (initial x.inputs) (.committed b) → b.claim ≠ 2) :
    Pr[= some () | experiment scope s p embed draw] ≤ 2 * ε := by
  cases h : issue scope s p with
  | none => simp [experiment,h]
  | some x =>
    simpa [experiment,h] using issued_acceptance_cap embed inj draw x ε (cap x h) (false_claim x h)
end ZkcArkLib.CapturedPrograms
