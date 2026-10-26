module

public meta import ZkcSecurity.Tools.InputLaws
public meta import ZkcSecurity.Tools.ComponentCost
public meta import ZkcSecurity.Tools.ComponentDerivation

@[expose] public section
set_option autoImplicit false
-- Failure-injection probes restore tactic state and intentionally discard binders
-- and usage traces; these options apply only to diagnostic controls.
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Search failures retain their cause. These controls inject the actual Lean
exception representation, avoiding timing-dependent resource exhaustion. A
kernel resource error is an ordinary diagnostic; tagged elaborator resource
errors skip ordinary catch branches already in Lean itself. Neither is evidence
of a false semantic proposition. -/
namespace TestsSecurity.ProofSearchDiagnostics
open Lean Meta Elab Tactic

elab "diagnostic_kernel_timeout" : tactic => throwKernelException .deterministicTimeout
elab "diagnostic_recursion_limit" : tactic => do throwMaxRecDepthAt (← getRef)

private def Related (left right : Nat) : Prop := left = right
private theorem needsProof (left right : Nat) (_required : False) :
    Related left right ↔ left = right := Iff.rfl

/-- error: the supplied input law does not apply with proved premises: [(kernel) deterministic timeout] -/
#guard_msgs (substring := true) in
example (left right : Nat) (_related : Related left right) : True := by
  apply_input_law needsProof solving diagnostic_kernel_timeout

/-- error: maximum recursion depth has been reached -/
#guard_msgs (substring := true) in
example (left right : Nat) (_related : Related left right) : True := by
  apply_input_law needsProof solving diagnostic_recursion_limit

/-- error: the supplied input law does not apply with proved premises: [mathematical side law missing -/
#guard_msgs (substring := true) in
example (left right : Nat) (_related : Related left right) : True := by
  apply_input_law needsProof solving (fail "mathematical side law missing")

-- Ordinary failed candidates still backtrack. A stronger, unusable bound must
-- not prevent a later installed proof of the same actual process from working.
open Zkc.Transcript ZkcSecurity.FiatShamir
example {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (process : PIR.Process I A) (history : List E) (price : ENNReal)
    (bound : Typed.ChargedCostBound absorb charge process history price) :
    Typed.ChargedCostBound absorb charge process history price := by
  derive_component_cost [(by fail "first candidate unavailable"), bound] unfolding []

/--
error: cost normalization failed: `simp` made no progress
installed/structural rules: [(kernel) deterministic timeout,
-/
#guard_msgs (substring := true) in
example {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (process : PIR.Process I A) (history : List E) (price : ENNReal) :
    Typed.ChargedCostBound absorb charge process history price := by
  derive_component_cost [(by diagnostic_kernel_timeout)] unfolding []

end TestsSecurity.ProofSearchDiagnostics
