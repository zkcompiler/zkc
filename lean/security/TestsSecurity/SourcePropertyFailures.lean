import TestsSecurity.PropertyCost
import Tests.Companions
import ZkcSecurityTools.SourceProperties.Loops
import ZkcSecurityTools.SourceProperties.Builder

/-! Expected mathematical mismatches permit another rule; unexpected internal
exceptions must escape both callback and property assembly. -/
set_option autoImplicit false
open Lean Elab Tactic
open TestsSecurity.PropertyCost Tests.Obligations ZkcSecurity.FiatShamir

elab "source_internal_failure%" : term =>
  throw (.internal Tests.Companions.proposalFailureId)

syntax "expect_source_internal " "{" tacticSeq "}" : tactic
elab_rules : tactic
  | `(tactic| expect_source_internal { $body:tacticSeq }) => do
    let saved ← saveState
    let propagated ← try
      evalTactic body
      pure false
    catch error =>
      match error with
      | .internal id _ =>
          if id == Tests.Companions.proposalFailureId then pure true else throw error
      | _ => throw error
    saved.restore
    unless propagated do throwError "internal source proposal failure was swallowed"

-- The control intentionally restores the goal after observing the exception.
set_option linter.unusedTactic false in
example : True := by
  expect_source_internal { source_loop_callback [source_internal_failure%, True.intro] }
  source_loop_callback [(0 : Nat), True.intro]

set_option linter.unusedTactic false in
example (history : List Unit) (runtime : Nat × Nat)
    (law : Typed.ChargedCostBound queryBit price
      ((counter.body runtime).bind PIR.Process.done) history 5) :
    Typed.ChargedCostBound queryBit price
      ((counter.body runtime).bind PIR.Process.done) history 5 := by
  expect_source_internal {
    assemble_source_cost [source_internal_failure%] simplifying []
  }
  exact law
