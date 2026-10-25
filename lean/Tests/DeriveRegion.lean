import Zkc.Source.DeriveRegion
import Zkc.Source.DerivationLaws
import Zkc.Source.Structured.Meaning

-- Deliberately unused input binders exercise failed and state-restored proof search.
set_option linter.unusedVariables false

namespace Tests.DeriveRegion
open Zkc.Source Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private def addition : Region dialect [.field "F", .field "F"] [.field "F"] :=
  .letOp (.fieldAdd "F") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

/-- One operation rule, reusable at every occurrence and over arbitrary fields. -/
theorem add_comm_law (table : Meanings F G) (domain : String) (a b : F) :
    (meaning F G table).OperationLaw (fun op => .call op .done) (.fieldAdd domain)
      (.cons a (.cons b .nil)) .nil (.done (.cons (b + a) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change @Eq (PIR.Process _ (Values (assignment F G) [.field domain]))
    (.done (.cons (a + b) .nil)) (.done (.cons (b + a) .nil))
  rw [add_comm a b]

theorem commuted (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + a) .nil)) := by
  derive_region using (exact add_comm_law _ _ _ _)

end Tests.DeriveRegion

namespace Tests.DeriveRegion
open Zkc.Source Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Failure to prove an operation law is not converted into a whole-body premise. -/
theorem unresolved_is_local (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + a) .nil)) := by
  fail_if_success solve | derive_region using (fail "unsupported operation")
  derive_region using (exact add_comm_law _ _ _ _)

-- A local rule cannot silently change the client's requested result.
/-- error: derive_region: generated target does not match the requested target -/
#guard_msgs in
example (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.halt .abort) := by
  derive_region using (exact add_comm_law _ _ _ _)

-- Test the fallback at the operation-law boundary, independent of how long
-- normal elaboration takes on a particular machine.
elab "kernel_timeout_control" : tactic =>
  Lean.throwKernelException .deterministicTimeout
elab "interrupt_control" : tactic => Lean.throwInterruptException
elab "heartbeat_control" : tactic =>
  Lean.Core.throwMaxHeartbeat `control `maxHeartbeats 1000

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
example (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + a) .nil)) := by
  derive_region using (kernel_timeout_control)

-- Interrupts have no diagnostic for guard_msgs. Catch outside derive_region
-- and check the exception kind; success or an unrelated error is a failure.
elab "check_resource_propagation" : tactic => do
  for solver in [← `(tacticSeq| interrupt_control), ← `(tacticSeq| heartbeat_control)] do
    let saved ← Lean.Elab.Tactic.saveState
    let failure ← try
      Zkc.Source.DeriveRegion.run solver
      pure none
    catch error => pure (some error)
    saved.restore
    match failure with
    | some error =>
      unless error.isInterrupt || error.isRuntime do
        throwError "unexpected failure: {error.toMessageData}"
    | none => throwError "derive_region swallowed a resource failure"

-- The probe restores its tactic state, including the linter's usage trace.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem resources_propagate (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + a) .nil)) := by
  check_resource_propagation
  derive_region using (exact add_comm_law _ _ _ _)

/-- Conditional mathematics is left as a real Lean obligation. -/
theorem conditional_add (table : Meanings F G) (a b : F) (same : a = b) :
    (meaning F G table).OperationLaw (fun op => .call op .done) (.fieldAdd "F")
      (.cons a (.cons b .nil)) .nil (.done (.cons (b + b) .nil)) := by
  subst a
  apply RegionMeaning.OperationLaw.identity
  rfl

theorem obligation_resumed (table : Meanings F G) (a b : F) (same : a = b) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + b) .nil)) := by
  derive_region using (apply conditional_add)
  exact same

end Tests.DeriveRegion

namespace Tests.DeriveRegion
open Zkc.Source Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

-- The supplied solver deliberately fails; the retained local obligation is
-- discharged below. Its failure is the behavior under test.
set_option linter.unusedTactic false in
/-- With a synthesized target, an unsupported operation remains visible and
can be discharged interactively. No whole-program law is requested. -/
theorem unsupported_resumed (table : Meanings F G) (a b : F) :
    ∃ target, Region.Derivation (meaning F G table) (fun op => .call op .done) addition
      (Values.cons a (.cons b .nil)).get target := by
  refine ⟨?target, ?proof⟩
  case proof =>
    derive_region using (fail "unsupported operation")
    exact add_comm_law _ _ _ _

/-- Omitting a required equality cannot yield a closed derivation. -/
example (table : Meanings F G) (a b : F) : True := by
  fail_if_success
    have : Region.Derivation (meaning F G table) (fun op => .call op .done) addition
        (Values.cons a (.cons b .nil)).get (.done (.cons (b + b) .nil)) := by
      derive_region using (apply conditional_add)
  trivial

end Tests.DeriveRegion
