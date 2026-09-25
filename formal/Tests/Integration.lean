import Zkc.Protocols.Sumcheck.LocalProver.Admission
import Zkc.Source.Frontend
import Zkc.Semantics.AuthorizedContinuation
import Zkc.Semantics.Disclosure
import Zkc.Semantics.Relation
import Zkc.Properties.Judgment
import Zkc.Protocols.AlgebraicRounds.EarlySource

set_option autoImplicit false

namespace PIR.IntegrationControls
open Continuation AuthorizedContinuation

def sig : Signature := ⟨Unit, fun _ => Unit⟩
def interaction : Interaction sig :=
  ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
abbrev frontend : Frontend sig Unit (Terminal Nat) where
  Source := Bool
  Binding := Nat
  inputs := fun _ _ _ => True
  elaborate := fun yes value _ => some (.done (if yes then .accepted value else .rejected))
def contract : EndpointContract interaction (Terminal Nat) := ⟨(), 0, fun _ _ => True⟩

def call (yes : Bool) (value : Nat) : Invocation frontend contract :=
  ⟨yes, value, (), .done (if yes then .accepted value else .rejected),
    ⟨rfl, trivial, trivial, trivial, trivial⟩⟩

/-- The installed policy binds source, capture, site, consumer and target. -/
def policy : Policy (P := interaction) frontend := fun source binding _ site consumer target =>
  source && binding == 7 && site == 2 && consumer == 4 && target == 9

def handler : Handler sig Nat Nat := fun _ s => ⟨.returned (), s+1, [42]⟩
def failingArm (_ : Nat) : Proc sig Nat := .call () (fun _ => .halt .abort)
def successfulArm (value : Nat) : Proc sig Nat := .done (value+1)
def service : Service frontend contract Nat Nat Nat where
  policy := policy
  handler := handler
  arm := failingArm
  armBound := 1
  armConforms := fun _ _ _ => ⟨trivial, fun _ => trivial⟩
  armBounded := fun _ _ => trivial

def failed := service.invoke (call true 7) 2 4 9 0 empty

theorem installed_service_retains_arm_formation :
    Conforms interaction (after (call true 7).body service.arm) () ∧
      Within (0 + service.armBound) (after (call true 7).body service.arm) :=
  ⟨service.formed (call true 7), service.bounded (call true 7)⟩

theorem failure_retains_acceptance :
    failed.receipt.map (fun r => r.report.verifier.outcome) = some (.returned (.accepted 7)) := rfl
theorem failure_retains_effects :
    (failed.combined.outcome, failed.combined.state, failed.combined.events) =
      (.stopped .abort, 1, [42]) := rfl
theorem failure_consumes_without_export :
    (failed.ledger, failed.authorizedExport) = (⟨1,[9]⟩, none) := rfl
theorem failed_replay_is_refused :
    (execute frontend contract policy (call true 7) 2 4 9 handler successfulArm
      failed.combined.state failed.ledger).combined.outcome = .stopped .refused := rfl
theorem wrong_consumer_is_refused :
    (execute frontend contract policy (call true 7) 2 5 9 handler successfulArm 0 empty).receipt = none := rfl
theorem wrong_source_binding_is_refused :
    (execute frontend contract policy (call true 8) 2 4 9 handler successfulArm 0 empty).receipt = none := rfl
theorem wrong_site_is_refused :
    (execute frontend contract policy (call true 7) 3 4 9 handler successfulArm 0 empty).receipt = none := rfl
theorem wrong_target_is_refused :
    (execute frontend contract policy (call true 7) 2 4 10 handler successfulArm 0 empty).receipt = none := rfl
theorem success_exports_actual_arm :
    (execute frontend contract policy (call true 7) 2 4 9 handler successfulArm 0 empty).authorizedExport =
      some 8 := rfl
theorem alternate_source_has_no_acceptance :
    (execute frontend contract (fun _ _ _ _ _ _ => true) (call false 7) 2 4 9 handler
      successfulArm 0 empty).authorizedExport = none ∧
    (execute frontend contract (fun _ _ _ _ _ _ => true) (call false 7) 2 4 9 handler
      successfulArm 0 empty).ledger.consumedTargets = [] := ⟨rfl,rfl⟩

def privateRun (capture : Nat) :=
  execute frontend contract (fun _ _ _ _ _ _ => true) (call true capture)
    2 4 9 handler failingArm 0 empty

theorem failed_arm_runtime_hides_capture (a b : Nat) :
    (privateRun a).combined = (privateRun b).combined := rfl

theorem full_receipt_discloses_capture (capture : Nat) :
    (privateRun capture).receipt.map (fun r => r.binding) = some capture := rfl

theorem released_status_hides_capture :
    Disclosure.Permitted (fun (_ _ : Nat) => True) (fun capture => publicStatus (privateRun capture)) :=
  fun _ _ _ => rfl

theorem actual_elaboration_rejects_wrong_body :
    ¬ Admitted (P := interaction) frontend contract true 7 () (.done (.accepted 8)) := by
  intro h
  have impossible := h.actual
  simp at impossible

def missingCode : Zkc.Protocols.Sumcheck.LocalProver.Code := .assign 0 (.var (.inl 0)) .abort
theorem causal_missing_capture_refused :
    (Zkc.Protocols.Sumcheck.LocalProver.Source.frontend (F := Int)).elaborate missingCode [] () = none := rfl
theorem causal_abort_is_admitted :
    Admitted (P := Zkc.Protocols.Sumcheck.LocalProver.Source.localInteraction) (Zkc.Protocols.Sumcheck.LocalProver.Source.frontend (F := Int)) (Zkc.Protocols.Sumcheck.LocalProver.Source.endpointContract (F := Int) .abort [])
      .abort [] () (Zkc.Protocols.Sumcheck.LocalProver.Source.source .abort (Zkc.Protocols.Sumcheck.LocalProver.initial [])) :=
  Zkc.Protocols.Sumcheck.LocalProver.Source.checked_admitted .abort [] rfl

theorem runtime_equality_does_not_hide_artifact :
    Disclosure.Permitted (fun (_ _ : Bool) => True) (fun _ => ()) ∧
    ¬ Disclosure.Permitted (fun (_ _ : Bool) => True)
      (Disclosure.publish (fun b => b) (fun _ => ())) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro hidden
  have impossible := congrArg Prod.fst (hidden true false trivial)
  contradiction

theorem intentional_disclosure_has_exact_policy :
    Disclosure.Permitted (fun (a b : Bool) => True ∧ a = b) (fun b => b) :=
  Disclosure.deliberate_release (fun _ _ => True) (fun b => b)

open Properties
def conditionalLower : Conditional Nat (fun n => 2 ≤ n) :=
  ⟨fun n => 3 ≤ n, fun _ h => Nat.le_trans (by decide) h⟩
def conditionalRule : Conditional Nat (fun n => 2 ≤ n → n < 6) :=
  ⟨fun n => n ≤ 5, fun _ h _ => Nat.lt_succ_of_le h⟩
theorem transport_retains_both_premises (n : Nat) :
    (conditionalLower.transport conditionalRule).requires n ↔ 3 ≤ n ∧ n ≤ 5 := Iff.rfl
theorem producer_does_not_discharge_rule :
    conditionalLower.requires 8 ∧ ¬ (conditionalLower.transport conditionalRule).requires 8 := by
  change 3 ≤ 8 ∧ ¬ (3 ≤ 8 ∧ 8 ≤ 5)
  decide
theorem unknown_does_not_refute_true :
    ¬ (Check.unknown .resourceLimit : Check True).proves ∧ True := ⟨id, trivial⟩
theorem legality_does_not_supply_requirement : ¬ Usable True False := fun h => h.requested
theorem smaller_upper_bound_can_have_larger_cost :
    9 ≤ 10 ∧ 1 ≤ 20 ∧ 10 < 20 ∧ ¬ 9 ≤ 1 := by decide

/-- The finished-round separator is joined to the actual terminal. -/
theorem finished_scalar_can_be_rejected :
    ((Zkc.Protocols.AlgebraicRounds.EarlySource.source Zkc.Protocols.AlgebraicRounds.Scalar.value 0 (3 : Int)).run
      (Zkc.Protocols.AlgebraicRounds.EarlySource.handler Zkc.Protocols.AlgebraicRounds.Early.badSend Zkc.Protocols.AlgebraicRounds.Early.ignoreChallenge Zkc.Protocols.AlgebraicRounds.Early.counterDraw) ((),0)).outcome =
        .returned 3 ∧ Relation.scalarTerminal (0 : Int) 3 = .rejected := ⟨rfl,rfl⟩
theorem matching_scalar_is_accepted : Relation.scalarTerminal (3 : Int) 3 = .accepted () := rfl

/-- `after` keeps no record of an acceptance whose arm then stops: the complete
    execution equals that of the stop alone. -/
theorem unrecorded_acceptance_then_abort :
    (after (Proc.done (.accepted ()) : Proc sig (Terminal Unit))
      (fun _ => (Proc.halt .abort : Proc sig Unit))).run handler 0 =
    (Proc.halt .abort : Proc sig Unit).run handler 0 := rfl

end PIR.IntegrationControls
