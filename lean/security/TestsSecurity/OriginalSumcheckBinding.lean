module

import ZkcExamples.Structured.OriginalSumcheckTerminal
import ZkcSecurity.Realizations.Sumcheck.OriginalRawSource

/-! Controls for original Reduce admission, optional ABI and call identity.
These use the actual source body and helpers, with arbitrary field inputs. -/
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open OriginalSumcheckLibrary OriginalSumcheckInstances SumcheckVerifierBodies

set_option autoImplicit false
namespace TestsSecurity.OriginalSumcheckBinding

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem smallClaims : SumcheckPendingLaws.Bodies Small.payload.definitions := by
  bind_structured_bodies

private theorem twoClaims : SumcheckPendingLaws.Bodies Two.payload.definitions := by
  bind_structured_bodies

/-- Missing counts stop even if an input claim is itself incomplete. -/
example (point : Option (List F)) (claim : Option F) (service : Option Nat) :
    reduce Small.payload 2 Small.context 1 []
      (verifierInputs (G := G) point claim none service) = .halt .incomplete := by
  refine (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] point claim none service).trans ?_
  rw [SumcheckPendingLaws.identity_owned Small.payload _ smallClaims.openClaim, ite_eq_left rfl]
  cases point <;> cases claim <;> rfl

/-- A complete Pending value reaches the count bound before any service use. -/
example (point : List F) (claim : F) (service : Option Nat) :
    reduce Small.payload 2 Small.context 1 []
      (verifierInputs (G := G) (some point) (some claim) (some 3) service) = .halt .refused := by
  refine (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] (some point) (some claim) (some 3) service).trans ?_
  rw [SumcheckPendingLaws.identity_owned Small.payload _ smallClaims.openClaim, ite_eq_left rfl]
  rfl

example (point : List F) (claim : F) (service : Option Nat) :
    reduce Two.payload 4 Two.leftContext 1 []
      (verifierInputs (G := G) (some point) (some claim) (some 5) service) = .halt .refused := by
  refine (reduce_verifier (F := F) (G := G) Two.payload Two.helpers_bound 4
    Two.leftContext Two.left_distinct [] (some point) (some claim) (some 5) service).trans ?_
  rw [SumcheckPendingLaws.identity_owned Two.payload _ twoClaims.openClaim, ite_eq_left rfl]
  rfl

/-- Zero trips retain the whole Pending pair. The unused service may be absent;
private producer outputs are masked away, but verifier-owned inputs are required. -/
theorem zero_trips (point : List F) (claim : F) :
    reduce Small.payload 2 Small.context 1 []
      (verifierInputs (G := G) (some point) (some claim) (some 0) none) =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons (some point) (.cons (some claim) .nil)))))) := by
  refine (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] (some point) (some claim) (some 0) none).trans ?_
  rw [SumcheckPendingLaws.identity_owned Small.payload _ smallClaims.openClaim, ite_eq_left rfl]
  exact return_verifier Small.payload smallClaims Small.context point claim

example (point : Option (List F)) :
    reduce Small.payload 2 Small.context 1 []
      (verifierInputs (G := G) point none (some 0) none) = .halt .incomplete := by
  refine (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] point none (some 0) none).trans ?_
  rw [SumcheckPendingLaws.identity_owned Small.payload _ smallClaims.openClaim, ite_eq_left rfl]
  cases point <;> rfl

example (claim : Option F) :
    reduce Small.payload 2 Small.context 1 []
      (verifierInputs (G := G) none claim (some 0) none) = .halt .incomplete := by
  refine (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] none claim (some 0) none).trans ?_
  rw [SumcheckPendingLaws.identity_owned Small.payload _ smallClaims.openClaim, ite_eq_left rfl]
  cases claim <;> rfl

/-- The same library declaration retains distinct nominal iteration sites. -/
example (handle : Nat) :
    ZkcSecurity.Realizations.Sumcheck.Original.loopSite ⟨Two.leftContext, handle⟩ ≠
      ZkcSecurity.Realizations.Sumcheck.Original.loopSite ⟨Two.rightContext, handle⟩ := by
  change qualifyProtocolSite Two.leftContext.applicationPrefix repeatSite ≠
    qualifyProtocolSite Two.rightContext.applicationPrefix repeatSite
  decide

/-- After a zero-trip call, an absent root table stops in the actual terminal
helper. A present claim distinguishes this from Pending construction refusal. -/
example (claim : F) :
    Occurrence.participant (ringModel F G) Small.imported.program 1
      (.cons none (.cons (some claim) (.cons (some 0) (.cons none .nil)))) = .halt .incomplete := by
  rw [OriginalSumcheckRoots.Small.root_binding]
  change (Participant.owned 1 1
    (invoke (helpers (F := F) (G := G) Small.payload).closed SumcheckPendingBodies.pendingHelper)
    (.cons (some claim) .nil)).bind _ = _
  rw [SumcheckPendingLaws.pending_owned Small.payload smallClaims]
  change (OriginalSumcheckRoots.Small.reduce (G := G) (some []) (some claim) (some 0) none).bind _ = _
  have reduced := congrArg
    (fun process => process.bind fun result =>
      PIR.Process.done (maskValues 1 (Small.context.mapScopes Small.reduceDefinition.outputScopes) result))
    (zero_trips (G := G) [] claim)
  rw [show OriginalSumcheckRoots.Small.reduce (G := G) (some []) (some claim) (some 0) none = _ from reduced]
  rfl

#print axioms OriginalSumcheckLibrary.round_producer
#print axioms OriginalSumcheckLibrary.reduce_verifier
#print axioms OriginalSumcheckInstances.Small.reduce_lookup
#print axioms OriginalSumcheckInstances.Two.reduce_lookup
#print axioms OriginalSumcheckRoots.Small.root_binding
#print axioms OriginalSumcheckRoots.Two.root_binding
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_step
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_loop
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalRaw.source_reduce
#print axioms OriginalSumcheckLibrary.check_terminal
#print axioms OriginalSumcheckInstances.Small.producer_bodies
#print axioms OriginalSumcheckInstances.Two.producer_bodies
#print axioms OriginalSumcheckRoots.Two.both_present

end TestsSecurity.OriginalSumcheckBinding
