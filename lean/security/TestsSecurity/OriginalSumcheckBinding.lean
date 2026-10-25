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

example (claim : Option F) (service : Option Nat) :
    reduce Small.payload 2 Small.context 1 []
      (OriginalSumcheckLibrary.verifierInputs (G := G) claim none service) = .halt .incomplete := by
  exact (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] claim none service).trans (by rfl)

example (claim : Option F) (service : Option Nat) :
    reduce Small.payload 2 Small.context 1 []
      (OriginalSumcheckLibrary.verifierInputs (G := G) claim (some 3) service) = .halt .refused := by
  exact (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] claim (some 3) service).trans (by rfl)

example (claim : Option F) (service : Option Nat) :
    reduce Two.payload 4 Two.leftContext 1 []
      (OriginalSumcheckLibrary.verifierInputs (G := G) claim (some 5) service) = .halt .refused := by
  exact (reduce_verifier (F := F) (G := G) Two.payload Two.helpers_bound 4
    Two.leftContext Two.left_distinct [] claim (some 5) service).trans (by rfl)

/-- A missing unused service does not prevent zero trips. Missing private
producer values and even an absent scalar are returned as the real optional ABI. -/
example (claim : Option F) :
    reduce Small.payload 2 Small.context 1 []
      (OriginalSumcheckLibrary.verifierInputs (G := G) claim (some 0) none) =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons (some []) (.cons claim .nil)))))) := by
  exact (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
    Small.context Small.distinct [] claim (some 0) none).trans (by rfl)

/-- One library declaration has genuinely different nominal iteration sites
in the two root calls, even when both induction coordinates are zero. -/
example (handle : Nat) :
    ZkcSecurity.Realizations.Sumcheck.Original.loopSite ⟨Two.leftContext, handle⟩ ≠
      ZkcSecurity.Realizations.Sumcheck.Original.loopSite ⟨Two.rightContext, handle⟩ := by
  change qualifyProtocolSite Two.leftContext.applicationPrefix "s15" ≠
    qualifyProtocolSite Two.rightContext.applicationPrefix "s15"
  decide

/-- The optional original ABI is still operational: after a zero-trip call,
an absent root table stops in the actual terminal helper. -/
example (claim : Option F) :
    Occurrence.participant (ringModel F G) Small.imported.program 1
      (.cons none (.cons claim (.cons (some 0) (.cons none .nil)))) = .halt .incomplete := by
  have reduced : OriginalSumcheckRoots.Small.reduce (G := G) claim (some 0) none =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons (some []) (.cons claim .nil)))))) :=
    (reduce_verifier (F := F) (G := G) Small.payload Small.helpers_bound 2
      Small.context Small.distinct [] claim (some 0) none).trans (by rfl)
  exact (OriginalSumcheckRoots.Small.root_binding (G := G) none claim (some 0) none).trans
    ((congrArg (fun process => process.bind (OriginalSumcheckRoots.Small.check none)) reduced).trans
      (by rfl))

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
