import Zkc.Source.Common.Region
import ZkcExamples.NativePrograms.Schnorr

/-! Kernel-checked component controls for the current scalar carrier lowering.
The imported Schnorr fixture is a test dependency only. These controls do not
claim general structured native import, native execution or security. -/

set_option autoImplicit false

namespace Tests.CommonRegion

open Zkc.Source Zkc.Source.Common PIR

inductive ValueSort where
  | datum | condition | handle
  deriving DecidableEq

inductive Operation where
  | literal (value : Nat)
  | add

abbrev language : Language where
  Ty := ValueSort
  Op := Operation
  arguments
    | .literal _ => []
    | .add => [.datum, .datum]
  result _ := .datum
  condition := .condition

abbrev services : Participant.Services ValueSort where
  Op := Unit
  arguments _ := [.handle, .datum]
  result _ := .datum

abbrev meaning : Mathematical.Meaning language where
  Value
    | .datum | .handle => Nat
    | .condition => Bool
  operation
    | .literal value, .nil => value
    | .add, .cons left (.cons right .nil) => left + right

abbrev localMeaning (self : Nat) :=
  participantMeaning (services := services) meaning id self

abbrev inputs {Γ : List ValueSort} (values : Values (fun sort => Option (meaning.Value sort)) Γ) :
    Environment (fun sort => Option (meaning.Value sort)) Γ :=
  values.get

abbrev actions := Participant.interface Nat ValueSort services meaning.Value

-- An empty input context needs no invented value. Empty rosters remain an
-- admission concern: lowering and denotation do not silently admit a program.
def constant : Common.Program Nat language services [] .datum :=
  .calculate (.letOp (.literal 7) .nil (.ret .here)) (.ret .here)

example : (constant.toRegion 9).denote (localMeaning 9) (inputs .nil) =
    .done (Values.singleton (some 7)) := rfl

example : constant.check [] (fun reference => nomatch reference) = false := rfl

example {Γ : List ValueSort} {ty : ValueSort}
    (program : Common.Program Empty language services Γ ty)
    (self : Empty) (env : Environment (fun sort => Option (meaning.Value sort)) Γ) :
    (program.toRegion self).denote (participantMeaning meaning id self) env =
      (program.denote meaning id self env).bind (fun value => .done (Values.singleton value)) :=
  program.denote_toRegion meaning id self env

def exchange : Common.Program Nat language services [.datum] .datum :=
  .exchange "delivery" 0 1 .here (.ret .here)

-- The sender aliases its own component after sending. The receiver's local
-- component may disagree or be absent; the continuation returns the actual reply.
example (sent : Nat) : (exchange.toRegion 0).denote (localMeaning 0)
    (inputs (Values.singleton (some sent))) =
      .call (.send (ty := .datum) "delivery" 1 sent) (fun _ => .done (Values.singleton (some sent))) := rfl

example (localValue : Option Nat) : (exchange.toRegion 1).denote (localMeaning 1)
    (inputs (Values.singleton localValue)) =
      .call (.receive .datum "delivery" 0)
        (fun actual => .done (Values.singleton (some actual))) := rfl

example : (exchange.toRegion 0).denote (localMeaning 0)
    (inputs (Values.singleton none)) = .halt .incomplete := rfl

example : (exchange.toRegion 2).denote (localMeaning 2)
    (inputs (Values.singleton (some 99))) = .done (Values.singleton none) := rfl

-- The universal equation includes unadmitted programs: sender precedence also
-- holds when sender and receiver coincide, while the source checker rejects it.
def sameParticipant : Common.Program Nat language services [.datum] .datum :=
  .exchange "self" 0 0 .here (.ret .here)

example : (sameParticipant.toRegion 0).denote (localMeaning 0)
    (inputs (Values.singleton (some 8))) =
      .call (.send (ty := .datum) "self" 0 8) (fun _ => .done (Values.singleton (some 8))) := rfl

example : sameParticipant.check [0] (fun _ _ => true) = false := rfl

def query : Common.Program Nat language services [.handle, .datum] .datum :=
  .query "challenge" 1 () (.cons .here (.cons (.there .here) .nil)) (.ret .here)

-- Both the service handle and its ordered argument reach the action unchanged.
-- An arbitrary actual reply supplies the continuation, not either input operand.
example (handle argument : Nat) : (query.toRegion 1).denote (localMeaning 1)
    (inputs (.cons (some handle) (.cons (some argument) .nil))) =
      .call (.query "challenge" () (.cons handle (.cons argument .nil)))
        (fun actual => .done (Values.singleton (some actual))) := rfl

example : (query.toRegion 1).denote (localMeaning 1)
    (inputs (.cons none (.cons (some 11) .nil))) = .halt .incomplete := rfl

example : (query.toRegion 1).denote (localMeaning 1)
    (inputs (.cons (some 73) (.cons none .nil))) = .halt .incomplete := rfl

example : (query.toRegion 0).denote (localMeaning 0)
    (inputs (.cons none (.cons none .nil))) = .done (Values.singleton none) := rfl

def guarded : Common.Program Nat language services [.condition, .datum] .datum :=
  .guard "verify" 1 .here (.exchange "after-guard" 1 0 (.there .here) (.ret .here))

example : (guarded.toRegion 1).denote (localMeaning 1)
    (inputs (.cons (some false) (.cons (some 5) .nil))) = .halt .reject := rfl

example : (guarded.toRegion 1).denote (localMeaning 1)
    (inputs (.cons none (.cons (some 5) .nil))) = .halt .incomplete := rfl

example : (guarded.toRegion 1).denote (localMeaning 1)
    (inputs (.cons (some true) (.cons (some 5) .nil))) =
      .call (.send (ty := .datum) "after-guard" 0 5) (fun _ => .done (Values.singleton (some 5))) := rfl

example : (guarded.toRegion 0).denote (localMeaning 0)
    (inputs (.cons none (.cons none .nil))) =
      .call (.receive .datum "after-guard" 1)
        (fun actual => .done (Values.singleton (some actual))) := rfl

-- Statements retain descriptor metadata and operands but do not require absent
-- runtime inputs, add a binding, emit an action or stop a participant.
def annotated : Common.Program Nat language services [.datum, .datum] .datum :=
  .statement "relation" [0, 1] (.cons .here (.cons (.there .here) .nil)) (.ret .here)

example : annotated.toRegion 0 =
    .letOp (.statement [.datum, .datum] "relation" [0, 1])
      (.cons .here (.cons (.there .here) .nil)) .nil (.ret (Values.singleton .here)) := rfl

example : (annotated.toRegion 0).denote (localMeaning 0)
    (inputs (.cons (some 6) (.cons none .nil))) = .done (Values.singleton (some 6)) := rfl

def calculation : Mathematical.Block Nat language [.datum, .datum] .datum :=
  .bind (.letOp .add (.cons .here (.cons (.there .here) .nil)) (.ret .here))
    (.restrict (fun role => role == 0) .here (.ret .here))

def calculated : Common.Program Nat language services [.datum, .datum] .datum :=
  .calculate calculation (.ret .here)

-- The calculation is visibly mathematical/restrict/bind syntax, not a callback
-- carrying a Block. Its inner binding remains lexical rather than leaking out.
example : calculated.toRegion 0 =
    .bind
      (.bind
        (.letOp (.mathematical .add) (.cons .here (.cons (.there .here) .nil)) .nil
          (.ret (Values.singleton .here)))
        (.letOp (.restrict .datum true) (Values.singleton .here) .nil
          (.ret (Values.singleton .here))))
      (.ret (Values.singleton .here)) := rfl

example : (calculated.toRegion 0).nodeCount = 7 := rfl

example : (calculated.toRegion 0).denote (localMeaning 0)
    (inputs (.cons (some 3) (.cons (some 4) .nil))) = .done (Values.singleton (some 7)) := rfl

example : (calculated.toRegion 1).denote (localMeaning 1)
    (inputs (.cons (some 30) (.cons (some 40) .nil))) = .done (Values.singleton none) := rfl

-- The selected participant is part of the dialect, not a convention between
-- lowering and interpretation. The old API returned some 7 for this mismatch.
example : True := by
  fail_if_success
    have := (calculated.toRegion 0).denote (localMeaning 1)
  trivial

example : (calculated.toRegion 0).denote (localMeaning 0)
    (inputs (.cons (some 3) (.cons none .nil))) = .done (Values.singleton none) := rfl

def unusedCalculation : Common.Program Nat language services [.datum, .datum] .datum :=
  .calculate calculation (.ret (.there .here))

example : (unusedCalculation.toRegion 0).denote (localMeaning 0)
    (inputs (.cons (some 3) (.cons none .nil))) = .done (Values.singleton (some 3)) := rfl

-- Disjoint operand availability makes the unused calculation fail admission.
-- The denotational adapter neither erases it nor converts absence into a stop.
def disjointScopes : Values (fun _ : ValueSort => Nat → Bool) [.datum, .datum] :=
  .cons (fun role => role == 0) (.cons (fun role => role == 1) .nil)

example : unusedCalculation.check [0, 1] disjointScopes.get = false := rfl

def emptyRestriction : Common.Program Nat language services [.datum] .datum :=
  .calculate (.restrict (fun _ => false) .here (.ret .here)) (.ret (.there .here))

example : emptyRestriction.check [0, 1] (fun _ _ => true) = false := rfl

example : (emptyRestriction.toRegion 0).denote (localMeaning 0)
    (inputs (Values.singleton (some 3))) = .done (Values.singleton (some 3)) := rfl

-- Exact dynamic meaning does not identify static source contracts. Changing a
-- relation annotation preserves the entire process, and removing an unused
-- restriction can turn a rejected source into an admitted source.
def anotherRelation : Common.Program Nat language services [.datum, .datum] .datum :=
  .statement "another-relation" [0, 1]
    (.cons .here (.cons (.there .here) .nil)) (.ret .here)

example (self : Nat) : Region.Equivalent (localMeaning self)
    (annotated.toRegion self) (anotherRelation.toRegion self) := by intro env; rfl

def withoutRestriction : Common.Program Nat language services [.datum] .datum := .ret .here

example (self : Nat) : Region.Equivalent (localMeaning self)
    (emptyRestriction.toRegion self) (withoutRestriction.toRegion self) := by intro env; rfl

example : withoutRestriction.check [0, 1] (fun _ _ => true) = true := rfl

def roundTrip : Common.Program Nat language services [.datum] .datum :=
  .exchange "out" 0 1 .here (.exchange "in" 1 0 .here (.ret .here))

example : (roundTrip.toRegion 0).denote (localMeaning 0)
    (inputs (Values.singleton (some 7))) =
      .call (.send (ty := .datum) "out" 1 7) (fun _ =>
        .call (.receive .datum "in" 1) (fun actual => .done (Values.singleton (some actual)))) := rfl

example (localValue : Option Nat) : (roundTrip.toRegion 1).denote (localMeaning 1)
    (inputs (Values.singleton localValue)) =
      .call (.receive .datum "out" 0) (fun actual =>
        .call (.send (ty := .datum) "in" 0 actual) (fun _ => .done (Values.singleton (some actual)))) := rfl

def stopAfterSend (reason : Stop) : Handler actions Nat String
  | .send site _ _, state => ⟨.returned (), state + 1, [site]⟩
  | .receive _ site _, state => ⟨.stopped reason, state + 1, [site]⟩
  | .query site _ _, state => ⟨.stopped reason, state + 1, [site]⟩

-- Every Stop constructor, post-state and event prefix survive lowering.
example (reason : Stop) :
    ((roundTrip.toRegion 0).denote (localMeaning 0)
      (inputs (Values.singleton (some 7)))).run (stopAfterSend reason) 10 =
        ⟨.stopped reason, 12, ["out", "in"]⟩ := rfl

example (reason : Stop) :
    ((roundTrip.toRegion 0).denote (localMeaning 0)
      (inputs (Values.singleton (some 7)))).runM (m := Id)
        (fun op state => pure (stopAfterSend reason op state)) 10 =
          pure ⟨.stopped reason, 12, ["out", "in"]⟩ := rfl

-- The adapter transports process equality even when the outer monad aborts
-- without an Execution record. It does not invent retained state or events.
example :
    ((roundTrip.toRegion 0).denote (localMeaning 0)
      (inputs (Values.singleton (some 7)))).runM (m := Except String)
        (fun (op : actions.Op) (state : Nat) => match op with
          | .send site _ _ => .ok ⟨.returned (), state + 1, [site]⟩
          | _ => .error "provider") 10 = .error "provider" := rfl

namespace ImportedSchnorr

open Zkc.Source.Common.Native
open ZkcExamples.NativePrograms

variable {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- Imported output filtering is tied to the same role as action interpretation.
example : True := by
  fail_if_success
    have := (Schnorr.imported.toRegion 0).denote
      (participantMeaning (scalarMeaning F G) id 1)
  trivial

-- This uses the actual checked native scalar carrier and its retained site
-- names, independent receive replies and concrete challenge-service operand.
theorem verifier_process (base key : G) (handle : Nat) :
    (Schnorr.imported.toRegion 1).denote
      (participantMeaning (scalarMeaning F G) id 1)
      (Schnorr.verifierInputs base key handle).get =
        (Schnorr.experiment (F := F) base key handle).bind
          (fun result => .done (Values.singleton result)) := by
  exact (Schnorr.imported.denote_toRegion (scalarMeaning F G) id 1
    (Schnorr.verifierInputs base key handle)).trans
      (by rfl)

example (base key : G) (handle : Nat) {S E : Type}
    (handler : Handler (Schnorr.actions (F := F) (G := G)) S E) (state : S) :
    ((Schnorr.imported.toRegion 1).denote
      (participantMeaning (scalarMeaning F G) id 1)
      (Schnorr.verifierInputs base key handle).get).run handler state =
        ((Schnorr.experiment (F := F) base key handle).bind
          (fun result => .done (Values.singleton result))).run handler state := by
  exact congrArg (fun process => process.run handler state) (verifier_process base key handle)

example {m : Type → Type} [Monad m] (base key : G) (handle : Nat) {S E : Type}
    (handler : MonadHandler m (Schnorr.actions (F := F) (G := G)) S E) (state : S) :
    ((Schnorr.imported.toRegion 1).denote
      (participantMeaning (scalarMeaning F G) id 1)
      (Schnorr.verifierInputs base key handle).get).runM handler state =
        ((Schnorr.experiment (F := F) base key handle).bind
          (fun result => .done (Values.singleton result))).runM handler state := by
  exact congrArg (fun process => process.runM handler state) (verifier_process base key handle)

-- Missing verifier service stops after the actual commitment is received.
example (base key : G) :
    (Schnorr.imported.toRegion 1).denote
      (participantMeaning (scalarMeaning F G) id 1)
      (Values.cons (some base) (.cons (some key) (.cons none (.cons none (.cons none .nil))))).get =
        .call (.receive (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 0)
          (fun _ => .halt .incomplete) := by
  exact (Schnorr.imported.denote_toRegion (scalarMeaning F G) id 1
    (.cons (some base) (.cons (some key) (.cons none (.cons none (.cons none .nil)))))).trans
      (by rfl)

-- An uninvolved role does not require either service and has no exported result.
example (base key : G) (handle : Nat) :
    (Schnorr.imported.toRegion 2).denote
      (participantMeaning (scalarMeaning F G) id 2)
      (Schnorr.verifierInputs base key handle).get = .done (Values.singleton none) := by
  exact (Schnorr.imported.denote_toRegion (scalarMeaning F G) id 2
    (Schnorr.verifierInputs base key handle)).trans (by rfl)

-- Output-role filtering happens after execution: the prover is not an output
-- owner, but its missing service still stops rather than returning absent.
example (base key : G) (handle : Nat) :
    (Schnorr.imported.toRegion 0).denote
      (participantMeaning (scalarMeaning F G) id 0)
      (Schnorr.verifierInputs base key handle).get = .halt .incomplete := by
  exact (Schnorr.imported.denote_toRegion (scalarMeaning F G) id 0
    (Schnorr.verifierInputs base key handle)).trans (by rfl)

end ImportedSchnorr
end Tests.CommonRegion
