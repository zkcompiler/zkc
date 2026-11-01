import Tests.ReusableAggregateTwoBatchesSource
import Zkc.Protocols.TableMembership.BatchProtocolInstallation
import Zkc.Source.Structured.BodyBindings
import Zkc.Source.Structured.NormalizedRoot
import Zkc.Source.Structured.ProtocolPresentation
import ZkcTools.StructuredSource.Association
import ZkcTools.StructuredSource.NormalizedRoot
import ZkcTools.StructuredSource.Composition

/-! A fresh native source: an inline batch check followed by one protocol call
on different inputs, returning both decisions and both ordered batches.
The data and typed root are generated from the same native source capture.
Only the mathematical composition below is authored for this instance. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.ReusableAggregateTwoBatches
open Zkc.Source Zkc.Source.Structured NormalForm
open Zkc.Protocols.TableMembership

open ReusableAggregateTwoBatchesSource

abbrev signature := BatchSource.callSignature "koala-bear" names protocolNames

def validator : NormalizedRoot.Checked program 1 signature := by
  derive_normalized_source_root

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev model := ringModel F G

def results : LawResults (model (F := F) (G := G)) signature.laws where
  result entry := entry.elim0

abbrev callees := BatchSource.validatorCallees (F := F) (G := G) "koala-bear" names protocolNames

/-- Four independent visible inputs; private batches are filled as absent. -/
def arguments (firstPoint firstValue secondPoint secondValue : Option F) :
    Binders (model (F := F) (G := G)) (NormalizedRoot.pattern program 1).scope :=
  .cons firstPoint (.cons firstValue (.cons secondPoint (.cons secondValue .nil)))

def presented (firstPoint firstValue secondPoint secondValue : Option F) :=
  source_composition (NormalizedRoot.process validator model
    (arguments (G := G) firstPoint firstValue secondPoint secondValue)
    results callees)
  components [] atoms [Participant.owned, BatchSource.validatorReference]

theorem presented_equation (firstPoint firstValue secondPoint secondValue : Option F) :
    Occurrence.participant model program 1
      (NormalizedRoot.inputs model
        (arguments (G := G) firstPoint firstValue secondPoint secondValue)) =
      presented (G := G) firstPoint firstValue secondPoint secondValue := by
  refine (NormalizedRoot.equation validator model
    (arguments (G := G) firstPoint firstValue secondPoint secondValue) results callees
    (fun entry => entry.elim0)
    (BatchSource.validator_callees_hold unit bodies batchSource _)).trans ?_
  source_composition_equation atoms [Participant.owned, BatchSource.validatorReference]

/-- The complete mathematical reference retains every receive, stop and output.
A false first decision still reaches the second call with independent inputs. -/
def reference (firstPoint firstValue secondPoint secondValue : Option F) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) pairSignature.outputs) :=
  (PIR.Process.call (I := Occurrence.signature (uniformCarriers F G))
    (.action (.receive batchTy "label_66697273745f6261746368_0" 0)) PIR.Process.done).bind fun first =>
    (BatchSource.ownedCheckReference (G := G) firstPoint firstValue (some first)).bind fun checked =>
      (BatchSource.validatorReference (G := G) "koala-bear" names protocolNames
        (({} : ProtocolContext).enter "label_7365636f6e645f6261746368" [0, 1])
        secondPoint secondValue).bind fun second =>
          .done (.cons (checked.get .here) (.cons (some first)
            (.cons (second.get .here) (.cons (second.get (.there .here)) .nil))))

theorem whole_reference (firstPoint firstValue secondPoint secondValue : Option F) :
    Occurrence.participant model program 1
      (NormalizedRoot.inputs model
        (arguments (G := G) firstPoint firstValue secondPoint secondValue)) =
      reference (G := G) firstPoint firstValue secondPoint secondValue := by
  rw [presented_equation]
  unfold presented
  simp only [BatchSource.owned_check_equation (F := F) (G := G) program.payload bodies]
  source_composition_equation atoms [BatchSource.ownedCheckReference, BatchSource.validatorReference]

/-- A concrete handler supplies two different batches at the two reached sites. -/
def replies (first second : BatchSource.Batch Rat) :
    PIR.Handler (Occurrence.signature (uniformCarriers Rat Rat)) Nat String
  | .enter _, count | .leave _, count => ⟨.returned (), count, []⟩
  | .action (.receive (.sequence (.product _ _ (.cons (.field _) (.cons (.field _) .nil)))) site _), count =>
      ⟨.returned (if count = 0 then first else second), count + 1, [site]⟩
  | .action (.receive ..), count | .action (.query ..), count =>
      ⟨.stopped .refused, count, []⟩
  | .action (.send ..), count => ⟨.returned (), count, []⟩

def firstBatch : BatchSource.Batch Rat := [(2, 9, ())]
def secondBatch : BatchSource.Batch Rat := [(5, 7, ()), (5, 7, ())]

def observed (firstPoint firstValue secondPoint secondValue : Option Rat) :=
  (Occurrence.participant (ringModel Rat Rat) program 1
    (NormalizedRoot.inputs (ringModel Rat Rat)
      (arguments (G := Rat) firstPoint firstValue secondPoint secondValue))).run
        (replies firstBatch secondBatch) 0

/-- A false first decision still runs the independent second check. The entire
ordered result keeps the first and second batches, with their distinct lengths. -/
theorem false_first_keeps_second :
    (observed (some 2) (some 3) (some 5) (some 7)).outcome =
      .returned (.cons (some false) (.cons (some firstBatch)
        (.cons (some true) (.cons (some secondBatch) .nil)))) ∧
    (observed (some 2) (some 3) (some 5) (some 7)).state = 2 ∧
    (observed (some 2) (some 3) (some 5) (some 7)).events =
      ["label_66697273745f6261746368_0",
       qualifyProtocolSite (some "label_7365636f6e645f6261746368") protocolNames.messageSite] := by
  unfold observed
  rw [whole_reference]
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

/-- Missing first inputs stop after the first receive. Missing second inputs
still receive the second batch before stopping; these are different prefixes. -/
theorem missing_inputs_keep_receive_prefix :
    (observed none (some 3) (some 5) (some 7)).outcome = .stopped .incomplete ∧
    (observed none (some 3) (some 5) (some 7)).state = 1 ∧
    (observed (some 2) (some 3) none (some 7)).outcome = .stopped .incomplete ∧
    (observed (some 2) (some 3) none (some 7)).state = 2 := by
  unfold observed
  rw [whole_reference, whole_reference]
  constructor
  · kernel_rfl
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

#print axioms validator
#print axioms presented_equation
#print axioms whole_reference
#print axioms false_first_keeps_second
#print axioms missing_inputs_keep_receive_prefix
end Tests.ReusableAggregateTwoBatches
