import Tests.ReusableAggregateTwoBatchesSource
import Zkc.Protocols.TableMembership.BatchProtocolInstallation
import Zkc.Source.Structured.BodyBindings
import Zkc.Source.Structured.NormalizedRoot
import Zkc.Source.Structured.ProtocolPresentation
import ZkcTools.StructuredSource.Association
import ZkcTools.StructuredSource.NormalizedRoot
import ZkcTools.StructuredSource.Composition
import ZkcTools.StructuredSource.ProcessReference
import Tests.MathematicalCompanionBatches

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
open MathematicalCompanionGoals MathematicalCompanionBatches

abbrev signature := BatchSource.callSignature "koala-bear" names protocolNames

def validator : NormalizedRoot.Checked program 1 signature := by
  derive_normalized_source_root

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev model := ringModel F G

def results : LawResults (model (F := F) (G := G)) signature.laws where
  result entry := entry.elim0

abbrev callees := BatchSource.validatorCallees (F := F) (G := G) "koala-bear" names protocolNames

named_values ValidatorArguments [firstPoint, firstValue, secondPoint, secondValue] :=
  (NormalizedRoot.pattern program 1).scope

/-- Four independent visible inputs; private batches are filled as absent. -/
def arguments (firstPoint firstValue secondPoint secondValue : Option F) :
    Binders (model (F := F) (G := G)) (NormalizedRoot.pattern program 1).scope :=
  ValidatorArguments.pack { firstPoint, firstValue, secondPoint, secondValue }

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

/- Derive the full reference and its equation from the actual presented source.
The installed batch law supplies the mathematics; output packing and source
sites are retained by generation rather than restated by this client. -/
source_reference reference from (@presented F G _ _ _ _ _)
  using [presented,
    (BatchSource.owned_check_equation (F := F) (G := G) program.payload bodies)]

theorem whole_reference (firstPoint firstValue secondPoint secondValue : Option F) :
    Occurrence.participant model program 1
      (NormalizedRoot.inputs model
        (arguments (G := G) firstPoint firstValue secondPoint secondValue)) =
      reference (G := G) firstPoint firstValue secondPoint secondValue := by
  rw [presented_equation]
  exact congrFun (congrFun (congrFun (congrFun
    (reference_equation (F := F) (G := G)) firstPoint) firstValue) secondPoint) secondValue

/-- Named author boundary. Hidden batches remain absent; all four public
coordinates remain optional. The normalizer owns their actual use sites. -/
def namedInputs (firstPoint firstValue secondPoint secondValue : Option F) :
    BatchInputs.View (Component (model (F := F) (G := G)).Value) :=
  { firstPoint, firstValue, firstBatch := none,
    secondPoint, secondValue, secondBatch := none }

def namedReference (input : BatchInputs.View (Component (model (F := F) (G := G)).Value)) :=
  (reference (G := G) input.firstPoint input.firstValue input.secondPoint input.secondValue).bind
    fun row => .done (BatchOutputs.unpack row)

/-- This is the entire returned row, not an acceptance projection. The input
mask ignores the two arbitrary private coordinates supplied by a caller. -/
theorem named_whole_reference
    (input : BatchInputs.View (Component (model (F := F) (G := G)).Value)) :
    (Occurrence.participant model program 1 (BatchInputs.pack input)).bind
      (fun row => .done (BatchOutputs.unpack row)) = namedReference input := by
  have masked : Occurrence.participant model program 1 (BatchInputs.pack input) =
      Occurrence.participant model program 1
        (NormalizedRoot.inputs model
          (arguments (G := G) input.firstPoint input.firstValue input.secondPoint input.secondValue)) := by
    rfl
  rw [masked, whole_reference]
  rfl

/-- The ordinary companion is installed only after fixing its full goal. Its
helper association still checks the actual generated definition list. -/
def openingLaw (selectedModel : DomainModel) :=
  Opening.law selectedModel (openingReference selectedModel) (fun _ _ _ _ _ _ => True)
    (zkc_companion ["mathematical-companion/batch-opening" [selectedModel]])

theorem actual_opening (selectedModel : DomainModel) (accepted : Bool)
    (point value expectedPoint expectedValue : selectedModel.Field "koala-bear") :
    invoke (unit.definitions.foldl (Evaluation.extendMeaningsOn selectedModel SiteObservations.closed) [])
      ReusableAggregateTwoBatchesBodies.checkOpeningHelper
      (OpeningInputs.pack { accepted, point, value, expectedPoint, expectedValue }) =
      primitiveOutcome (Opening.encodeOutcome selectedModel
        (openingReference selectedModel accepted point value expectedPoint expectedValue)) := by
  exact ReferenceLaw.invoke
    (helper := ReusableAggregateTwoBatchesBodies.checkOpeningHelper)
    (openingLaw selectedModel) unit.definitions unit.linked
    (by bind_structured_bodies) _ trivial

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
  ((Occurrence.participant (ringModel Rat Rat) program 1
    (BatchInputs.pack (namedInputs (G := Rat) firstPoint firstValue secondPoint secondValue))).bind
      (fun row => .done (BatchOutputs.unpack row))).run (replies firstBatch secondBatch) 0

/-- A false first decision still runs the independent second check. The entire
ordered result keeps the first and second batches, with their distinct lengths. -/
theorem false_first_keeps_second :
    (observed (some 2) (some 3) (some 5) (some 7)).outcome =
      .returned
        { firstDecision := some false, firstBatch := some firstBatch,
          secondDecision := some true, secondBatch := some secondBatch } ∧
    (observed (some 2) (some 3) (some 5) (some 7)).state = 2 ∧
    (observed (some 2) (some 3) (some 5) (some 7)).events =
      ["label_66697273745f6261746368_0",
       qualifyProtocolSite (some "label_7365636f6e645f6261746368") protocolNames.messageSite] := by
  unfold observed
  rw [named_whole_reference]
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
  rw [named_whole_reference, named_whole_reference]
  constructor
  · kernel_rfl
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

#print axioms validator
#print axioms presented_equation
#print axioms whole_reference
#print axioms named_whole_reference
#print axioms actual_opening
#print axioms false_first_keeps_second
#print axioms missing_inputs_keep_receive_prefix
end Tests.ReusableAggregateTwoBatches
