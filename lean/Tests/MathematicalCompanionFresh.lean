import Tests.MathematicalCompanionFreshSources
import ZkcExamples.Structured.GkrGateCompanion
import Zkc.Source.TypedABI
import ZkcTools.StructuredSource.ProcessReference
import ZkcTools.StructuredSource.NamedEquations
import ZkcTools.Companions

/-! Named mathematical companions for the two fresh retained-source fixtures.
No new engine rule or representation library is installed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.MathematicalCompanionFresh
open Zkc.Source Zkc.Source.Structured
open MathematicalCompanionFreshSources

def wrappedReference (model : DomainModel)
    (right mulWeight addWeight left : model.Field scalarDomain) :
    PIR.Outcome (WrappedGate.Output model) := .returned ⟨
      Zkc.Protocols.AlgebraicRounds.Gate.value addWeight mulWeight left right, right, left⟩

companion_goal WrappedGoal for theorem wrapped (model : DomainModel) :
  WrappedGate.Goal model (wrappedReference model) (fun _ _ _ _ _ => True)

@[zkc "mathematical-companion/wrapped-gate"]
theorem wrapped_companion : WrappedGoal := by
  intro model table right mulWeight addWeight left _
  have installed := ZkcExamples.Structured.GkrGateCompanion.value model table
    addWeight mulWeight left right trivial
  have value := congrArg (fun process => process.bind fun result =>
    PIR.Process.done (WrappedGate.Output.mk result.value right left)) installed
  exact value

def readReference (model : DomainModel) (enabled : Bool)
    (values : List (model.Field scalarDomain)) (index : Nat)
    (expected : model.Field scalarDomain) : PIR.Outcome (GuardedRead.Output model) :=
  if enabled then
    match values[index]? with
    | some selected => .returned ⟨selected - expected, values, index⟩
    | none => .stopped .refused
  else .stopped .reject

companion_goal ReadGoal for theorem read (model : DomainModel) :
  GuardedRead.Goal model (readReference model) (fun _ _ _ _ _ => True)

@[zkc "mathematical-companion/guarded-read"]
theorem read_companion : ReadGoal := by
  intro model table enabled values index expected _
  change model.Field "bls12-381.fr" at expected
  change List (model.Field "bls12-381.fr") at values
  cases enabled with
  | false => rfl
  | true =>
    cases selected : values[index]? <;>
      named_reduce [GuardedRead.run, field, scalarDomain, ConnectionHelperCertificate.field,
        ↓reduceIte, readReference, primitiveOutcome] <;> rw [selected] <;> rfl

def wrappedSource (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (right mulWeight addWeight left : model.Field scalarDomain) :
    PIR.Process closedInterface (WrappedGate.Output model) :=
  WrappedGate.run model table right mulWeight addWeight left

def readSource (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (enabled : Bool) (values : List (model.Field scalarDomain)) (index : Nat)
    (expected : model.Field scalarDomain) : PIR.Process closedInterface (GuardedRead.Output model) :=
  GuardedRead.run model table enabled values index expected

theorem wrapped_equation (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (right mulWeight addWeight left : model.Field scalarDomain) :
    WrappedGate.run model table right mulWeight addWeight left =
      primitiveOutcome (wrappedReference model right mulWeight addWeight left) :=
  wrapped_companion model table right mulWeight addWeight left trivial

theorem read_equation (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (enabled : Bool) (values : List (model.Field scalarDomain)) (index : Nat)
    (expected : model.Field scalarDomain) :
    GuardedRead.run model table enabled values index expected =
      primitiveOutcome (readReference model enabled values index expected) :=
  read_companion model table enabled values index expected trivial

source_reference wrappedProcess from @wrappedSource using [wrappedSource, wrapped_equation]
source_reference readProcess from @readSource using [readSource, read_equation]

/-- Reinstall the mathematical goal on the complete retained source row.
The reordered inputs and all three outputs are part of the equation. -/
def wrappedLaw (model : DomainModel) :=
  WrappedGate.law model (wrappedReference model) (fun _ _ _ _ _ => True)
    (zkc_companion ["mathematical-companion/wrapped-gate" [model]])

theorem actual_wrapped (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (input : WrappedInputs.View model.Value) :
    wrappedGate.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (WrappedInputs.pack input).get =
      primitiveOutcome (WrappedGate.encodeOutcome model
        (wrappedReference model input.right input.mulWeight input.addWeight input.left)) :=
  (wrappedLaw model).valid table (WrappedInputs.pack input) trivial

def readLaw (model : DomainModel) :=
  GuardedRead.law model (readReference model) (fun _ _ _ _ _ => True)
    (zkc_companion ["mathematical-companion/guarded-read" [model]])

/-- Both reject and refused stops remain observable alongside every output. -/
theorem actual_guarded (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (input : ReadInputs.View model.Value) :
    guardedRead.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (ReadInputs.pack input).get =
      primitiveOutcome (GuardedRead.encodeOutcome model
        (readReference model input.enabled input.values input.index input.expected)) :=
  (readLaw model).valid table (ReadInputs.pack input) trivial

#print axioms actual_wrapped
#print axioms actual_guarded
end Tests.MathematicalCompanionFresh
