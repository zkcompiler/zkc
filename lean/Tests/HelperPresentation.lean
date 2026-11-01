import ZkcTools.StructuredSource.HelperPresentation
import ZkcTools.Companions
import Zkc.Source.Structured.ReferenceLibrary
import Zkc.Source.Structured.CollectLaws
import Zkc.Protocols.Gkr.Source.RoundHelpers
import Tests.ConnectionHelperCertificate
import Tests.ReusableAggregateTwoBatchesBodies

/-! Generated goals precede mathematical companions; assembly follows them.
The controls preserve ordered operands, complete aggregate returns and stops.
-/
set_option autoImplicit false
noncomputable section
namespace Tests.HelperPresentation
open Zkc.Source Zkc.Source.Structured
open Tests.ConnectionHelperCertificate

/-- Importing the command must not reserve common mathematical binder names. -/
def inputs (outputs : Nat) : Nat := outputs
example (inputs outputs : Nat) : inputs + outputs = outputs + inputs := Nat.add_comm _ _

/-- error: helper_presentation names must cover every input and output in ABI order -/
#guard_msgs in
helper_presentation Incomplete inputs [left, right] outputs [] := scalarLeafBody false

/-- error: helper_presentation requires distinct field names -/
#guard_msgs in
helper_presentation Duplicated inputs [left, left] outputs [value] := scalarLeafBody false

/-- error: helper_presentation field name is reserved or qualified: Output -/
#guard_msgs in
helper_presentation Reserved inputs [Output, right] outputs [value] := scalarLeafBody false

/-- error: helper_presentation field name is reserved or qualified: decodeOutcome -/
#guard_msgs in
helper_presentation ReservedDecoder inputs [left, right] outputs [decodeOutcome] := scalarLeafBody false

/-- error: helper_presentation field name is reserved or qualified: of_installed -/
#guard_msgs in
helper_presentation ReservedTransport inputs [of_installed, right] outputs [value] := scalarLeafBody false

/-- error: helper_presentation field name is reserved or qualified: encode_decode_outcome -/
#guard_msgs in
helper_presentation ReservedRoundtrip inputs [left, right] outputs [encode_decode_outcome] := scalarLeafBody false

/-- error: helper_presentation expects an actual typed helper Region -/
#guard_msgs in
helper_presentation NotRegion inputs [] outputs [] := (7 : Nat)

/-- error: helper_presentation expects the existing closed helper dialect -/
#guard_msgs in
helper_presentation Interactive inputs [] outputs [] := (.ret .nil : Region protocolDialect [] [])

section
variable (selected : Region dialect [] [])
/-- error: helper_presentation expects a closed typed helper/template; instantiate its static parameters first -/
#guard_msgs in
helper_presentation OpenBody inputs [] outputs [] := selected
end

opaque unknownInputs : List Ty := []
opaque unknownBody : Region dialect unknownInputs [] := .stop .abort

/-- error: helper_presentation requires a statically known complete ABI -/
#guard_msgs in
helper_presentation UnknownABI inputs [] outputs [] := unknownBody

namespace Rollback
def law : Unit := ()
end Rollback

/-- error: helper_presentation: generated declaration failed to check
`Tests.HelperPresentation.Rollback.law` has already been declared -/
#guard_msgs in
helper_presentation Rollback inputs [left, right] outputs [value] := scalarLeafBody false

/-- error: Unknown identifier `Rollback.run` -/
#guard_msgs in
#check Rollback.run

example : Rollback.law = () := rfl

helper_presentation Difference inputs [left, right] outputs [value] := scalarLeafBody false

def differenceReference (model : DomainModel) (left right : model.Field "bls12-381.fr") :
    PIR.Outcome (Difference.Output model) := .returned ⟨left - right⟩

companion_goal DifferenceObligation for theorem differenceCorrespondence (model : DomainModel) :
  Difference.Goal model (differenceReference model) (fun _ _ _ => True)

theorem difference_companion : DifferenceObligation := by
  intro model table left right _
  rfl

/-- Assembly consumes the proof only after the complete goal was generated. -/
noncomputable def differenceLaw (model : DomainModel) :=
  Difference.law model (differenceReference model) (fun _ _ _ => True)
    (difference_companion model)

theorem actual_difference (model : DomainModel) (left right : model.Field "bls12-381.fr") :
    invoke ((scalarProgram false).payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (scalarLeaf false).helper (.cons left (.cons right .nil)) =
      .done (.cons (left - right) .nil) := by
  apply ReferenceLaw.invoke (helper := (scalarLeaf false).helper) (differenceLaw model)
    (scalarProgram false).payload.definitions (scalarProgram false).payload.linked
  · bind_structured_bodies
  · trivial

-- The direct application above needed no registration. The existing resolver
-- also accepts exactly the already generated goal.
attribute [zkc "helper-presentation/difference"] difference_companion

example (model : DomainModel) :
    Difference.Goal model (differenceReference model) (fun _ _ _ => True) :=
  zkc_companion ["helper-presentation/difference" [model]]

/-- Swapping two identically typed operands changes the fixed goal. -/
theorem swapped_reference_refused :
    ¬ Difference.Goal (ringModel Int Int)
      (fun left right => .returned ⟨right - left⟩) (fun _ _ _ => True) := by
  intro wrong
  have values := PIR.Process.done.inj (wrong [] 5 2 trivial)
  have impossible : (3 : Int) = -3 := congrArg Difference.Output.value values
  norm_num at impossible

example (_model : DomainModel) : True := by
  fail_if_success
    have : Difference.Goal _model (fun left right => .returned ⟨right - left⟩)
        (fun _ _ _ => True) :=
      zkc_companion ["helper-presentation/difference" [_model]]
  trivial

def swappedBody : Region dialect scalarInputs [field] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

def swappedDefinition : CheckedDefinition :=
  ⟨"difference", .math, scalarInputs, [field], swappedBody.erase,
    swappedBody, swappedBody.elaborate_erase⟩

/-- Same signature and spelling do not authorize a changed operand order. -/
example (_model : DomainModel) : True := by
  fail_if_success
    have : BodyIn [swappedDefinition] (scalarLeaf false).helper (differenceLaw _model).body := by
      bind_structured_bodies
  trivial

/-- Installed transport still demands equality with the complete actual body. -/
example (model : DomainModel) (installed : ReferenceLaw model scalarInputs [field])
    (_same : installed.body = swappedBody) : True := by
  fail_if_success
    have := Difference.of_installed model installed _same
  trivial

/-- A law may carry any table- and input-dependent premise. Transport must
retain that very proposition, even when this particular body needs less. -/
def conditionalDifferenceLaw (model : DomainModel)
    (condition : Evaluation.MeaningsOn model.toCarriers closedInterface →
      Values model.Value scalarInputs → Prop) : ReferenceLaw model scalarInputs [field] :=
  { differenceLaw model with
    Requires := condition
    valid := by
      intro table arguments _
      cases arguments with
      | cons left rest => cases rest with
        | cons right rest =>
          cases rest
          exact (differenceLaw model).valid table (.cons left (.cons right .nil)) trivial }

theorem conditional_difference (model : DomainModel)
    (condition : Evaluation.MeaningsOn model.toCarriers closedInterface →
      Values model.Value scalarInputs → Prop) :
    Difference.Goal model (differenceReference model)
      (fun table left right => condition table (.cons left (.cons right .nil))) :=
  Difference.of_installed model (conditionalDifferenceLaw model condition) rfl

example (model : DomainModel)
    (_condition : Evaluation.MeaningsOn model.toCarriers closedInterface →
      Values model.Value scalarInputs → Prop)
    (_table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (_left _right : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : Difference.run model _table _left _right =
        primitiveOutcome (differenceReference model _left _right) := by
      exact Difference.of_installed model (conditionalDifferenceLaw model _condition) rfl
        _table _left _right (by trivial)
  trivial

def aggregateType : Ty :=
  .product "helper-presentation-pair" "pair" (.cons (.field "bls12-381.fr") (.cons .index .nil))

def aggregateBody : Region dialect [aggregateType, .vector "bls12-381.fr", .boolean]
    [.boolean, aggregateType, .vector "bls12-381.fr", .index] :=
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there .here) .nil) .nil <|
    .ret (.cons (.there (.there (.there .here)))
      (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))))

helper_presentation Aggregate inputs [record, batch, accepted]
  outputs [decision, pair, values, size] := aggregateBody

def aggregateReference (model : DomainModel) (record : model.Value aggregateType)
    (batch : List (model.Field "bls12-381.fr")) (accepted : Bool) :
    PIR.Outcome (Aggregate.Output model) := .returned ⟨accepted, record, batch, batch.length⟩

theorem aggregate_companion (model : DomainModel) :
    Aggregate.Goal model (aggregateReference model) (fun _ _ _ _ => True) := by
  intro table record batch accepted _
  rfl

theorem installed_aggregate (model : DomainModel) :
    Aggregate.Goal model (aggregateReference model) (fun _ _ _ _ => True) :=
  Aggregate.of_installed model
    (Aggregate.law model (aggregateReference model) (fun _ _ _ _ => True) (aggregate_companion model)) rfl

example (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (record : model.Value aggregateType) (batch : List (model.Field "bls12-381.fr")) :
    Aggregate.run model table record batch false = .done ⟨false, record, batch, batch.length⟩ :=
  installed_aggregate model table record batch false trivial

/-- Complete, ordered transport includes a returned false, an aggregate, a
vector and the independent final index coordinate. -/
example (model : DomainModel) (record : model.Value aggregateType)
    (batch : List (model.Field "bls12-381.fr")) (size : Nat) :
    Aggregate.decodeOutcome model (.returned (.cons false
      (.cons record (.cons batch (.cons size .nil))))) =
      .returned ⟨false, record, batch, size⟩ := rfl

example (model : DomainModel)
    (outcome : PIR.Outcome (Values model.Value [.boolean, aggregateType, .vector "bls12-381.fr", .index])) :
    Aggregate.encodeOutcome model (Aggregate.decodeOutcome model outcome) = outcome :=
  Aggregate.encode_decode_outcome model outcome

example (model : DomainModel) (outcome : PIR.Outcome (Aggregate.Output model)) :
    Aggregate.decodeOutcome model (Aggregate.encodeOutcome model outcome) = outcome :=
  Aggregate.decode_encode_outcome model outcome

example (model : DomainModel) (reason : PIR.Stop) :
    Aggregate.decodeOutcome model (.stopped reason) = .stopped reason := rfl

helper_presentation OrderedPair inputs [left, right] outputs [difference, original] := scalarPairBody

/-- Equal carrier types must not hide a permutation of the two ABI positions. -/
example (model : DomainModel) (left right : model.Field "bls12-381.fr") :
    OrderedPair.decodeOutcome model (.returned (.cons left (.cons right .nil))) =
      .returned ⟨left, right⟩ := rfl

/-- The decision is insufficient: every aggregate and vector result is fixed. -/
example (_model : DomainModel) : True := by
  fail_if_success
    have : Aggregate.Goal _model
        (fun record _ accepted => .returned ⟨accepted, record, [], 0⟩)
        (fun _ _ _ _ => True) := aggregate_companion _model
  trivial

helper_presentation Read inputs [batch, index] outputs [value] := readLeafBody

def readReference (model : DomainModel) (batch : List (model.Field "bls12-381.fr")) (index : Nat) :
    PIR.Outcome (Read.Output model) :=
  match batch[index]? with
  | some value => .returned ⟨value⟩
  | none => .stopped .refused

theorem read_companion (model : DomainModel) :
    Read.Goal model (readReference model) (fun _ _ _ => True) := by
  intro table batch index _
  cases selected : batch[index]? with
  | none => simp only [Read.run, readReference, selected, primitiveOutcome, PIR.Process.bind]
  | some value =>
      simp only [Read.run, readReference, selected, primitiveOutcome, PIR.Process.bind]
      rfl

helper_presentation Cursor inputs [batch, index] outputs [value, cursor] := readPairBody

/-- Reuse the existing call law and actual two-result wrapper body, including
the caller's cursor. Its dependency is required on the arbitrary caller table. -/
def cursorLibrary (model : DomainModel) : ReferenceLaw model readInputs [field, .index] :=
  ReferenceLibrary.call model readLeaf.helper (.cons .here (.cons (.there .here) .nil))
    (.cons .here (.cons (.there (.there .here)) .nil))
    (fun arguments => Read.encodeOutcome model
      (readReference model (arguments.get .here) (arguments.get (.there .here))))

theorem cursor_transport (model : DomainModel) :
    Cursor.Goal model
      (fun batch index => Cursor.decodeOutcome model
        ((cursorLibrary model).reference (.cons batch (.cons index .nil))))
      (fun table batch index => (cursorLibrary model).Requires table (.cons batch (.cons index .nil))) :=
  Cursor.of_installed model (cursorLibrary model) rfl

example (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (first value : model.Field "bls12-381.fr")
    (dependency : invoke table readLeaf.helper (.cons [first, value] (.cons 1 .nil)) =
      .done (.cons value .nil)) :
    Cursor.run model table [first, value] 1 = .done ⟨value, 1⟩ :=
  cursor_transport model table [first, value] 1 dependency

example (model : DomainModel) (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (dependency : invoke table readLeaf.helper (.cons [] (.cons 7 .nil)) = .halt .refused) :
    Cursor.run model table [] 7 = .halt .refused :=
  cursor_transport model table [] 7 dependency

example (model : DomainModel) (_table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (_batch : List (model.Field "bls12-381.fr")) (_index : Nat) : True := by
  fail_if_success
    have : Cursor.run model _table _batch _index = primitiveOutcome
        (Cursor.decodeOutcome model ((cursorLibrary model).reference (.cons _batch (.cons _index .nil)))) := by
      exact cursor_transport model _table _batch _index (by rfl)
  trivial

example (model : DomainModel) (batch : List (model.Field "bls12-381.fr")) :
    Read.run model [] batch batch.length = .halt .refused := by
  simpa [readReference, primitiveOutcome] using read_companion model [] batch batch.length trivial

helper_presentation Sum inputs [batch] outputs [value] :=
  (ReferenceLibrary.sumVector (ringModel Int Int) "bls12-381.fr" "s0").body

/-- An existing mathematical library theorem discharges the generated statement
without registering a rule or exposing positional ABI construction to its author. -/
theorem sum_companion (model : DomainModel) :
    Sum.Goal model (fun batch => .returned ⟨batch.sum⟩) (fun _ _ => True) := by
  apply Sum.of_law model _ _ (ReferenceLibrary.sumVector model "bls12-381.fr" "s0") rfl
  · intro batch; rfl
  · intro table batch _; trivial

helper_presentation Stop inputs [] outputs [] := (.stop .exhausted : Region dialect [] [])

theorem stopping_companion (model : DomainModel) :
    Stop.Goal model (.stopped .exhausted) (fun _ => True) := by
  intro table _
  rfl

/-- Both rows are empty: no curried input binder or returned coordinate may
be invented, and a stop still carries its exact reason. -/
example (model : DomainModel) : Stop.Goal model (.stopped .exhausted) (fun _ => True) :=
  Stop.of_installed model
    (Stop.law model (.stopped .exhausted) (fun _ => True) (stopping_companion model)) rfl

example (model : DomainModel) (outcome : PIR.Outcome (Values model.Value [])) :
    Stop.encodeOutcome model (Stop.decodeOutcome model outcome) = outcome :=
  Stop.encode_decode_outcome model outcome

example (model : DomainModel) (outcome : PIR.Outcome (Stop.Output model)) :
    Stop.decodeOutcome model (Stop.encodeOutcome model outcome) = outcome :=
  Stop.decode_encode_outcome model outcome

helper_presentation Empty inputs [] outputs [] := (.ret .nil : Region dialect [] [])

example (model : DomainModel) : Empty.Goal model (.returned {}) (fun _ => True) :=
  Empty.of_installed model (ReferenceLibrary.projection model .nil) rfl

example (model : DomainModel) :
    Empty.decodeOutcome model (.returned .nil) = .returned {} := rfl

helper_presentation EmptyVector inputs [] outputs [batch] :=
  (ReferenceLibrary.emptyVector (ringModel Int Int) "bls12-381.fr" "s0").body

example (model : DomainModel) : EmptyVector.Goal model (.returned ⟨[]⟩) (fun _ => True) :=
  EmptyVector.of_installed model (ReferenceLibrary.emptyVector model "bls12-381.fr" "s0") rfl

helper_presentation Discard inputs [accepted] outputs [] := (.ret .nil : Region dialect [.boolean] [])

example (model : DomainModel) : Discard.Goal model (fun _ => .returned {}) (fun _ _ => True) :=
  Discard.of_installed model (ReferenceLibrary.projection model .nil) rfl

def stopThenReturn : Region dialect [.boolean] [.boolean] :=
  .bind (.stop .abort : Region dialect [.boolean] []) (.ret (.cons .here .nil))

helper_presentation StopBeforeReturn inputs [accepted] outputs [decision] := stopThenReturn

example (model : DomainModel) :
    StopBeforeReturn.Goal model (fun _ => .stopped .abort) (fun _ _ => True) := by
  intro table accepted _
  rfl

open Tests.ReusableAggregateTwoBatchesBodies

helper_presentation CheckOpening
  inputs [accepted, value, tag, claimedValue, claimedTag] outputs [decision] := checkOpeningBody

theorem check_opening_companion (model : DomainModel) :
    CheckOpening.Goal model
      (fun accepted value tag claimedValue claimedTag =>
        .returned ⟨(accepted && decide (value = claimedValue)) && decide (tag = claimedTag)⟩)
      (fun _ _ _ _ _ _ => True) := by
  intro table accepted value tag claimedValue claimedTag _
  rfl

helper_presentation BatchStep inputs [accepted, opening, batch, expectedValue, expectedTag]
  outputs [decision] := batchStepBody

open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

helper_presentation Gate inputs [addWeight, mulWeight, left, right] outputs [value] := gateValueBody

def gateReference (model : DomainModel)
    (addWeight mulWeight left right : model.Field "bls12-381.fr") : PIR.Outcome (Gate.Output model) :=
  .returned ⟨addWeight * (left + right) + (mulWeight * left) * right⟩

theorem gate_companion (model : DomainModel) :
    Gate.Goal model (gateReference model) (fun _ _ _ _ _ => True) := by
  intro table addWeight mulWeight left right _
  rfl

helper_presentation GateCallback
  inputs [addWeight, mulWeight, left, right, addWeights, mulWeights, lefts, rights]
  outputs [value] := gateValueCallbackBody

example (model : DomainModel) (addWeight mulWeight left right : model.Field "bls12-381.fr")
    (addWeights mulWeights lefts rights : List (model.Field "bls12-381.fr")) :
    GateCallback.run model [] addWeight mulWeight left right addWeights mulWeights lefts rights =
      .halt .refused := by rfl

helper_presentation GateMap inputs [addWeights, mulWeights, lefts, rights]
  outputs [values] := gateValuesLeftBody

/-- These are the retained actual templates, not copied callback algorithms. -/
def gateDefinition : CheckedDefinition :=
  ⟨gateValueHelper.name, gateValueHelper.kind, gateValueHelper.inputs, gateValueHelper.outputs,
    gateValueBody.erase, gateValueBody, gateValueBody.elaborate_erase⟩

def realizationDefinition : CheckedDefinition :=
  ⟨gateValueRealizationHelper.name, gateValueRealizationHelper.kind,
    gateValueRealizationHelper.inputs, gateValueRealizationHelper.outputs,
    gateValueRealizationBody.erase, gateValueRealizationBody, gateValueRealizationBody.elaborate_erase⟩

def callbackDefinition : CheckedDefinition :=
  ⟨gateValueCallbackHelper.name, gateValueCallbackHelper.kind,
    gateValueCallbackHelper.inputs, gateValueCallbackHelper.outputs,
    gateValueCallbackBody.erase, gateValueCallbackBody, gateValueCallbackBody.elaborate_erase⟩

def stoppingCallback : CheckedDefinition :=
  ⟨gateValueCallbackHelper.name, gateValueCallbackHelper.kind,
    gateValueCallbackHelper.inputs, gateValueCallbackHelper.outputs,
    (.stop .abort : Region dialect gateValueCallbackHelper.inputs gateValueCallbackHelper.outputs).erase,
    .stop .abort, Region.elaborate_erase _⟩

example (model : DomainModel) : GateMap.run model [] [] [] [] [] = .done ⟨[]⟩ := by rfl

example (model : DomainModel) (value : model.Field "bls12-381.fr") :
    GateMap.run model [] [value] [] [] [] = .halt .refused := by rfl

set_option maxHeartbeats 2000000 in
theorem gate_map_singleton (model : DomainModel)
    (addWeight mulWeight left right : model.Field "bls12-381.fr") :
    GateMap.run model ([gateDefinition, realizationDefinition, callbackDefinition].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      [addWeight] [mulWeight] [left] [right] =
      .done ⟨[addWeight * (left + right) + (mulWeight * left) * right]⟩ := by rfl

set_option maxHeartbeats 2000000 in
theorem gate_map_stops (model : DomainModel) (value : model.Field "bls12-381.fr") :
    GateMap.run model ([stoppingCallback].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      [value] [value] [value] [value] = .halt .abort := by rfl

#print axioms actual_difference
#print axioms Difference.of_installed
#print axioms conditional_difference
#print axioms installed_aggregate
#print axioms Aggregate.encode_decode_outcome
#print axioms Aggregate.decode_encode_outcome
#print axioms cursor_transport
#print axioms Stop.of_installed
#print axioms Empty.of_installed
#print axioms aggregate_companion
#print axioms read_companion
#print axioms sum_companion
#print axioms stopping_companion
#print axioms Stop.equation
#print axioms CheckOpening.equation
#print axioms check_opening_companion
#print axioms gate_companion
#print axioms GateMap.equation
#print axioms gate_map_singleton
#print axioms gate_map_stops

end Tests.HelperPresentation
