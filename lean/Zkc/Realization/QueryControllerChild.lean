module

public import Zkc.Realization.QueryContinuation
public import Zkc.Realization.QueryController
public import Zkc.Realization.RecordProjection
public import Zkc.Construction.ConnectionMathRegionSoundness
public import Zkc.Construction.ConnectionClosedSimulation

@[expose] public section

/-! The generated child transition saves the parent before calculating the
child position and unpacking its reference. This composition is shared by first
entry and sibling dispatch. The position certificate comes from the original
Math slice; it does not supply frame storage, reference routing or checkpoints.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryController
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace IndexLiterals

def instructions (values : List Nat) : List Construction.Instruction :=
  values.map fun value ↦ ⟨.execute (.indexConstant value), [], [.data .index], []⟩

def encode {carriers : Carriers} (values : List Nat) : Domain.Environment carriers :=
  values.map fun value ↦ .data (.index value)

/-- Constants remaining after common-subexpression elimination are interpreted
in their emitted order. Reused literals need not be reintroduced. -/
noncomputable def simulation (model : DomainModel) (program : Program) (context : Context)
    (values : List Nat) (bounded : ∀ value ∈ values, value < indexLimit)
    (environment : Domain.Environment model.toCarriers) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ encode values))
      (Domain.evaluate model program context (instructions values) environment) := by
  induction values generalizing environment with
  | nil => exact .done (by simp [encode])
  | cons value rest ih =>
      have constant : Domain.View.execute model (.indexConstant value) [] [.data .index]
          environment = .done (environment ++ [.data (.index value)]) := by
        have law := ConnectionPrimitives.view_execute model (.indexConstant value)
          .nil rfl rfl environment [] rfl
        simpa [Primitive.results, Primitive.evaluateOn, bounded value (by simp),
          primitiveOutcome, PIR.Process.bind, Original.encodeHelperResult,
          Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
          Domain.Payload.ofValue, Ty.isHandle] using law
      rw [show instructions (value :: rest) =
        ⟨.execute (.indexConstant value), [], [.data .index], []⟩ :: instructions rest from rfl,
        Domain.Correspondence.evaluate_cons]
      rw [Domain.Correspondence.execute, constant]
      simp only [PIR.Process.bind]
      refine .checkpoint _ (List.prefix_refl _) (.checkpoint _ (List.prefix_append _ _) ?_)
      have tail := (ih (fun item member ↦ bounded item (by simp [member]))
        (environment ++ [.data (.index value)])).mapRelations
          (fun _ _ equal ↦ equal) (fun _ _ held ↦ (List.prefix_append _ _).trans held)
      simpa only [encode, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] using tail

end IndexLiterals

namespace Child

def referenceLayout (identity : String) : RecordProjection.Layout :=
  ⟨identity, "Record", .cons .index (.cons .index .nil)⟩

def referenceInstructions (identity : String) (reference : Nat) :
    List Construction.Instruction :=
  RecordProjection.instructions (referenceLayout identity) reference
    (RecordProjection.allFields (referenceLayout identity).fields)

structure Recognized (body : List Construction.Instruction) where
  frameBody : List Construction.Instruction
  frame : RecordAppend.Recognized frameBody
  position : Construction.Instruction
  referenceIdentity : String
  reference : Nat
  literals : List Nat
  exactBody : body = frameBody ++ [position] ++
    referenceInstructions referenceIdentity reference ++ IndexLiterals.instructions literals

/-- The complete tail is checked, including the order of equal-typed reference
fields and every literal. Math-body admission is the existing slice certificate. -/
def recognize (start : Nat) (body : List Construction.Instruction) : Option (Recognized body) := do
  let frameBody := body.take 3
  let frame ← RecordAppend.recognizeAt start frameBody
  let position :: first :: _ :: constants := body.drop 3 | none
  let .calculate (.getProduct identity "Record" _ _ _) := first.operation | none
  let [reference] := first.operands | none
  let literals ← constants.mapM fun instruction ↦
    match instruction.operation with
    | .execute (.indexConstant value) => some value
    | _ => none
  if exactBody : body = frameBody ++ [position] ++ referenceInstructions identity reference ++
      IndexLiterals.instructions literals then
    some ⟨frameBody, frame, position, identity, reference, literals, exactBody⟩
  else none

def positioned (model : DomainModel) (layout : RecordAppend.Layout)
    (data : layout.type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value layout.type)) (record : model.Value layout.type) (position : Nat) :
    Domain.Environment model.toCarriers :=
  RecordAppend.result model layout data environment records record ++ [.data (.index position)]

def result (model : DomainModel) (layout : RecordAppend.Layout)
    (data : layout.type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value layout.type)) (record : model.Value layout.type)
    (position constructor anchorInstance : Nat) (literals : List Nat) :
    Domain.Environment model.toCarriers :=
  positioned model layout data environment records record position ++
    [.data (.index constructor), .data (.index anchorInstance)] ++ IndexLiterals.encode literals

/-- Save, evaluate the actual position slice, project the installed child
reference and execute the emitted constants as one transition. Stops in the
position computation propagate before projection; a full store stops before it.
No assumption about a successful position result is required. -/
theorem Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context)
    (data : checked.frame.layout.type.isHandle = false)
    (fieldData : checked.frame.layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value checked.frame.layout.type))
    (record : model.Value checked.frame.layout.type)
    (start : checked.frame.placement.start = environment.length)
    (readStore : environment[checked.frame.placement.store]? =
      some (.data ⟨.sequence checked.frame.layout.type, data, records⟩))
    (readFields : Domain.read environment checked.frame.placement.fields =
      Domain.encodeValues (checked.frame.layout.fields.unpack record))
    (constructor anchorInstance : Nat)
    (readReference : environment[checked.reference]? = some (.data
      ⟨(referenceLayout checked.referenceIdentity).type, rfl, (constructor, anchorInstance, ())⟩))
    (bounded : ∀ value ∈ checked.literals, value < indexLimit)
    (source : Closed Nat)
    (positionLaw : Original.Simulation
      (fun position frame ↦ frame = positioned model checked.frame.layout data
        environment records record position)
      (fun _ frame ↦ ArtifactBinding.Captures
        (RecordAppend.result model checked.frame.layout data environment records record) frame)
      (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context checked.position
        (RecordAppend.result model checked.frame.layout data environment records record))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if records.length < indexLimit then
        (source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun position ↦
          .done (result model checked.frame.layout data environment records record
            position constructor anchorInstance checked.literals)
       else .halt .exhausted)
      (Domain.evaluate model program context body environment)) := by
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  by_cases room : records.length < indexLimit
  · simp only [room, ↓reduceIte]
    have save := checked.frame.simulation model program context data fieldData environment records
      record start readStore readFields room
    refine ⟨save.continueDone (fun _ held ↦ held) ?_⟩
    rw [Domain.Correspondence.evaluate_cons]
    refine .checkpoint _ (List.prefix_append _ _) ?_
    rw [PIR.Process.bind_assoc]
    apply positionLaw.bind
    · intro process frame retained
      exact (List.prefix_append _ _).trans (List.prefix_iff_eq_take.mpr retained.symm)
    · intro position frame equal
      subst frame
      simp only [PIR.Process.bind]
      refine .checkpoint _ ((List.prefix_append _ _).trans (List.prefix_append _ _)) ?_
      change Original.Simulation _ _ _
        ((Domain.evaluate model program context (referenceInstructions _ _)
          (positioned model checked.frame.layout data environment records record position)).bind _)
      let before := positioned model checked.frame.layout data environment records record position
      have retainedCaller : environment <+: before :=
        (List.prefix_append _ _).trans (List.prefix_append _ _)
      have reference : before[checked.reference]? = some (.data
          ⟨(referenceLayout checked.referenceIdentity).type, rfl, (constructor, anchorInstance, ())⟩) := by
        exact Original.read_append (Original.read_append readReference _) _
      have projection := Classical.choice (RecordProjection.simulation model
        (referenceLayout checked.referenceIdentity) rfl
        (RecordProjection.allFields (referenceLayout checked.referenceIdentity).fields)
        (RecordProjection.allFields_local _ rfl)
        before environment retainedCaller checked.reference (constructor, anchorInstance, ()) reference)
      rw [← RecordProjection.correspondence model program context] at projection
      have projected : RecordProjection.results model (referenceLayout checked.referenceIdentity)
          (constructor, anchorInstance, ())
          (RecordProjection.allFields (referenceLayout checked.referenceIdentity).fields) =
          [.data (.index constructor), .data (.index anchorInstance)] := rfl
      rw [projected] at projection
      apply projection.continueDone (fun _ held ↦ held)
      have constants := (IndexLiterals.simulation model program context checked.literals bounded
        (before ++ [.data (.index constructor), .data (.index anchorInstance)])).mapRelations
        (fun _ _ equal ↦ equal)
        (fun _ _ held ↦ (retainedCaller.trans (List.prefix_append _ _)).trans held)
      exact constants
  · simp only [room, ↓reduceIte]
    have full := RecordAppend.exhausted model checked.frame.layout checked.frame.placement data
      environment records readStore room
    rw [← checked.frame.correspondence model program context] at full
    exact ⟨full.continueHalt _ (fun _ held ↦ held)⟩

structure Output where
  continuation : Nat
  kind : Nat
  phase : Nat
  answer : Nat
  before : List Nat
  after : List Nat

def Output.references (output : Output) (start : Nat) : List Nat :=
  [start + 4, start + 5, start + 3, output.continuation, start, output.kind,
    output.phase, output.answer] ++ output.before ++ [start + 2] ++ output.after

def outputValues (model : DomainModel) (layout : RecordAppend.Layout)
    (data : layout.type.isHandle = false) (records : List (model.Value layout.type))
    (record : model.Value layout.type) (position constructor anchorInstance continuation kind answer : Nat)
    (before after : Domain.Environment model.toCarriers) : Domain.Environment model.toCarriers :=
  (show Header from ⟨⟨constructor, anchorInstance, position, continuation, records.length⟩,
    kind, 0, answer⟩).encode
      (before ++ [.data ⟨.sequence layout.type, data, records ++ [record]⟩] ++ after)

/-- The child yield routes the newly saved frame and computed position while
retaining the previous answer cell and every other store. Literal references
may name either a fresh constant or an earlier CSE result. Their readback remains
an installation fact, never a replacement for the checked body or output list. -/
theorem read_output (model : DomainModel) (layout : RecordAppend.Layout)
    (data : layout.type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value layout.type)) (record : model.Value layout.type)
    (position constructor anchorInstance : Nat) (literals : List Nat) (output : Output)
    (continuation kind answer : Nat) (before after : Domain.Environment model.toCarriers)
    (readAnswer : environment[output.answer]? = some (.data (.index answer)))
    (readBefore : Domain.read environment output.before = some before)
    (readAfter : Domain.read environment output.after = some after)
    (readContinuation : (result model layout data environment records record
      position constructor anchorInstance literals)[output.continuation]? =
        some (.data (.index continuation)))
    (readKind : (result model layout data environment records record
      position constructor anchorInstance literals)[output.kind]? = some (.data (.index kind)))
    (readPhase : (result model layout data environment records record
      position constructor anchorInstance literals)[output.phase]? = some (.data (.index 0))) :
    Domain.read (result model layout data environment records record
      position constructor anchorInstance literals) (output.references environment.length) =
        some (outputValues model layout data records record position constructor anchorInstance
          continuation kind answer before after) := by
  let final := result model layout data environment records record
    position constructor anchorInstance literals
  have answerRead : final[output.answer]? = some (.data (.index answer)) :=
    Original.read_append (Original.read_append (Original.read_append (Original.read_append readAnswer _) _) _) _
  have beforeRead : Domain.read final output.before = some before :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _ readBefore)))
  have afterRead : Domain.read final output.after = some after :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _ readAfter)))
  have header : Domain.read final
      [environment.length + 4, environment.length + 5, environment.length + 3,
        output.continuation, environment.length, output.kind, output.phase, output.answer] =
      some [.data (.index constructor), .data (.index anchorInstance), .data (.index position),
        .data (.index continuation), .data (.index records.length), .data (.index kind),
        .data (.index 0), .data (.index answer)] := by
    have atStart : final[environment.length]? = some (.data (.index records.length)) := by
      simp [final, result, positioned, RecordAppend.result, List.append_assoc]
    have atPosition : final[environment.length + 3]? = some (.data (.index position)) := by
      simp [final, result, positioned, RecordAppend.result, List.append_assoc]
    have atConstructor : final[environment.length + 4]? = some (.data (.index constructor)) := by
      simp [final, result, positioned, RecordAppend.result, List.append_assoc]
    have atInstance : final[environment.length + 5]? = some (.data (.index anchorInstance)) := by
      simp [final, result, positioned, RecordAppend.result, List.append_assoc]
    simp [Domain.read, atStart, atPosition, atConstructor, atInstance,
      readContinuation, readKind, readPhase, answerRead, final]
  have store : Domain.read final [environment.length + 2] =
      some [.data ⟨.sequence layout.type, data, records ++ [record]⟩] := by
    simp [Domain.read, final, result, positioned, RecordAppend.result, List.append_assoc]
  change Domain.read final _ = _
  simp only [Output.references, Domain.read, List.mapM_append] at header beforeRead afterRead store ⊢
  rw [header, beforeRead, store, afterRead]
  rfl

end Child
end Zkc.Realization.QueryController
