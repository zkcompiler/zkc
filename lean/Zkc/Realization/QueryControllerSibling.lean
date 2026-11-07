module

public import Zkc.Realization.QueryControllerReturn

@[expose] public section

/-! A sibling transition restores the actual parent frame, adds the current
reply to its ordered answer indices, and enters the next child. Its certificate
checks the entire arm and yield. No source companion chooses the saved fields.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryController.Sibling
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  returnBody : List Construction.Instruction
  childBody : List Construction.Instruction
  restore : ReturnPrefix.Recognized returnBody
  child : Child.Recognized childBody
  output : Child.Output
  childStart : child.frame.placement.start =
    restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length
  storeSplit : restore.state.drop 8 = output.before ++ child.frame.placement.store :: output.after
  answerField : restore.state[7]? = some output.answer
  frameShape : child.frame.layout.fields = QueryContinuation.fields (restore.frame.count + 1)
  savedFields : child.frame.placement.fields =
    List.range' (restore.frame.start + 1) (4 + restore.frame.count) ++ [output.answer]
  exactBody : body = returnBody ++ childBody
  exactOutput : returned = output.references child.frame.placement.start

def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) :=
  (List.range (body.length + 1)).findSome? fun split ↦ do
    let returnBody := body.take split
    let childBody := body.drop split
    let restore ← ReturnPrefix.recognize start state returnBody
    let child ← Child.recognize
      (restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length)
      childBody
    let some continuation := returned[3]? | none
    let some kind := returned[5]? | none
    let some phase := returned[6]? | none
    let some answer := restore.state[7]? | none
    let stores := restore.state.drop 8
    let slot := stores.idxOf child.frame.placement.store
    let output : Child.Output :=
      ⟨continuation, kind, phase, answer, stores.take slot, stores.drop (slot + 1)⟩
    if childStart : child.frame.placement.start =
        restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length then
      if storeSplit : restore.state.drop 8 = output.before ++ child.frame.placement.store :: output.after then
        if answerField : restore.state[7]? = some output.answer then
          if frameShape : child.frame.layout.fields = QueryContinuation.fields (restore.frame.count + 1) then
            if savedFields : child.frame.placement.fields =
                List.range' (restore.frame.start + 1) (4 + restore.frame.count) ++ [output.answer] then
              if exactOutput : returned = output.references child.frame.placement.start then
                some ⟨returnBody, childBody, restore, child, output, childStart, storeSplit,
                  answerField, frameShape, savedFields, (List.take_append_drop split body).symm,
                  exactOutput⟩
              else none
            else none
          else none
        else none
      else none
    else none

def saved (frame : QueryContinuation.Frame) (answer : Nat) : QueryContinuation.Frame :=
  { frame with answers := frame.answers ++ [answer] }

/-- The newly saved record is related to the loaded parent and actual returned
answer. Its nominal layout comes from the checked child allocation. -/
def Encodes {model : DomainModel} (layout : RecordAppend.Layout) (count : Nat)
    (shape : layout.fields = QueryContinuation.fields (count + 1))
    (frame : QueryContinuation.Frame) (answer : Nat) (record : model.Value layout.type) : Prop := by
  rcases layout with ⟨identity, fields⟩
  dsimp only at shape
  subst fields
  exact QueryContinuation.Encodes identity (count + 1) (saved frame answer) record

theorem encoding_exists (model : DomainModel) (layout : RecordAppend.Layout) (count : Nat)
    (shape : layout.fields = QueryContinuation.fields (count + 1))
    (frame : QueryContinuation.Frame) (answer : Nat) (width : frame.answers.length = count) :
    ∃ record : model.Value layout.type, Encodes layout count shape frame answer record := by
  rcases layout with ⟨identity, fields⟩
  dsimp only at shape
  subst fields
  exact QueryContinuation.encoding_exists identity (count + 1) (saved frame answer)
    (by simp [saved, width])

theorem Encodes.values_encoded {model : DomainModel} {layout : RecordAppend.Layout} {count : Nat}
    {shape : layout.fields = QueryContinuation.fields (count + 1)}
    {frame : QueryContinuation.Frame} {answer : Nat} {record : model.Value layout.type}
    (encoding : Encodes layout count shape frame answer record) :
    Domain.encodeValues (layout.fields.unpack record) =
      some ((saved frame answer).values.map (fun value ↦ Domain.Value.data (.index value))) := by
  rcases layout with ⟨identity, fields⟩
  dsimp only at shape
  subst fields
  exact QueryContinuation.Encodes.values_encoded encoding

/-- Reading the emitted saved-field operands derives their full association,
including the last answer's position. This is common installation work. -/
theorem read_saved {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (oldRecord : model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type)
    (frame : QueryContinuation.Frame)
    (oldEncoding : QueryContinuation.Encodes checked.restore.frame.identity
      checked.restore.frame.count frame oldRecord)
    (parent : model.Value checked.restore.lookup.projection.layout.type)
    (answer : Nat) (readAnswer : environment[checked.output.answer]? = some (.data (.index answer)))
    (record : model.Value checked.child.frame.layout.type)
    (encoding : Encodes checked.child.frame.layout checked.restore.frame.count checked.frameShape
      frame answer record) :
    Domain.read (ReturnPrefix.projected checked.restore model data environment oldRecord frame parent)
      checked.child.frame.placement.fields =
        Domain.encodeValues (checked.child.frame.layout.fields.unpack record) := by
  let prefixValues : Domain.Environment model.toCarriers :=
    environment ++ [.data (.index checked.restore.continuation), .data (.boolean true)] ++
      [.data (.index checked.restore.kind), .data (.boolean true)] ++
      [.data ⟨(QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type,
        QueryContinuation.frameData _ _, oldRecord⟩]
  have prefixLength : prefixValues.length = checked.restore.frame.start + 1 := by
    simp [prefixValues, checked.restore.frameStart, start]
  have width : frame.values.length = 4 + checked.restore.frame.count := by
    simp [QueryContinuation.Frame.values, oldEncoding.answers_length,
      Nat.add_comm, Nat.add_left_comm]
  have read := RecordAllocator.read_appended prefixValues
    (frame.values.map (fun value ↦ Domain.Value.data (.index value)))
  rw [List.length_map, width, prefixLength] at read
  have readRestored : Domain.read
      (ReturnPrefix.projected checked.restore model data environment oldRecord frame parent)
      (List.range' (checked.restore.frame.start + 1) (4 + checked.restore.frame.count)) =
        some (frame.values.map (fun value ↦ Domain.Value.data (.index value))) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ read))
  have current :
      (ReturnPrefix.projected checked.restore model data environment oldRecord frame parent)[checked.output.answer]? =
        some (.data (.index answer)) :=
    Original.read_append (Original.read_append (Original.read_append
      (Original.read_append (Original.read_append (Original.read_append
        (Original.read_append readAnswer _) _) _) _) _) _) _
  rw [checked.savedFields, encoding.values_encoded]
  simp only [Domain.read, List.mapM_append] at readRestored ⊢
  rw [readRestored]
  simp [List.mapM_cons, current, saved, QueryContinuation.Frame.values, List.map_append]

/-- Complete sibling execution, including restoration, saved-answer association,
capacity, the original position computation and the full controller output.
The premises after restoration concern only installed stores, references and
the original Math slice; saved-field and output plumbing are derived here. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program) (context : Context)
    (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (read : Domain.read environment checked.restore.state = some (header.encode stores))
    (continuation : header.continuation = checked.restore.continuation)
    (kind : header.kind = checked.restore.kind)
    (continuationBound : checked.restore.continuation < indexLimit)
    (kindBound : checked.restore.kind < indexLimit)
    (oldFrames : List (model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type))
    (frame : QueryContinuation.Frame)
    (stored : QueryContinuation.Stored checked.restore.frame.identity checked.restore.frame.count
      oldFrames header.continuationInstance frame)
    (readOldFrames : environment[checked.restore.frame.store]? = some (.data
      ⟨.sequence (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type,
        QueryContinuation.frameData _ _, oldFrames⟩))
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.restore.lookup.projection.selections,
      Domain.localType selection.type = true)
    (parents : List (model.Value checked.restore.lookup.projection.layout.type))
    (parent : model.Value checked.restore.lookup.projection.layout.type)
    (readParents : environment[checked.restore.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.restore.lookup.projection.layout.type, data, parents⟩))
    (found : parents[frame.parentInstance]? = some parent)
    (tagBound : checked.restore.lookup.lookup.layout.constructor < indexLimit)
    (frameData : checked.child.frame.layout.type.isHandle = false)
    (frames : List (model.Value checked.child.frame.layout.type))
    (constructor anchorInstance : Nat)
    (installed : ∀ oldRecord, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame oldRecord →
      let ready := ReturnPrefix.projected checked.restore model data environment oldRecord frame parent
      ready[checked.child.frame.placement.store]? =
        some (.data ⟨.sequence checked.child.frame.layout.type, frameData, frames⟩) ∧
      ready[checked.child.reference]? = some (.data
        ⟨(Child.referenceLayout checked.child.referenceIdentity).type, rfl, (constructor, anchorInstance, ())⟩))
    (literalBounds : ∀ value ∈ checked.child.literals, value < indexLimit)
    (source : Closed Nat)
    (positionLaw : ∀ oldRecord, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame oldRecord →
      ∀ record, Encodes checked.child.frame.layout checked.restore.frame.count checked.frameShape
          frame header.answer record →
      let ready := ReturnPrefix.projected checked.restore model data environment oldRecord frame parent
      Nonempty (Original.Simulation
        (fun position final ↦ final = Child.positioned model checked.child.frame.layout frameData
          ready frames record position)
        (fun _ live ↦ ArtifactBinding.Captures
          (RecordAppend.result model checked.child.frame.layout frameData ready frames record) live)
        (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
        (Domain.step model program context checked.child.position
          (RecordAppend.result model checked.child.frame.layout frameData ready frames record))))
    (nextContinuation childKind : Nat)
    (readLiterals : ∀ oldRecord, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame oldRecord →
      ∀ record, Encodes checked.child.frame.layout checked.restore.frame.count checked.frameShape
          frame header.answer record → ∀ position,
      let ready := ReturnPrefix.projected checked.restore model data environment oldRecord frame parent
      let final := Child.result model checked.child.frame.layout frameData ready frames record
        position constructor anchorInstance checked.child.literals
      final[checked.output.continuation]? = some (.data (.index nextContinuation)) ∧
      final[checked.output.kind]? = some (.data (.index childKind)) ∧
      final[checked.output.phase]? = some (.data (.index 0))) :
    ∃ record, Encodes checked.child.frame.layout checked.restore.frame.count checked.frameShape
        frame header.answer record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (if frames.length < indexLimit then
          (source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun position ↦
            .done (Child.outputValues model checked.child.frame.layout frameData frames record
              position constructor anchorInstance nextContinuation childKind header.answer
                (stores.take checked.output.before.length) (stores.drop (checked.output.before.length + 1)))
         else .halt .exhausted)
        ((Domain.evaluate model program context body environment).bind fun final ↦
          (Domain.read final returned).elim (.halt .refused) .done)) := by
  obtain ⟨oldRecord, oldEncoding, restore⟩ := checked.restore.simulation model program context
    header stores environment start read continuation kind continuationBound kindBound
    oldFrames frame stored readOldFrames data localFields parents parent readParents found tagBound
  obtain ⟨restore⟩ := restore
  obtain ⟨record, encoding⟩ := encoding_exists model checked.child.frame.layout
    checked.restore.frame.count checked.frameShape frame header.answer oldEncoding.answers_length
  let ready := ReturnPrefix.projected checked.restore model data environment oldRecord frame parent
  have readyLength : ready.length = checked.child.frame.placement.start := by
    rw [checked.childStart]
    simp [ready, ReturnPrefix.projected, ReturnPrefix.restored,
      QueryContinuation.Frame.values, oldEncoding.answers_length,
      RecordProjection.results_length model _ parent _ localFields,
      checked.restore.frameStart, start]
    omega
  have retained : environment <+: ready :=
    ((((((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have stateRead : Domain.read ready checked.restore.state = some (header.encode stores) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
        (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
          (RecordAllocator.read_extended _ _ _ _ read))))))
  have initialAnswer : environment[checked.output.answer]? = some (.data (.index header.answer)) := by
    have field := Domain.View.read_getElem? read 7
    rw [checked.answerField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using field.symm
  have readSaved := read_saved checked model data environment start oldRecord frame oldEncoding
    parent header.answer initialAnswer record encoding
  have frameFields : checked.child.frame.layout.fields.toList.all Domain.localType = true := by
    rw [checked.frameShape]
    exact QueryContinuation.fields_local _
  have answerRead : ready[checked.output.answer]? = some (.data (.index header.answer)) := by
    have field := Domain.View.read_getElem? stateRead 7
    rw [checked.answerField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using field.symm
  have storesRead : Domain.read ready (checked.restore.state.drop 8) = some stores := by
    have selected := (Phase.read_parts ready checked.restore.state (header.encode stores) stateRead 8).2
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using selected
  have beforeRead : Domain.read ready checked.output.before = some (stores.take checked.output.before.length) := by
    have first := (Phase.read_parts ready _ stores storesRead checked.output.before.length).1
    rw [checked.storeSplit] at first
    simpa using first
  have afterRead : Domain.read ready checked.output.after = some (stores.drop (checked.output.before.length + 1)) := by
    have last := (Phase.read_parts ready _ stores storesRead (checked.output.before.length + 1)).2
    rw [checked.storeSplit] at last
    simpa using last
  obtain ⟨position⟩ := positionLaw oldRecord oldEncoding record encoding
  obtain ⟨child⟩ := checked.child.simulation model program context frameData frameFields ready frames
    record readyLength.symm (installed oldRecord oldEncoding).1 readSaved constructor anchorInstance
    (installed oldRecord oldEncoding).2 literalBounds source position
  have childWeakened := child.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ retained.trans held)
  refine ⟨record, encoding, ⟨?_⟩⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  apply restore.continueDone (fun _ held ↦ held)
  by_cases room : frames.length < indexLimit
  · simp only [room, ↓reduceIte] at childWeakened ⊢
    apply childWeakened.continueClosed source
      (fun position ↦ Child.result model checked.child.frame.layout frameData ready frames record
        position constructor anchorInstance checked.child.literals) (fun _ _ _ held ↦ held)
    intro position
    have literals := readLiterals oldRecord oldEncoding record encoding position
    have projected := Child.read_output model checked.child.frame.layout frameData ready frames record
      position constructor anchorInstance checked.child.literals checked.output nextContinuation childKind
      header.answer (stores.take checked.output.before.length) (stores.drop (checked.output.before.length + 1))
      answerRead beforeRead afterRead literals.1 literals.2.1 literals.2.2
    rw [readyLength, ← checked.exactOutput] at projected
    rw [projected]
    exact .done rfl
  · simp only [room, ↓reduceIte] at childWeakened ⊢
    exact childWeakened.continueHalt _ (fun _ held ↦ held)

end Zkc.Realization.QueryController.Sibling
