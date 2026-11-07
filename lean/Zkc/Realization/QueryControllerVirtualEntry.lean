module

public import Zkc.Realization.QueryControllerEnter
public import Zkc.Realization.QueryControllerChild

@[expose] public section

/-! Whole virtual-entry arms use the same admission prefix as base entry and
the same saved-child transition as sibling return. The certificate fixes both
pieces, the saved store's position and the complete returned controller state.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryController.VirtualEntry
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  entryBody : List Construction.Instruction
  childBody : List Construction.Instruction
  entry : EntryPrefix.Recognized entryBody
  child : Child.Recognized childBody
  output : Child.Output
  childStart : child.frame.placement.start = entry.start + 6 + entry.lookup.projection.selections.length
  storeSplit : entry.state.drop 8 = output.before ++ child.frame.placement.store :: output.after
  answerField : entry.state[7]? = some output.answer
  frameShape : child.frame.layout.fields = QueryContinuation.fields 0
  parentFields : [3, 4, 1, 2].mapM (entry.state[·]?) = some child.frame.placement.fields
  exactBody : body = entryBody ++ childBody
  exactOutput : returned = output.references child.frame.placement.start

/-- Recognition inspects the whole arm. It cannot exchange adjacent frame
stores or the old answer slot merely because they have equal types. -/
def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) :=
  (List.range (body.length + 1)).findSome? fun split ↦ do
    let entryBody := body.take split
    let childBody := body.drop split
    let entry ← EntryPrefix.recognize start state entryBody
    let child ← Child.recognize (entry.start + 6 + entry.lookup.projection.selections.length) childBody
    let some continuation := returned[3]? | none
    let some kind := returned[5]? | none
    let some phase := returned[6]? | none
    let some answer := entry.state[7]? | none
    let stores := entry.state.drop 8
    let slot := stores.idxOf child.frame.placement.store
    let output : Child.Output := ⟨continuation, kind, phase, answer, stores.take slot, stores.drop (slot + 1)⟩
    if childStart : child.frame.placement.start = entry.start + 6 + entry.lookup.projection.selections.length then
      if storeSplit : entry.state.drop 8 = output.before ++ child.frame.placement.store :: output.after then
        if answerField : entry.state[7]? = some output.answer then
          if frameShape : child.frame.layout.fields = QueryContinuation.fields 0 then
            if parentFields : [3, 4, 1, 2].mapM (entry.state[·]?) = some child.frame.placement.fields then
              if exactOutput : returned = output.references child.frame.placement.start then
                some ⟨entryBody, childBody, entry, child, output, childStart, storeSplit, answerField,
                  frameShape, parentFields, (List.take_append_drop split body).symm, exactOutput⟩
              else none
            else none
          else none
        else none
      else none
    else none

def admitted {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (data : checked.entry.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (record : model.Value checked.entry.lookup.projection.layout.type) : Domain.Environment model.toCarriers :=
  EntryPrefix.projected checked.entry model data environment record ++ [.data (.boolean true)]

def parentRecord (model : DomainModel) (layout : RecordAppend.Layout)
    (shape : layout.fields = QueryContinuation.fields 0) (header : Header) : model.Value layout.type := by
  rcases layout with ⟨identity, fields⟩
  dsimp only at shape
  subst fields
  exact (header.continuation, header.continuationInstance, header.anchorInstance, header.position, ())

private theorem read_selected {carriers : Carriers} {environment values : Domain.Environment carriers}
    {state : List Nat} (read : Domain.read environment state = some values)
    (indices references : List Nat) (selected : indices.mapM (state[·]?) = some references) :
    Domain.read environment references = indices.mapM (values[·]?) := by
  induction indices generalizing references with
  | nil => simp at selected; subst references; rfl
  | cons index rest ih =>
      cases slot : state[index]? with
      | none => simp [List.mapM_cons, slot] at selected
      | some reference =>
          cases others : rest.mapM (state[·]?) with
          | none => simp [List.mapM_cons, slot, others] at selected
          | some suffix =>
              simp [List.mapM_cons, slot, others] at selected
              subst references
              have field := Domain.View.read_getElem? read index
              simp only [slot, Option.bind_some] at field
              simp only [Domain.read, List.mapM_cons] at ih ⊢
              rw [ih suffix others, field]

/-- Saving the first child uses the current parent coordinates in their emitted
order. A caller cannot choose another same-typed parent record. -/
theorem read_parent (model : DomainModel) (layout : RecordAppend.Layout)
    (shape : layout.fields = QueryContinuation.fields 0) (header : Header)
    (stores environment : Domain.Environment model.toCarriers) (state references : List Nat)
    (read : Domain.read environment state = some (header.encode stores))
    (selected : [3, 4, 1, 2].mapM (state[·]?) = some references) :
    Domain.read environment references = Domain.encodeValues
      (layout.fields.unpack (parentRecord model layout shape header)) := by
  have fieldsRead := read_selected read [3, 4, 1, 2] references selected
  rcases layout with ⟨identity, fields⟩
  dsimp only at shape
  subst fields
  change Domain.read environment references = some
    [.data (.index header.continuation), .data (.index header.continuationInstance),
      .data (.index header.anchorInstance), .data (.index header.position)]
  simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using fieldsRead

/-- Compose the actual entry and child bodies, including output selection.
All readback premises concern the installed nominal records and current stores.
The original Math slice supplies only its own complete computation certificate;
domain rejection, capacity, saved state and routing are constructed here. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program) (context : Context)
    (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.entry.start = environment.length)
    (read : Domain.read environment checked.entry.state = some (header.encode stores))
    (kind : header.kind = checked.entry.kind) (kindBound : checked.entry.kind < indexLimit)
    (data : checked.entry.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.entry.lookup.projection.selections,
      Domain.localType selection.type = true)
    (recordIndex : Nat) (records : List (model.Value checked.entry.lookup.projection.layout.type))
    (record : model.Value checked.entry.lookup.projection.layout.type)
    (readTag : environment[checked.entry.lookup.lookup.placement.constructor]? =
      some (.data (.index checked.entry.lookup.lookup.layout.constructor)))
    (readInstance : environment[checked.entry.lookup.lookup.placement.slot]? = some (.data (.index recordIndex)))
    (readStore : environment[checked.entry.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.entry.lookup.projection.layout.type, data, records⟩))
    (found : records[recordIndex]? = some record)
    (tagBound : checked.entry.lookup.lookup.layout.constructor < indexLimit) (rows : Nat)
    (readRows : (EntryPrefix.projected checked.entry model data environment record)[checked.entry.rows]? =
      some (.data (.index rows)))
    (frameData : checked.child.frame.layout.type.isHandle = false)
    (frames : List (model.Value checked.child.frame.layout.type))
    (readFrames : (admitted checked model data environment record)[checked.child.frame.placement.store]? =
      some (.data ⟨.sequence checked.child.frame.layout.type, frameData, frames⟩))
    (constructor anchorInstance : Nat)
    (readReference : (admitted checked model data environment record)[checked.child.reference]? = some (.data
      ⟨(Child.referenceLayout checked.child.referenceIdentity).type, rfl, (constructor, anchorInstance, ())⟩))
    (literalBounds : ∀ value ∈ checked.child.literals, value < indexLimit)
    (source : Closed Nat)
    (positionLaw : Original.Simulation
      (fun position frame ↦ frame = Child.positioned model checked.child.frame.layout frameData
        (admitted checked model data environment record) frames (parentRecord model checked.child.frame.layout checked.frameShape header) position)
      (fun _ frame ↦ ArtifactBinding.Captures
        (RecordAppend.result model checked.child.frame.layout frameData
          (admitted checked model data environment record) frames (parentRecord model checked.child.frame.layout checked.frameShape header)) frame)
      (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context checked.child.position
        (RecordAppend.result model checked.child.frame.layout frameData
          (admitted checked model data environment record) frames (parentRecord model checked.child.frame.layout checked.frameShape header))))
    (continuation childKind : Nat)
    (readLiterals : ∀ position,
      let final := Child.result model checked.child.frame.layout frameData
        (admitted checked model data environment record) frames (parentRecord model checked.child.frame.layout checked.frameShape header) position constructor anchorInstance checked.child.literals
      final[checked.output.continuation]? = some (.data (.index continuation)) ∧
      final[checked.output.kind]? = some (.data (.index childKind)) ∧
      final[checked.output.phase]? = some (.data (.index 0))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if DomainGuard.Accepted header.position rows then
        if frames.length < indexLimit then
          (source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun position ↦
            .done (Child.outputValues model checked.child.frame.layout frameData frames (parentRecord model checked.child.frame.layout checked.frameShape header)
              position constructor anchorInstance continuation childKind header.answer
                (stores.take checked.output.before.length) (stores.drop (checked.output.before.length + 1)))
        else .halt .exhausted
       else .halt .refused)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  let ready := admitted checked model data environment record
  let saved := parentRecord model checked.child.frame.layout checked.frameShape header
  have readyLength : ready.length = checked.child.frame.placement.start := by
    rw [checked.childStart]
    simp [ready, admitted, EntryPrefix.projected,
      RecordProjection.results_length model _ record _ localFields, start]
    omega
  have retained : environment <+: ready :=
    (((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have stateRead : Domain.read ready checked.entry.state = some (header.encode stores) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _ read)))
  have frameFields : checked.child.frame.layout.fields.toList.all Domain.localType = true := by
    rw [checked.frameShape]
    rfl
  have readSaved := read_parent model checked.child.frame.layout checked.frameShape header
    stores ready checked.entry.state checked.child.frame.placement.fields stateRead checked.parentFields
  have answerRead : ready[checked.output.answer]? = some (.data (.index header.answer)) := by
    have field := Domain.View.read_getElem? stateRead 7
    rw [checked.answerField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using field.symm
  have storesRead : Domain.read ready (checked.entry.state.drop 8) = some stores := by
    have selected := (Phase.read_parts ready checked.entry.state (header.encode stores) stateRead 8).2
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using selected
  have beforeRead : Domain.read ready checked.output.before = some (stores.take checked.output.before.length) := by
    have first := (Phase.read_parts ready _ stores storesRead checked.output.before.length).1
    rw [checked.storeSplit] at first
    simpa using first
  have afterRead : Domain.read ready checked.output.after = some (stores.drop (checked.output.before.length + 1)) := by
    have last := (Phase.read_parts ready _ stores storesRead (checked.output.before.length + 1)).2
    rw [checked.storeSplit] at last
    simpa using last
  obtain ⟨entry⟩ := checked.entry.simulation model program context header stores environment start
    read kind kindBound data localFields recordIndex records record readTag readInstance readStore
    found tagBound rows readRows
  obtain ⟨child⟩ := checked.child.simulation model program context frameData frameFields ready frames
    saved readyLength.symm readFrames readSaved constructor anchorInstance readReference literalBounds source positionLaw
  have childWeakened := child.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ retained.trans held)
  refine ⟨?_⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  by_cases allowed : DomainGuard.Accepted header.position rows
  · simp only [allowed, ↓reduceIte] at entry ⊢
    apply entry.continueDone (fun _ held ↦ held)
    by_cases room : frames.length < indexLimit
    · simp only [room, ↓reduceIte] at childWeakened ⊢
      apply childWeakened.continueClosed source
        (fun position ↦ Child.result model checked.child.frame.layout frameData ready frames saved
          position constructor anchorInstance checked.child.literals) (fun _ _ _ held ↦ held)
      intro position
      have projected := Child.read_output model checked.child.frame.layout frameData ready frames saved
        position constructor anchorInstance checked.child.literals checked.output continuation childKind header.answer
        (stores.take checked.output.before.length) (stores.drop (checked.output.before.length + 1))
        answerRead beforeRead afterRead (readLiterals position).1
        (readLiterals position).2.1 (readLiterals position).2.2
      rw [readyLength, ← checked.exactOutput] at projected
      rw [projected]
      exact .done rfl
    · simp only [room, ↓reduceIte] at childWeakened ⊢
      exact childWeakened.continueHalt _ (fun _ held ↦ held)
  · simp only [allowed, ↓reduceIte] at entry ⊢
    exact entry.continueHalt _ (fun _ held ↦ held)

end Zkc.Realization.QueryController.VirtualEntry
