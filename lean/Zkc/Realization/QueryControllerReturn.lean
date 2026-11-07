module

public import Zkc.Realization.QueryControllerEnter
public import Zkc.Realization.QueryControllerChild
public import Zkc.Realization.QueryContinuationProjection

@[expose] public section

/-! The common return prefix selects the static continuation and answer kind,
loads its actual saved frame, and recovers the parent record. Sibling and final
answer arms share this prefix. Parent coordinates and prior-answer width are
derived from the stored frame; they are not chosen independently by a client. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryController.ReturnPrefix
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) where
  start : Nat
  state : List Nat
  continuation : Nat
  continuationReference : Nat
  continuationSite : String
  kind : Nat
  kindReference : Nat
  kindSite : String
  frameBody : List Construction.Instruction
  frame : QueryContinuation.Loaded frameBody
  lookupBody : List Construction.Instruction
  lookup : RecordLookupProjection.Recognized lookupBody
  continuationField : state[3]? = some continuationReference
  kindField : state[5]? = some kindReference
  frameField : state[4]? = some frame.slot
  frameStart : frame.start = start + 4
  lookupStart : lookup.lookup.placement.start = frame.start + 6 + frame.count
  parentTag : lookup.lookup.placement.constructor = frame.start + 5 + frame.count
  parentInstance : lookup.lookup.placement.slot = frame.start + 3
  exactBody : body =
    RequiredIndices.constantInstructions start continuationReference continuation continuationSite ++
    RequiredIndices.constantInstructions (start + 2) kindReference kind kindSite ++ frameBody ++
    IndexLiterals.instructions [lookup.lookup.layout.constructor] ++ lookupBody

def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction) :
    Option (Recognized body) := do
  let [contConstant, contCompare, contGuard, kindConstant, kindCompare, kindGuard] := body.take 6 | none
  let .execute (.indexConstant continuation) := contConstant.operation | none
  let [continuationReference, _] := contCompare.operands | none
  let .require continuationSite := contGuard.operation | none
  let .execute (.indexConstant kind) := kindConstant.operation | none
  let [kindReference, _] := kindCompare.operands | none
  let .require kindSite := kindGuard.operation | none
  let load :: _ := body.drop 6 | none
  let .execute (.sequenceAt (.product _ "Record" fields)) := load.operation | none
  let frameBody := (body.drop 6).take (1 + fields.toList.length)
  let frame ← QueryContinuation.recognizeLoad (start + 4) frameBody
  let lookupBody := body.drop (7 + frameBody.length)
  let lookup ← RecordLookupProjection.recognize lookupBody
  if continuationField : state[3]? = some continuationReference then
    if kindField : state[5]? = some kindReference then
      if frameField : state[4]? = some frame.slot then
        if frameStart : frame.start = start + 4 then
          if lookupStart : lookup.lookup.placement.start = frame.start + 6 + frame.count then
            if parentTag : lookup.lookup.placement.constructor = frame.start + 5 + frame.count then
              if parentInstance : lookup.lookup.placement.slot = frame.start + 3 then
                if exactBody : body =
                    RequiredIndices.constantInstructions start continuationReference continuation continuationSite ++
                    RequiredIndices.constantInstructions (start + 2) kindReference kind kindSite ++ frameBody ++
                    IndexLiterals.instructions [lookup.lookup.layout.constructor] ++ lookupBody then
                  some ⟨start, state, continuation, continuationReference, continuationSite, kind,
                    kindReference, kindSite, frameBody, frame, lookupBody, lookup, continuationField,
                    kindField, frameField, frameStart, lookupStart, parentTag, parentInstance, exactBody⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

def restored {body : List Construction.Instruction} (checked : Recognized body) (model : DomainModel)
    (environment : Domain.Environment model.toCarriers)
    (record : model.Value (QueryContinuation.layout checked.frame.identity checked.frame.count).type)
    (frame : QueryContinuation.Frame) : Domain.Environment model.toCarriers :=
  environment ++ [.data (.index checked.continuation), .data (.boolean true)] ++
    [.data (.index checked.kind), .data (.boolean true)] ++
    [.data ⟨(QueryContinuation.layout checked.frame.identity checked.frame.count).type,
      QueryContinuation.frameData checked.frame.identity checked.frame.count, record⟩] ++
    frame.values.map (fun value ↦ .data (.index value))

def projected {body : List Construction.Instruction} (checked : Recognized body) (model : DomainModel)
    (data : checked.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (record : model.Value (QueryContinuation.layout checked.frame.identity checked.frame.count).type)
    (frame : QueryContinuation.Frame) (parent : model.Value checked.lookup.projection.layout.type) :
    Domain.Environment model.toCarriers :=
  restored checked model environment record frame ++ [.data (.index checked.lookup.lookup.layout.constructor)] ++
    [.data (.index checked.lookup.lookup.layout.constructor), .data (.boolean true),
      .data ⟨checked.lookup.projection.layout.type, data, parent⟩] ++
    RecordProjection.results model checked.lookup.projection.layout parent checked.lookup.projection.selections

/-- Under the selected continuation's installed frame association, derive the
entire return prefix. Parent lookup uses the saved parent instance, not the
child's instance or a separately supplied coordinate. -/
theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context) (header : Header)
    (stores environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (read : Domain.read environment checked.state = some (header.encode stores))
    (continuation : header.continuation = checked.continuation)
    (kind : header.kind = checked.kind)
    (continuationBound : checked.continuation < indexLimit) (kindBound : checked.kind < indexLimit)
    (frames : List (model.Value (QueryContinuation.layout checked.frame.identity checked.frame.count).type))
    (saved : QueryContinuation.Frame)
    (stored : QueryContinuation.Stored checked.frame.identity checked.frame.count frames
      header.continuationInstance saved)
    (readFrames : environment[checked.frame.store]? = some (.data
      ⟨.sequence (QueryContinuation.layout checked.frame.identity checked.frame.count).type,
        QueryContinuation.frameData checked.frame.identity checked.frame.count, frames⟩))
    (data : checked.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.lookup.projection.selections, Domain.localType selection.type = true)
    (parents : List (model.Value checked.lookup.projection.layout.type))
    (parent : model.Value checked.lookup.projection.layout.type)
    (readParents : environment[checked.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.lookup.projection.layout.type, data, parents⟩))
    (found : parents[saved.parentInstance]? = some parent)
    (tagBound : checked.lookup.lookup.layout.constructor < indexLimit) :
    ∃ record, QueryContinuation.Encodes checked.frame.identity checked.frame.count saved record ∧
      Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
        (.done (projected checked model data environment record saved parent))
        (Domain.evaluate model program context body environment)) := by
  have readContinuation : environment[checked.continuationReference]? = some (.data (.index checked.continuation)) := by
    have field := Domain.View.read_getElem? read 3
    rw [checked.continuationField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values, continuation] using field.symm
  have readKind : environment[checked.kindReference]? = some (.data (.index checked.kind)) := by
    have field := Domain.View.read_getElem? read 5
    rw [checked.kindField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values, kind] using field.symm
  have readSlot : environment[checked.frame.slot]? = some (.data (.index header.continuationInstance)) := by
    have field := Domain.View.read_getElem? read 4
    rw [checked.frameField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using field.symm
  let contValues : Domain.Environment model.toCarriers := [.data (.index checked.continuation), .data (.boolean true)]
  let kindValues : Domain.Environment model.toCarriers := [.data (.index checked.kind), .data (.boolean true)]
  let guarded := environment ++ contValues ++ kindValues
  have guardLength : guarded.length = checked.frame.start := by
    rw [checked.frameStart, start]
    simp [guarded, contValues, kindValues]
  have frameRead : Domain.read guarded [checked.frame.store, checked.frame.slot] = Domain.encodeValues
      (tys := [.sequence (QueryContinuation.layout checked.frame.identity checked.frame.count).type, .index])
      (.cons frames (.cons header.continuationInstance .nil)) := by
    have readStore : guarded[checked.frame.store]? = some (.data
        ⟨.sequence (QueryContinuation.layout checked.frame.identity checked.frame.count).type,
          QueryContinuation.frameData checked.frame.identity checked.frame.count, frames⟩) :=
      Original.read_append (Original.read_append readFrames contValues) kindValues
    have slot : guarded[checked.frame.slot]? = some (.data (.index header.continuationInstance)) :=
      Original.read_append (Original.read_append readSlot contValues) kindValues
    simp only [Domain.read, List.mapM_cons, List.mapM_nil, readStore, slot]
    simp [Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, QueryContinuation.frameData]
  obtain ⟨record, encoding, loaded⟩ := checked.frame.simulation model program context frames
    header.continuationInstance saved stored guarded guardLength.symm frameRead
  obtain ⟨loaded⟩ := loaded
  have loadedWeakened := loaded.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans held)
  let restored := ReturnPrefix.restored checked model environment record saved
  have restoredLength : restored.length = checked.frame.start + 5 + checked.frame.count := by
    have width := encoding.answers_length
    simp [restored, ReturnPrefix.restored, QueryContinuation.Frame.values, width,
      checked.frameStart, start]
    omega
  let parentTag : Domain.Value model.toCarriers := .data (.index checked.lookup.lookup.layout.constructor)
  let parentReady := restored ++ [parentTag]
  have parentReadyLength : parentReady.length = checked.lookup.lookup.placement.start := by
    rw [checked.lookupStart]
    simp [parentReady, restoredLength]
    omega
  have parentIndex : parentReady[checked.lookup.lookup.placement.slot]? = some (.data (.index saved.parentInstance)) := by
    rw [checked.parentInstance, checked.frameStart, start]
    simp [parentReady, restored, ReturnPrefix.restored, QueryContinuation.Frame.values,
      List.append_assoc, Nat.add_assoc]
  have parentConstructor : parentReady[checked.lookup.lookup.placement.constructor]? =
      some (.data (.index checked.lookup.lookup.layout.constructor)) := by
    rw [checked.parentTag, ← restoredLength]
    simp [parentReady, parentTag]
  have parentStore : parentReady[checked.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.lookup.projection.layout.type, data, parents⟩) :=
    Original.read_append (Original.read_append (Original.read_append
      (Original.read_append (Original.read_append readParents _) _) _) _) _
  obtain ⟨parentLookup⟩ := checked.lookup.simulation model program context data localFields parentReady
    saved.parentInstance parents parent parentReadyLength.symm parentConstructor parentIndex parentStore found tagBound
  have retained : environment <+: parentReady :=
    ((((List.prefix_append _ _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have parentWeakened := parentLookup.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ retained.trans held)
  have literal := (IndexLiterals.simulation model program context
    [checked.lookup.lookup.layout.constructor]
    (by intro value member; rw [List.mem_singleton] at member; exact member ▸ tagBound) restored).mapRelations
      (fun _ _ equal ↦ equal)
      (fun _ _ held ↦ ((((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
        (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans held)
  obtain ⟨contGuard⟩ := RequiredIndices.constant model environment environment (List.prefix_refl _)
    checked.continuationReference checked.continuation checked.continuation checked.continuationSite
    continuationBound readContinuation
  have contAccepted : RequiredIndices.Accepted [(checked.continuation, checked.continuation)] := by
    simpa [RequiredIndices.Accepted] using continuationBound
  simp only [contAccepted, ↓reduceIte] at contGuard
  rw [← RequiredIndices.constantCorrespondence model program context, ← start] at contGuard
  obtain ⟨kindGuard⟩ := RequiredIndices.constant model (environment ++ contValues) environment
    (List.prefix_append _ _) checked.kindReference checked.kind checked.kind checked.kindSite kindBound
    (Original.read_append readKind contValues)
  have kindAccepted : RequiredIndices.Accepted [(checked.kind, checked.kind)] := by
    simpa [RequiredIndices.Accepted] using kindBound
  simp only [kindAccepted, ↓reduceIte] at kindGuard
  rw [← RequiredIndices.constantCorrespondence model program context] at kindGuard
  have kindStart : (environment ++ contValues).length = checked.start + 2 := by
    simp [contValues, start]
  rw [kindStart] at kindGuard
  refine ⟨record, encoding, ⟨?_⟩⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  exact contGuard.continueDone (fun _ held ↦ held)
    (kindGuard.continueDone (fun _ held ↦ held)
      (loadedWeakened.continueDone (fun _ held ↦ held)
        (literal.continueDone (fun _ held ↦ held) parentWeakened)))

end Zkc.Realization.QueryController.ReturnPrefix
