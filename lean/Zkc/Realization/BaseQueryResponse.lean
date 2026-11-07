module

public import Zkc.Realization.RecordLookupProjection
public import Zkc.Realization.QueryReadResponse

@[expose] public section

/-! A complete clear-base response arm: immutable record lookup, nominal field
projection, checked table access, request resumption and returned controller
state. Provider membership and reached-state associations remain explicit. -/
set_option autoImplicit false
namespace Zkc.Realization.BaseQueryResponse
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) where
  lookupBody : List Construction.Instruction
  responseBody : List Construction.Instruction
  lookup : RecordLookupProjection.Recognized lookupBody
  response : QueryReadResponse.Recognized responseBody
  contiguous : response.read.start = lookup.lookup.placement.start + 3 +
    lookup.projection.selections.length
  exactBody : body = lookupBody ++ responseBody

def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let boundary := body.length - 22
  let lookupBody := body.take boundary
  let responseBody := body.drop boundary
  let lookup ← RecordLookupProjection.recognize lookupBody
  let response ← QueryReadResponse.recognize responseBody
  if contiguous : response.read.start = lookup.lookup.placement.start + 3 +
      lookup.projection.selections.length then
    some ⟨lookupBody, responseBody, lookup, response, contiguous,
      (List.take_append_drop boundary body).symm⟩
  else none

def projected {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (data : checked.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (record : model.Value checked.lookup.projection.layout.type) :
    Domain.Environment model.toCarriers :=
  environment ++ [.data (.index checked.lookup.lookup.layout.constructor), .data (.boolean true),
    .data ⟨checked.lookup.projection.layout.type, data, record⟩] ++
    RecordProjection.results model checked.lookup.projection.layout record
      checked.lookup.projection.selections

/-- The actual body is composed once for all clear-base callers. The provider
establishes membership and the meaning of the projected cells; the reached
controller invariant establishes its header and stores. No successful table
access, resumption, or complete-body equation is assumed. -/
theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.lookup.projection.selections,
      Domain.localType selection.type = true)
    (environment : Domain.Environment model.toCarriers) (recordIndex : Nat)
    (records : List (model.Value checked.lookup.projection.layout.type))
    (record : model.Value checked.lookup.projection.layout.type)
    (start : checked.lookup.lookup.placement.start = environment.length)
    (readTag : environment[checked.lookup.lookup.placement.constructor]? =
      some (.data (.index checked.lookup.lookup.layout.constructor)))
    (readInstance : environment[checked.lookup.lookup.placement.slot]? =
      some (.data (.index recordIndex)))
    (readStore : environment[checked.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.lookup.projection.layout.type, data, records⟩))
    (found : records[recordIndex]? = some record)
    (tagBound : checked.lookup.lookup.layout.constructor < indexLimit)
    (kindBound : checked.response.kind < indexLimit)
    (cells : List (model.Field checked.response.domain)) (rows phase actualKind : Nat)
    (pending supplied : QueryResumption.Coordinates)
    (answers : List (model.Field checked.response.domain)) (before after : List Nat)
    (beforeValues afterValues : Domain.Environment model.toCarriers)
    (readData : (projected checked model data environment record)[checked.response.read.data]? =
      some (.data ⟨.vector checked.response.domain, rfl, cells⟩))
    (readRows : (projected checked model data environment record)[checked.response.read.rows]? =
      some (.data (.index rows)))
    (readPhase :
      (projected checked model data environment record)[checked.response.response.phase]? =
      some (.data (.index phase)))
    (readKind :
      (projected checked model data environment record)[checked.response.response.kind]? =
      some (.data (.index actualKind)))
    (coordinates : RequiredIndices.Readback (projected checked model data environment record)
      checked.response.response.checks (QueryResumption.pairs pending supplied))
    (readArena :
      (projected checked model data environment record)[checked.response.response.arena]? =
      some (.data ⟨.sequence (.field checked.response.domain), rfl, answers⟩))
    (readBefore : Domain.read (projected checked model data environment record) before =
      some beforeValues)
    (readAfter : Domain.read (projected checked model data environment record) after =
      some afterValues) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((TableRead.read model checked.response.domain cells rows pending.position).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        QueryReadResponse.response model checked.response.domain checked.response.kind
          phase actualKind
          pending supplied answers answer beforeValues afterValues)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final
          (QueryResumption.outputReferences checked.response.response before after) with
        | some values => .done values
        | none => .halt .refused)) := by
  have head := checked.lookup.simulation model program context data localFields
    environment recordIndex
    records record start readTag readInstance readStore found tagBound
  obtain ⟨head⟩ := head
  have responseStart : checked.response.read.start =
      (projected checked model data environment record).length := by
    simpa only [projected, List.length_append, List.length_cons, List.length_nil,
      RecordProjection.results_length model _ record _ localFields, start] using checked.contiguous
  obtain ⟨tail⟩ := checked.response.simulation model program context kindBound
    (projected checked model data environment record) responseStart cells rows phase actualKind
    pending supplied answers before after beforeValues afterValues readData readRows
    readPhase readKind coordinates readArena readBefore readAfter
  have retained : environment <+: projected checked model data environment record := by
    unfold projected
    exact (List.prefix_append _ _).trans (List.prefix_append _ _)
  have composed := head.continueDone
    (targetNext := fun intermediate ↦
      (Domain.evaluate model program context checked.responseBody intermediate).bind fun final ↦
        match Domain.read final
          (QueryResumption.outputReferences checked.response.response before after) with
        | some values => .done values
        | none => .halt .refused)
    (fun _ held ↦ held)
    (tail.mapRelations (fun _ _ held ↦ held) (fun _ _ held ↦ retained.trans held))
  simpa only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc] using
    (show Nonempty _ from ⟨composed⟩)

end Zkc.Realization.BaseQueryResponse
