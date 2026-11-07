module

public import Zkc.Realization.BaseQueryResponse
public import Zkc.Realization.ClearStorageRead

@[expose] public section

/-! Complete clear-base response associated with the word actually published.
The common installation checks the ordered field selections and operand links.
The reached-state relation supplies the original request and immutable storage;
projection, lookup identity and intermediate-frame preservation are derived.
-/
set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {domain : String} {shape : Option Nat}

/-- Physical placement facts checked against the actual generated arm. These
are installation obligations, not mathematical companion arguments. -/
structure ResponseGeometry (layout : Layout (.table (.field domain) shape))
    (selections : List (RecordProjection.Selection layout.fields))
    (lookup : RecordLookup.Placement) (read : TableRead.Placement)
    (response : QueryResumption.Placement) : Prop where
  readStart : read.start = lookup.start + 3 + selections.length
  responseStart : response.start = read.start + 2
  answer : response.answer = read.start + 1
  position : read.position = response.pending.position
  constructor : lookup.constructor = response.pending.constructor
  instanceSlot : lookup.slot = response.pending.anchorInstance
  rows : ∃ ordinal, selections[ordinal]? = some layout.rowField ∧
    read.rows = lookup.start + 3 + ordinal
  data : ∃ ordinal, selections[ordinal]? = some layout.dataField ∧
    read.data = lookup.start + 3 + ordinal

def Layout.responseInstructions (layout : Layout (.table (.field domain) shape))
    (selections : List (RecordProjection.Selection layout.fields))
    (lookup : RecordLookup.Placement) (read : TableRead.Placement)
    (kind : Nat) (response : QueryResumption.Placement) : List Construction.Instruction :=
  (RecordLookup.instructions layout.lookup lookup ++
    RecordProjection.instructions layout.projection (lookup.start + 2) selections) ++
    QueryReadResponse.instructions domain kind read response

def ResponseGeometry.checked {layout : Layout (.table (.field domain) shape)}
    {selections : List (RecordProjection.Selection layout.fields)}
    {lookup : RecordLookup.Placement} {read : TableRead.Placement}
    {response : QueryResumption.Placement}
    (geometry : ResponseGeometry layout selections lookup read response) (kind : Nat) :
    BaseQueryResponse.Recognized
      (layout.responseInstructions selections lookup read kind response) :=
  ⟨_, _, ⟨_, _, ⟨layout.lookup, lookup, rfl⟩,
    ⟨layout.projection, lookup.start + 2, selections, rfl⟩, rfl, rfl, rfl⟩,
    ⟨domain, kind, read, response, geometry.responseStart, geometry.answer,
      geometry.position, rfl⟩, geometry.readStart, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The pending reference selects the actual publication. Lookup and product
projection derive its cells and rows; the exact provider outcome, including an
out-of-range refusal, precedes the generated resumption and output selection.
No independent cells/rows equation or intermediate header readback is assumed. -/
theorem Stored.response_simulation {model : DomainModel} {Aux E : Type}
    {layout : Layout (.table (.field domain) shape)}
    {state : PublishedWords.State model Aux}
    {records : List (model.Value layout.recordType)}
    {word : PublishedWords.Word model (.field domain)}
    (pending supplied : QueryResumption.Coordinates)
    (stored : Stored layout state.words records (pending.constructor, pending.anchorInstance) word)
    (valid : OracleStore.validRows word.kind word.rows = true)
    (requestedShape : Option Nat)
    (compatible : OracleStore.validRows (.table (.field domain) requestedShape) word.rows = true)
    (length : word.cells.length = word.rows)
    (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (selections : List (RecordProjection.Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true)
    (lookup : RecordLookup.Placement) (read : TableRead.Placement)
    (response : QueryResumption.Placement)
    (geometry : ResponseGeometry layout selections lookup read response)
    (program : Program) (context : Context) (data : layout.recordType.isHandle = false)
    (body : List Construction.Instruction)
    (kind : Nat) (actual : body = layout.responseInstructions selections lookup read kind response)
    (tagBound : layout.constructor < indexLimit) (kindBound : kind < indexLimit)
    (environment : Domain.Environment model.toCarriers) (start : lookup.start = environment.length)
    (phase actualKind : Nat) (answers : List (model.Field domain)) (before after : List Nat)
    (beforeValues afterValues : Domain.Environment model.toCarriers)
    (readStore : environment[lookup.store]? =
      some (.data ⟨.sequence layout.recordType, data, records⟩))
    (readPhase : environment[response.phase]? = some (.data (.index phase)))
    (readKind : environment[response.kind]? = some (.data (.index actualKind)))
    (coordinates : RequiredIndices.Readback environment response.checks
      (QueryResumption.pairs pending supplied))
    (readArena : environment[response.arena]? =
      some (.data ⟨.sequence (.field domain), rfl, answers⟩))
    (readBefore : Domain.read environment before = some beforeValues)
    (readAfter : Domain.read environment after = some afterValues) :
    let request : OracleRead :=
      ⟨.table (.field domain) requestedShape, word.anchor, pending.position, location, expansion⟩
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((primitiveOutcome (I := closedInterface)
          (PublishedWords.read (E := E) request state).outcome).interpret
            (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        QueryReadResponse.response model domain kind phase actualKind pending supplied
          answers answer beforeValues afterValues)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final (QueryResumption.outputReferences response before after) with
        | some values => .done values
        | none => .halt .refused)) := by
  dsimp only
  obtain ⟨record, tag, found, published, encoding⟩ := stored
  change pending.constructor = layout.constructor at tag
  let checked := geometry.checked kind
  let added : Domain.Environment model.toCarriers :=
    [.data (.index layout.constructor), .data (.boolean true),
      .data ⟨layout.recordType, data, record⟩]
  let projected := RecordProjection.results model layout.projection record selections
  have frame : BaseQueryResponse.projected checked model data environment record =
      environment ++ (added ++ projected) := by
    simp only [BaseQueryResponse.projected, checked, ResponseGeometry.checked,
      added, projected, Layout.lookup, List.append_assoc]
    rfl
  have reference := QueryResumption.read_pending_reference coordinates
  have readTag : environment[lookup.constructor]? = some (.data (.index layout.constructor)) := by
    rw [geometry.constructor]
    simpa only [tag] using reference.1
  have readInstance : environment[lookup.slot]? = some (.data (.index pending.anchorInstance)) := by
    rw [geometry.instanceSlot]
    exact reference.2
  have dataRead : (BaseQueryResponse.projected checked model data environment record)[read.data]? =
      some (.data ⟨.vector domain, rfl, word.cells⟩) := by
    obtain ⟨ordinal, selected, position⟩ := geometry.data
    have selectedRead := encoding.projected_data selections localFields ordinal selected
      (environment ++ added)
    simpa only [frame, position, start, List.length_append, added,
      List.length_cons, List.length_nil, Nat.add_zero, List.append_assoc] using selectedRead
  have rowsRead : (BaseQueryResponse.projected checked model data environment record)[read.rows]? =
      some (.data (.index word.rows)) := by
    obtain ⟨ordinal, selected, position⟩ := geometry.rows
    have selectedRead := encoding.projected_rows selections localFields ordinal selected
      (environment ++ added)
    simpa only [frame, position, start, List.length_append, added,
      List.length_cons, List.length_nil, Nat.add_zero, List.append_assoc] using selectedRead
  have execution := checked.simulation model program context data localFields environment
    pending.anchorInstance records record start readTag readInstance readStore found
    tagBound kindBound word.cells word.rows phase actualKind pending supplied answers
    before after beforeValues afterValues
    dataRead rowsRead
    (by rw [frame]; exact Original.read_append readPhase _)
    (by rw [frame]; exact Original.read_append readKind _)
    (by rw [frame]; exact coordinates.extended _)
    (by rw [frame]; exact Original.read_append readArena _)
    (by rw [frame]; exact RecordAllocator.read_extended _ _ _ _ readBefore)
    (by rw [frame]; exact RecordAllocator.read_extended _ _ _ _ readAfter)
  rw [published_read word state published encoding.kind_eq valid compatible length]
  have closed : primitiveOutcome (I := closedInterface)
      (Domain.closedOutcome (TableRead.read model domain word.cells word.rows pending.position)) =
      TableRead.read model domain word.cells word.rows pending.position := by
    cases TableRead.read model domain word.cells word.rows pending.position with
    | done value => rfl
    | halt reason => rfl
    | call operation next => exact nomatch operation
  rw [closed, actual]
  exact execution

end Zkc.Realization.ClearStorage
