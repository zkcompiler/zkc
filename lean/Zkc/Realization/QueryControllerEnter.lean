module

public import Zkc.Realization.QueryControllerPhase
public import Zkc.Realization.RecordLookupProjection

@[expose] public section

/-! Entry into the generated query controller. The actual kind check, immutable
record lookup and domain check precede any child suspension or provider request.
These rules retain that order, complete state projection and checked-index
refusals. Installation supplies the record's meaning; no protocol companion
supplies an execution proof for this administrative prefix. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryController
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace DomainGuard

def instructions (start position rows : Nat) (site : String) : List Construction.Instruction :=
  [⟨.execute .indexLess, [position, rows], [.data .boolean], []⟩,
   ⟨.require site, [start], [], []⟩]

def Accepted (position rows : Nat) : Prop :=
  position < indexLimit ∧ rows < indexLimit ∧ position < rows

instance (position rows : Nat) : Decidable (Accepted position rows) :=
  inferInstanceAs (Decidable (position < indexLimit ∧ rows < indexLimit ∧ position < rows))

/-- No in-range premise is assumed: a malformed index or out-of-domain
position refuses before the controller can request a provider response. -/
theorem simulation (model : DomainModel) (program : Program) (context : Context)
    (environment : Domain.Environment model.toCarriers) (positionSlot rowsSlot : Nat)
    (site : String) (position rows : Nat)
    (readPosition : environment[positionSlot]? = some (.data (.index position)))
    (readRows : environment[rowsSlot]? = some (.data (.index rows))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if Accepted position rows then .done (environment ++ [.data (.boolean true)])
        else .halt .refused)
      (Domain.evaluate model program context
        (instructions environment.length positionSlot rowsSlot site) environment)) := by
  have read : Domain.read environment [positionSlot, rowsSlot] =
      Domain.encodeValues (tys := [.index, .index]) (.cons position (.cons rows .nil)) := by
    simp [Domain.read, readPosition, readRows, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle]
  have comparison : Domain.View.execute model .indexLess
      [positionSlot, rowsSlot] [.data .boolean] environment =
      if position < indexLimit ∧ rows < indexLimit then
        .done (environment ++ [.data (.boolean (decide (position < rows)))])
      else .halt .refused := by
    have law := ConnectionPrimitives.view_execute model .indexLess
      (.cons position (.cons rows .nil)) rfl rfl environment _ read
    by_cases bounds : position < indexLimit ∧ rows < indexLimit <;>
      simpa [Primitive.results, Primitive.evaluateOn, checkedIndices, bounds,
        primitiveOutcome, PIR.Process.bind, Original.encodeHelperResult,
        Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
        Domain.Payload.ofValue, Ty.isHandle] using law
  have bodyLaw := Domain.Correspondence.sequence
    (Domain.Correspondence.execute .indexLess [positionSlot, rowsSlot] [.data .boolean])
    (Domain.Correspondence.sequence (Domain.Correspondence.require site environment.length [])
      Domain.Correspondence.empty) (model := model) (program := program) (context := context)
  change Domain.Correspondence.Block (instructions environment.length positionSlot rowsSlot site)
    _ at bodyLaw
  refine ⟨?_⟩
  rw [bodyLaw]
  by_cases bounds : position < indexLimit ∧ rows < indexLimit
  · simp only [bounds] at comparison
    by_cases inside : position < rows
    · simp only [inside, decide_true] at comparison
      simp only [Accepted, bounds.1, bounds.2, inside, and_self, ↓reduceIte]
      have guard : Domain.View.require environment.length []
          (environment ++ [.data (.boolean true)]) =
          .done (environment ++ [.data (.boolean true)]) := by simp [Domain.View.require]
      apply RecordAllocator.silent_sequence comparison (List.prefix_refl _) (by simp)
      apply RecordAllocator.silent_sequence guard (by simp) (by simp)
      exact .done rfl
    · simp only [inside, decide_false] at comparison
      simp only [Accepted, inside, and_false, ↓reduceIte]
      rw [Domain.View.sequence_return _ _ _ _ comparison]
      refine .checkpoint _ (List.prefix_refl _) (.checkpoint _ (by simp) ?_)
      have guard : Domain.View.require environment.length []
          (environment ++ [.data (.boolean false)]) = .halt .refused := by
        simp [Domain.View.require]
      simp only [Domain.View.sequence, guard, PIR.Process.bind]
      exact .checkpoint _ (by simp) (.halt .refused)
  · have invalid : ¬ Accepted position rows := fun all ↦ bounds ⟨all.1, all.2.1⟩
    simp only [bounds, ↓reduceIte] at comparison
    simp only [invalid, ↓reduceIte, Domain.View.sequence, comparison, PIR.Process.bind]
    exact .checkpoint _ (List.prefix_refl _) (.halt .refused)

end DomainGuard

namespace EntryPrefix

structure Recognized (body : List Construction.Instruction) where
  start : Nat
  kind : Nat
  kindReference : Nat
  kindSite : String
  position : Nat
  rows : Nat
  domainSite : String
  state : List Nat
  lookupBody : List Construction.Instruction
  lookup : RecordLookupProjection.Recognized lookupBody
  kindField : state[5]? = some kindReference
  positionField : state[2]? = some position
  lookupStart : lookup.lookup.placement.start = start + 2
  exactBody : body =
    RequiredIndices.constantInstructions start kindReference kind kindSite ++ lookupBody ++
    DomainGuard.instructions (start + 5 + lookup.projection.selections.length)
      position rows domainSite

/-- Admit the common kind, immutable record and domain prefix of base and
virtual entry. The complete prefix ends at the checked domain guard. -/
def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction) :
    Option (Recognized body) := do
  let constant :: compare :: require :: _ := body | none
  let .execute (.indexConstant kind) := constant.operation | none
  let [kindReference, _] := compare.operands | none
  let .require kindSite := require.operation | none
  let [domain, guard] := body.drop (body.length - 2) | none
  let [position, rows] := domain.operands | none
  let .require domainSite := guard.operation | none
  let lookupBody := (body.drop 3).take (body.length - 5)
  let lookup ← RecordLookupProjection.recognize lookupBody
  if kindField : state[5]? = some kindReference then
    if positionField : state[2]? = some position then
      if lookupStart : lookup.lookup.placement.start = start + 2 then
        if exactBody : body =
            RequiredIndices.constantInstructions start kindReference kind kindSite ++ lookupBody ++
            DomainGuard.instructions (start + 5 + lookup.projection.selections.length)
              position rows domainSite then
          some ⟨start, kind, kindReference, kindSite, position, rows, domainSite, state,
            lookupBody, lookup, kindField, positionField, lookupStart, exactBody⟩
        else none
      else none
    else none
  else none

def projected {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel)
    (data : checked.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (record : model.Value checked.lookup.projection.layout.type) :
    Domain.Environment model.toCarriers :=
  (environment ++ [.data (.index checked.kind), .data (.boolean true)]) ++
    [.data (.index checked.lookup.lookup.layout.constructor), .data (.boolean true),
      .data ⟨checked.lookup.projection.layout.type, data, record⟩] ++
    RecordProjection.results model checked.lookup.projection.layout record
      checked.lookup.projection.selections

/-- The common entry prefix retains exact refusal order and the caller frame. -/
theorem Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program)
    (context : Context) (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (read : Domain.read environment checked.state = some (header.encode stores))
    (kind : header.kind = checked.kind) (kindBound : checked.kind < indexLimit)
    (data : checked.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.lookup.projection.selections,
      Domain.localType selection.type = true)
    (recordIndex : Nat) (records : List (model.Value checked.lookup.projection.layout.type))
    (record : model.Value checked.lookup.projection.layout.type)
    (readTag : environment[checked.lookup.lookup.placement.constructor]? =
      some (.data (.index checked.lookup.lookup.layout.constructor)))
    (readInstance : environment[checked.lookup.lookup.placement.slot]? =
      some (.data (.index recordIndex)))
    (readStore : environment[checked.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.lookup.projection.layout.type, data, records⟩))
    (found : records[recordIndex]? = some record)
    (tagBound : checked.lookup.lookup.layout.constructor < indexLimit) (rows : Nat)
    (readRows : (projected checked model data environment record)[checked.rows]? =
      some (.data (.index rows))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if DomainGuard.Accepted header.position rows then
        .done (projected checked model data environment record ++ [.data (.boolean true)])
       else .halt .refused)
      (Domain.evaluate model program context body environment)) := by
  have readKind : environment[checked.kindReference]? = some (.data (.index checked.kind)) := by
    have field := Domain.View.read_getElem? read 5
    rw [checked.kindField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values, kind] using field.symm
  have readPosition : environment[checked.position]? = some (.data (.index header.position)) := by
    have field := Domain.View.read_getElem? read 2
    rw [checked.positionField] at field
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using field.symm
  let kindValues : Domain.Environment model.toCarriers :=
    [.data (.index checked.kind), .data (.boolean true)]
  let lookupValues : Domain.Environment model.toCarriers :=
    [.data (.index checked.lookup.lookup.layout.constructor), .data (.boolean true),
      .data ⟨checked.lookup.projection.layout.type, data, record⟩]
  let fields := RecordProjection.results model checked.lookup.projection.layout record
    checked.lookup.projection.selections
  have selected : projected checked model data environment record =
      environment ++ kindValues ++ lookupValues ++ fields := rfl
  have selectedLength : (projected checked model data environment record).length =
      checked.start + 5 + checked.lookup.projection.selections.length := by
    simp [projected, RecordProjection.results_length model _ record _ localFields, start]
    omega
  have selectedPosition : (projected checked model data environment record)[checked.position]? =
      some (.data (.index header.position)) :=
    Original.read_append (Original.read_append (Original.read_append readPosition kindValues)
      lookupValues) fields
  obtain ⟨kindGuard⟩ := RequiredIndices.constant model environment environment
    (List.prefix_refl _) checked.kindReference checked.kind checked.kind checked.kindSite
    kindBound readKind
  have kindAccepted : RequiredIndices.Accepted [(checked.kind, checked.kind)] := by
    simpa [RequiredIndices.Accepted] using kindBound
  simp only [kindAccepted, ↓reduceIte] at kindGuard
  rw [← RequiredIndices.constantCorrespondence model program context environment.length
    checked.kindReference checked.kind checked.kindSite, ← start] at kindGuard
  obtain ⟨lookup⟩ := checked.lookup.simulation model program context data localFields
    (environment ++ kindValues) recordIndex records record
    (by simpa [kindValues, start] using checked.lookupStart)
    (Original.read_append readTag kindValues) (Original.read_append readInstance kindValues)
    (Original.read_append readStore kindValues) found tagBound
  have lookupWeakened := lookup.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ (List.prefix_append environment kindValues).trans held)
  obtain ⟨domain⟩ := DomainGuard.simulation model program context
    (projected checked model data environment record) checked.position checked.rows checked.domainSite
    header.position rows selectedPosition readRows
  have retained : environment <+: projected checked model data environment record := by
    rw [selected]
    exact ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have domainWeakened := domain.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ retained.trans held)
  rw [selectedLength] at domainWeakened
  refine ⟨?_⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  exact kindGuard.continueDone (fun _ held ↦ held)
    (lookupWeakened.continueDone (fun _ held ↦ held) domainWeakened)

end EntryPrefix

namespace BaseEntry

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  entryBody : List Construction.Instruction
  entry : EntryPrefix.Recognized entryBody
  exactBody : body = entryBody ++ Phase.instructions 2
  exactOutput : returned = Phase.output entry.state
    (entry.start + 6 + entry.lookup.projection.selections.length)

def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) := do
  let entryBody := body.take (body.length - 1)
  let entry ← EntryPrefix.recognize start state entryBody
  if exactBody : body = entryBody ++ Phase.instructions 2 then
    if exactOutput : returned = Phase.output entry.state
        (entry.start + 6 + entry.lookup.projection.selections.length) then
      some ⟨entryBody, entry, exactBody, exactOutput⟩
    else none
  else none

/-- The complete base entry uses the same prefix as virtual dispatch. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program)
    (context : Context) (header : Header) (stores environment : Domain.Environment model.toCarriers)
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
    (readInstance : environment[checked.entry.lookup.lookup.placement.slot]? =
      some (.data (.index recordIndex)))
    (readStore : environment[checked.entry.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.entry.lookup.projection.layout.type, data, records⟩))
    (found : records[recordIndex]? = some record)
    (tagBound : checked.entry.lookup.lookup.layout.constructor < indexLimit) (rows : Nat)
    (readRows : (EntryPrefix.projected checked.entry model data environment record)[checked.entry.rows]? =
      some (.data (.index rows))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if DomainGuard.Accepted header.position rows then
        .done ({header with phase := 2}.encode stores) else .halt .refused)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  let selected := EntryPrefix.projected checked.entry model data environment record
  have selectedLength : selected.length =
      checked.entry.start + 5 + checked.entry.lookup.projection.selections.length := by
    simp [selected, EntryPrefix.projected,
      RecordProjection.results_length model _ record _ localFields, start]
    omega
  have retained : environment <+: selected :=
    ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have selectedState : Domain.read selected checked.entry.state = some (header.encode stores) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ read))
  obtain ⟨entry⟩ := checked.entry.simulation model program context header stores environment start
    read kind kindBound data localFields recordIndex records record readTag readInstance readStore
    found tagBound rows readRows
  let literal : Phase.Recognized (Phase.instructions 2) returned :=
    ⟨2, checked.entry.start + 6 + checked.entry.lookup.projection.selections.length,
      checked.entry.state, rfl, checked.exactOutput⟩
  obtain ⟨phase⟩ := literal.simulation model program context header stores
    (selected ++ [.data (.boolean true)])
    (by dsimp only [literal]; simp only [List.length_append, List.length_cons, List.length_nil,
      selectedLength]; omega)
    (by change 2 < indexLimit; decide)
    (RecordAllocator.read_extended selected [.data (.boolean true)] _ _ selectedState)
  have phaseWeakened := phase.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ (retained.trans (List.prefix_append _ _)).trans held)
  refine ⟨?_⟩
  rw [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  by_cases accepted : DomainGuard.Accepted header.position rows
  · simp only [accepted, ↓reduceIte] at entry ⊢
    exact entry.continueDone (fun _ held ↦ held) phaseWeakened
  · simp only [accepted, ↓reduceIte] at entry ⊢
    exact entry.continueHalt _ (fun _ held ↦ held)

end BaseEntry
end Zkc.Realization.QueryController
