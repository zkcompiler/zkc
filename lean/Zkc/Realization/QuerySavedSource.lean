module

public import Zkc.Realization.QuerySourceExecution
public import Zkc.Realization.QueryContinuationProjection
public import Zkc.Realization.VirtualStorageLifetime

@[expose] public section

/-! A saved frame belongs to a particular installed source closure and a
particular suspension in its original body. Loading the frame recovers that
association; it cannot choose another parent with the same type. The source
cursor records returned child answers, while the provider/phase simulation
must establish that those answers were actually produced.
-/
set_option autoImplicit false
namespace Zkc.Realization.QuerySavedSource
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {checked : CheckedOracle snapshot domains math}

/-- Parent identity and captures come from the actual immutable installation.
The saved frame supplies its dynamic instance and query position. -/
structure Parent (layout : VirtualStorage.Layout checked.declaration.inputs.dropLast)
    (references : CaptureLayout.References) (entries : OracleEntries model snapshot domains math)
    (records : List (model.Value layout.recordType)) (frame : QueryContinuation.Frame) where
  location : OracleLocation
  rows : Nat
  leaves : Nat
  holder : Nat
  receivers : List Nat
  captures : Values model.Value checked.declaration.inputs.dropLast
  signature : checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index]
  installed : VirtualStorage.Stored checked layout references entries records
    (layout.constructor, frame.parentInstance) location rows leaves holder receivers captures

variable {layout : VirtualStorage.Layout checked.declaration.inputs.dropLast}
  {references : CaptureLayout.References} {entries : OracleEntries model snapshot domains math}
  {records : List (model.Value layout.recordType)} {frame : QueryContinuation.Frame}

def Parent.body (parent : Parent layout references entries records frame) :
    PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]) :=
  checked.denote model (parent.signature.symm ▸
    parent.captures.append (.cons frame.position .nil)).present

/-- The parent slot fixes its complete source capture tuple, including
distinct handles with equal answer types. -/
theorem Parent.captures_unique (first second : Parent layout references entries records frame)
    (unique : CaptureLayout.Unambiguous references) : first.captures = second.captures := by
  obtain ⟨left, foundLeft, encodedLeft⟩ := first.installed.2.2
  obtain ⟨right, foundRight, encodedRight⟩ := second.installed.2.2
  cases Option.some.inj (foundLeft.symm.trans foundRight)
  exact encodedLeft.captures_unique unique encodedRight

theorem Parent.location_unique (first second : Parent layout references entries records frame) :
    first.location = second.location := by
  obtain ⟨left, foundLeft, encodedLeft⟩ := first.installed.2.2
  obtain ⟨right, foundRight, encodedRight⟩ := second.installed.2.2
  cases Option.some.inj (foundLeft.symm.trans foundRight)
  exact encodedLeft.location_unique encodedRight

/-- Restoring the same saved parent cannot select a different source meaning.
This equality is derived from storage, not supplied as a companion premise. -/
theorem Parent.body_unique (first second : Parent layout references entries records frame)
    (unique : CaptureLayout.Unambiguous references) : first.body = second.body := by
  simp only [Parent.body, first.captures_unique second unique]

/-- Every captured reference and saved record retains its existing owner when
the registry and physical stores grow. No source-body traversal is repeated. -/
def Parent.transport (parent : Parent layout references entries records frame)
    {newReferences : CaptureLayout.References}
    {newEntries : OracleEntries model snapshot domains math}
    {newRecords : List (model.Value layout.recordType)}
    (registry : OracleStore.FreshExtension entries newEntries) (physical : records <+: newRecords)
    (kept : ∀ kind identity anchor reference,
      references kind identity anchor reference → newReferences kind identity anchor reference) :
    Parent layout newReferences newEntries newRecords frame :=
  {parent with installed := parent.installed.transport registry physical kept}

theorem Parent.transport_body (parent : Parent layout references entries records frame)
    {newReferences : CaptureLayout.References}
    {newEntries : OracleEntries model snapshot domains math}
    {newRecords : List (model.Value layout.recordType)}
    (registry : OracleStore.FreshExtension entries newEntries) (physical : records <+: newRecords)
    (kept : ∀ kind identity anchor reference,
      references kind identity anchor reference → newReferences kind identity anchor reference) :
    (parent.transport registry physical kept).body = parent.body := rfl

/-- Static continuation selection fixes the declaration and frame arena.
Within that selection, these fields connect the physical saved slot, its
installed parent and the next actual source request. -/
structure Saved (identity : String) (count : Nat)
    (frames : List (model.Value (QueryContinuation.layout identity count).type)) (slot : Nat)
    (arenas : (kind : OracleKind) → List (model.Value kind.answer))
    (parent : Parent layout references entries records frame) (request : OracleRead)
    (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer])) where
  stored : QueryContinuation.Stored identity count frames slot frame
  cursor : QuerySourceContinuation.Associated arenas parent.body (.call request next) frame.answers

/-- Saving at the actual append slot installs the source suspension alongside
the immutable frame. It uses the existing encoder and source-cursor rules. -/
def save {identity : String} {count : Nat}
    (frames : List (model.Value (QueryContinuation.layout identity count).type))
    {record : model.Value (QueryContinuation.layout identity count).type}
    (encoded : QueryContinuation.Encodes identity count frame record)
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {parent : Parent layout references entries records frame} {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer])}
    (cursor : QuerySourceContinuation.Associated arenas parent.body
      (.call request next) frame.answers) :
    Saved identity count (frames ++ [record]) frames.length arenas parent request next :=
  ⟨QueryContinuation.stored_append frames encoded, cursor⟩

variable {identity : String} {count slot : Nat}
  {frames : List (model.Value (QueryContinuation.layout identity count).type)}
  {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
  {parent : Parent layout references entries records frame} {request : OracleRead}
  {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers)
    (Values (Component model.Value) [checked.declaration.kind.answer])}

/-- The common invariant is stable across child allocations and fresh source
constructions. It retains the same captures, source residual and answer order. -/
def Saved.transport (saved : Saved identity count frames slot arenas parent request next)
    {newReferences : CaptureLayout.References}
    {newEntries : OracleEntries model snapshot domains math}
    {newRecords : List (model.Value layout.recordType)}
    {newFrames : List (model.Value (QueryContinuation.layout identity count).type)}
    {newArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    (registry : OracleStore.FreshExtension entries newEntries)
    (physical : records <+: newRecords) (frameExtension : frames <+: newFrames)
    (answerExtension : ∀ kind, arenas kind <+: newArenas kind)
    (kept : ∀ kind identity anchor reference,
      references kind identity anchor reference → newReferences kind identity anchor reference) :
    Saved identity count newFrames slot newArenas
      (parent.transport registry physical kept) request next :=
  ⟨saved.stored.transport frameExtension, saved.cursor.transport answerExtension⟩

/-- Loading another encoding at the saved slot cannot change the parent,
position, outer continuation or ordered prior answers. -/
theorem Saved.decoded (saved : Saved identity count frames slot arenas parent request next)
    {decoded : QueryContinuation.Frame}
    (loaded : QueryContinuation.Stored identity count frames slot decoded) :
    decoded = frame := loaded.unique saved.stored

/-- A returned child resumes the original installed source body. The physical
cell is appended after all saved answers; it cannot replace an earlier cell. -/
def Saved.resume (saved : Saved identity count frames slot arenas parent request next)
    {answerSlot : Nat} {answer : model.Value request.kind.answer}
    (returned : (arenas request.kind)[answerSlot]? = some answer) :
    QuerySourceContinuation.Associated arenas parent.body (next answer)
      (frame.answers ++ [answerSlot]) := saved.cursor.resume returned

/-- Strengthen the physical restore with the actual source child execution.
The derived progress retains its provider poststate, phase and events as well
as the ordered saved value. It cannot be supplied as two independent proofs
of a value cursor and an eventual root result. -/
theorem Saved.load_produced {I : PIR.Signature} {S E : Type}
    (saved : Saved identity count frames slot arenas parent request next)
    {interaction : PIR.Interaction I}
    {operations : (query : OracleRead) → S →
      PIR.Process I (PIR.Execution S E (model.Value query.kind.answer))}
    {initial current after : S} {initialPhase currentPhase finalPhase : interaction.Phase}
    {events following : List E}
    (produced : QuerySourceContinuation.Produced interaction operations parent.body
      initial initialPhase arenas (.call request next) frame.answers current currentPhase events)
    {answerSlot : Nat} {answer : model.Value request.kind.answer}
    (child : PIR.Reaches interaction (operations request current) currentPhase
      (.done ⟨.returned answer, after, following⟩) finalPhase)
    (returned : (arenas request.kind)[answerSlot]? = some answer)
    (environment : Domain.Environment model.toCarriers) (storeReference slotReference : Nat)
    (read : Domain.read environment [storeReference, slotReference] = Domain.encodeValues
      (tys := [.sequence (QueryContinuation.layout identity count).type, .index])
      (.cons frames (.cons slot .nil))) (program : Program) (context : Context) :
    Nonempty (QuerySourceContinuation.Produced interaction operations parent.body
      initial initialPhase arenas (next answer) (frame.answers ++ [answerSlot])
      after finalPhase (events ++ following)) ∧
    ∃ record, QueryContinuation.Encodes identity count frame record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(QueryContinuation.layout identity count).type,
            QueryContinuation.frameData identity count, record⟩] ++
          frame.values.map (fun value ↦ Domain.Value.data (.index value))))
        (Domain.evaluate model program context
          (QueryContinuation.loadInstructions identity count environment.length
            storeReference slotReference) environment)) :=
  ⟨⟨produced.resume child returned⟩,
    saved.stored.load_project environment storeReference slotReference read program context⟩

end Zkc.Realization.QuerySavedSource
