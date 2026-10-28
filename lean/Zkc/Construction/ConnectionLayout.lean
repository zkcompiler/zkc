module

public import Zkc.Construction.ConnectionOutputs
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! Finite layout checks and their semantic readback laws.

Layouts propose SSA locations. Source scopes determine which components must
be present or absent. The checked map accounts for every source component and
retains the full nominal payload, without evaluating protocol mathematics.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

/-- Select exactly the role-visible source outputs. Hidden components require
an absent location; visible capabilities cannot be returned as encoded data.
The entire scope and location lists must be consumed. -/
def outputReferences (role : Nat) : List (List Nat) → List Location → Option (List Nat)
  | [], [] => some []
  | scope :: scopes, location :: locations => do
      let rest ← outputReferences role scopes locations
      if role ∈ scope then
        match location with
        | .data reference => some (reference :: rest)
        | _ => none
      else
        match location with
        | .absent => some rest
        | _ => none
  | _, _ => none

/-- A checked output map reads precisely the complete encoded source row.
No instance-level equality for an entire program is an input to this law. -/
theorem outputReferences_read {role : Nat} {scopes : List (List Nat)}
    {locations : List Location} {references : List Nat} {types : List Structured.Ty}
    {environment : Domain.Environment carriers}
    (values : Values (Component carriers.Value) types)
    (checked : outputReferences role scopes locations = some references)
    (related : ValuesHolds environment locations values) :
    ∃ encoded, roleOutputValues role scopes values = some encoded ∧
      Domain.read environment references = some encoded := by
  induction values generalizing scopes locations references with
  | nil =>
    cases locations with
    | cons _ _ => exact False.elim related
    | nil =>
      cases scopes with
      | cons _ _ => simp [outputReferences] at checked
      | nil =>
        simp only [outputReferences, Option.some.injEq] at checked
        subst references
        exact ⟨[], rfl, rfl⟩
  | @cons ty types value values ih =>
    cases locations with
    | nil => exact False.elim related
    | cons location locations =>
      obtain ⟨head, tail⟩ := related
      cases scopes with
      | nil => simp [outputReferences] at checked
      | cons scope scopes =>
        cases remaining : outputReferences role scopes locations with
        | none => simp [outputReferences, remaining] at checked
        | some rest =>
          obtain ⟨encoded, encoding, read⟩ := ih remaining tail
          by_cases visible : role ∈ scope
          · cases location with
            | absent => simp [outputReferences, remaining, visible] at checked
            | capability _ => simp [outputReferences, remaining, visible] at checked
            | data reference =>
              simp only [outputReferences, remaining, bind, Option.bind, visible,
                ↓reduceIte, Option.some.injEq] at checked
              subst references
              obtain ⟨actual, valueEq, decoded⟩ := head
              subst value
              cases found : environment[reference]? with
              | none => simp [found] at decoded
              | some physical =>
                have decodedValue : physical.decode ty = some actual := by simpa [found] using decoded
                have encodedValue := Domain.Value.encode_decode decodedValue
                refine ⟨physical :: encoded, ?_, ?_⟩
                · simp [roleOutputValues, encoding, visible, encodedValue]
                · change rest.mapM (fun reference => environment[reference]?) = some encoded at read
                  simp [Domain.read, List.mapM_cons, found, read]
          · cases location with
            | data _ => simp [outputReferences, remaining, visible] at checked
            | capability _ => simp [outputReferences, remaining, visible] at checked
            | absent =>
              simp only [outputReferences, remaining, bind, Option.bind, visible,
                ↓reduceIte, Option.some.injEq] at checked
              subst references
              change value = none at head
              subst value
              exact ⟨encoded, by simp [roleOutputValues, encoding, visible], read⟩

/-- Readback implies the same source-owned nominal sort map as complete
encoding. Aliasing locations is allowed only when they really hold the same
source values; changing a residual cannot be concealed by an acceptance bit. -/
theorem outputReferences_sorts {role : Nat} {scopes : List (List Nat)}
    {locations : List Location} {references : List Nat} {types : List Structured.Ty}
    {environment : Domain.Environment carriers}
    (values : Values (Component carriers.Value) types)
    (checked : outputReferences role scopes locations = some references)
    (related : ValuesHolds environment locations values) :
    ∃ encoded, Domain.read environment references = some encoded ∧
      roleOutputSorts role scopes types = some (encoded.map Domain.Value.sort) := by
  obtain ⟨encoded, encoding, read⟩ := outputReferences_read values checked related
  exact ⟨encoded, read, roleOutputValues_sorts role values encoding⟩

/-- The source profile alone decides whether the returned row includes a
transcript. A candidate supplies only its physical location. -/
def profileReferences (context : Context) (data : List Nat) (history : Option Nat) : Option (List Nat) :=
  match context.profile, history with
  | .plain, none => some data
  | .fiatShamir _, some reference => some (data ++ [reference])
  | _, _ => none

/-- The nominated transcript slot contains the exact reached source history.
Plain profiles have no transcript slot to invent or silently discard. -/
def HistoryLocation (context : Context) (reference : Option Nat)
    (environment : Domain.Environment carriers) (history : Domain.History carriers) : Prop :=
  match context.profile, reference with
  | .plain, none => True
  | .fiatShamir replacement, some reference =>
      environment[reference]? = some (.transcript replacement.suite history)
  | _, _ => False

theorem profileReferences_read {context : Context} {dataReferences references : List Nat}
    {historyReference : Option Nat} {environment data : Domain.Environment carriers}
    {history : Domain.History carriers}
    (checked : profileReferences context dataReferences historyReference = some references)
    (read : Domain.read environment dataReferences = some data)
    (located : HistoryLocation context historyReference environment history) :
    Domain.read environment references = some (Domain.inputFrame context data history) := by
  cases profile : context.profile with
  | plain =>
    cases historyReference with
    | none =>
      simp only [profileReferences, profile, Option.some.injEq] at checked
      subst references
      simpa only [Domain.inputFrame, profile] using read
    | some _ => simp [HistoryLocation, profile] at located
  | fiatShamir replacement =>
    cases historyReference with
    | none => simp [HistoryLocation, profile] at located
    | some reference =>
      simp only [profileReferences, profile, Option.some.injEq] at checked
      subst references
      change dataReferences.mapM (fun reference => environment[reference]?) = some data at read
      have located : environment[reference]? = some (.transcript replacement.suite history) := by
        simpa only [HistoryLocation, profile] using located
      simp [Domain.read, List.mapM_append, List.mapM_cons, read, located, Domain.inputFrame, profile]

/-- Assemble complete root returns from the finite physical layout, using the
source-owned schema. Every semantic premise is a local readback or exact
source frame fact; no acceptance-only equation can discharge the contract. -/
theorem CompleteReturns.of_layout {signature : Structured.ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    {source : Values (Component carriers.Value) signature.outputs × State carriers}
    {target : Domain.Result carriers}
    {locations : List Location} {dataReferences : List Nat} {historyReference : Option Nat}
    {dataSorts : List ValueSort}
    (schema : roleOutputSorts role signature.outputScopes signature.outputs = some dataSorts)
    (outputs : artifact.outputs = profileOutputSorts context dataSorts)
    (checked : outputReferences role signature.outputScopes locations = some dataReferences)
    (profile : profileReferences context dataReferences historyReference = some artifact.returned)
    (related : ValuesHolds target.environment locations source.1)
    (history : HistoryLocation context historyReference target.environment source.2.history)
    (returned : Domain.read target.environment artifact.returned = some target.values)
    (closed : source.2.frames = []) : CompleteReturns signature context role artifact source target := by
  obtain ⟨data, encoded, dataRead⟩ := outputReferences_read source.1 checked related
  have fullRead := profileReferences_read profile dataRead history
  have values : target.values = Domain.inputFrame context data source.2.history :=
    Option.some.inj (returned.symm.trans fullRead)
  have dataTypes : data.map Domain.Value.sort = dataSorts :=
    Option.some.inj ((roleOutputValues_sorts role source.1 encoded).symm.trans schema)
  refine ⟨⟨dataSorts, schema, outputs⟩, ⟨data, encoded, values⟩, returned, ?_, closed⟩
  rw [values, outputs]
  cases selected : context.profile <;>
    simp [Domain.sortsMatch, Domain.inputFrame, profileOutputSorts, selected, dataTypes, Domain.Value.sort]

end Zkc.Construction.Original
