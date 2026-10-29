module

public import Zkc.Construction.ConnectionCertificate

@[expose] public section

/-! Reuse checked subframes of a stored connection. This projection preserves
its source form, symbolic frame, target and derivation; it never proposes or
checks another connection. There are no artifact or root-name cases. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarCheckedFrames
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionCertificate

structure Frame (routing : Original.Routing) (definitions : List CheckedDefinition)
    where
  callees : List CalleeKey
  selection : ConnectionLibrary.Selection definitions callees
  context : ProtocolContext
  out : List Ty
  role : Nat
  scopes : List (List Nat)
  outputs : List Original.Location
  history : Option Nat
  scope : Scope
  frames : ScopedFrames scope
  layout : Layout scope
  form : Form [] callees scope out
  target : ConnectionCertificate.Block
  checked : Alignment routing context definitions callees (selection := selection)
    out role scopes outputs history frames layout form target

  roster : Nat
  distinct : RosterDistinct context role roster
  inputTypes : List Ty
  region : Region protocolDialect inputTypes out
  inputs : Values (Comp [] scope) inputTypes
  normalized : normalizeRegion {strict := true, callees := callees} role roster region
    ⟨inputs, inputs⟩ = .ok form

def ofRegion {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees}
    {out : List Ty} {role : Nat} {scopes : List (List Nat)} {outputs : List Original.Location}
    {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : ConnectionCertificate.Block}
    (checked : Alignment routing context definitions callees (selection := selection)
      out role scopes outputs history frames layout form target)
    (roster : Nat) (distinct : RosterDistinct context role roster) {inputTypes : List Ty}
    (region : Region protocolDialect inputTypes out) (inputs : Values (Comp [] scope) inputTypes)
    (normalized : normalizeRegion {strict := true, callees := callees} role roster region ⟨inputs, inputs⟩ = .ok form) :
    Frame routing definitions :=
  ⟨callees, selection, context, out, role, scopes, outputs, history, scope, frames, layout,
    form, target, checked, roster, distinct, inputTypes, region, inputs, normalized⟩

/-- Name a checked frame's output index explicitly, without recomputing its
certificate. The equality is only metadata; every semantic field is retained. -/
def Frame.withOutput {routing : Original.Routing} {definitions : List CheckedDefinition}
    (frame : Frame routing definitions) (out : List Ty) (same : frame.out = out) : Frame routing definitions where
  callees := frame.callees
  selection := frame.selection
  context := frame.context
  out := out
  role := frame.role
  scopes := frame.scopes
  outputs := frame.outputs
  history := frame.history
  scope := frame.scope
  frames := frame.frames
  layout := frame.layout
  form := same ▸ frame.form
  target := frame.target
  checked := by cases same; exact frame.checked
  roster := frame.roster
  distinct := frame.distinct
  inputTypes := frame.inputTypes
  region := same ▸ frame.region
  inputs := frame.inputs
  normalized := by cases same; exact frame.normalized

/-- The body frames of symbolic loops, in source traversal order. -/
def loops {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees}
    {out : List Ty} {role : Nat} {scopes : List (List Nat)} {outputs : List Original.Location}
    {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : ConnectionCertificate.Block} :
    Alignment routing context definitions callees (selection := selection)
      out role scopes outputs history frames layout form target → List (Frame routing definitions)
  | .done .. | .halt _ | .falseGuard .. => []
  | .split _ absent present => loops absent ++ loops present
  | .splitAbsent _ tail => loops tail
  | .splitValue _ _ tail => loops tail
  | .splitPresent _ _ _ _ tail => loops tail
  | .compute _ _ _ _ _ _ tail => loops tail
  | .strictHelper _ _ _ _ _ _ _ _ tail => loops tail
  | .ownedHelper _ _ _ _ _ _ _ _ _ tail => loops tail
  | .mathHelper _ _ _ _ _ _ _ _ _ tail => loops tail
  | .projectionHelper _ _ _ _ tail => loops tail
  | .inlineCalculation _ _ _ _ tail => loops tail
  | .inlineMissingCalculation _ _ _ _ _ tail => loops tail
  | .calculation _ _ _ _ _ _ _ tail => loops tail
  | .receive _ _ _ _ _ _ _ tail => loops tail
  | .send _ _ _ _ _ _ _ _ _ tail => loops tail
  | .observedSend (tail := tail) .. => loops tail
  | .observedReceive (tail := tail) .. => loops tail
  | .delivery (tail := tail) .. => loops tail
  | .indicesEmpty tail => loops tail
  | .indicesAppend _ _ _ _ _ _ tail => loops tail
  | .publicQuery (tail := tail) .. => loops tail
  | .localQuery _ _ _ _ _ _ _ _ _ _ tail => loops tail
  | .repeat (roster := roster) (distinct := distinct) (callback := callback)
      (normalized := normalized) (bodyCertificate := body) (tail := tail) .. =>
      ofRegion body roster distinct callback _ normalized :: (loops body ++ loops tail)
  | .projectedRepeat (roster := roster) (distinct := distinct) (callback := callback)
      (normalized := normalized) (bodyCertificate := body) (tail := tail) .. =>
      ofRegion body roster distinct callback _ normalized :: (loops body ++ loops tail)
  | .application (bodyCertificate := body) (tail := tail) .. => loops body ++ loops tail
  | .applicationRetainedHistory (bodyCertificate := body) (tail := tail) .. => loops body ++ loops tail
  | .guard _ _ _ _ _ tail => loops tail
  | .trueGuard _ _ tail => loops tail

/-- Reuse the normalizer soundness law captured in the stored loop body. -/
theorem Frame.source_eq {payload : UnitPayload} {routing : Original.Routing}
    (frame : Frame routing payload.definitions) (library : ConnectionLibrary.Library payload frame.callees)
    (model : DomainModel) (binders : Binders model frame.scope) :
    frame.region.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (Occurrence.helpers model payload) (Occurrence.table model payload) frame.context frame.role)
      (Comps.eval (LawResults.empty model) frame.inputs binders).get =
    frame.form.denoteOn model Occurrence.actions (Occurrence.helpers model payload)
      (LawResults.empty model) frame.context
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) frame.context frame.role) (library.processes model) binders :=
  normalizeRegion_soundOn (model := model) (actions := Occurrence.actions) (iterations := Occurrence.iterations)
    (tables := Occurrence.helpers model payload) (protocols := Occurrence.table model payload)
    (context := frame.context) {strict := true, callees := frame.callees} (LawResults.empty model)
    (library.processes model) frame.role frame.roster frame.distinct
    (Comps.eval (LawResults.empty model) frame.inputs binders) (LawsHold.empty _ _) (library.holds model _)
    frame.region ⟨frame.inputs, frame.inputs⟩ frame.form frame.normalized
    (frame.form.lawsMatch_of_callsMatch frame.checked.callsMatch) binders rfl

/-- A symbolic cell can be realized using its source value; untracked cells
retain the caller's existing value. This is a frame constructor, not execution. -/
def realizeCell (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) (fallback : Domain.Value model.toCarriers) :
    Cell scope → Option (Domain.Value model.toCarriers)
  | .data component => do
      let value ← component.eval (LawResults.empty model) binders
      Domain.Value.encode _ value
  | .guarded component => do
      let value ← component.eval (LawResults.empty model) binders
      if value then some (.data (.boolean true)) else none
  | .history suite => some (.transcript suite history)
  | .coordinates terms => some (.indices (terms.map (fun term => term.eval (LawResults.empty model) binders)))
  | .unused => some fallback

def realize (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) : Layout scope → Domain.Environment model.toCarriers →
      Option (Domain.Environment model.toCarriers)
  | [], [] => some []
  | cell :: cells, value :: values => do
      let first ← realizeCell model binders history value cell
      let rest ← realize model binders history cells values
      pure (first :: rest)
  | _, _ => none

private theorem realizeCell_holds (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) (fallback : Domain.Value model.toCarriers)
    (cell : Cell scope) (value : Domain.Value model.toCarriers)
    (found : realizeCell model binders history fallback cell = some value) :
    Cell.Holds model binders history cell value := by
  cases cell with
  | data component =>
    simp only [realizeCell] at found
    cases evaluated : component.eval (LawResults.empty model) binders with
    | none => simp [evaluated] at found
    | some actual => exact ⟨actual, evaluated, by simpa [evaluated] using found⟩
  | guarded component =>
    simp only [realizeCell] at found
    cases evaluated : component.eval (LawResults.empty model) binders with
    | none => simp [evaluated] at found
    | some actual =>
      cases actual with
      | false => simp [evaluated] at found
      | true =>
        have same : value = .data (.boolean true) := by simpa [evaluated] using found.symm
        subst value
        exact ⟨⟨true, evaluated, rfl⟩, rfl⟩
  | history | coordinates | unused => simp_all [realizeCell, Cell.Holds]

/-- A successful frame realization supplies the complete generic Holds fact. -/
theorem realize_holds (model : DomainModel) {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) : ∀ layout fallback environment,
    realize model binders history layout fallback = some environment → Holds model binders history layout environment
  | [], [], environment, found => by cases found; exact .nil
  | [], _ :: _, _, found | _ :: _, [], _, found => by cases found
  | cell :: cells, value :: values, environment, found => by
    simp only [realize] at found
    cases first : realizeCell model binders history value cell with
    | none => simp [first] at found
    | some actual =>
      cases rest : realize model binders history cells values with
      | none => simp [first, rest] at found
      | some remaining =>
        simp [first, rest] at found
        subst environment
        exact .cons (realizeCell_holds model binders history value cell actual first)
          (realize_holds model binders history cells values remaining rest)

end Zkc.Construction.Uniform.ScalarCheckedFrames
