module

public import Zkc.Construction.ConnectionOutputs
public import Zkc.Construction.OriginalLoop

@[expose] public section

/-! Source-owned loop interfaces for structural connection certificates.

The source role and carried-state scopes fix the data schema. The construction
profile fixes the history slot. A proposed layout chooses physical references,
not a weaker carried relation or a protocol-specific invariant. Mathematical
loop invariants belong to property derivations and are not used here.
-/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

/-- The entire role-visible carried tuple and the exact reached history.
Hidden source components must be absent. Private data is retained when visible
to this role, even if it has no bearing on the validator's acceptance bit. -/
def CarriedValues (context : Context) (role : Nat) (scopes : List (List Nat))
    {types : List Structured.Ty}
    (source : Values (Component carriers.Value) types × State carriers)
    (carried : Domain.Environment carriers) : Prop :=
  ∃ data, roleOutputValues role scopes source.1 = some data ∧
    carried = Domain.inputFrame context data source.2.history

theorem CarriedValues.mask {context : Context} {role : Nat} {scopes : List (List Nat)}
    {types : List Structured.Ty}
    {source : Values (Component carriers.Value) types × State carriers}
    {carried : Domain.Environment carriers}
    (related : CarriedValues context role scopes source carried) :
    CarriedValues context role scopes (Structured.maskValues role scopes source.1, source.2) carried := by
  obtain ⟨data, encoded, frame⟩ := related
  rw [roleOutputValues_mask role source.1 encoded]
  exact ⟨data, encoded, frame⟩

theorem CarriedValues.sorts {context : Context} {role : Nat} {scopes : List (List Nat)}
    {types : List Structured.Ty} {declared : List ValueSort}
    (schema : roleOutputSorts role scopes types = some declared)
    {source : Values (Component carriers.Value) types × State carriers}
    {carried : Domain.Environment carriers}
    (related : CarriedValues context role scopes source carried) :
    Domain.sortsMatch (profileOutputSorts context declared) carried = true := by
  obtain ⟨data, encoded, frame⟩ := related
  have sorts : data.map Domain.Value.sort = declared :=
    Option.some.inj ((roleOutputValues_sorts role source.1 encoded).symm.trans schema)
  rw [frame]
  cases profile : context.profile <;>
    simp [Domain.sortsMatch, Domain.inputFrame, profileOutputSorts, profile, sorts, Domain.Value.sort]

/-- The structural repeat rule derives masking and sort invariants from the
source-owned interface. Its callback covers all indices, optional source
states, histories and typed replies; it never unrolls a runtime count. Only
physical readbacks and the recursively checked callback remain to be built. -/
def Simulation.encodedRepeat
    (routing : Routing) (spec : Structured.RepeatSpec)
    (context : Structured.ProtocolContext) (role : Nat)
    (active : (spec.roles.map context.roles).contains role = true)
    (captures : Values (Component carriers.Value) spec.captures)
    (sourceBody : RegionFunction (Component carriers.Value)
      (Structured.Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (body : Domain.View.Block carriers)
    (captured : Domain.Environment carriers) (yielded : List Nat) (dataSorts : List ValueSort)
    (schema : roleOutputSorts role (context.mapScopes spec.stateScopes) spec.state = some dataSorts)
    (callback : ∀ value state carried index,
      CarriedValues routing.context role (context.mapScopes spec.stateScopes) (value, state) carried →
      Simulation (IterationReturns (CarriedValues routing.context role (context.mapScopes spec.stateScopes))
        state.frames (Structured.qualifyProtocolSite context.applicationPrefix site) index yielded
        (profileOutputSorts routing.context dataSorts))
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing
          (sourceBody (.cons (some index)
            ((Structured.maskValues role (context.mapScopes spec.stateScopes) value).append captures)))
          { state with frames := state.frames ++
            [⟨Structured.qualifyProtocolSite context.applicationPrefix site, index⟩] })
        (body (captured ++ .data (.index index) :: carried)))
    (count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (value : Values (Component carriers.Value) spec.state) (state : State carriers)
    (carried : Domain.Environment carriers)
    (initialRead : Domain.read captured initialReferences = some carried)
    (related : CarriedValues routing.context role (context.mapScopes spec.stateScopes)
      (value, state) carried) :
    Simulation
      (fun original final => ∃ next,
        CarriedValues routing.context role (context.mapScopes spec.stateScopes) original next ∧
        final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (Structured.denoteRepeatOn spec context role (some count) value
        captures sourceBody Structured.Occurrence.iterations site) state)
      (Domain.View.loop spec.maximum yielded countReference initialReferences
        (profileOutputSorts routing.context dataSorts) body captured) :=
  Simulation.occurrenceRepeat routing spec context role active captures sourceBody site body captured
    yielded (profileOutputSorts routing.context dataSorts)
    (CarriedValues routing.context role (context.mapScopes spec.stateScopes))
    (fun _ _ holds => holds.mask) callback (fun _ _ holds => holds.sorts schema)
    count countReference initialReferences countRead value state carried initialRead
    (related.sorts schema) related.mask

end Zkc.Construction.Original
