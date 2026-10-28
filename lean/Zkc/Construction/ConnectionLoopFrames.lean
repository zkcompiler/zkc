module

public import Zkc.Construction.ConnectionLoops

@[expose] public section

/-! Compose occurrence loops with a fixed enclosing frame stack. The carried
interface is the complete source-owned tuple and reached history. A callback
must preserve the exact enclosing frames, including through a nested loop. -/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

def FramedCarriedValues (context : Context) (role : Nat) (scopes : List (List Nat))
    (frames : Frames) {types : List Structured.Ty}
    (source : Values (Component carriers.Value) types × State carriers)
    (carried : Domain.Environment carriers) : Prop :=
  source.2.frames = frames ∧ CarriedValues context role scopes source carried

/-- The callback is uniform in count, index, optional state and history. Fixed
outer frames are part of the structural interface, rather than a property of
field values or an assumed equation for the source body. -/
def Simulation.framedRepeat
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
    (frames : Frames)
    (callback : ∀ value state carried index,
      FramedCarriedValues routing.context role (context.mapScopes spec.stateScopes) frames (value,state) carried →
      Simulation (IterationReturns
        (FramedCarriedValues routing.context role (context.mapScopes spec.stateScopes) frames)
        state.frames (Structured.qualifyProtocolSite context.applicationPrefix site) index yielded
        (profileOutputSorts routing.context dataSorts))
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing (sourceBody (.cons (some index)
          ((Structured.maskValues role (context.mapScopes spec.stateScopes) value).append captures)))
          {state with frames := state.frames ++
            [⟨Structured.qualifyProtocolSite context.applicationPrefix site,index⟩]})
        (body (captured ++ .data (.index index) :: carried)))
    (count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (value : Values (Component carriers.Value) spec.state) (state : State carriers)
    (carried : Domain.Environment carriers)
    (initialRead : Domain.read captured initialReferences = some carried)
    (related : FramedCarriedValues routing.context role (context.mapScopes spec.stateScopes)
      frames (value,state) carried) :
    Simulation (fun original final => ∃ next,
      FramedCarriedValues routing.context role (context.mapScopes spec.stateScopes) frames original next ∧
        final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (Structured.denoteRepeatOn spec context role (some count) value captures
        sourceBody Structured.Occurrence.iterations site) state)
      (Domain.View.loop spec.maximum yielded countReference initialReferences
        (profileOutputSorts routing.context dataSorts) body captured) :=
  Simulation.occurrenceRepeat routing spec context role active captures sourceBody site body captured
    yielded (profileOutputSorts routing.context dataSorts)
    (FramedCarriedValues routing.context role (context.mapScopes spec.stateScopes) frames)
    (fun _ _ holds => ⟨holds.1,holds.2.mask⟩) callback (fun _ _ holds => holds.2.sorts schema)
    count countReference initialReferences countRead value state carried initialRead
    (related.2.sorts schema) ⟨related.1,related.2.mask⟩

end Zkc.Construction.Original
