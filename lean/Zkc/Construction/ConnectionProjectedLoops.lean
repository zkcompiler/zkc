module

public import Zkc.Construction.ConnectionProjectedFrames

@[expose] public section

/-! Repeat correspondence whose callback relation observes the source-owned
role mask. This permits private callback results without exposing them as
physical carried state and preserves the actual source mask after each step. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

def ProjectedCarried (context : Context) (role : Nat) (scopes : List (List Nat))
    (frames : Frames) {types : List Ty}
    (source : Values (Component carriers.Value) types × State carriers)
    (carried : Domain.Environment carriers) : Prop :=
  FramedCarriedValues context role scopes frames (maskValues role scopes source.1, source.2) carried

theorem ProjectedCarried.mask {context : Context} {role : Nat} {scopes : List (List Nat)}
    {frames : Frames} {types : List Ty}
    {source : Values (Component carriers.Value) types × State carriers}
    {carried : Domain.Environment carriers} (related : ProjectedCarried context role scopes frames source carried) :
    ProjectedCarried context role scopes frames (maskValues role scopes source.1, source.2) carried := by
  simpa only [ProjectedCarried, maskValues_idempotent] using related

noncomputable def Simulation.projectedFramedRepeat
    (routing : Routing) (spec : RepeatSpec) (context : ProtocolContext) (role : Nat)
    (active : (spec.roles.map context.roles).contains role = true)
    (captures : Values (Component carriers.Value) spec.captures)
    (sourceBody : RegionFunction (Component carriers.Value) (Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (body : Domain.View.Block carriers)
    (captured : Domain.Environment carriers) (yielded : List Nat) (dataSorts : List ValueSort)
    (schema : roleOutputSorts role (context.mapScopes spec.stateScopes) spec.state = some dataSorts)
    (frames : Frames)
    (callback : ∀ value state carried index,
      ProjectedCarried routing.context role (context.mapScopes spec.stateScopes) frames (value,state) carried →
      Simulation (IterationReturns
        (ProjectedCarried routing.context role (context.mapScopes spec.stateScopes) frames)
        state.frames (qualifyProtocolSite context.applicationPrefix site) index yielded
        (profileOutputSorts routing.context dataSorts))
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing (sourceBody (.cons (some index)
          ((maskValues role (context.mapScopes spec.stateScopes) value).append captures)))
          {state with frames := state.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩]})
        (body (captured ++ .data (.index index) :: carried)))
    (count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (value : Values (Component carriers.Value) spec.state) (state : State carriers)
    (carried : Domain.Environment carriers)
    (initialRead : Domain.read captured initialReferences = some carried)
    (related : ProjectedCarried routing.context role (context.mapScopes spec.stateScopes) frames (value,state) carried) :
    Simulation (fun original final => ∃ next,
      ProjectedCarried routing.context role (context.mapScopes spec.stateScopes) frames original next ∧
        final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (denoteRepeatOn spec context role (some count) value captures sourceBody Occurrence.iterations site) state)
      (Domain.View.loop spec.maximum yielded countReference initialReferences
        (profileOutputSorts routing.context dataSorts) body captured) :=
  Simulation.occurrenceRepeat routing spec context role active captures sourceBody site body captured yielded
    (profileOutputSorts routing.context dataSorts)
    (ProjectedCarried routing.context role (context.mapScopes spec.stateScopes) frames)
    (fun _ _ holds => holds.mask) callback (fun _ _ holds => holds.2.sorts schema)
    count countReference initialReferences countRead value state carried initialRead
    (related.2.sorts schema) related.mask

/-- Reapplying the source output mask does not change any effect, stop or
returned repeat value. This is a structural finite-fold proof. -/
theorem repeat_masked {I : PIR.Signature} (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat) (state : Values (Component carriers.Value) spec.state)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I (.index :: (spec.state ++ spec.captures), spec.state))
    (iterations : IterationObservations I) (site : String) :
    (denoteRepeatOn spec context self count state captures body iterations site).bind
      (fun values => .done (maskValues self (context.mapScopes spec.stateScopes) values)) =
      denoteRepeatOn spec context self count state captures body iterations site := by
  have folded : ∀ indices values, maskValues self (context.mapScopes spec.stateScopes) values = values →
      (Finite.fold (fun values index => Repeat.stepOn spec context self captures body values index iterations site)
        indices values).bind (fun values => .done (maskValues self (context.mapScopes spec.stateScopes) values)) =
      Finite.fold (fun values index => Repeat.stepOn spec context self captures body values index iterations site) indices values := by
    intro indices
    induction indices with
    | nil => intro values masked; simp only [Finite.fold, PIR.Process.bind, masked]
    | cons index indices ih =>
      intro values _masked
      simp only [Finite.fold, Repeat.stepOn, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext results
      exact ih _ (maskValues_idempotent _ _ _)
  by_cases active : (spec.roles.map context.roles).contains self = true
  · cases count with
    | none => simp only [denoteRepeatOn, active, ↓reduceIte, PIR.Process.bind]
    | some count =>
      by_cases bounded : count ≤ spec.maximum
      · simp only [denoteRepeatOn, active, bounded, ↓reduceIte, Finite.execute]
        exact folded _ _ (maskValues_idempotent _ _ _)
      · simp only [denoteRepeatOn, active, bounded, ↓reduceIte, PIR.Process.bind]
  · unfold denoteRepeatOn
    rw [ite_eq_right active]
    simp only [PIR.Process.bind, maskValues_absent]


theorem repeat_bind_mask {I : PIR.Signature} {A : Type}
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat) (state : Values (Component carriers.Value) spec.state)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I (.index :: (spec.state ++ spec.captures), spec.state))
    (iterations : IterationObservations I) (site : String)
    (next : Values (Component carriers.Value) spec.state → PIR.Process I A) :
    (denoteRepeatOn spec context self count state captures body iterations site).bind next =
    (denoteRepeatOn spec context self count state captures body iterations site).bind
      (fun values => next (maskValues self (context.mapScopes spec.stateScopes) values)) := by
  calc
    _ = ((denoteRepeatOn spec context self count state captures body iterations site).bind
        (fun values => .done (maskValues self (context.mapScopes spec.stateScopes) values))).bind next :=
      congrArg (fun process => process.bind next) (repeat_masked spec context self count state captures body iterations site).symm
    _ = _ := by rw [PIR.Process.bind_assoc]; rfl

end Zkc.Construction.Original
