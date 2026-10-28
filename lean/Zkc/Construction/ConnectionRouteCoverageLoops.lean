module

public import Zkc.Construction.ConnectionRouteCoverageFrames

@[expose] public section

/-! Symbolic loop coverage. The invariant concerns complete typed source state,
and the actual ordered occurrence enter/leave boundaries are retained. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRouteCoverage
open Zkc.Source Zkc.Source.Structured

noncomputable def repeatCovered {carriers : Carriers} (routing : Original.Routing)
    (frames : Original.Frames) (spec : RepeatSpec) (context : ProtocolContext) (role : Nat)
    (active : (spec.roles.map context.roles).contains role = true)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) (Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (post : Values (Component carriers.Value) spec.state → Prop)
    (mask : ∀ value, post value → post (maskValues role (context.mapScopes spec.stateScopes) value))
    (law : ∀ value, post value → ∀ index,
      Covered routing post (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
        (frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
        (body (.cons (some index) ((maskValues role (context.mapScopes spec.stateScopes) value).append captures))))
    (count : Nat) (initial : Values (Component carriers.Value) spec.state)
    (holds : post initial) :
    Covered routing post frames frames
      (denoteRepeatOn spec context role (some count) initial captures body Occurrence.iterations site) := by
  simp only [denoteRepeatOn, active, ↓reduceIte]
  split
  · apply Covered.finite
    · intro value holds index
      apply (Covered.within _ _ (law value holds index)).bind
      intro result valid
      exact .done _ _ (mask result valid)
    · exact mask initial holds
  · exact .halt _ _ .refused

end Zkc.Construction.ConnectionRouteCoverage
