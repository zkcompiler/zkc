module

public import Zkc.Construction.ConnectionProjectedFrames
public import Zkc.Construction.ConnectionSubstitution

@[expose] public section

/-! Reconstruct the caller's entire SSA frame after a flat application. The
caller prefix is retained cell for cell; fresh temporaries retain their exact
extent and cannot masquerade as source values. Output readback and history
refine only the finitely selected locations. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

/-- Finite admission needed to reconstruct a source-presence witness without
executing the target. A transcript result occupies a fresh, separate cell. -/
def applicationAdmitted (input extent : Nat) (outputs : List Original.Location)
    (history : Option Nat) : Prop :=
  input ≤ extent ∧
  outputs.all (fun | .data reference => reference < extent | _ => true) = true ∧
  match history with
  | none => True
  | some reference => input ≤ reference ∧ reference < extent ∧ .data reference ∉ outputs

instance (input extent : Nat) (outputs : List Original.Location) (history : Option Nat) :
    Decidable (applicationAdmitted input extent outputs history) := by
  unfold applicationAdmitted
  cases history <;> infer_instance

private theorem unused_frame {model : DomainModel} {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) (frame : Domain.Environment model.toCarriers) :
    Holds model binders history (List.replicate frame.length .unused) frame := by
  induction frame with
  | nil => exact .nil
  | cons _ _ ih => exact .cons trivial ih

/-- Install all nominal components in source output order. Locations carry no
permission to discard another logical component. Hidden components consume no
physical cell, while the complete logical tuple remains in the binder. -/
def installComponents {scope : Scope} : {types : List Ty} → Values (Comp [] scope) types →
    List Original.Location → Layout scope → Layout scope
  | _, .nil, _, layout => layout
  | _, .cons component components, locations, layout =>
    let next := match locations.head? with
      | some (.data reference) => layout.set reference (.data component)
      | _ => layout
    installComponents components locations.tail next

theorem installComponents_holds {model : DomainModel} {scope : Scope}
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {frame : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout frame) {types : List Ty}
    (components : Values (Comp [] scope) types) (locations : List Original.Location)
    (read : Original.ValuesHolds frame locations (Comps.eval (LawResults.empty model) components binders)) :
    Holds model binders history (installComponents components locations layout) frame := by
  induction components generalizing locations layout with
  | nil => exact related
  | @cons ty types component components ih =>
    cases locations with
    | nil => exact False.elim read
    | cons location locations =>
      have head := read.1
      have tail := read.2
      cases location with
      | absent => exact ih related locations tail
      | capability handle => exact ih related locations tail
      | data reference =>
        obtain ⟨value, present, decoded⟩ := head
        cases found : frame[reference]? with
        | none => simp [found] at decoded
        | some physical =>
          have encoded := Domain.Value.encode_decode (by simpa [found] using decoded)
          exact ih (related.set reference (.data component) found ⟨value,present,encoded⟩) locations tail

def applicationLayout {scope : Scope} (layout : Layout scope) (extent : Nat)
    (role : Nat) (scopes : List (List Nat)) (types : List Ty)
    (outputs : List Original.Location) (history : Option Nat) (suite : String) : Layout (.tuple types :: scope) :=
  let base := (layout.map Cell.retireHistory).map (Cell.rename .there) ++
    List.replicate (extent - layout.length) .unused
  let values := installComponents (calleeOutputs role scopes (Operands.identity types)) outputs base
  match history with
  | none => values
  | some reference => values.set reference (.history suite)

theorem Holds.applicationExit {model : DomainModel} {scope : Scope}
    (binders : Binders model scope) {oldHistory nextHistory : Domain.History model.toCarriers}
    {layout : Layout scope} {before frame : Domain.Environment model.toCarriers}
    (related : Holds model binders oldHistory layout before)
    (retained : ArtifactBinding.Captures before frame) (extent : Nat) (size : frame.length = extent)
    {types : List Ty} (values : Values (Component model.Value) types)
    (role : Nat) (scopes : List (List Nat)) (outputs : List Original.Location)
    (read : Original.ValuesHolds frame outputs (maskValues role scopes values))
    (history : Option Nat) (suite : String)
    (historyRead : match history with
      | none => True
      | some reference => frame[reference]? = some (.transcript suite nextHistory)) :
    Holds model (.cons values binders) nextHistory
      (applicationLayout layout extent role scopes types outputs history suite) frame := by
  have split : frame = before ++ frame.drop before.length := by
    calc
      frame = frame.take before.length ++ frame.drop before.length := (List.take_append_drop before.length frame).symm
      _ = before ++ frame.drop before.length := by rw [retained]
  have rest := unused_frame (show Binders model (.tuple types :: scope) from .cons values binders)
    nextHistory (frame.drop before.length)
  have base := ((related.retireHistory nextHistory).rename (target := .tuple types :: scope) .there
    (next := .cons values binders) (fun _ => rfl)).append rest
  rw [← split] at base
  have remaining : (frame.drop before.length).length = extent - layout.length := by
    simp only [List.length_drop, size, related.length]
  rw [remaining] at base
  have installed := installComponents_holds (.cons values binders) base
    (calleeOutputs role scopes (Operands.identity types)) outputs (by
      rw [comps_eval_calleeOutputs, ConnectionLibrary.staticMask_identity]
      exact read)
  cases history with
  | none => exact installed
  | some reference => exact installed.set reference (.history suite) historyRead rfl

end Zkc.Construction.ConnectionFrame
