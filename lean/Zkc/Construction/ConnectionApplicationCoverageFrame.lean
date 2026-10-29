module

public import Zkc.Construction.ConnectionApplicationFrame

@[expose] public section

/-! Presence witnesses for the independent route induction. These witnesses do
not assert that the target executes: immutable captures and selected source
components alone reconstruct a well formed continuation frame. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

private def fitFrame {carriers : Carriers} (extent : Nat) (frame : Domain.Environment carriers) :=
  frame.take extent ++ List.replicate (extent - frame.length) (.indices [])

private theorem fitFrame_length {carriers : Carriers} (extent : Nat) (frame : Domain.Environment carriers) :
    (fitFrame extent frame).length = extent := by
  simp only [fitFrame, List.length_append, List.length_take, List.length_replicate]
  omega

private theorem fitFrame_read {carriers : Carriers} {extent reference : Nat}
    {frame : Domain.Environment carriers} {value : Domain.Value carriers}
    (bound : reference < extent) (found : frame[reference]? = some value) :
    (fitFrame extent frame)[reference]? = some value := by
  have inFrame : reference < frame.length := List.getElem?_eq_some_iff.mp found |>.1
  rw [fitFrame, List.getElem?_append_left (by simp only [List.length_take]; omega),
    List.getElem?_take_of_lt bound, found]

private theorem fitFrame_captures {carriers : Carriers} {extent : Nat}
    {captured frame : Domain.Environment carriers} (bound : captured.length ≤ extent)
    (retained : ArtifactBinding.Captures captured frame) :
    ArtifactBinding.Captures captured (fitFrame extent frame) := by
  have size := congrArg List.length retained
  simp only [List.length_take] at size
  change (fitFrame extent frame).take captured.length = captured
  rw [fitFrame, List.take_append_of_le_length (by simp only [List.length_take]; omega),
    List.take_take, Nat.min_eq_left bound]
  exact retained

private theorem valuesHolds_transport {model : DomainModel} {types : List Ty}
    {before after : Domain.Environment model.toCarriers} (outputs : List Original.Location)
    (values : Values (Component model.Value) types)
    (read : Original.ValuesHolds before outputs values)
    (same : ∀ reference, .data reference ∈ outputs → ∀ value,
      before[reference]? = some value → after[reference]? = some value) :
    Original.ValuesHolds after outputs values := by
  induction values generalizing outputs with
  | nil => cases outputs <;> exact read
  | @cons ty types value values ih =>
    cases outputs with
    | nil => exact False.elim read
    | cons location outputs =>
      refine ⟨?_, ih outputs read.2 (fun reference member => same reference (by simp [member]))⟩
      cases location with
      | absent => exact read.1
      | capability handle => cases ty <;> exact read.1
      | data reference =>
        obtain ⟨actual, present, decoded⟩ := read.1
        refine ⟨actual, present, ?_⟩
        cases found : before[reference]? with
        | none => simp [found] at decoded
        | some physical => simpa only [same reference (by simp) physical found, found, Option.bind_some] using decoded

/-- Reconstruct exactly the admitted physical extent, retaining every caller
cell, every nominal result and the selected history position. -/
theorem applicationWitness {model : DomainModel} {scope : Scope}
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {before frame : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout before)
    (retained : ArtifactBinding.Captures before frame) (extent : Nat)
    {types : List Ty} (values : Values (Component model.Value) types)
    (role : Nat) (scopes : List (List Nat)) (outputs : List Original.Location)
    (read : Original.ValuesHolds frame outputs (maskValues role scopes values))
    (selector : Option Nat) (suite : String)
    (admission : applicationAdmitted layout.length extent outputs selector) :
    ∃ result, ArtifactBinding.Captures before result ∧
      Holds model (.cons values binders) history
        (applicationLayout layout extent role scopes types outputs selector suite) result := by
  have bound : before.length ≤ extent := by rw [← related.length]; exact admission.1
  have kept := fitFrame_captures bound retained
  have outputBound : ∀ reference, .data reference ∈ outputs → reference < extent := by
    intro reference member
    have check := List.all_eq_true.mp admission.2.1 (.data reference) member
    simpa using check
  have readFit := valuesHolds_transport outputs (maskValues role scopes values) read
    (fun reference member _ found => fitFrame_read (outputBound reference member) found)
  cases selector with
  | none =>
    exact ⟨fitFrame extent frame, kept, related.applicationExit binders kept extent
      (fitFrame_length _ _) values role scopes outputs readFit none suite trivial⟩
  | some reference =>
    obtain ⟨fresh, inFrame, separate⟩ := admission.2.2
    let result := (fitFrame extent frame).set reference (.transcript suite history)
    have keptResult : ArtifactBinding.Captures before result := by
      change result.take before.length = before
      dsimp only [result]
      rw [List.take_set_of_le (by rw [← related.length]; exact fresh)]
      exact kept
    have resultSize : result.length = extent := by simp [result, fitFrame_length]
    have readResult := valuesHolds_transport (after := result) outputs (maskValues role scopes values) readFit
      (fun ref member _ found => by
        have different : reference ≠ ref := by intro same; subst ref; exact separate member
        simpa only [result, List.getElem?_set_ne different] using found)
    have historyRead : result[reference]? = some (.transcript suite history) :=
      List.getElem?_set_self (by simpa only [fitFrame_length] using inFrame)
    exact ⟨result, keptResult, related.applicationExit binders keptResult extent resultSize values
      role scopes outputs readResult (some reference) suite historyRead⟩

end Zkc.Construction.ConnectionFrame
