module

public import Zkc.Construction.ConnectionMathRegionSoundness
public import Zkc.Construction.ConnectionApplicationFrame
public import Zkc.Construction.ConnectionComputation
public import Zkc.Source.Structured.DomainLinking

@[expose] public section

/-! Caller reconstruction at an inlined Math boundary. The actual complete
source body supplies the returned values. The physical frame may contain
intermediate cells, but those cells have no invented source meaning. The caller's
history and source state are unchanged by the closed computation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionMathApplication
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

/-- Preserve the caller, mark internal temporaries unused, then install the
complete returned tuple at its checked physical coordinates. -/
def layout {scope : Scope} (before : Layout scope) (extent : Nat)
    (types : List Ty) (references : List Nat) : Layout (.tuple types :: scope) :=
  installComponents (readComps types) (references.map Original.Location.data)
    (before.map (Cell.rename .there) ++ List.replicate (extent - before.length) .unused)

theorem exit {model : DomainModel} {scope : Scope} (binders : Binders model scope)
    {history : Domain.History model.toCarriers} {before : Layout scope}
    {environment frame : Domain.Environment model.toCarriers}
    (related : Holds model binders history before environment)
    (retained : ArtifactBinding.Captures environment frame)
    (extent : Nat) (size : frame.length = extent)
    {types : List Ty} (values : Values model.Value types) (references : List Nat)
    (read : Original.ValuesHolds frame (references.map Original.Location.data) values.present) :
    Holds model (.cons values.present binders) history (layout before extent types references) frame := by
  have split : frame = environment ++ frame.drop environment.length := by
    calc
      frame = frame.take environment.length ++ frame.drop environment.length :=
        (List.take_append_drop environment.length frame).symm
      _ = environment ++ frame.drop environment.length := by rw [retained]
  have rest := Holds.unused (show Binders model (.tuple types :: scope) from .cons values.present binders)
    history (frame.drop environment.length)
  have base := (related.rename (target := .tuple types :: scope) .there
    (next := .cons values.present binders) (fun _ => rfl)).append rest
  rw [← split] at base
  have remaining : (frame.drop environment.length).length = extent - before.length := by
    simp only [List.length_drop, size, related.length]
  rw [remaining] at base
  exact installComponents_holds (.cons values.present binders) base (readComps types)
    (references.map Original.Location.data)
    (by simpa only [comps_eval_reads] using read)

end Zkc.Construction.ConnectionMathApplication

namespace Zkc.Construction.ConnectionMathRegion
open Zkc.Source Zkc.Source.Structured

/-- Exact declaration lookup exposes the actual body under its own lexical
prefix, including all stopping behavior. No mathematical reference is used. -/
theorem Declaration.invoke (model : DomainModel)
    {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (association : Declaration definitions definition)
    (values : Values model.Value definition.inputs) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      definition.helper values =
      definition.body.denote (meaning model association.before) values.get := by
  rcases association with ⟨before, after, declarations, fresh⟩
  subst definitions
  rw [List.foldl_append, List.foldl_cons,
    Evaluation.invoke_foldl_otherOn model SiteObservations.closed _ after definition.helper]
  · simp [Evaluation.extendMeaningsOn, Zkc.Source.Structured.invoke]
    rfl
  · intro other present
    have different := List.all_eq_true.mp fresh other present
    simpa only [bne_iff_ne, CheckedDefinition.helper] using different

end Zkc.Construction.ConnectionMathRegion
