module

public import Zkc.Construction.ConnectionFrame
public import Zkc.Construction.DomainViewLaws

@[expose] public section

/-! Symbolic transcript and loop-coordinate readback. The static layout fixes
ordered source terms, while the existing view reads the actual reached values.
Neither a loop bound nor equality of two runtime indices substitutes for that
ordered correspondence. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured
variable {model : DomainModel} {scope : NormalForm.Scope}
  {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
  {layout : Layout scope} {environment : Domain.Environment model.toCarriers}

/-- Only a cell designated for the current history supplies a transcript. -/
theorem Holds.readHistory (related : Holds model binders history layout environment)
    {reference : Nat} {suite : String} (checked : layout[reference]? = some (.history suite)) :
    environment[reference]? = some (.transcript suite history) := by
  obtain ⟨physical, read, meaning⟩ := related.lookup checked
  exact meaning ▸ read

/-- The entire ordered coordinate list is retained, including repeated values. -/
theorem Holds.coordinates (related : Holds model binders history layout environment)
    {reference : Nat} {terms : List (NormalForm.Term [] scope .index)}
    (checked : layout[reference]? = some (.coordinates terms)) :
    environment[reference]? = some (.indices
      (terms.map fun term => term.eval (NormalForm.LawResults.empty model) binders)) := by
  obtain ⟨physical, read, meaning⟩ := related.lookup checked
  exact meaning ▸ read

/-- A tracked total index term yields its exact nominal physical value. -/
theorem Holds.index (related : Holds model binders history layout environment)
    {reference : Nat} {term : NormalForm.Term [] scope .index}
    (checked : layout[reference]? = some (.data (.present term))) :
    environment[reference]? = some (.data (.index
      (term.eval (NormalForm.LawResults.empty model) binders))) := by
  obtain ⟨value, physical, present, encoded, read⟩ := related.data checked
  have same : term.eval (NormalForm.LawResults.empty model) binders = value :=
    Option.some.inj present
  subst value
  have physicalEq : physical = .data (.index
      (term.eval (NormalForm.LawResults.empty model) binders)) := (Option.some.inj encoded).symm
  exact physicalEq ▸ read

/-- An empty coordinate instruction appends a tracked empty coordinate cell. -/
theorem Holds.indicesEmpty (related : Holds model binders history layout environment) :
    Holds model binders history (layout ++ [.coordinates []]) (environment ++ [.indices []]) :=
  related.append (.cons rfl .nil)

/-- Appending a loop index preserves the other cells and the full ordered path.
Both operands are checked against the source-term layout before evaluation. -/
theorem Holds.indicesAppend (related : Holds model binders history layout environment)
    {coordinateRef indexRef : Nat} {terms : List (NormalForm.Term [] scope .index)}
    {term : NormalForm.Term [] scope .index}
    (coordinates : layout[coordinateRef]? = some (.coordinates terms))
    (index : layout[indexRef]? = some (.data (.present term))) :
    Domain.View.indicesAppend coordinateRef indexRef [.indices] environment =
      .done (environment ++ [.indices
        ((terms ++ [term]).map fun value => value.eval (NormalForm.LawResults.empty model) binders)]) ∧
    Holds model binders history (layout ++ [.coordinates (terms ++ [term])])
      (environment ++ [.indices
        ((terms ++ [term]).map fun value => value.eval (NormalForm.LawResults.empty model) binders)]) := by
  constructor
  · simpa only [List.map_append, List.map_cons, List.map_nil] using
      Domain.View.indicesAppend_eq coordinateRef indexRef environment _ _
        (related.coordinates coordinates) (related.index index)
  · exact related.append (.cons rfl .nil)

end Zkc.Construction.ConnectionFrame
