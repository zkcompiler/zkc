module

public import Zkc.Construction.ConnectionFrame
public import Zkc.Construction.OriginalInputs

@[expose] public section

/-! Root input assembly for connection certificates. The source ABI fixes the
presence of every component and the identity of every service capability.
Finite layout checks then recover the initial symbolic frame from that same
ABI. No instance supplies a relation between whole programs. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionInputs
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

/-- Input patterns obtained from the actual ABI. Literal data specializations
are deliberately absent: a decoded data input remains arbitrary. -/
inductive Shape : {types : List Ty} → InputPattern types → List Original.Location → Type where
  | nil : Shape .nil []
  | absent {ty : Ty} {types : List Ty} {pattern : InputPattern types} {locations : List Original.Location}
      (tail : Shape pattern locations) : Shape (.cons (.absent (ty := ty)) pattern) (.absent :: locations)
  | data {ty : Ty} {types : List Ty} {pattern : InputPattern types} {locations : List Original.Location}
      (reference : Nat) (allowed : ty.isService = false) (tail : Shape pattern locations) :
      Shape (.cons (.present (ty := ty)) pattern) (.data reference :: locations)
  | capability {service : String} {handle : Nat} {types : List Ty}
      {pattern : InputPattern types} {locations : List Original.Location}
      (tail : Shape pattern locations) :
      Shape (.cons (.capability service handle) pattern) (.capability handle :: locations)

/-- Every successfully decoded input tuple supplies precisely the binders of
its ABI-derived pattern. In particular no service handle is chosen by a proof. -/
theorem Shape.binders {model : DomainModel} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} (shape : Shape pattern locations)
    (frame : Domain.Environment model.toCarriers) (values : Values (Component model.Value) types)
    (related : Original.ValuesHolds frame locations values) :
    ∃ binders : Binders model pattern.scope, pattern.environment model binders = values := by
  induction shape with
  | nil => cases values; exact ⟨.nil, rfl⟩
  | absent tail ih =>
    cases values with
    | cons value rest =>
      obtain ⟨binders, same⟩ := ih rest related.2
      exact ⟨binders, congrArg₂ (fun head tail => Values.cons head tail) related.1.symm same⟩
  | data reference allowed tail ih =>
    cases values with
    | cons value rest =>
      obtain ⟨actual, present, read⟩ := related.1
      obtain ⟨binders, same⟩ := ih rest related.2
      exact ⟨.cons actual binders, congrArg₂ (fun head tail => Values.cons head tail) present.symm same⟩
  | capability tail ih =>
    cases values with
    | cons value rest =>
      obtain ⟨binders, same⟩ := ih rest related.2
      exact ⟨binders, congrArg₂ (fun head tail => Values.cons head tail) related.1.symm same⟩

private theorem valuesHolds_at {carriers : Carriers} {types : List Ty}
    {frame : Domain.Environment carriers} {locations : List Original.Location}
    (values : Values (Component carriers.Value) types)
    (related : Original.ValuesHolds frame locations values) {ty : Ty} (position : Var types ty)
    {location : Original.Location} (selected : locations[position.index]? = some location) :
    Original.ComponentHolds frame location ty (values.get position) := by
  induction values generalizing locations with
  | nil => cases position
  | cons value rest ih =>
    cases locations with
    | nil => exact False.elim related
    | cons head tail =>
      cases position with
      | here =>
        simp only [Var.index, List.getElem?_cons_zero, Option.some.injEq] at selected
        subst location
        exact related.1
      | there position =>
        exact ih related.2 position (by simpa only [Var.index, List.getElem?_cons_succ] using selected)

/-- A physical cell is either a selected source input, the source's initial
history, or unused. Every choice carries only finite location/type checks. -/
inductive InitialCell {types : List Ty} (pattern : InputPattern types)
    (locations : List Original.Location) (suite : String) (historySlot : Option Nat) :
    Nat → Cell pattern.scope → Type where
  | input {ty : Ty} (position : Var types ty) (reference : Nat)
      (selected : locations[position.index]? = some (.data reference)) :
      InitialCell pattern locations suite historySlot reference (.data (pattern.initial.get position))
  | history (reference : Nat) (selected : historySlot = some reference) :
      InitialCell pattern locations suite historySlot reference (.history suite)
  | unused (reference : Nat) : InitialCell pattern locations suite historySlot reference .unused

/-- A finite row of input-cell checks; the physical reference increases exactly
once per cell, so aliases cannot hide a dropped or additional physical slot. -/
inductive InitialLayout {types : List Ty} (pattern : InputPattern types)
    (locations : List Original.Location) (suite : String) (historySlot : Option Nat) :
    Nat → Layout pattern.scope → Type where
  | nil (start : Nat) : InitialLayout pattern locations suite historySlot start []
  | cons {start : Nat} {cell : Cell pattern.scope} {rest : Layout pattern.scope}
      (head : InitialCell pattern locations suite historySlot start cell)
      (tail : InitialLayout pattern locations suite historySlot (start + 1) rest) :
      InitialLayout pattern locations suite historySlot start (cell :: rest)

theorem InitialCell.sound {model : DomainModel} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} {suite : String} {historySlot : Option Nat}
    {reference : Nat} {cell : Cell pattern.scope}
    (checked : InitialCell pattern locations suite historySlot reference cell)
    (binders : Binders model pattern.scope) (history : Domain.History model.toCarriers)
    (frame : Domain.Environment model.toCarriers)
    (inputs : Original.ValuesHolds frame locations (pattern.environment model binders))
    (readHistory : ∀ slot, historySlot = some slot → frame[slot]? = some (.transcript suite history))
    (physical : Domain.Value model.toCarriers) (read : frame[reference]? = some physical) :
    Cell.Holds model binders history cell physical := by
  cases checked with
  | input position reference selected =>
    obtain ⟨actual, present, decoded⟩ := valuesHolds_at _ inputs position selected
    have evaluated : (pattern.initial.get position).eval (LawResults.empty model) binders = some actual := by
      rw [← comps_get_eval, initial_eval]
      exact present
    have decode : physical.decode _ = some actual := by simpa only [read, Option.bind_some] using decoded
    exact ⟨actual, evaluated, Domain.Value.encode_decode decode⟩
  | history reference selected => exact Option.some.inj (read.symm.trans (readHistory reference selected))
  | unused => trivial

def InitialLayout.at {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} {suite : String} {historySlot : Option Nat} :
    {start : Nat} → {layout : Layout pattern.scope} →
    InitialLayout pattern locations suite historySlot start layout →
    (index : Nat) → {cell : Cell pattern.scope} → layout[index]? = some cell →
    InitialCell pattern locations suite historySlot (start + index) cell
  | _, _, .nil _, _, _, selected => by simp at selected
  | _, _, .cons head _, 0, _, selected => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
    subst selected
    exact head
  | _, _, .cons _ tail, index + 1, _, selected => by
    simpa only [Nat.add_assoc, Nat.add_comm 1 index] using
      tail.at index (by simpa only [List.getElem?_cons_succ] using selected)

/-- Initial frame assembly is shared by all protocols. The sole runtime
premises are the actual ABI decoding, row length and initial history readback. -/
theorem InitialLayout.sound {model : DomainModel} {types : List Ty} {pattern : InputPattern types}
    {locations : List Original.Location} {suite : String} {historySlot : Option Nat}
    {layout : Layout pattern.scope}
    (checked : InitialLayout pattern locations suite historySlot 0 layout)
    (binders : Binders model pattern.scope) (history : Domain.History model.toCarriers)
    (frame : Domain.Environment model.toCarriers) (length : layout.length = frame.length)
    (inputs : Original.ValuesHolds frame locations (pattern.environment model binders))
    (readHistory : ∀ slot, historySlot = some slot → frame[slot]? = some (.transcript suite history)) :
    Holds model binders history layout frame := by
  apply List.forall₂_of_length_eq_of_get length
  intro index left right
  exact (checked.at index (by simp)).sound binders history frame inputs readHistory _ (by simp)

end Zkc.Construction.ConnectionInputs
