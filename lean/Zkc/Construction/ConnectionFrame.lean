module

public import Zkc.Construction.ConnectionLayout
public import Zkc.Source.Structured.NormalForm.Observation

@[expose] public section

/-! Symbolic physical frames for source-normal-form alignment.

Cells contain source terms, never a second arithmetic evaluator. Their meaning
uses the same normalized binders and nominal encoder. History cells refer to
the current reached history; when an event extends it, old history cells lose
that designation. Unused SSA temporaries can remain unconstrained, but cannot
supply a data, transcript or coordinate readback.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured

inductive Cell (scope : NormalForm.Scope) where
  | data {ty : Ty} (component : NormalForm.Comp [] scope ty)
  | history (suite : String)
  | coordinates (values : List (NormalForm.Term [] scope .index))
  | unused

abbrev Layout (scope : NormalForm.Scope) := List (Cell scope)

/-- The current meaning of a proposed physical cell. -/
def Cell.Holds (model : DomainModel) {scope : NormalForm.Scope} (binders : NormalForm.Binders model scope)
    (history : Domain.History model.toCarriers) : Cell scope → Domain.Value model.toCarriers → Prop
  | .data (ty := ty) component, physical =>
      ∃ value, component.eval (NormalForm.LawResults.empty model) binders = some value ∧
        Domain.Value.encode ty value = some physical
  | .history suite, physical => physical = .transcript suite history
  | .coordinates values, physical =>
      physical = .indices (values.map fun term => term.eval (NormalForm.LawResults.empty model) binders)
  | .unused, _ => True

/-- A layout retains physical arity and the meaning of every tracked cell. -/
def Holds (model : DomainModel) {scope : NormalForm.Scope} (binders : NormalForm.Binders model scope)
    (history : Domain.History model.toCarriers) (layout : Layout scope)
    (environment : Domain.Environment model.toCarriers) : Prop :=
  List.Forall₂ (Cell.Holds model binders history) layout environment

theorem Holds.length {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) : layout.length = environment.length :=
  List.Forall₂.length_eq related

/-- Finite location equality supplies a semantic readback for all models and
binders. An untracked temporary cannot establish this premise. -/
theorem Holds.lookup {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) {reference : Nat} {cell : Cell scope}
    (checked : layout[reference]? = some cell) :
    ∃ physical, environment[reference]? = some physical ∧ Cell.Holds model binders history cell physical := by
  induction related generalizing reference with
  | nil => simp at checked
  | @cons left right layout environment holds tail ih =>
    cases reference with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at checked
      subst cell
      exact ⟨right, rfl, holds⟩
    | succ reference =>
      simp only [List.getElem?_cons_succ] at checked ⊢
      exact ih checked

/-- A nominal data readback recovers the precise source component. -/
theorem Holds.data {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) {reference : Nat} {ty : Ty}
    {component : NormalForm.Comp [] scope ty} (checked : layout[reference]? = some (.data component)) :
    ∃ value physical, component.eval (NormalForm.LawResults.empty model) binders = some value ∧
      Domain.Value.encode ty value = some physical ∧ environment[reference]? = some physical := by
  obtain ⟨physical, read, value, present, encoded⟩ := related.lookup checked
  exact ⟨value, physical, present, encoded, read⟩

/-- Retiring a history designation preserves data and coordinate facts. It
never turns an old physical transcript into a witness of the new history. -/
def Cell.retireHistory {scope : NormalForm.Scope} : Cell scope → Cell scope
  | .history _ => .unused
  | cell => cell

theorem Cell.Holds.retireHistory {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
    {cell : Cell scope} {physical : Domain.Value model.toCarriers}
    (related : Cell.Holds model binders history cell physical)
    (next : Domain.History model.toCarriers) :
    Cell.Holds model binders next cell.retireHistory physical := by
  cases cell <;> first | exact related | trivial

theorem Holds.retireHistory {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) (next : Domain.History model.toCarriers) :
    Holds model binders next (layout.map Cell.retireHistory) environment := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.retireHistory next) ih

/-- Binding a reply or helper result changes names, not the existing values. -/
def Cell.rename {scope target : NormalForm.Scope} (rename : NormalForm.Rename scope target) : Cell scope → Cell target
  | .data component => .data (component.rename rename)
  | .history suite => .history suite
  | .coordinates values => .coordinates (values.map fun term => term.rename rename)
  | .unused => .unused

theorem Cell.Holds.rename {model : DomainModel} {scope target : NormalForm.Scope}
    (rename : NormalForm.Rename scope target) {binders : NormalForm.Binders model scope} {next : NormalForm.Binders model target}
    (same : ∀ {slot : NormalForm.Slot} (binder : Var scope slot), next.get (rename binder) = binders.get binder)
    {history : Domain.History model.toCarriers} {cell : Cell scope} {physical : Domain.Value model.toCarriers}
    (related : Cell.Holds model binders history cell physical) :
    Cell.Holds model next history (cell.rename rename) physical := by
  cases cell with
  | data component =>
    simpa only [Cell.rename, Cell.Holds, NormalForm.comp_eval_rename (NormalForm.LawResults.empty model)
      rename binders next same] using related
  | history => exact related
  | unused => trivial
  | coordinates values =>
    simp only [Cell.rename, Cell.Holds] at related ⊢
    rw [related, List.map_map]
    congr 1
    apply List.map_congr_left
    intro term _
    exact (NormalForm.term_eval_rename (NormalForm.LawResults.empty model)
      rename binders next same term).symm

theorem Holds.rename {model : DomainModel} {scope target : NormalForm.Scope}
    (rename : NormalForm.Rename scope target) {binders : NormalForm.Binders model scope} {next : NormalForm.Binders model target}
    (same : ∀ {slot : NormalForm.Slot} (binder : Var scope slot), next.get (rename binder) = binders.get binder)
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model next history (layout.map (Cell.rename rename)) environment := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.rename rename same) ih

theorem Holds.append {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {left right : Layout scope}
    {first second : Domain.Environment model.toCarriers}
    (one : Holds model binders history left first) (two : Holds model binders history right second) :
    Holds model binders history (left ++ right) (first ++ second) := by
  induction one with
  | nil => exact two
  | cons head tail ih => exact .cons head ih

/-- The same immutable physical prefix retains all its tracked source values. -/
theorem Holds.captures {model : DomainModel} {scope : NormalForm.Scope} {binders : NormalForm.Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {captured suffix : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout captured) :
    (captured ++ suffix).take layout.length = captured := by
  rw [related.length]
  simp

/-- A reply extends the symbolic scope and the physical frame together. All
previous cells are renamed by the one proved weakening operation. -/
theorem Holds.bindData {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) {ty : Ty}
    (value : model.Value ty) {physical : Domain.Value model.toCarriers}
    (encoded : Domain.Value.encode ty value = some physical) :
    Holds model (.cons value binders) history
      (layout.map (Cell.rename (target := .value ty :: scope) .there) ++
        [.data (.present (.var .here))]) (environment ++ [physical]) :=
  (related.rename (target := .value ty :: scope) .there (fun _ => rfl)).append
    (.cons ⟨value, rfl, encoded⟩ .nil)

/-- A finite output alignment. Its leaves contain only equality of static
locations and source terms. The kernel checks those equalities; no leaf can
supply a semantic whole-program equation or an author-chosen return relation. -/
inductive Readback {scope : NormalForm.Scope} (layout : Layout scope) :
    {types : List Ty} → Values (NormalForm.Comp [] scope) types → List Original.Location → Type where
  | nil : Readback layout .nil []
  | absent {ty : Ty} {types : List Ty} {values : Values (NormalForm.Comp [] scope) types}
      {locations : List Original.Location} (tail : Readback layout values locations) :
      Readback layout (.cons (.absent (ty := ty)) values) (.absent :: locations)
  | capability {service : String} {handle : Nat} {types : List Ty}
      {values : Values (NormalForm.Comp [] scope) types} {locations : List Original.Location}
      (tail : Readback layout values locations) :
      Readback layout (.cons (.present (.capability service handle)) values)
        (.capability handle :: locations)
  | data {ty : Ty} {types : List Ty} {component : NormalForm.Comp [] scope ty}
      {values : Values (NormalForm.Comp [] scope) types} {locations : List Original.Location}
      (reference : Nat) (checked : layout[reference]? = some (.data component))
      (tail : Readback layout values locations) :
      Readback layout (.cons component values) (.data reference :: locations)

/-- Static alignment yields full nominal source-value readback for every
model and binder assignment satisfying the established frame invariant. -/
theorem Readback.sound {model : DomainModel} {scope : NormalForm.Scope}
    {binders : NormalForm.Binders model scope} {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {values : Values (NormalForm.Comp [] scope) types}
    {locations : List Original.Location}
    (certificate : Readback layout values locations)
    (related : Holds model binders history layout environment) :
    Original.ValuesHolds environment locations
      (NormalForm.Comps.eval (NormalForm.LawResults.empty model) values binders) := by
  induction certificate with
  | nil => trivial
  | absent tail ih => exact ⟨rfl, ih⟩
  | capability tail ih => exact ⟨rfl, ih⟩
  | data reference checked tail ih =>
    obtain ⟨value, physical, present, encoded, read⟩ := related.data checked
    refine ⟨⟨value, present, ?_⟩, ih⟩
    simp only [read, Option.bind_some, Domain.Value.decode_encode encoded]

end Zkc.Construction.ConnectionFrame
