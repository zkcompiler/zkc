module

public import Zkc.Source.Structured.MultilinearReferenceInstallation
public import Zkc.Source.Structured.NaturalPowerOfTwo

@[expose] public section

/-! Nominal finite-sum and relation mathematics. Dependency names are data;
only exact typed bodies and complete helper signatures install these laws.
The finite sum retains its admission bound, and scalar claims are arbitrary.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ReferenceLibrary.Sum
open Zkc.Source Zkc.Polynomial.Multilinear
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

structure Bindings where
  add : String
  step : String
  total : String
  domain : String

def addHelper (field : String) (b : Bindings) : Helper :=
  ⟨b.add, .math, [.field field, .field field], [.field field]⟩
def totalHelper (field : String) (b : Bindings) : Helper :=
  ⟨b.total, .math, [.vector field], [.field field]⟩
def foldSpec (field : String) (b : Bindings) : FoldSpec :=
  ⟨DomainSpec.elements b.domain [.vector field] (.vector field) .here,
    [.field field], [], b.step, "", .math⟩

attribute [local implicit_reducible] addHelper totalHelper foldSpec

variable (model : DomainModel) (field : String) (b : Bindings)

def add : ReferenceLaw model [.field field, .field field] [.field field] where
  body := .letOp (.fieldAdd field) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here + args.get (.there .here)) .nil)
  valid _ args _ := by
    cases args with | cons a rest => cases rest with | cons c rest => cases rest; rfl

def step : ReferenceLaw model (foldSpec field b).stepHelper.inputs [.field field] :=
  forward model (addHelper field b) (.cons .here (.cons (.there .here) .nil))
    (add model field).reference

/-- The reference is defined on all lists, even when admission will exhaust. -/
def totalOutcome (xs : List (model.Field field)) :
    PIR.Outcome (Values model.Value [.field field]) :=
  if xs.length < indexLimit then .returned (.cons xs.sum .nil) else .stopped .exhausted

theorem fold_sum (xs : List (model.Field field)) (initial : model.Field field) :
    xs.foldl (fun (state : Values model.Value [.field field]) value =>
      .cons (state.get .here + value) .nil) (.cons initial .nil) =
      .cons (initial + xs.sum) .nil := by
  induction xs generalizing initial with
  | nil => simp
  | cons value rest ih =>
    simpa only [List.foldl_cons, Values.get, List.sum_cons, add_assoc] using ih (initial + value)

set_option backward.isDefEq.respectTransparency false in
def total : ReferenceLaw model [.vector field] [.field field] where
  body := .letOp (.fieldConstant field 0) .nil .nil <|
    .letOp (.fold (foldSpec field b)) (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil))
  Requires table args := ∀ a value : model.Field field,
    invoke table (foldSpec field b).stepHelper
      (.cons a (.cons value (.cons (args.get .here) .nil))) = .done (.cons (a + value) .nil)
  reference args := totalOutcome model field (args.get .here)
  valid table args stepLaw := by
    match args with
    | .cons xs .nil =>
      simp only [Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
        Operands.eval, Regions.denote, Values.get, PIR.Process.bind,
        Environment.prepend, Environment.push, Nat.cast_zero]
      change (Evaluation.denoteFoldOn table (foldSpec field b)
        (.cons xs (.cons (0 : model.Field field) .nil))).bind _ = _
      by_cases bounded : xs.length < indexLimit
      · have admitted : (foldSpec field b).domain.admit (carriers := model.toCarriers)
            (.cons xs .nil) = .returned (xs.map fun value => .cons value .nil) := by
          simp [foldSpec, DomainSpec.admit_elements, Collection.values, Values.get, bounded]
        change (Finite.admitThen ((foldSpec field b).domain.admit
          (carriers := model.toCarriers) (.cons xs .nil)) (fun items => Finite.fold
            (Evaluation.foldTransitionOn table (foldSpec field b) (.cons xs .nil) .nil)
            items (.cons (0 : model.Field field) .nil))).bind _ = _
        rw [admitted]
        simp only [Finite.admitThen, Finite.fold_map]
        have folded := Finite.fold_total
          (fun (state : Values model.Value [.field field]) (value : model.Field field) =>
            Evaluation.foldTransitionOn table (foldSpec field b) (.cons xs .nil) .nil state (.cons value .nil))
          (fun (state : Values model.Value [.field field]) value => .cons (state.get .here + value) .nil)
          (by
            intro state value
            match state with
            | .cons a .nil => exact stepLaw a value)
          xs (.cons (0 : model.Field field) .nil)
        dsimp only [foldSpec, DomainSpec.elements, Collection.type, Collection.element] at folded ⊢
        rw [folded, fold_sum]
        simp [totalOutcome, bounded, primitiveOutcome, PIR.Process.bind, zero_add]
        rfl
      · have exhausted : (foldSpec field b).domain.admit (carriers := model.toCarriers)
            (.cons xs .nil) = .stopped .exhausted := by
          simp [foldSpec, DomainSpec.admit_elements, Collection.values, bounded]
        change (Finite.admitThen ((foldSpec field b).domain.admit
          (carriers := model.toCarriers) (.cons xs .nil)) (fun items => Finite.fold
            (Evaluation.foldTransitionOn table (foldSpec field b) (.cons xs .nil) .nil)
            items (.cons (0 : model.Field field) .nil))).bind _ = _
        rw [exhausted]
        simp [bounded, Finite.admitThen, totalOutcome, primitiveOutcome, PIR.Process.bind]

set_option backward.isDefEq.respectTransparency false in
def scalarRelation : ReferenceLaw model [.vector field, .field field] [.boolean] where
  body := .letOp (.invoke (totalHelper field b)) (.cons .here .nil) .nil <|
    .letOp (.fieldEqual field) (.cons (.there (.there .here)) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil))
  Requires table args := invoke table (totalHelper field b) (.cons (args.get .here) .nil) =
    primitiveOutcome (totalOutcome model field (args.get .here))
  reference args := if (args.get .here).length < indexLimit then
    .returned (.cons (decide (args.get (.there .here) = (args.get .here).sum)) .nil)
    else .stopped .exhausted
  valid table args dependency := by
    match args with
    | .cons xs (.cons scalar .nil) =>
      change (invoke table (totalHelper field b) (.cons xs .nil)).bind _ = _
      change invoke table (totalHelper field b) (.cons xs .nil) = _ at dependency
      rw [dependency]
      by_cases bounded : xs.length < indexLimit <;>
        simp [totalOutcome, bounded, primitiveOutcome, PIR.Process.bind]
      rfl

def initial (site : String) : ReferenceLaw model [.field field] [.vector field, .field field] where
  body := .letOp (.mark site) .nil .nil <|
    .letOp (.exec (.vectorEmpty field)) .nil .nil <|
      .ret (.cons .here (.cons (.there .here) .nil))
  Requires _ _ := True
  reference args := .returned (.cons [] (.cons (args.get .here) .nil))
  valid _ args _ := by cases args with | cons scalar rest => cases rest; rfl

def identity : ReferenceLaw model [.vector field, .field field] [.vector field, .field field] :=
  projection model (.cons .here (.cons (.there .here) .nil))

/-- The source's explicit maximum is part of its formula, not a global law. -/
def inputShape (maximum : Nat) : ReferenceLaw model [.vector field, .index] [.boolean] where
  body := .letOp (.vectorLength field) (.cons .here .nil) .nil <|
    .letOp .indexPowerOfTwo (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.indexConstant maximum) .nil .nil <|
    .letOp .indexLess (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.booleanConstant false) .nil .nil <|
    .letOp .booleanEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
    .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)
  Requires _ _ := True
  reference args := .returned (.cons
    (decide ((args.get .here).length = 2 ^ args.get (.there .here) ∧
      args.get (.there .here) ≤ maximum)) .nil)
  valid _ args _ := by
    match args with
    | .cons xs (.cons count .nil) =>
      change (PIR.Process.done (.cons
        (naturalPowerOfTwo xs.length count && (decide (maximum < count) == false)) .nil) :
        Closed (Values model.Value [.boolean])) = _
      rw [naturalPowerOfTwo_eq_decide]
      by_cases bound : count ≤ maximum
      · simp [bound, Nat.not_lt.mpr bound, primitiveOutcome]
      · simp [bound, Nat.lt_of_not_ge bound, primitiveOutcome]


/- The continuation tests the restricted original table for an arbitrary scalar.
Only the complete projection and finite-sum dependencies are required. -/
set_option backward.isDefEq.respectTransparency false in
def pendingRelation (valuesName : String) : ReferenceLaw model
    [.vector field, .index, .index, .vector field, .field field] [.boolean] where
  body := .letOp (.invoke ⟨valuesName, .math, [.vector field, .index, .index], [.vector field]⟩)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
    .letOp (.multilinearRestrictPrefix field)
      (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.invoke (totalHelper field b)) (.cons .here .nil) .nil <|
    .letOp (.fieldEqual field)
      (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)
  Requires table args :=
    invoke table ⟨valuesName, .math, [.vector field, .index, .index], [.vector field]⟩
      (.cons (args.get .here) (.cons (args.get (.there .here))
        (.cons (args.get (.there (.there .here))) .nil))) = .done (.cons (args.get .here) .nil) ∧
    invoke table (totalHelper field b)
      (.cons (restrictPrefixValues (args.get .here) (args.get (.there (.there (.there .here))))) .nil) =
      primitiveOutcome (totalOutcome model field
        (restrictPrefixValues (args.get .here) (args.get (.there (.there (.there .here))))))
  reference args :=
    let xs := restrictPrefixValues (args.get .here) (args.get (.there (.there (.there .here))))
    if xs.length < indexLimit then .returned (.cons
      (decide (args.get (.there (.there (.there (.there .here)))) = xs.sum)) .nil)
    else .stopped .exhausted
  valid table args dependencies := by
    match args with
    | .cons xs (.cons n (.cons w (.cons point (.cons scalar .nil)))) =>
      obtain ⟨values, total⟩ := dependencies
      change (invoke table ⟨valuesName, .math, [.vector field, .index, .index], [.vector field]⟩
        (.cons xs (.cons n (.cons w .nil)))).bind _ = _
      change invoke table ⟨valuesName, .math, [.vector field, .index, .index], [.vector field]⟩
        (.cons xs (.cons n (.cons w .nil))) = _ at values
      rw [values]
      change (invoke table (totalHelper field b) (.cons (restrictPrefixValues xs point) .nil)).bind _ = _
      change invoke table (totalHelper field b) (.cons (restrictPrefixValues xs point) .nil) = _ at total
      rw [total]
      by_cases bounded : (restrictPrefixValues xs point).length < indexLimit <;>
        simp [totalOutcome, bounded, primitiveOutcome, PIR.Process.bind]
      rfl

/-- Conjunction is ordinary relation composition; no independence premise is used. -/
def both : ReferenceLaw model [.boolean, .boolean] [.boolean] where
  body := .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here && args.get (.there .here)) .nil)
  valid _ args _ := by
    match args with | .cons a (.cons c .nil) => rfl

/- The outer two-table relation uses the same finite-sum installation twice. -/
set_option backward.isDefEq.respectTransparency false in
def pairRelation : ReferenceLaw model
    [.vector field, .vector field, .field field, .field field] [.boolean] where
  body := .letOp (.invoke (totalHelper field b)) (.cons .here .nil) .nil <|
    .letOp (.fieldEqual field) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.invoke (totalHelper field b)) (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.fieldEqual field) (.cons (.there (.there (.there (.there (.there (.there .here))))))
      (.cons .here .nil)) .nil <|
    .letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)
  Requires table args :=
    invoke table (totalHelper field b) (.cons (args.get .here) .nil) =
      primitiveOutcome (totalOutcome model field (args.get .here)) ∧
    invoke table (totalHelper field b) (.cons (args.get (.there .here)) .nil) =
      primitiveOutcome (totalOutcome model field (args.get (.there .here)))
  reference args :=
    if (args.get .here).length < indexLimit then
      if (args.get (.there .here)).length < indexLimit then
        .returned (.cons (decide (args.get (.there (.there .here)) = (args.get .here).sum ∧
          args.get (.there (.there (.there .here))) = (args.get (.there .here)).sum)) .nil)
      else .stopped .exhausted
    else .stopped .exhausted
  valid table args dependencies := by
    match args with
    | .cons xs (.cons ys (.cons a (.cons c .nil))) =>
      obtain ⟨left, right⟩ := dependencies
      change (invoke table (totalHelper field b) (.cons xs .nil)).bind _ = _
      change invoke table (totalHelper field b) (.cons xs .nil) = _ at left
      change invoke table (totalHelper field b) (.cons ys .nil) = _ at right
      rw [left]
      by_cases bx : xs.length < indexLimit
      · simp only [totalOutcome, Values.get, bx, ↓reduceIte, primitiveOutcome, PIR.Process.bind]
        change (invoke table (totalHelper field b) (.cons ys .nil)).bind _ = _
        rw [right]
        by_cases bys : ys.length < indexLimit <;>
          simp [totalOutcome, Values.get, bys, primitiveOutcome, PIR.Process.bind]
        rfl
      · simp [totalOutcome, Values.get, bx, primitiveOutcome, PIR.Process.bind]


set_option backward.isDefEq.respectTransparency false in
/-- Table shape is independent of scalar truth and helper admission. -/
def tableShape (metadata : MultilinearBodies.Bindings) : ReferenceLaw model
    [.vector field, .index, .index] [.boolean] where
  body := .letOp (.invoke (⟨ metadata.width, .math, [(.vector field), .index, .index], [.index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.invoke (⟨ metadata.values, .math, [(.vector field), .index, .index], [(.vector field)] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.vectorLength field) (.cons .here .nil) .nil <|
  .letOp (.invoke (⟨ metadata.dimension, .math, [(.vector field), .index, .index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .letOp .indexPowerOfTwo (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)
  Requires table args :=
    invoke table ⟨metadata.width, .math, [.vector field, .index, .index], [.index]⟩ args =
      .done (.cons (args.get (.there (.there .here))) .nil) ∧
    invoke table ⟨metadata.values, .math, [.vector field, .index, .index], [.vector field]⟩ args =
      .done (.cons (args.get .here) .nil) ∧
    invoke table ⟨metadata.dimension, .math, [.vector field, .index, .index], [.index]⟩ args =
      .done (.cons (args.get (.there .here)) .nil)
  reference args := .returned (.cons (decide (args.get (.there (.there .here)) = 1 ∧
    (args.get .here).length = 2 ^ args.get (.there .here))) .nil)
  valid table args dependencies := by
    match args with
    | .cons xs (.cons n (.cons w .nil)) =>
      obtain ⟨width, values, dimension⟩ := dependencies
      change (invoke table ⟨metadata.width, .math, [.vector field, .index, .index], [.index]⟩
        (.cons xs (.cons n (.cons w .nil)))).bind _ = _
      rw [width]
      change (invoke table ⟨metadata.values, .math, [.vector field, .index, .index], [.vector field]⟩
        (.cons xs (.cons n (.cons w .nil)))).bind _ = _
      rw [values]
      change (invoke table ⟨metadata.dimension, .math, [.vector field, .index, .index], [.index]⟩
        (.cons xs (.cons n (.cons w .nil)))).bind _ = _
      rw [dimension]
      change (PIR.Process.done (.cons (decide (w = 1) && naturalPowerOfTwo xs.length n) .nil) :
        Closed (Values model.Value [.boolean])) = _
      rw [naturalPowerOfTwo_eq_decide]
      simp [primitiveOutcome]

end Zkc.Source.Structured.ReferenceLibrary.Sum
