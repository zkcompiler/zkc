module

public import Zkc.Source.Structured.MultilinearReference

@[expose] public section

/-! Admission and terminal-table mathematics for the same nominal library.
Guards and representation bounds are explicit; scalar claim truth is absent
from helper applicability. The doubling loop remains a symbolic finite fold. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ReferenceLibrary.Multilinear.Admission
open Zkc.Source MultilinearBodies

attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable (model : DomainModel) (domain : String) (bindings : Bindings)

def indexResult (n : Nat) : Values model.Value [.index] := .cons n .nil
def boolResult (b : Bool) : Values model.Value [.boolean] := .cons b .nil

private theorem get_cons_here {types : List Ty} {type : Ty} (value : model.Value type)
    (rest : Values model.Value types) : (Values.cons value rest).get .here = value := rfl
private theorem get_cons_there {types : List Ty} {type head : Ty} (value : model.Value head)
    (rest : Values model.Value types) (ref : Var types type) :
    (Values.cons value rest).get (.there ref) = rest.get ref := rfl

private theorem prepend_empty {types : List Ty} (env : Environment model.Value types)
    (values : Values model.Value []) : @Eq (Environment model.Value types) (env.prepend values) env := by cases values; rfl
private theorem prepend_one {types : List Ty} {type : Ty} (env : Environment model.Value types)
    (values : Values model.Value [type]) : @Eq (Environment model.Value (type :: types))
      (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl

private theorem prepend_three {types : List Ty} {a b c : Ty}
    (env : Environment model.Value types) (values : Values model.Value [a,b,c]) :
    @Eq (Environment model.Value ([a,b,c] ++ types)) (env.prepend values)
      (Environment.push (Environment.push (Environment.push env
        (values.get (.there (.there .here)))) (values.get (.there .here))) (values.get .here)) := by
  cases values with
  | cons x values => cases values with
    | cons y values => cases values with
      | cons z values => cases values; rfl

private theorem singleton_prepend {types : List Ty} {type : Ty}
    (env : Environment model.Value types) (values : Values model.Value [type]) :
    env.prepend values .here = values.get .here := by
  cases values with | cons value rest => cases rest; rfl
private theorem singleton_eta {type : Ty} (values : Values model.Value [type]) :
    Values.cons (values.get .here) Values.nil = values := by
  cases values with | cons value rest => cases rest; rfl
private theorem singleton_append {type : Ty} (values : Values model.Value [type]) :
    values.append Values.nil = values := by
  cases values with | cons value rest => cases rest; rfl
private theorem singleton_split {type : Ty} (values : Values model.Value [type]) :
    (values.split [type]).1 = values := by
  cases values with | cons value rest => cases rest; rfl

theorem power_bound (dimension : Nat) (bound : dimension < 64) : 2^dimension < indexLimit :=
  Nat.pow_lt_pow_right (by decide) bound

set_option backward.isDefEq.respectTransparency false in
theorem rows_body (table : MeaningsOn model.toCarriers) (dimension : Nat)
    (bound : dimension < 64)
    (comparison : invoke table (lessHelper bindings) (.cons dimension (.cons 64 .nil)) =
      .done (boolResult model true)) :
    (rowsBody domain bindings).denote (Evaluation.meaningOn model SiteObservations.closed table)
      (indexResult model dimension).get = .done (indexResult model (2^dimension)) := by
  simp only [rowsBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
    Operands.eval, Regions.denote, Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend, indexResult,
    SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluateOn, primitiveOutcome]
  simp only [show 64 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
    show 0 < indexLimit by decide +kernel, ite_true, PIR.Process.bind,
    comparison, boolResult, decide_eq_true bound, Evaluation.invokeCallbackOn, Environment.prepend, Environment.push, Values.split]
  simp only [Evaluation.denoteLoopOn, Evaluation.invokeCallbackOn, Finite.execute,
    Finite.Domain.admit, Finite.admitThen, Nat.sub_zero]
  have folded := Finite.fold_range_state
    (I := closedInterface)
    (fun (current : Values model.Value [.index]) (_ : Nat) =>
      (primitiveOutcome ((Primitive.indexMul).evaluateOn model.toFieldModel
        (.cons (current.get .here) (.cons 2 .nil))) : Closed _))
    (fun i => indexResult model (2 ^ i)) 0 dimension (by
      intro i _ upper
      have iBound : i < 64 := by omega
      have nextBound : i + 1 < 64 := by omega
      have multiplyBound : 2 ^ i * 2 < indexLimit := by
        simpa only [Nat.pow_succ] using power_bound (i + 1) nextBound
      simp [indexResult, Values.get_cons, get_cons_here, get_cons_there, Values.get, Primitive.evaluateOn, checkedIndices,
        power_bound i iBound, show 2 < indexLimit by decide +kernel, multiplyBound,
        primitiveOutcome, Nat.pow_succ])
  simp only [indexResult, Values.get_cons, get_cons_here, get_cons_there, Values.get, show 2 < indexLimit by decide +kernel,
    primitiveOutcome, PIR.Process.bind, Nat.pow_zero, Environment.prepend, Environment.push,
    Values.get_cons, get_cons_here, get_cons_there, Values.get, Primitive.evaluateOn, checkedIndices,
    singleton_prepend, singleton_eta, singleton_append, singleton_split, PIR.Process.bind_done, ite_true, and_true, Nat.zero_add] at folded ⊢
  refine Eq.trans ?_ folded
  congr 1


abbrev rowsHelper : Helper := ⟨bindings.rows, .local, [.index], [.index]⟩
abbrev shapeHelper : Helper := ⟨bindings.shape, .local, triple domain, [.boolean]⟩
abbrev tableHelper : Helper := ⟨bindings.table, .local, triple domain, triple domain⟩

def rows : ReferenceLaw model [.index] [.index] where
  body := rowsBody domain bindings
  Requires table args := args.get .here < 64 ∧
    invoke table (lessHelper bindings) (.cons (args.get .here) (.cons 64 .nil)) =
      .done (boolResult model true)
  reference args := .returned (indexResult model (2^args.get .here))
  valid table args premises := by
    cases args with
    | cons n rest =>
      cases rest
      exact rows_body model domain bindings table n premises.1 premises.2

def HasShape {A : Type} (xs : List A) (n w : Nat) : Prop :=
  0 < w ∧ n < 64 ∧ xs.length % w = 0 ∧ xs.length / w = 2^n
instance {A : Type} (xs : List A) (n w : Nat) : Decidable (HasShape xs n w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem HasShape.length {A : Type} {xs : List A} {n w : Nat} (shape : HasShape xs n w) :
    xs.length = 2^n*w := by
  have equation := Nat.mod_add_div xs.length w
  rw [shape.2.2.1, shape.2.2.2, Nat.zero_add, Nat.mul_comm] at equation
  exact equation.symm

theorem hasShape_of_length {A : Type} (xs : List A) (n w : Nat)
    (positive : 0 < w) (small : n < 64) (size : xs.length = 2^n*w) : HasShape xs n w := by
  exact ⟨positive, small, by simp [size], by simp [size, positive]⟩

set_option backward.isDefEq.respectTransparency false in
theorem shape_body (table : MeaningsOn model.toCarriers)
    (xs : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (_nBound : n < indexLimit) (wBound : w < indexLimit)
    (first : invoke table (lessHelper bindings) (.cons 0 (.cons w .nil)) =
      .done (boolResult model (decide (0 < w))))
    (second : invoke table (lessHelper bindings) (.cons n (.cons 64 .nil)) =
      .done (boolResult model (decide (n < 64))))
    (row : n < 64 → invoke table (rowsHelper bindings) (indexResult model n) =
      .done (indexResult model (2^n))) :
    (shapeBody domain bindings).denote (Evaluation.meaningOn model SiteObservations.closed table)
      (tableValues model domain xs n w).get =
      .done (boolResult model (decide (HasShape xs n w))) := by
  simp only [shapeBody, tableValues, Region.denote, Evaluation.meaningOn,
    Evaluation.operationOn, Operands.eval, Regions.denote, Values.get_cons, get_cons_here, get_cons_there, Values.get,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Evaluation.invokeCallbackOn, Values.split]
  by_cases positive : 0 < w
  · have nonzero : w ≠ 0 := by omega
    have modBound : xs.length % w < indexLimit := Nat.lt_trans (Nat.mod_lt _ positive) wBound
    have divBound : xs.length / w < indexLimit :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) lengthBound
    by_cases small : n < 64
    · have rowResult := row small
      simp only [indexResult] at rowResult
      have rowBound := power_bound n small
      by_cases divisible : xs.length % w = 0 <;>
        simp [Primitive.evaluateOn, primitiveOutcome, checkedIndices,
          first, second, rowResult, boolResult, HasShape, positive, nonzero,
          small, divisible, lengthBound, wBound, modBound, divBound, rowBound,
          show 0 < indexLimit by decide +kernel, show 64 < indexLimit by decide +kernel,
          PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push, Values.split]
    · simp [Primitive.evaluateOn, primitiveOutcome, first, second, boolResult,
        HasShape, positive, small, show 0 < indexLimit by decide +kernel,
        show 64 < indexLimit by decide +kernel, PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there, Values.get,
        Environment.prepend, Environment.push, Values.split]
  · simp [Primitive.evaluateOn, primitiveOutcome, first, boolResult,
      HasShape, positive, show 0 < indexLimit by decide +kernel,
      PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push, Values.split]


def shape : ReferenceLaw model (triple domain) [.boolean] where
  body := shapeBody domain bindings
  Requires table args :=
    (args.get .here).length < indexLimit ∧ args.get (.there .here) < indexLimit ∧
    args.get (.there (.there .here)) < indexLimit ∧
    invoke table (lessHelper bindings) (.cons 0 (.cons (args.get (.there (.there .here))) .nil)) =
      .done (boolResult model (decide (0 < args.get (.there (.there .here))))) ∧
    invoke table (lessHelper bindings) (.cons (args.get (.there .here)) (.cons 64 .nil)) =
      .done (boolResult model (decide (args.get (.there .here) < 64))) ∧
    (args.get (.there .here) < 64 →
      invoke table (rowsHelper bindings) (indexResult model (args.get (.there .here))) =
        .done (indexResult model (2^args.get (.there .here))))
  reference args := .returned (boolResult model (decide
    (HasShape (args.get .here) (args.get (.there .here)) (args.get (.there (.there .here))))))
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons n rest => cases rest with
        | cons w rest =>
          cases rest
          exact shape_body model domain bindings table xs n w premises.1 premises.2.1
            premises.2.2.1 premises.2.2.2.1 premises.2.2.2.2.1 premises.2.2.2.2.2

def tableOutcome (xs : List (model.Field domain)) (n w : Nat) :
    PIR.Outcome (Values model.Value (triple domain)) :=
  if HasShape xs n w then .returned (tableValues model domain xs n w) else .stopped .reject

set_option backward.isDefEq.respectTransparency false in
def table : ReferenceLaw model (triple domain) (triple domain) where
  body := tableBody domain bindings
  Requires table args := invoke table (shapeHelper domain bindings) args =
    primitiveOutcome ((shape model domain bindings).reference args)
  reference args := tableOutcome model domain (args.get .here)
    (args.get (.there .here)) (args.get (.there (.there .here)))
  valid table args dependency := by
    cases args with
    | cons xs rest => cases rest with
      | cons n rest => cases rest with
        | cons w rest =>
          cases rest
          change invoke table (shapeHelper domain bindings) (tableValues model domain xs n w) = _ at dependency
          simp only [tableBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
            Operands.eval, Regions.denote, Values.get_cons, get_cons_here, get_cons_there, Values.get, prepend_empty, prepend_one,
            Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
            tableValues, Evaluation.invokeCallbackOn]
          simp only [tableValues] at dependency
          rw [dependency]
          by_cases valid : HasShape xs n w <;>
            simp [shape, tableValues, tableOutcome, boolResult, valid, primitiveOutcome,
              PIR.Process.bind, Evaluation.invokeCallbackOn, Values.get_cons, get_cons_here, get_cons_there, Values.get, Region.denote,
              Regions.denote, Environment.prepend, Environment.push]

def checkInputs (xs point : List (model.Field domain)) (claim : model.Field domain) :
    Values model.Value [.vector domain, .vector domain, .field domain] :=
  .cons xs (.cons point (.cons claim .nil))
abbrev checkTableHelper : Helper := ⟨bindings.checkTable, .local,
  [.vector domain, .vector domain, .field domain], [.boolean]⟩
abbrev prefixHelper : Helper := ⟨bindings.restrictPrefix, .local,
  [.vector domain, .index, .index, .vector domain], triple domain⟩
abbrev valuesHelper : Helper := ⟨bindings.valuesRealization, .local, triple domain, [.vector domain]⟩

def checkTableOutcome (xs point : List (model.Field domain)) (claim : model.Field domain) :
    PIR.Outcome (Values model.Value [.boolean]) :=
  if HasShape xs point.length 1 then .returned (boolResult model
    (decide ((Zkc.Polynomial.Multilinear.restrictPrefixValues xs point).sum = claim)))
  else .stopped .reject

set_option backward.isDefEq.respectTransparency false in
theorem checkTable_body (table : MeaningsOn model.toCarriers)
    (xs point : List (model.Field domain)) (claim : model.Field domain)
    (pointBound : point.length < indexLimit)
    (constructor : invoke table (tableHelper domain bindings)
      (tableValues model domain xs point.length 1) = primitiveOutcome (tableOutcome model domain xs point.length 1))
    (restriction : HasShape xs point.length 1 → invoke table (prefixHelper domain bindings)
      (.cons xs (.cons point.length (.cons 1 (.cons point .nil)))) =
      .done (tableValues model domain (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) 0 1))
    (projection : HasShape xs point.length 1 → invoke table (valuesHelper domain bindings)
      (tableValues model domain (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) 0 1) =
      .done (.cons (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) .nil)) :
    (checkTableBody domain bindings).denote (Evaluation.meaningOn model SiteObservations.closed table)
      (checkInputs model domain xs point claim).get = primitiveOutcome (checkTableOutcome model domain xs point claim) := by
  simp only [checkTableBody, checkInputs, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
    Operands.eval, Regions.denote, Values.get_cons, get_cons_here, get_cons_there, Values.get, prepend_empty, prepend_one, prepend_three,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind]
  simp only [Primitive.evaluateOn, pointBound, show 1 < indexLimit by decide +kernel,
    ite_true, primitiveOutcome, PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there, Values.get, prepend_one, Environment.push]
  simp only [tableValues] at constructor restriction projection
  rw [constructor]
  by_cases valid : HasShape xs point.length 1
  · simp only [tableOutcome, valid, ite_true, primitiveOutcome, PIR.Process.bind, tableValues,
      Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push]
    rw [restriction valid]
    simp only [PIR.Process.bind, tableValues, Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push]
    rw [projection valid]
    simp [checkTableOutcome, valid, boolResult, primitiveOutcome, PIR.Process.bind, List.sum_eq_foldl, get_cons_here, get_cons_there]
  · simp [tableOutcome, checkTableOutcome, valid, primitiveOutcome, PIR.Process.bind]

def checkTable : ReferenceLaw model [.vector domain, .vector domain, .field domain] [.boolean] where
  body := checkTableBody domain bindings
  Requires table args :=
    let xs := args.get .here
    let point := args.get (.there .here)
    point.length < indexLimit ∧
    invoke table (tableHelper domain bindings) (tableValues model domain xs point.length 1) =
      primitiveOutcome (tableOutcome model domain xs point.length 1) ∧
    (HasShape xs point.length 1 → invoke table (prefixHelper domain bindings)
      (.cons xs (.cons point.length (.cons 1 (.cons point .nil)))) =
        .done (tableValues model domain (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) 0 1)) ∧
    (HasShape xs point.length 1 → invoke table (valuesHelper domain bindings)
      (tableValues model domain (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) 0 1) =
        .done (.cons (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) .nil))
  reference args := checkTableOutcome model domain (args.get .here) (args.get (.there .here))
    (args.get (.there (.there .here)))
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons point rest => cases rest with
        | cons claim rest =>
          cases rest
          exact checkTable_body model domain bindings table xs point claim premises.1 premises.2.1
            premises.2.2.1 premises.2.2.2

set_option backward.isDefEq.respectTransparency false in
def check : ReferenceLaw model [.vector domain, .vector domain, .field domain] [.boolean] where
  body := checkBody domain bindings
  Requires table args :=
    let xs := args.get .here
    let point := args.get (.there .here)
    point.length < indexLimit ∧
    invoke table (shapeHelper domain bindings) (tableValues model domain xs point.length 1) =
      primitiveOutcome ((shape model domain bindings).reference (tableValues model domain xs point.length 1)) ∧
    (HasShape xs point.length 1 → invoke table (checkTableHelper domain bindings) args =
      primitiveOutcome ((checkTable model domain bindings).reference args))
  reference args := .returned (boolResult model (decide
    (HasShape (args.get .here) (args.get (.there .here)).length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues (args.get .here) (args.get (.there .here))).sum =
        args.get (.there (.there .here)))))
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons point rest => cases rest with
        | cons claim rest =>
          cases rest
          change point.length < indexLimit ∧ _ at premises
          simp only [checkBody, checkTrueBody, checkFalseBody, checkInputs, Region.denote,
            Evaluation.meaningOn, Evaluation.operationOn, Operands.eval, Regions.denote,
            Values.get_cons, get_cons_here, get_cons_there, Values.get, prepend_empty, prepend_one, Environment.push,
            SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
            Evaluation.invokeCallbackOn, Values.split]
          simp only [Primitive.evaluateOn, premises.1, show 1 < indexLimit by decide +kernel,
            ite_true, primitiveOutcome, PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there, Values.get, prepend_one,
            Environment.push]
          simp only [Values.get_cons, get_cons_here, get_cons_there, Values.get, tableValues] at premises
          rw [premises.2.1]
          by_cases valid : HasShape xs point.length 1
          · simp only [shape, tableValues, Values.get_cons, get_cons_here, get_cons_there, Values.get, valid, decide_true, boolResult,
              primitiveOutcome, PIR.Process.bind, ite_true, prepend_one, Environment.push]
            rw [premises.2.2 valid]
            simp [checkTable, checkInputs, checkTableOutcome, valid, primitiveOutcome,
              boolResult, Values.get_cons, get_cons_here, get_cons_there, Values.get, PIR.Process.bind]
          · simp [shape, tableValues, Values.get_cons, get_cons_here, get_cons_there, Values.get, valid, boolResult, primitiveOutcome, PIR.Process.bind]

end Zkc.Source.Structured.ReferenceLibrary.Multilinear.Admission
