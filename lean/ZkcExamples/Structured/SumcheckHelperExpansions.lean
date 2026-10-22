module

public import Zkc.Source.DeriveRegion
public import Zkc.Source.Structured.DerivationRules
public import ZkcExamples.Structured.SumcheckHelperBodies

@[expose] public section
namespace ZkcExamples.Structured.SumcheckHelperLaws
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open PrimitiveLibrary MapPrefixBodies SumcheckHelperBodies

theorem prepend_empty {Value : Ty → Type} {types : List Ty}
    (env : Environment Value types) (values : Values Value []) :
    @Eq (Environment Value types) (env.prepend values) env := by cases values; rfl
theorem prepend_one {Value : Ty → Type} {types : List Ty} {type : Ty}
    (env : Environment Value types) (values : Values Value [type]) :
    @Eq (Environment Value (type :: types)) (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl
theorem prepend_two {Value : Ty → Type} {types : List Ty} {first second : Ty}
    (env : Environment Value types) (values : Values Value [first, second]) :
    @Eq (Environment Value (first :: second :: types)) (env.prepend values)
      (Environment.push (Environment.push env (values.get (.there .here))) (values.get .here)) := by
  cases values with | cons a rest => cases rest with | cons b rest => cases rest; rfl

theorem prepend_three {Value : Ty → Type} {types : List Ty} {type0 type1 type2 : Ty}
    (env : Environment Value types) (values : Values Value [type0, type1, type2]) :
    @Eq (Environment Value ([type0, type1, type2] ++ types)) (env.prepend values) (Environment.push (Environment.push (Environment.push env (values.get (.there (.there .here)))) (values.get (.there .here))) (values.get .here)) := by
  cases values with | cons value0 values => cases values with | cons value1 values => cases values with | cons value2 values => cases values; rfl

theorem singleton_eta {Value : Ty → Type} {a : Ty} (result : Values Value [a]) :
    Values.cons (result.get .here) .nil = result := by
  cases result with | cons x rest => cases rest; rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def checkInputs (xs point : List F) (claim : F) :
    Values (assignment F G) [vector, vector, scalar] :=
  .cons xs (.cons point (.cons claim .nil))

def messageResult (low high : F) : Values (assignment F G) [scalar, scalar] :=
  .cons low (.cons high .nil)

/-- Literal split, low sum, high sum. The input triple is arbitrary. -/
theorem sums_expansion (table : Meanings F G) (xs : List F) (dimension columns : Nat) :
    sumsBody.denote (meaning F G table) (inputs xs dimension columns).get =
      (invoke table halvesHelper (inputs xs dimension columns)).bind fun halves =>
        .done (messageResult (halves.get .here).sum (halves.get (.there .here)).sum) := by
  derive_process using (exact vectorSum_law _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- The initial length can stop before the constructor or prefix. -/
theorem checkTable_expansion (table : Meanings F G) (xs point : List F) (claim : F) :
    checkTableBody.denote (meaning F G table) (checkInputs xs point claim).get =
      if point.length < indexLimit then
        (invoke table tableHelper (inputs xs point.length 1)).bind fun constructed =>
        (invoke table prefixHelper (constructed.append (.cons point .nil))).bind fun residual =>
        (invoke table valuesRealizationHelper residual).bind fun values =>
        .done (boolResult (decide ((values.get .here).sum = claim)))
      else .halt .exhausted := by
  simp only [checkTableBody, checkInputs, inputs, boolResult, Region.denote, meaning,
    Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
    Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate]
  split
  · simp only [primitiveOutcome, PIR.Process.bind, show 1 < indexLimit by decide +kernel,
      ite_true, Values.get_cons, Values.get, Environment.push, ← List.sum_eq_foldl]
    congr 1
    funext constructed
    cases constructed with
    | cons xs rest =>
      cases rest with
      | cons n rest =>
        cases rest with
        | cons w rest =>
          cases rest
          congr 1
          funext residual
          cases residual with
          | cons xs rest =>
            cases rest with
            | cons n rest =>
              cases rest with
              | cons w rest => cases rest; rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- Actual Local.if only invokes check_table in its true callback. -/
theorem check_expansion (table : Meanings F G) (xs point : List F) (claim : F) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get =
      if point.length < indexLimit then
        (invoke table shapeHelper (inputs xs point.length 1)).bind fun valid =>
          if valid.get .here then invoke table checkTableHelper (checkInputs xs point claim)
          else .done (boolResult false)
      else .halt .exhausted := by
  simp only [checkBody, checkTrueBody, checkFalseBody, checkInputs, inputs, boolResult,
    Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_empty, prepend_one, prepend_two, prepend_three, Environment.prepend,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate]
  split
  · simp only [primitiveOutcome, PIR.Process.bind, show 1 < indexLimit by decide +kernel,
      ite_true, Values.get_cons, Values.get, Environment.push, Evaluation.invokeCallback]
    congr 1
    funext valid
    cases valid with
    | cons b rest =>
      cases rest
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        PIR.Process.bind, Values.get_cons, Values.get, Environment.prepend, Environment.push,
        singleton_eta, PIR.Process.bind_done]
      rfl
  · rfl

end ZkcExamples.Structured.SumcheckHelperLaws
