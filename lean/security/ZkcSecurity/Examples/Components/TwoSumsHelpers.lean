module

public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public import ZkcExamples.Structured.SumcheckUnitContracts
public import ZkcExamples.Structured.MapPrefixContracts
public import Zkc.Source.Structured.BodyBindings
public import ZkcSecurity.Realizations.Sumcheck.DomainHelpers

@[expose] public section

/-! Mathematical helper laws for the actual updated TwoSums source. Each
association checks a complete admitted body and ABI in this unit's own helper
table. No helper name authorizes a mathematical interpretation by itself.
-/

set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.TwoSums
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcExamples.Structured.Generated.Bindings
open PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws

/-- Install the reusable mathematical body templates against this actual unit.
The tactic searches full signatures and bodies; no helper-number table is supplied. -/
theorem source_bodies : ZkcSecurity.Realizations.Sumcheck.DomainHelpers.Bodies TwoSumsInputs.imported.program := by
  bind_structured_bodies

theorem first_bodies : MapFirstContracts.Bodies TwoSumsInputs.unit.definitions :=
  source_bodies.sumcheck.first

theorem prefix_bodies : MapPrefixContracts.Bodies TwoSumsInputs.unit.definitions :=
  source_bodies.prefixBodies

theorem helper_bodies : SumcheckUnitContracts.Bodies TwoSumsInputs.unit.definitions :=
  source_bodies.sumcheck

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

noncomputable abbrev helperMeanings : Meanings F G := closedMeanings TwoSumsInputs.unit.definitions

theorem prefix_laws : MapPrefixContracts.Laws (helperMeanings (F := F) (G := G)) :=
  MapPrefixContracts.laws_of_bodies TwoSumsInputs.unit.linked prefix_bodies first_bodies

/-- The actual producer endpoint helper, including raw-shape and index stops. -/
theorem sums_all (raw : List F) (dimension columns : Nat) :
    invoke (helperMeanings (G := G)) sumsHelper (inputs raw dimension columns) =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < raw.length ∧ raw.length % 2 = 0 then
            .done (messageResult (raw.take (raw.length / 2)).sum
              (raw.drop (raw.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused :=
  SumcheckUnitContracts.sums_all TwoSumsInputs.unit.linked helper_bodies raw dimension columns

/-- Terminal correctness uses the same raw-table reference for every scalar,
including false claims and malformed representable raw vectors. -/
theorem check_equation (raw point : List F) (claim : F)
    (rawBound : raw.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (helperMeanings (G := G)) checkHelper (checkInputs raw point claim) =
      .done (boolResult (decide (HasShape raw point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim))) :=
  (source_bodies.check.invoke TwoSumsInputs.unit.linked (checkInputs raw point claim)).trans
    (check_generic_body _ prefix_laws
      (fun raw point claim => source_bodies.checkTable.invoke TwoSumsInputs.unit.linked
        (checkInputs raw point claim)) raw point claim rawBound pointBound)

/-- The actual final math function is conjunction, for arbitrary inputs. -/
theorem both_equation (left right : Bool) :
    invoke (helperMeanings (F := F) (G := G)) TwoSumsInputs.helper30Helper
      (.cons left (.cons right .nil)) = .done (.cons (left && right) .nil) :=
  ((show BodyIn TwoSumsInputs.unit.definitions TwoSumsInputs.helper30Helper
      TwoSumsInputs.helper30Body from by bind_structured_bodies).invoke
      TwoSumsInputs.unit.linked (.cons left (.cons right .nil))).trans
    (by rfl)

end ZkcSecurity.Examples.Components.TwoSums
