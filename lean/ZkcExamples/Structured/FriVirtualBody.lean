module

public import ZkcExamples.Structured.FriSource

@[expose] public section

/-! Nominal selection and body identity for the retained virtual Fold. -/

set_option autoImplicit false
namespace ZkcExamples.Structured.FriVirtualBody
open Zkc.Source Zkc.Source.Structured FriSource FriSourceBodies FriSourceViews

def installed : CheckedOracle checkedUnit.snapshot checkedUnit.domains checkedUnit.math :=
  checkedUnit.oracles[0]'(by decide +kernel)

theorem selected : checkedUnit.oracles.find?
    (fun checked ↦ checked.declaration.signature == oracle0Signature) = some installed := by
  kernel_rfl

/-- The companion chooses the first and second reads. Both locations come
from the typed region the source checker admitted. -/
def querySites : List OracleLocation := oracle0Body.erase.operations.filterMap fun op ↦ match op with
  | .oracle (.query _ none) site => some site
  | _ => none

theorem twoSites : querySites.length = 2 := by decide

theorem signature : installed.declaration.signature = oracle0Signature := by kernel_rfl

theorem body : installed.body = oracle0Body := by
  apply installed.body_eq_of_raw
  kernel_rfl

/-- Open the installed declaration once, at its printed signature. Subsequent
algebraic reasoning can use the body without re-evaluating unit admission. -/
theorem denote (model : DomainModel) (args : Values (Component model.Value) oracle0Signature.inputs) :
    installed.denote model args = oracle0Body.denote
      (oracleBodyMeaning model (checkedUnit.math.tables model (oracleReadInterface model.toCarriers))) args.get := by
  unfold CheckedOracle.denote
  rw [body]
  rfl

/-- The virtual evaluator captures only the Math declarations. This exact
list equality permits the same checked helper laws on both execution paths. -/
theorem mathDefinitions : checkedUnit.math.definitions = [
    helper5Definition, helper7Definition, helper8Definition,
    helper9Definition, helper10Definition, helper11Definition,
    helper12Definition, formulaDefinition, helper14Definition,
    helper15Definition, helper27Definition, helper28Definition,
    helper33Definition] := by
  kernel_rfl

end ZkcExamples.Structured.FriVirtualBody
