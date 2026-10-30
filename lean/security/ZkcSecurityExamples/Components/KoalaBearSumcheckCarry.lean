module

public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import Zkc.Source.Structured.NormalForm.Denote

@[expose] public section

/-! Strict readback of the explicit linear point/value carry. This adapter
retains an arbitrary prior point and accepts exactly one new challenge. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity)
abbrev extension : Ty := .field octicIdentity

abbrev Octic := ZkcSecurity.Domains.KoalaBear.Octic
abbrev Base := ZkcSecurity.Domains.KoalaBear.Base
local instance : DecidableEq Octic := model.fieldDecEq octicIdentity

/-- Decode one extension of the retained point. -/
def decodeCarry (priorPoint : List Octic) (point : Option (List Octic))
    (value : Option Octic) :
    PIR.Process (Interface model) (Values (Component model.Value) [extension, extension]) :=
  match point, value with
  | some point, some value =>
      if point.take priorPoint.length = priorPoint then
        match point.drop priorPoint.length with
        | [challenge] => .done (.cons (some value) (.cons (some challenge) .nil))
        | _ => .halt .reject
      else .halt .reject
  | _, _ => .halt .incomplete

/-- Read the actual linear carry. Partial values stop incomplete; any change
to the prior point is rejected before a logical state can be constructed. -/
def decodeEvaluation (priorPoint : List Octic)
    (out : Values (Component model.Value) [.vector octicIdentity, extension]) :
    PIR.Process (Interface model) (Values (Component model.Value) [extension, extension]) :=
  decodeCarry priorPoint (out.get .here) (out.get (.there .here))

theorem decodeEvaluation_complete (priorPoint : List Octic) (challenge value : Octic) :
    decodeEvaluation priorPoint (.cons (some (priorPoint ++ [challenge])) (.cons (some value) .nil)) =
      .done (.cons (some value) (.cons (some challenge) .nil)) := by
  simp [decodeEvaluation, decodeCarry, Values.get]

end ZkcSecurity.Examples.Components.KoalaBearSumcheckSource
