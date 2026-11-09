module

public import Zkc.Applications.Security.Gkr.HonestLineGoals
public import Zkc.Program.Polynomial.Multilinear.CoefficientRows
public import Zkc.IR.Source.Structured.CursorFold

public meta import Zkc.Tools.IR.StructuredSource.ReferenceInstallation

@[expose] public section

/-! Mathematical line companions. Scalar references and complete forwarding
laws are independent of declaration names. Row shifting is ordinary list
mathematics; source association and finite admission belong to assembly. -/
namespace ZkcSecurity.Realizations.Gkr.HonestLine.Companion
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open Goals Zkc.Polynomial.Multilinear.CoefficientRows

set_option backward.isDefEq.respectTransparency false

def differenceReference (model : DomainModel) (high low : model.Field scalarDomain) :
    PIR.Outcome (Difference.Output model) := .returned ⟨high - low⟩

theorem difference (model : DomainModel) :
    Difference.Goal model (differenceReference model) (fun _ _ _ => True) := by
  intro table high low _
  rfl

noncomputable def differenceLaw (model : DomainModel) :=
  Difference.law model (differenceReference model) (fun _ _ _ => True) (difference model)

def slopeReference (model : DomainModel) (low high delta : model.Field scalarDomain) :
    PIR.Outcome (Slope.Output model) := .returned ⟨(high - low) * delta⟩

theorem slope (model : DomainModel) :
    Slope.Goal model (slopeReference model) (fun _ _ _ _ => True) := by
  intro table low high delta _
  rfl

noncomputable def slopeLaw (model : DomainModel) :=
  Slope.law model (slopeReference model) (fun _ _ _ _ => True) (slope model)

def totalReference (model : DomainModel) (left right : model.Field scalarDomain) :
    PIR.Outcome (Total.Output model) := .returned ⟨left + right⟩

theorem total (model : DomainModel) :
    Total.Goal model (totalReference model) (fun _ _ _ => True) := by
  intro table left right _
  rfl

noncomputable def totalLaw (model : DomainModel) :=
  Total.law model (totalReference model) (fun _ _ _ => True) (total model)

noncomputable def differenceWrapperLaw (model : DomainModel) :=
  forward_reference% DifferenceWrapper.body using (differenceLaw model)

noncomputable def slopeWrapperLaw (model : DomainModel) :=
  forward_reference% SlopeWrapper.body using (slopeLaw model)

noncomputable def slopeCallbackLaw (model : DomainModel) :=
  forward_reference% SlopeCallback.body using (slopeWrapperLaw model)

noncomputable def totalWrapperLaw (model : DomainModel) :=
  forward_reference% TotalWrapper.body using (totalLaw model)

noncomputable def totalCallbackLaw (model : DomainModel) :=
  forward_reference% TotalCallback.body using (totalWrapperLaw model)

/-- Complete scalar laws installed against the actual associated declarations. -/
structure ScalarLaws (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  difference : (differenceLaw model).Realizes (helper := GkrSourceBodies.helper31Helper) table
  slope : (slopeLaw model).Realizes (helper := GkrSourceBodies.helper32Helper) table
  total : (totalLaw model).Realizes (helper := GkrSourceBodies.helper33Helper) table
  differenceWrapper : (differenceWrapperLaw model).Realizes (helper := GkrSourceBodies.helper80Helper) table
  slopeWrapper : (slopeWrapperLaw model).Realizes (helper := GkrSourceBodies.helper81Helper) table
  slopeCallback : (slopeCallbackLaw model).Realizes (helper := GkrSourceBodies.helper82Helper) table
  totalWrapper : (totalWrapperLaw model).Realizes (helper := GkrSourceBodies.helper84Helper) table
  totalCallback : (totalCallbackLaw model).Realizes (helper := GkrSourceBodies.helper85Helper) table

theorem installScalars (model : DomainModel) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : ScalarBodies definitions) :
    ScalarLaws model (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) := by
  install_reference_laws using linked with bodies

/-- Mathematical state of a row-reset scan, including its final cursor. -/
structure ShiftState (F : Type) where
  values : List F
  previous : F
  offset : Nat

def shiftTransition {F : Type} [Zero F] (count : Nat) (state : ShiftState F) (value : F) :
    ShiftState F :=
  ⟨state.values ++ [if state.offset % count = 0 then 0 else state.previous], value, state.offset + 1⟩

theorem shift_fold {F : Type} [CommRing F] (count : Nat) (values : List F) (state : ShiftState F) :
    values.foldl (shiftTransition count) state =
      ⟨state.values ++ shiftAux count state.offset state.previous values,
        values.getLastD state.previous, state.offset + values.length⟩ := by
  induction values generalizing state with
  | nil => simp [List.foldl, List.getLastD, shiftAux]
  | cons value rest ih =>
    rw [List.foldl_cons, ih]
    simp only [shiftTransition, shiftAux, List.length_cons, List.append_assoc, List.singleton_append]
    have last : (value :: rest).getLastD state.previous = rest.getLastD value := by
      cases rest <;> rfl
    rw [last, show state.offset + 1 + rest.length = state.offset + (rest.length + 1) by omega]

end ZkcSecurity.Realizations.Gkr.HonestLine.Companion
