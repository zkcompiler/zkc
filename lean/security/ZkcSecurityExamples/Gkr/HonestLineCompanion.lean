module

public import ZkcSecurityExamples.Gkr.HonestLineGoals
public import Zkc.Polynomial.Multilinear.CoefficientRows
public import Zkc.Source.Structured.CursorFold

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

noncomputable def differenceWrapperLibrary (model : DomainModel) :=
  forward_reference% DifferenceWrapper.body using (differenceLaw model)

def differenceWrapperReference (model : DomainModel) (high : model.Field scalarDomain) (low : model.Field scalarDomain) :
    PIR.Outcome (DifferenceWrapper.Output model) := .returned ⟨high - low⟩

def differenceWrapperCondition (model : DomainModel) := fun table (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) =>
  (differenceLaw model).Realizes (helper := GkrSourceBodies.helper58Helper) table

theorem differenceWrapper (model : DomainModel) :
    DifferenceWrapper.Goal model (differenceWrapperReference model) (differenceWrapperCondition model) := by
  apply DifferenceWrapper.of_law model _ _ (differenceWrapperLibrary model) rfl
  · intro high low; rfl
  · intro table high low dependency; exact dependency

noncomputable def differenceWrapperLaw (model : DomainModel) :=
  DifferenceWrapper.law model (differenceWrapperReference model) (differenceWrapperCondition model) (differenceWrapper model)

noncomputable def slopeWrapperLibrary (model : DomainModel) :=
  forward_reference% SlopeWrapper.body using (slopeLaw model)

def slopeWrapperReference (model : DomainModel) (low : model.Field scalarDomain) (high : model.Field scalarDomain) (delta : model.Field scalarDomain) :
    PIR.Outcome (SlopeWrapper.Output model) := .returned ⟨(high - low) * delta⟩

def slopeWrapperCondition (model : DomainModel) := fun table (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) =>
  (slopeLaw model).Realizes (helper := GkrSourceBodies.helper60Helper) table

theorem slopeWrapper (model : DomainModel) :
    SlopeWrapper.Goal model (slopeWrapperReference model) (slopeWrapperCondition model) := by
  apply SlopeWrapper.of_law model _ _ (slopeWrapperLibrary model) rfl
  · intro low high delta; rfl
  · intro table low high delta dependency; exact dependency

noncomputable def slopeWrapperLaw (model : DomainModel) :=
  SlopeWrapper.law model (slopeWrapperReference model) (slopeWrapperCondition model) (slopeWrapper model)

noncomputable def slopeCallbackLibrary (model : DomainModel) :=
  forward_reference% SlopeCallback.body using (slopeWrapperLaw model)

def slopeCallbackReference (model : DomainModel) (low : model.Field scalarDomain) (high : model.Field scalarDomain) (_left : List (model.Field scalarDomain)) (_right : List (model.Field scalarDomain)) (delta : model.Field scalarDomain) :
    PIR.Outcome (SlopeCallback.Output model) := .returned ⟨(high - low) * delta⟩

def slopeCallbackCondition (model : DomainModel) := fun table (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) (_ : List (model.Field scalarDomain)) (_ : List (model.Field scalarDomain)) (_ : model.Field scalarDomain) =>
  (slopeWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper68Helper) table

theorem slopeCallback (model : DomainModel) :
    SlopeCallback.Goal model (slopeCallbackReference model) (slopeCallbackCondition model) := by
  apply SlopeCallback.of_law model _ _ (slopeCallbackLibrary model) rfl
  · intro low high left right delta; rfl
  · intro table low high left right delta dependency; exact dependency

noncomputable def slopeCallbackLaw (model : DomainModel) :=
  SlopeCallback.law model (slopeCallbackReference model) (slopeCallbackCondition model) (slopeCallback model)

noncomputable def totalWrapperLibrary (model : DomainModel) :=
  forward_reference% TotalWrapper.body using (totalLaw model)

def totalWrapperReference (model : DomainModel) (left : model.Field scalarDomain) (right : model.Field scalarDomain) :
    PIR.Outcome (TotalWrapper.Output model) := .returned ⟨left + right⟩

def totalWrapperCondition (model : DomainModel) := fun table (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) =>
  (totalLaw model).Realizes (helper := GkrSourceBodies.helper67Helper) table

theorem totalWrapper (model : DomainModel) :
    TotalWrapper.Goal model (totalWrapperReference model) (totalWrapperCondition model) := by
  apply TotalWrapper.of_law model _ _ (totalWrapperLibrary model) rfl
  · intro left right; rfl
  · intro table left right dependency; exact dependency

noncomputable def totalWrapperLaw (model : DomainModel) :=
  TotalWrapper.law model (totalWrapperReference model) (totalWrapperCondition model) (totalWrapper model)

noncomputable def totalCallbackLibrary (model : DomainModel) :=
  forward_reference% TotalCallback.body using (totalWrapperLaw model)

def totalCallbackReference (model : DomainModel) (low : model.Field scalarDomain) (high : model.Field scalarDomain) (_left : List (model.Field scalarDomain)) (_right : List (model.Field scalarDomain)) :
    PIR.Outcome (TotalCallback.Output model) := .returned ⟨low + high⟩

def totalCallbackCondition (model : DomainModel) := fun table (_ : model.Field scalarDomain) (_ : model.Field scalarDomain) (_ : List (model.Field scalarDomain)) (_ : List (model.Field scalarDomain)) =>
  (totalWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper71Helper) table

theorem totalCallback (model : DomainModel) :
    TotalCallback.Goal model (totalCallbackReference model) (totalCallbackCondition model) := by
  apply TotalCallback.of_law model _ _ (totalCallbackLibrary model) rfl
  · intro low high left right; rfl
  · intro table low high left right dependency; exact dependency

noncomputable def totalCallbackLaw (model : DomainModel) :=
  TotalCallback.law model (totalCallbackReference model) (totalCallbackCondition model) (totalCallback model)

/-- Complete scalar laws installed against the actual associated declarations. -/
structure ScalarLaws (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  difference : (differenceLaw model).Realizes (helper := GkrSourceBodies.helper58Helper) table
  slope : (slopeLaw model).Realizes (helper := GkrSourceBodies.helper60Helper) table
  total : (totalLaw model).Realizes (helper := GkrSourceBodies.helper67Helper) table
  differenceWrapper : (differenceWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper67Helper) table
  slopeWrapper : (slopeWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper68Helper) table
  slopeCallback : (slopeCallbackLaw model).Realizes (helper := GkrSourceBodies.scopedHelper69Helper) table
  totalWrapper : (totalWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper71Helper) table
  totalCallback : (totalCallbackLaw model).Realizes (helper := GkrSourceBodies.scopedHelper72Helper) table

theorem installScalars (model : DomainModel) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : ScalarBodies definitions) :
    ScalarLaws model (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) := by
  have difference := (differenceLaw model).realizes (helper := GkrSourceBodies.helper58Helper)
    definitions linked bodies.difference (by
      intro arguments
      obtain ⟨view, rfl⟩ := DifferenceArguments.pack_surjective arguments
      trivial)
  have slope := (slopeLaw model).realizes (helper := GkrSourceBodies.helper60Helper)
    definitions linked bodies.slope (by
      intro arguments
      obtain ⟨view, rfl⟩ := SlopeArguments.pack_surjective arguments
      trivial)
  have total := (totalLaw model).realizes (helper := GkrSourceBodies.helper67Helper)
    definitions linked bodies.total (by
      intro arguments
      obtain ⟨view, rfl⟩ := TotalArguments.pack_surjective arguments
      trivial)
  have differenceWrapper := (differenceWrapperLaw model).realizes (helper := GkrSourceBodies.scopedHelper67Helper)
    definitions linked bodies.differenceWrapper (by
      intro arguments
      obtain ⟨view, rfl⟩ := DifferenceWrapperArguments.pack_surjective arguments
      exact difference)
  have slopeWrapper := (slopeWrapperLaw model).realizes (helper := GkrSourceBodies.scopedHelper68Helper)
    definitions linked bodies.slopeWrapper (by
      intro arguments
      obtain ⟨view, rfl⟩ := SlopeWrapperArguments.pack_surjective arguments
      exact slope)
  have slopeCallback := (slopeCallbackLaw model).realizes (helper := GkrSourceBodies.scopedHelper69Helper)
    definitions linked bodies.slopeCallback (by
      intro arguments
      obtain ⟨view, rfl⟩ := SlopeCallbackArguments.pack_surjective arguments
      exact slopeWrapper)
  have totalWrapper := (totalWrapperLaw model).realizes (helper := GkrSourceBodies.scopedHelper71Helper)
    definitions linked bodies.totalWrapper (by
      intro arguments
      obtain ⟨view, rfl⟩ := TotalWrapperArguments.pack_surjective arguments
      exact total)
  have totalCallback := (totalCallbackLaw model).realizes (helper := GkrSourceBodies.scopedHelper72Helper)
    definitions linked bodies.totalCallback (by
      intro arguments
      obtain ⟨view, rfl⟩ := TotalCallbackArguments.pack_surjective arguments
      exact totalWrapper)
  exact ⟨difference, slope, total, differenceWrapper, slopeWrapper, slopeCallback, totalWrapper, totalCallback⟩

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
