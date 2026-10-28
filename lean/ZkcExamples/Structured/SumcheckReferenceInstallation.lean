module

public import Zkc.Source.Structured.MultilinearReferenceInstallation
public import Zkc.Source.Structured.SumReferenceInstallation
public import Zkc.Source.Structured.ProjectionReferenceInstallation
public import ZkcExamples.Structured.SumcheckPreludeNormalForms
public import Zkc.Source.Structured.NormalForm.Reference
public import Zkc.Source.Structured.NormalForm.Observation
public import ZkcExamples.Structured.SumcheckRoundNormalForms
public import ZkcExamples.Structured.MultilinearSourceBindings

@[expose] public section

/-! Nominal installation for the retained Sumcheck round. The old typed body
and normal-form syntax are reused. Mathematical helper results come from the
same linked library as the source; no whole-source equation is an input. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.SumcheckReferenceInstallation
open Zkc.Source Zkc.Source.Structured NormalForm
open ReferenceLibrary.Multilinear
namespace Syntax
abbrev signature := SumcheckRoundNormalForms.verifierSignature
abbrev pattern := SumcheckRoundNormalForms.verifierPattern
noncomputable abbrev form := SumcheckRoundNormalForms.verifierForm
end Syntax

abbrev field : String := "bls12-381.fr"

structure Bodies (definitions : List CheckedDefinition) (bindings : MultilinearBodies.Bindings) : Prop
    extends ReferenceLibrary.Multilinear.Bodies definitions field bindings where
  append : BodyIn definitions SumcheckHelperBodies.appendHelper SumcheckHelperBodies.appendBody

variable (model : DomainModel)

abbrev tables (definitions : List CheckedDefinition) :
    Tables model (Occurrence.signature model.toCarriers) :=
  definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

def results : LawResults model Syntax.signature.laws where
  result entry := match entry with
    | ⟨0, _⟩ => fun args => .cons (args.get .here ++ [args.get (.there .here)]) .nil
    | ⟨_ + 1, outside⟩ => absurd outside (by simp [Syntax.signature, SumcheckRoundNormalForms.verifierSignature])

def state (point : Option (List (model.Field field))) (claim : Option (model.Field field)) :
    Values (Component model.Value) SumcheckVerifierBodies.repeatState :=
  .cons none (.cons none (.cons none (.cons none (.cons point (.cons claim .nil)))))

def inputs (index : Nat) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (service : Option Nat) :
    Binders model Syntax.pattern.scope := .cons index (.cons point (.cons claim (.cons service .nil)))

def reference (ctx : ProtocolContext) (service : Option Nat)
    (point : Option (List (model.Field field))) (claim : Option (model.Field field)) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) SumcheckVerifierBodies.repeatState) :=
  .call (.action (.receive (.field field) (SumcheckRoundNormalForms.round0Site ctx) (ctx.roles 0))) fun (lo : model.Field field) =>
  .call (.action (.receive (.field field) (SumcheckRoundNormalForms.round1Site ctx) (ctx.roles 0))) fun (hi : model.Field field) =>
  match claim with
  | none => .halt .incomplete
  | some scalar => if scalar = lo + hi then
    match service with
    | none => .halt .incomplete
    | some handle =>
      .call (.action (.query (SumcheckRoundNormalForms.challengeSite ctx) field (.cons handle .nil))) fun (r : model.Field field) =>
      .call (.action (.send (ty := .field field) (SumcheckRoundNormalForms.deliverySite ctx)
        (ctx.roles 0) r)) fun _ =>
      match point with
      | none => .halt .incomplete
      | some point => .done (state model (some (point ++ [r])) (some ((1-r)*lo+r*hi)))
    else .halt .reject

theorem laws (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    {bindings : MultilinearBodies.Bindings} (bodies : Bodies definitions bindings)
    (index : Nat) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (service : Option Nat) :
    LawsHold (tables model definitions) (results model)
      (Syntax.pattern.environment model (inputs model index point claim service)) := by
  intro entry
  match entry with
  | ⟨0, _⟩ =>
    exact reference_returns definitions linked (ReferenceLibrary.appendVector model field "s0")
      bodies.append _ [.free, .free] _ (fun _ _ => trivial) (fun _ _ => rfl)
  | ⟨_ + 1, outside⟩ => exact absurd outside (by simp [Syntax.signature, SumcheckRoundNormalForms.verifierSignature])

/-- This is presentation of the single shared normal form, including all
absent/private output slots and every incomplete/reject branch. -/
theorem presentation (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (index : Nat) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (service : Option Nat) :
    Syntax.form.denoteOn model Occurrence.actions (tables model definitions) (results model) ctx
      (runsAtOn model Occurrence.actions Occurrence.iterations (tables model definitions) protocols ctx 1)
      (noCallees model _) (inputs model index point claim service) =
      reference model ctx service point claim := by
  kernel_rfl

/-- One body theorem for both admitted libraries. Arbitrary replies remain
universally quantified in the equality of open occurrence processes. -/
theorem body_reference (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) {bindings : MultilinearBodies.Bindings}
    (bodies : Bodies definitions bindings)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (index : Nat) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (service : Option Nat) :
    SumcheckVerifierBodies.roundBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 1) protocols ctx Occurrence.iterations)
      (Syntax.pattern.environment model (inputs model index point claim service)).get =
      reference model ctx service point claim :=
  (normalize_occurrence_sound Syntax.signature SumcheckVerifierBodies.roundBody 1 2 Syntax.pattern
    Syntax.form SumcheckRoundNormalForms.verifier_normalized SumcheckRoundNormalForms.verifier_lawsMatch
    distinct (results model) (noCallees model _) (inputs model index point claim service)
    (laws model definitions linked bodies index point claim service) (noCallees_hold _ _)).trans
      (presentation model definitions protocols ctx index point claim service)

namespace Prover
open Zkc.Polynomial.Multilinear
abbrev signature := SumcheckRoundNormalForms.proverSignature
abbrev pattern := SumcheckRoundNormalForms.proverPattern
noncomputable abbrev form := SumcheckRoundNormalForms.proverForm
abbrev bindings := MultilinearSourceBindings.sumcheck

def results : LawResults model signature.laws where
  result entry := match entry with
    | ⟨0, _⟩ => fun args => .cons ((args.get .here).take ((args.get .here).length / 2)).sum
        (.cons ((args.get .here).drop ((args.get .here).length / 2)).sum .nil)
    | ⟨1, _⟩ => fun args => tableValues model field
        (restrictValues (args.get .here) (args.get (.there (.there (.there .here)))))
        (args.get (.there .here) - 1) (args.get (.there (.there .here)))
    | ⟨2, _⟩ => fun args => .cons (args.get .here ++ [args.get (.there .here)]) .nil
    | ⟨_ + 3, outside⟩ => absurd outside (by simp [signature, SumcheckRoundNormalForms.proverSignature])

def inputs (index : Nat) (xs : List (model.Field field)) (n w : Nat)
    (point : List (model.Field field)) (service : Option Nat) : Binders model pattern.scope :=
  .cons index (.cons xs (.cons n (.cons w (.cons point (.cons service .nil)))))

set_option backward.isDefEq.respectTransparency false in
/-- The three installed mathematical laws account for every local helper used
by the actual honest producer. Captures and columns remain in its full output. -/
theorem laws (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions bindings) (index : Nat) (xs : List (model.Field field)) (n w : Nat)
    (point : List (model.Field field)) (service : Option Nat)
    (bound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) (positive : 0 < n) :
    LawsHold (tables model definitions) (results model)
      (pattern.environment model (inputs model index xs n w point service)) := by
  intro entry
  match entry with
  | ⟨0, _⟩ =>
    change LawHolds (tables model definitions) _
      ⟨SumcheckHelperBodies.sumsHelper, .returns [], [.input 1, .input 2, .input 3]⟩
      (fun args => .cons ((args.get .here).take ((args.get .here).length / 2)).sum
        (.cons ((args.get .here).drop ((args.get .here).length / 2)).sum .nil))
    intro args pinned
    match args, pinned with
    | .cons a (.cons b (.cons c .nil)), ⟨p0, p1, p2, _⟩ =>
      intro values found
      have aeq : xs = a := Option.some.inj p0
      have beq : n = b := Option.some.inj p1
      have ceq : w = c := Option.some.inj p2
      subst a; subst b; subst c
      have veq : values = (show Values model.Value [.field field, .field field] from
          .cons ((xs.take (xs.length / 2)).sum)
            (.cons ((xs.drop (xs.length / 2)).sum) .nil)) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      subst values
      rw [Evaluation.closed_invoke_componentTablesOn]
      have eq := sums_eq model linked bodies.toBodies xs n w
      change invoke _ SumcheckHelperBodies.sumsHelper _ = _ at eq
      refine (congrArg (PIR.Process.interpret (closedLift (I := Occurrence.signature model.toCarriers))) eq).trans ?_
      have split := split_shape model field xs n w positive width shape
      simp [sums, halves, halvesOutcome, tableValues, positive, split,
        show n < indexLimit from Nat.lt_trans small (by decide +kernel), primitiveOutcome, PIR.Process.interpret]
  | ⟨1, _⟩ =>
    change LawHolds (tables model definitions) _
      ⟨MapFirstBodies.firstHelper, .returns [.result, .result, .argument 2],
        [.input 1, .input 2, .input 3, .free]⟩
      (fun args => tableValues model field
        (restrictValues (args.get .here) (args.get (.there (.there (.there .here)))))
        (args.get (.there .here) - 1) (args.get (.there (.there .here))))
    intro args pinned
    match args, pinned with
    | .cons a (.cons b (.cons c (.cons r .nil))), ⟨p0, p1, p2, _⟩ =>
      intro values found
      have aeq : xs = a := Option.some.inj p0
      have beq : n = b := Option.some.inj p1
      have ceq : w = c := Option.some.inj p2
      subst a; subst b; subst c
      have veq : values = tableValues model field (restrictValues xs r) (n-1) w :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      subst values
      rw [Evaluation.closed_invoke_componentTablesOn]
      have eq := first_eq model linked bodies.toBodies xs n w r bound small width shape
      change invoke _ MapFirstBodies.firstHelper _ = _ at eq
      refine (congrArg (PIR.Process.interpret (closedLift (I := Occurrence.signature model.toCarriers))) eq).trans ?_
      simp [firstOutcome, positive, primitiveOutcome, PIR.Process.interpret]
  | ⟨2, _⟩ =>
    exact reference_returns definitions linked (ReferenceLibrary.appendVector model field "s0")
      bodies.append _ [.input 4, .free] _ (fun _ _ => trivial) (fun _ _ => rfl)
  | ⟨_ + 3, outside⟩ => exact absurd outside (by simp [signature, SumcheckRoundNormalForms.proverSignature])

/-- Complete prover output: table, remaining dimension, columns and private
point are retained, while verifier-only components remain absent. -/
def state (xs : List (model.Field field)) (n w : Nat) (point : List (model.Field field)) :
    Values (Component model.Value) SumcheckVerifierBodies.repeatState :=
  .cons (some xs) (.cons (some n) (.cons (some w) (.cons (some point) (.cons none (.cons none .nil)))))

def reference (ctx : ProtocolContext) (xs : List (model.Field field)) (n w : Nat)
    (point : List (model.Field field)) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) SumcheckVerifierBodies.repeatState) :=
  .call (.action (.send (ty := .field field) (SumcheckRoundNormalForms.round0Site ctx) (ctx.roles 1)
    (xs.take (xs.length/2)).sum)) fun _ =>
  .call (.action (.send (ty := .field field) (SumcheckRoundNormalForms.round1Site ctx) (ctx.roles 1)
    (xs.drop (xs.length/2)).sum)) fun _ =>
  .call (.action (.receive (.field field) (SumcheckRoundNormalForms.deliverySite ctx) (ctx.roles 1)))
    fun (r : model.Field field) => .done (state model (restrictValues xs r) (n-1) w (point ++ [r]))

theorem presentation (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (index : Nat) (xs : List (model.Field field)) (n w : Nat)
    (point : List (model.Field field)) (service : Option Nat) :
    form.denoteOn model Occurrence.actions (tables model definitions) (results model) ctx
      (runsAtOn model Occurrence.actions Occurrence.iterations (tables model definitions) protocols ctx 0)
      (noCallees model _) (inputs model index xs n w point service) =
      reference model ctx xs n w point := by
  kernel_rfl

theorem body_reference (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions bindings)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (index : Nat) (xs : List (model.Field field)) (n w : Nat)
    (point : List (model.Field field)) (service : Option Nat)
    (bound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) (positive : 0 < n) :
    SumcheckVerifierBodies.roundBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 0) protocols ctx Occurrence.iterations)
      (pattern.environment model (inputs model index xs n w point service)).get =
      reference model ctx xs n w point :=
  (normalize_occurrence_sound signature SumcheckVerifierBodies.roundBody 0 2 pattern form
    SumcheckRoundNormalForms.prover_normalized SumcheckRoundNormalForms.prover_lawsMatch distinct
    (results model) (noCallees model _) (inputs model index xs n w point service)
    (laws model definitions linked bodies index xs n w point service bound small width shape positive)
    (noCallees_hold _ _)).trans (presentation model definitions protocols ctx index xs n w point service)

end Prover

end ZkcExamples.Structured.SumcheckReferenceInstallation


/-! Complete nominal reduction installation, sharing the retained source syntax. -/
namespace ZkcExamples.Structured.SumcheckReductionReference
open Zkc.Source Zkc.Source.Structured NormalForm ReferenceLibrary
open SumcheckReferenceInstallation
abbrev signature := SumcheckPreludeNormalForms.verifierReduceSignature
abbrev pattern := SumcheckPreludeNormalForms.verifierReducePattern
noncomputable abbrev form := SumcheckPreludeNormalForms.verifierReduceForm

variable (model : DomainModel)

def results : LawResults model signature.laws where
  result entry := match entry with
    | ⟨0, _⟩ => fun _ => .cons 0 .nil
    | ⟨1, _⟩ => fun _ => .cons 0 .nil
    | ⟨2, _⟩ => fun args => args
    | ⟨3, _⟩ => fun args => args
    | ⟨_ + 4, outside⟩ => absurd outside (by simp [signature, SumcheckPreludeNormalForms.verifierReduceSignature])

def inputs (point : Option (List (model.Field field))) (claim : Option (model.Field field))
    (count service : Option Nat) : Binders model pattern.scope :=
  .cons point (.cons claim (.cons count (.cons service .nil)))

structure Bodies (definitions : List CheckedDefinition) : Prop where
  width : BodyIn definitions MapFirstBodies.widthHelper
    (.ret (.cons (.there (.there .here)) .nil))
  dimension : BodyIn definitions MapFirstBodies.variablesHelper (.ret (.cons (.there .here) .nil))
  openClaim : BodyIn definitions SumcheckPendingBodies.openClaimHelper (Sum.identity model field).body
  atPrefix : BodyIn definitions SumcheckPendingBodies.atPrefixHelper (Sum.identity model field).body


theorem laws (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies model definitions) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (count service : Option Nat) :
    LawsHold (tables model definitions) (results model)
      (pattern.environment model (inputs model point claim count service)) := by
  intro entry
  match entry with
  | ⟨0, _⟩ =>
    intro args values found
    match args with
    | .cons a (.cons b (.cons c .nil)) =>
      obtain rfl : values = (.cons c .nil : Values (Component model.Value) [.index]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      exact projection_components model definitions linked _ _ bodies.width _
  | ⟨1, _⟩ =>
    intro args values found
    match args with
    | .cons a (.cons b (.cons c .nil)) =>
      obtain rfl : values = (.cons b .nil : Values (Component model.Value) [.index]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      exact projection_components model definitions linked _ _ bodies.dimension _
  | ⟨2, _⟩ =>
    intro args pinned values found
    match args with
    | .cons a (.cons b .nil) =>
      obtain rfl : values = (.cons a (.cons b .nil) : Values model.Value [.vector field, .field field]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      change invoke (tables model definitions).closed SumcheckPendingBodies.openClaimHelper _ = _
      exact (Sum.identity model field).invokeOn (model := model)
        (helper := SumcheckPendingBodies.openClaimHelper) definitions linked bodies.openClaim _ trivial
  | ⟨3, _⟩ =>
    intro args pinned values found
    match args with
    | .cons a (.cons b .nil) =>
      obtain rfl : values = (.cons a (.cons b .nil) : Values model.Value [.vector field, .field field]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      change invoke (tables model definitions).closed SumcheckPendingBodies.atPrefixHelper _ = _
      exact (Sum.identity model field).invokeOn (model := model)
        (helper := SumcheckPendingBodies.atPrefixHelper) definitions linked bodies.atPrefix _ trivial
  | ⟨_ + 4, outside⟩ => exact absurd outside (by simp [signature, SumcheckPreludeNormalForms.verifierReduceSignature])

/-- All six returned source slots are retained in their actual order. -/
def terminal (returned : Values (Component model.Value) SumcheckVerifierBodies.repeatState) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :=
  match returned.get (.there (.there (.there (.there .here)))) with
  | none => .halt .incomplete
  | some point => match returned.get (.there (.there (.there (.there (.there .here))))) with
    | none => .halt .incomplete
    | some scalar => .done (.cons (returned.get (.there (.there (.there .here))))
        (.cons (returned.get .here) (.cons (returned.get (.there .here))
        (.cons (returned.get (.there (.there .here))) (.cons (some point) (.cons (some scalar) .nil))))))

def reference (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (count service : Option Nat) :=
  match point, claim with
  | some point, some claim =>
    (denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 1) count
      (state model (some point) (some claim)) (.cons service .nil)
      (fun args => SumcheckVerifierBodies.roundBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 1) protocols ctx Occurrence.iterations) args.get)
      Occurrence.iterations SumcheckVerifierBodies.repeatSite).bind (terminal model)
  | _, _ => .halt .incomplete

theorem presentation (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (point : Option (List (model.Field field)))
    (claim : Option (model.Field field)) (count service : Option Nat) :
    (form maximum).denoteOn model Occurrence.actions (tables model definitions) (results model) ctx
      (runsAtOn model Occurrence.actions Occurrence.iterations (tables model definitions) protocols ctx 1)
      (noCallees model _) (inputs model point claim count service) =
      reference model definitions protocols maximum ctx point claim count service := by
  cases point <;> cases claim <;> kernel_rfl

/-- The premise is an exact, local nominal library installation. No whole-body
semantic equation, evaluator or source/compiled connection is assumed. -/
theorem body_reference (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies model definitions)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (point : Option (List (model.Field field))) (claim : Option (model.Field field))
    (count service : Option Nat) :
    (SumcheckVerifierBodies.reduceBody maximum).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 1) protocols ctx Occurrence.iterations)
      (pattern.environment model (inputs model point claim count service)).get =
      reference model definitions protocols maximum ctx point claim count service :=
  (normalize_occurrence_sound signature (SumcheckVerifierBodies.reduceBody maximum) 1 2 pattern
    (form maximum) (SumcheckPreludeNormalForms.verifierReduce_normalized maximum)
    (SumcheckPreludeNormalForms.verifierReduce_lawsMatch maximum) distinct (results model)
    (noCallees model _) (inputs model point claim count service)
    (laws model definitions linked bodies point claim count service) (noCallees_hold _ _)).trans
      (presentation model definitions protocols maximum ctx point claim count service)

end ZkcExamples.Structured.SumcheckReductionReference
