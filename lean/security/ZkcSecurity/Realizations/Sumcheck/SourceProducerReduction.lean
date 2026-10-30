module

public import Zkc.Protocols.Sumcheck.Source.PreludeNormalForms
public import Zkc.Protocols.Sumcheck.Source.ReferenceInstallation

@[expose] public section

/-! Producer reduction support for the same source template as the validator.
Only local body laws are installed. The repeat and its complete returned row
remain the source language's existing occurrence semantics.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceProducerReduction
open Zkc.Source Zkc.Source.Structured NormalForm ReferenceLibrary
open ZkcExamples.Structured SumcheckReferenceInstallation

abbrev signature := SumcheckPreludeNormalForms.proverReduceSignature
abbrev pattern := SumcheckPreludeNormalForms.proverReducePattern
noncomputable abbrev form := SumcheckPreludeNormalForms.proverReduceForm

variable (model : DomainModel)

def results : LawResults model signature.laws where
  result entry := match entry with
    | ⟨0, _⟩ => fun _ => .cons 0 .nil
    | ⟨1, _⟩ => fun _ => .cons 0 .nil
    | ⟨2, _⟩ => fun _ => .cons false .nil
    | ⟨3, _⟩ => fun _ => .cons [] .nil
    | ⟨_ + 4, outside⟩ => absurd outside (by simp [signature,
        SumcheckPreludeNormalForms.proverReduceSignature])

def inputs (entries : List (model.Field field)) (count rounds : Nat) :
    Binders model pattern.scope := .cons entries (.cons count (.cons rounds .nil))

/-- Exact typed associations, including the comparison and empty-point helper.
A same-typed replacement helper cannot discharge this installation. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  width : BodyIn definitions MapFirstBodies.widthHelper
    (.ret (.cons (.there (.there .here)) .nil))
  dimension : BodyIn definitions MapFirstBodies.variablesHelper (.ret (.cons (.there .here) .nil))
  less : BodyIn definitions MapFirstBodies.lessHelper
    (Multilinear.less model field MultilinearSourceBindings.sumcheck).body
  empty : BodyIn definitions SumcheckHelperBodies.emptyHelper (emptyVector model field "s0").body


theorem laws (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies model definitions) (entries : List (model.Field field)) (count rounds : Nat)
    (countBound : count < indexLimit) (roundsBound : rounds < indexLimit) (enough : rounds ≤ count) :
    LawsHold (tables model definitions) (results model)
      (pattern.environment model (inputs model entries count rounds)) := by
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
    match args, pinned with
    | .cons a (.cons b .nil), ⟨first, second, _⟩ =>
      obtain rfl : values = (.cons false .nil : Values model.Value [.boolean]) :=
        Option.some.inj (found.symm.trans (by kernel_rfl))
      rw [← (Option.some.inj first : count = a), ← (Option.some.inj second : rounds = b)]
      change invoke (tables model definitions).closed MapFirstBodies.lessHelper _ = _
      rw [(Multilinear.less model field MultilinearSourceBindings.sumcheck).invokeOn
        (model := model) (helper := MapFirstBodies.lessHelper) definitions linked bodies.less _ trivial]
      change (primitiveOutcome (if count < indexLimit ∧ rounds < indexLimit then
        .returned (.cons (decide (count < rounds)) .nil : Values model.Value [.boolean])
        else .stopped .refused)) = _
      simp [countBound, roundsBound, Nat.not_lt.mpr enough, primitiveOutcome]
      rfl
  | ⟨3, _⟩ =>
    intro args pinned values found
    cases args
    obtain rfl : values = (.cons [] .nil : Values model.Value [.vector field]) :=
      Option.some.inj (found.symm.trans (by kernel_rfl))
    change invoke (tables model definitions).closed SumcheckHelperBodies.emptyHelper _ = _
    exact (emptyVector model field "s0").invokeOn (model := model)
      (helper := SumcheckHelperBodies.emptyHelper) definitions linked bodies.empty _ trivial
  | ⟨_ + 4, outside⟩ => exact absurd outside (by simp [signature,
      SumcheckPreludeNormalForms.proverReduceSignature])

def terminal (returned : Values (Component model.Value) SumcheckVerifierBodies.repeatState) :
    Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs :=
  .cons (returned.get (.there (.there (.there .here))))
    (.cons (returned.get .here) (.cons (returned.get (.there .here))
    (.cons (returned.get (.there (.there .here))) (.cons none (.cons none .nil)))))

def reference (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (entries : List (model.Field field)) (count rounds : Nat) :=
  (denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) ctx (ctx.roles 0) (some rounds)
    (Prover.state model entries count 1 []) (.cons none .nil)
    (fun args => SumcheckVerifierBodies.roundBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 0) protocols ctx Occurrence.iterations) args.get)
    Occurrence.iterations SumcheckVerifierBodies.repeatSite).bind fun out => .done (terminal model out)

theorem presentation (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (entries : List (model.Field field)) (count rounds : Nat) :
    (form maximum).denoteOn model Occurrence.actions (tables model definitions) (results model) ctx
      (runsAtOn model Occurrence.actions Occurrence.iterations (tables model definitions) protocols ctx 0)
      (noCallees model _) (inputs model entries count rounds) =
      reference model definitions protocols maximum ctx entries count rounds := by
  kernel_rfl

theorem body_reference (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies model definitions)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (maximum : Nat) (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (entries : List (model.Field field)) (count rounds : Nat)
    (countBound : count < indexLimit) (roundsBound : rounds < indexLimit) (enough : rounds ≤ count) :
    (SumcheckVerifierBodies.reduceBody maximum).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 0) protocols ctx Occurrence.iterations)
      (pattern.environment model (inputs model entries count rounds)).get =
      reference model definitions protocols maximum ctx entries count rounds :=
  (normalize_occurrence_sound signature (SumcheckVerifierBodies.reduceBody maximum) 0 2 pattern
    (form maximum) (SumcheckPreludeNormalForms.proverReduce_normalized maximum)
    (SumcheckPreludeNormalForms.proverReduce_lawsMatch maximum) distinct (results model)
    (noCallees model _) (inputs model entries count rounds)
    (laws model definitions linked bodies entries count rounds countBound roundsBound enough)
    (noCallees_hold _ _)).trans
      (presentation model definitions protocols maximum ctx entries count rounds)

end ZkcSecurity.Realizations.Sumcheck.SourceProducerReduction
