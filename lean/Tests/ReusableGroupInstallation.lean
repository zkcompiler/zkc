import ZkcExamples.Structured.SchnorrVariants
import ZkcTools.Companions
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Prod

/-! Bounded controls with distinct group and scalar carriers, using the actual
admitted relation declarations and the installed full validator process. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Tests.ReusableGroupInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Protocols.Sigma.Source
open ZkcExamples.Structured.SchnorrVariants.Installations
open ZkcExamples.Structured.Generated.Bindings

abbrev Scalar := ZMod 5
abbrev Group := Scalar × Scalar
abbrev model := ringModel Scalar Group
example : Fintype.card Scalar = 5 ∧ Fintype.card Group = 25 := by decide
example : Ty.group domains.group ≠ Ty.field domains.scalar := by decide

noncomputable def table := SchnorrRandomizedInputs.program.payload.definitions.foldl
  (Evaluation.extendMeaningsOn model SiteObservations.closed) []

attribute [local implicit_reducible] relationHelper independentHelper sharedHelper table

example : invoke table (relationHelper domains randomizedRelation.val)
    (.cons ((1, 2) : Group) (.cons (3 • ((1, 2) : Group)) (.cons (3 : Scalar) .nil))) =
    .done (.cons true .nil) := by
  unfold table
  rw [randomized_relation model]
  rfl

example : invoke table (relationHelper domains randomizedRelation.val)
    (.cons ((1, 2) : Group) (.cons ((0, 1) : Group) (.cons (0 : Scalar) .nil))) =
    .done (.cons false .nil) := by
  unfold table
  rw [randomized_relation model]
  apply congrArg (fun value : Bool =>
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.boolean])))
  decide

example : invoke (SchnorrAndRandomizedInputs.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
    (independentHelper domains randomizedAndRelation.val)
    (.cons ((1, 0) : Group) (.cons ((0, 0) : Group) (.cons ((1, 0) : Group)
      (.cons ((1, 0) : Group) (.cons (0 : Scalar) (.cons (1 : Scalar) .nil)))))) =
    .done (.cons true .nil) := by
  rw [randomizedAnd_relation model]
  apply congrArg (fun value : Bool =>
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.boolean])))
  decide

example : ¬ ∃ witness : Scalar,
    ((0, 0) : Group) = witness • ((1, 0) : Group) ∧
    ((1, 0) : Group) = witness • ((1, 0) : Group) := by
  rintro ⟨witness, first, second⟩
  have impossible := congrArg Prod.fst (first.trans second.symm)
  exact (by decide : (0 : Scalar) ≠ 1) impossible

example : invoke (ZkcExamples.Structured.ChaumPedersenViews.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
    (sharedHelper domains chaumPedersenRelation.val)
    (.cons ((1, 0) : Group) (.cons ((0, 0) : Group) (.cons ((1, 0) : Group)
      (.cons ((1, 0) : Group) (.cons (0 : Scalar) .nil))))) =
    .done (.cons false .nil) := by
  rw [chaumPedersen_relation model]
  apply congrArg (fun value : Bool =>
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.boolean])))
  decide

example : invoke (ZkcExamples.Structured.ChaumPedersenViews.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
    (sharedHelper domains chaumPedersenRelation.val)
    (.cons ((1, 0) : Group) (.cons ((3, 0) : Group) (.cons ((0, 1) : Group)
      (.cons ((0, 3) : Group) (.cons (3 : Scalar) .nil))))) =
    .done (.cons true .nil) := by
  rw [chaumPedersen_relation model]
  apply congrArg (fun value : Bool =>
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [.boolean])))
  decide

/-- The same nominal signature with the inverse ordered relation. -/
def reversedRelationBody : Region dialect (relationHelper domains "").inputs [.boolean] :=
  .letOp (.groupScale domains.group domains.scalar)
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.groupEqual domains.group) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

example : True := by
  fail_if_success
    have _ : {name : String // BodyIn SchnorrRandomizedInputs.program.payload.definitions
      (relationHelper domains name) reversedRelationBody} := by
        infer_reference_installation
  trivial

example : True := by
  fail_if_success
    have _ : {name : String // BodyIn SchnorrRandomizedInputs.program.payload.definitions
      (relationHelper ⟨domains.group, "different.scalar"⟩ name)
      (relationBody ⟨domains.group, "different.scalar"⟩)} := by
        infer_reference_installation
  trivial

def validatorPattern : NormalForm.InputPattern (singleSignature domains randomizedMetadata).inputs :=
  .cons .optional (.cons .optional (.cons .absent (.cons .absent
    (.cons (.capability ("random." ++ domains.scalar ++ "/0") 7) .nil))))

/-- Every typed receive and query reply remains arbitrary. Missing public
components remain missing; hidden physical inputs may contain any values. -/
theorem validator_every_reply (base point : Option Group)
    (hiddenWitness : Option Scalar) (hiddenService : Option Nat) :
    invokeProtocol (Occurrence.table model SchnorrRandomizedInputs.program.payload)
      (singleSignature domains randomizedMetadata) {} 1
      (.cons base (.cons point (.cons hiddenWitness (.cons hiddenService (.cons (some 7) .nil))))) =
    (.call (.action (.receive (.group domains.group) singleSites.commitment 0)) fun commitment =>
      .call (.action (.query singleSites.challenge domains.scalar (.cons 7 .nil))) fun challenge =>
      .call (.action (.send singleSites.delivery 0 challenge)) fun _ =>
      .call (.action (.receive (.field domains.scalar) singleSites.response 0)) fun response =>
      .done (.cons (equal model domains.group (scale model domains base (some response))
        (optional₂ (· + ·) (some commitment) (scale model domains point (some challenge)))) .nil)) := by
  exact randomized_installed model 1 {} (fun _ _ same => same) validatorPattern rfl
    (.cons base (.cons point .nil)) (.cons hiddenWitness (.cons hiddenService .nil))

def producerPattern : NormalForm.InputPattern (singleSignature domains randomizedMetadata).inputs :=
  .cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent .nil))))

/-- A missing owned service input stops before any fabricated private sample;
the hidden physical challenge handle does not change that stop. -/
theorem missing_private_service (base point : Option Group) (witness : Option Scalar)
    (hiddenChallenge : Option Nat) :
    invokeProtocol (Occurrence.table model SchnorrRandomizedInputs.program.payload)
      (singleSignature domains randomizedMetadata) {} 0
      (.cons base (.cons point (.cons witness (.cons none (.cons hiddenChallenge .nil))))) =
      .halt .incomplete := by
  exact randomized_installed model 0 {} (NormalForm.RosterDistinct.root 0 2) producerPattern rfl
    (.cons base (.cons point (.cons witness (.cons none .nil)))) (.cons hiddenChallenge .nil)

-- Same nominal helper signature and carriers, but reversed ordered inputs and
-- therefore a different mathematical reference. Registration is only data.
@[zkc "ReusableGroup.wrongReference"] theorem swapped_reference (base point : Group) (witness : Scalar) :
    invoke table (relationHelper domains randomizedRelation.val)
      (.cons point (.cons base (.cons witness .nil))) =
      .done (.cons (decide (base = witness • point)) .nil) :=
  randomized_relation model _

@[zkc "ReusableGroup.correctReference"] theorem retained_reference (base point : Group) (witness : Scalar) :
    invoke table (relationHelper domains randomizedRelation.val)
      (.cons base (.cons point (.cons witness .nil))) =
      .done (.cons (decide (point = witness • base)) .nil) :=
  randomized_relation model _

open Lean Elab Command Term Meta in
run_elab do
  let expected ← elabTerm (← `(term| ∀ (base point : Group) (witness : Scalar),
    invoke table (relationHelper domains randomizedRelation.val)
      (.cons base (.cons point (.cons witness .nil))) =
      PIR.Process.done (.cons (decide (point = witness • base)) .nil))) none
  let wrong ← ZkcTools.Companions.resolve
    #[⟨"ReusableGroup.wrongReference", #[]⟩, ⟨"ReusableGroup.correctReference", #[]⟩] expected
  unless (match wrong with | .refused _ _ => true | _ => false) do
    throwError "changed ordered reference was accepted or silently replaced"
  let correct ← ZkcTools.Companions.resolve #[⟨"ReusableGroup.correctReference", #[]⟩] expected
  unless (match correct with | .matched _ _ _ => true | _ => false) do
    throwError "the actual retained relation reference did not install"

#print axioms randomized_installed
#print axioms randomizedAnd_installed
#print axioms chaumPedersen_installed
#print axioms validator_every_reply
end Tests.ReusableGroupInstallation
