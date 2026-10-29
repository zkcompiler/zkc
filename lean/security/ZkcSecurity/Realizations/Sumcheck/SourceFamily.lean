module

public import Zkc.Source.Structured.Template
public import ZkcSecurity.Realizations.Sumcheck.SourcePairReduction
public meta import ZkcTools.StructuredSource.Association

@[expose] public section

/-! A source family installation is indexed by the complete admitted program.
The shared two-value, degree-one reduction template fixes its helper identities,
roles and ABI. An installation checks those identities and bodies once; a root
may instantiate the template any number of times at source-owned occurrences.
No protocol name, digest or selected-source enumeration authorizes a body.
This representation does not cover GKR's three-coefficient message layout.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamily
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured NormalForm ReferenceLibrary
open ZkcExamples.Structured SumcheckReferenceInstallation

def initialHelper : Helper :=
  ⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local,
    [.field field], [.vector field, .field field]⟩

def tableHelper : Helper :=
  ⟨MultilinearSourceBindings.sumcheck.table, .local,
    [.vector field, .index, .index], [.vector field, .index, .index]⟩

def reductionSignature (name : String) : ProtocolSignature :=
  ⟨name, ["role00000000", "role00000001"], SumcheckVerifierBodies.reduceInputs,
    SumcheckVerifierBodies.reduceOutputs, [[0],[0],[0],[1],[1],[0,1],[1]], [[0],[0],[0],[0],[1],[1]]⟩

/-- All source-specific evidence consists of exact typed associations. The
mathematical laws below consume this evidence without rechecking the source.
The strict bound supports all-input terminal rejection, including malformed
raw tables; it is not a shape assumption on an adversarial input. -/
structure Installation (program : Zkc.Source.Structured.Program) where
  maximum : Nat
  maximum_small : maximum < 64
  reductionName : String
  reduction : Zkc.Source.Structured.Template.Association program.payload
    (reductionSignature reductionName) (SumcheckVerifierBodies.reduceBody maximum)
  roundBodies : Bodies program.payload.definitions MultilinearSourceBindings.sumcheck
  admissionBodies : Multilinear.Admission.Bodies program.payload.definitions field
    MultilinearSourceBindings.sumcheck SumcheckHelperBodies.checkHelper.name
  validatorBodies : ∀ model, SumcheckReductionReference.Bodies model program.payload.definitions
  producerBodies : ∀ model, SourceProducerReduction.Bodies model program.payload.definitions
  initial : ∀ model, BodyIn program.payload.definitions
    initialHelper (Sum.initial model field "s0").body

variable {program : Zkc.Source.Structured.Program} (installation : Installation program) (model : DomainModel)

def validatorPattern : InputPattern SumcheckVerifierBodies.reduceInputs :=
  .cons .absent (.cons .absent (.cons .absent (.cons .optional
    (.cons .optional (.cons .optional (.cons .optional .nil))))))

def producerPattern : InputPattern SumcheckVerifierBodies.reduceInputs :=
  .cons .optional (.cons .optional (.cons .optional (.cons .absent
    (.cons .absent (.cons .optional (.cons .absent .nil))))))

/-- The reusable callee law retains every optional input and full return slot. -/
theorem validator_invoke (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (args : Binders model validatorPattern.scope)
    (others : Values (Component model.Value) validatorPattern.absentTypes) :
    invokeProtocol (Occurrence.table model program.payload)
      (reductionSignature installation.reductionName) ctx (ctx.roles 1)
      (validatorPattern.fill model args others) =
      (SumcheckReductionReference.reference model program.payload.definitions
        (Occurrence.table model program.payload) installation.maximum ctx
        (entryAt args .here) (entryAt args (.there .here)) (entryAt args (.there (.there .here)))
        (entryAt args (.there (.there (.there .here))))).bind fun out =>
          .done (staticMask 1 out (reductionSignature installation.reductionName).outputScopes
            (Operands.identity SumcheckVerifierBodies.reduceOutputs)) := by
  apply installation.reduction.invoke 1 ctx distinct validatorPattern (by dsimp only [reductionSignature]; decide +kernel) args others
  · cases args with | cons point rest => cases rest with | cons scalar rest =>
      cases rest with | cons count rest => cases rest with | cons service rest =>
        cases rest
        exact SumcheckReductionReference.body_reference model _ program.payload.linked
          (installation.validatorBodies model) _ _ ctx distinct point scalar count service
  · dsimp only [reductionSignature]
    decide +kernel
  · dsimp only [reductionSignature]
    decide +kernel

def producerReduction (ctx : ProtocolContext) (args : Binders model producerPattern.scope) :=
  (SumcheckVerifierBodies.reduceBody installation.maximum).denote
    (participantMeaningWithOn model (.silent _) Occurrence.actions
      (tables model program.payload.definitions) (ctx.roles 0)
      (Occurrence.table model program.payload) ctx Occurrence.iterations)
    (producerPattern.environment model args).get

theorem producer_invoke (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (args : Binders model producerPattern.scope)
    (others : Values (Component model.Value) producerPattern.absentTypes) :
    invokeProtocol (Occurrence.table model program.payload)
      (reductionSignature installation.reductionName) ctx (ctx.roles 0)
      (producerPattern.fill model args others) =
      (producerReduction installation model ctx args).bind fun out =>
        .done (staticMask 0 out (reductionSignature installation.reductionName).outputScopes
          (Operands.identity SumcheckVerifierBodies.reduceOutputs)) :=
  installation.reduction.invoke 0 ctx distinct producerPattern (by dsimp only [reductionSignature]; decide +kernel) args others _ rfl
    (by dsimp only [reductionSignature]; decide +kernel) (by dsimp only [reductionSignature]; decide +kernel)

def one (ctx : ProtocolContext) (site : String)
    (raw : Option (List (model.Field field))) (scalar : Option (model.Field field))
    (count service : Option Nat) :=
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (tables model program.payload.definitions).closed initialHelper)
    (.cons scalar .nil)).bind fun initial =>
  (SumcheckReductionReference.reference model program.payload.definitions
    (Occurrence.table model program.payload) installation.maximum (ctx.enter site [0,1])
    (initial.get .here) (initial.get (.there .here)) count service).bind fun reduced =>
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (tables model program.payload.definitions).closed SumcheckHelperBodies.checkHelper)
    (.cons raw (.cons (reduced.get (.there (.there (.there (.there .here)))))
      (.cons (reduced.get (.there (.there (.there (.there (.there .here)))))) .nil)))).bind fun checked =>
  PIR.Process.done (checked.get .here)

def producerOne (site : String) (original : List (model.Field field)) (count : Nat) :=
  (Participant.owned 0 0
    (invoke (tables model program.payload.definitions).closed
      tableHelper)
    (.cons (some original) (.cons (some count) (.cons (some 1) .nil)))).bind fun admitted =>
  producerReduction installation model (ProtocolContext.enter {} site [0,1])
    (.cons (admitted.get .here) (.cons (admitted.get (.there .here))
      (.cons (admitted.get (.there (.there .here))) (.cons (some count) .nil))))

end ZkcSecurity.Realizations.Sumcheck.SourceFamily
