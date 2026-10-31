module

public import Zkc.Protocols.Sigma.SourceInstallation
public meta import ZkcTools.StructuredSource.InferReferenceInstallation
public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs
public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs
public import ZkcExamples.Structured.ChaumPedersenViews
public import ZkcExamples.Structured.SchnorrInteractive
public import ZkcExamples.Structured.SchnorrVariantsBodies
public import ZkcExamples.Structured.SchnorrHelpersData
public import ZkcExamples.Structured.SchnorrReorderedData
public import ZkcExamples.Structured.SchnorrEarlyChallengeData

@[expose] public section

/-! Actual original-stage source forms retain their named bodies. The shared
contract follows from open-process equations. Early challenge is admitted as a
different program, and its changed first action refutes that contract equation. -/
namespace ZkcExamples.Structured.SchnorrVariants
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

inductive Form where
  | original | helpers | reordered

namespace Helpers
structured_views SchnorrHelpersData.snapshot
  helpers [response := SchnorrVariantsBodies.response, equation := SchnorrVariantsBodies.equation]
  protocols [protocol := SchnorrVariantsBodies.helpers]
end Helpers

namespace Reordered
structured_views SchnorrReorderedData.snapshot
  helpers [] protocols [reordered := SchnorrVariantsBodies.reordered]
end Reordered

namespace Early
structured_views SchnorrEarlyChallengeData.snapshot
  helpers [] protocols [early := SchnorrVariantsBodies.early]
end Early

def helpersProgram : Program := Helpers.program
def reorderedProgram : Program := Reordered.program
def earlyProgram : Program := Early.program

theorem helpers_admitted : check SchnorrHelpersData.snapshot = .ok helpersProgram := Helpers.kernel_admission
theorem reordered_admitted : check SchnorrReorderedData.snapshot = .ok reorderedProgram :=
  Reordered.kernel_admission
theorem early_admitted : check SchnorrEarlyChallengeData.snapshot = .ok earlyProgram := Early.kernel_admission

def helpersImported : Imported SchnorrHelpersData.snapshot := ⟨helpersProgram, helpers_admitted⟩
def reorderedImported : Imported SchnorrReorderedData.snapshot := ⟨reorderedProgram, reordered_admitted⟩
def earlyImported : Imported SchnorrEarlyChallengeData.snapshot := ⟨earlyProgram, early_admitted⟩

theorem helpers_exact_subject : helpersProgram.snapshot = SchnorrHelpersData.snapshot := rfl
theorem reordered_exact_subject : reorderedProgram.snapshot = SchnorrReorderedData.snapshot := rfl
theorem early_exact_subject : earlyProgram.snapshot = SchnorrEarlyChallengeData.snapshot := rfl

def program : Form → Program
  | .original => SchnorrInteractive.program
  | .helpers => helpersProgram
  | .reordered => reorderedProgram

abbrev wiring := SchnorrInteractive.wiring

def responseHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math,
    [.field scalarDomain, .field scalarDomain, .field scalarDomain], [.field scalarDomain]⟩

def equationHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math,
    [.group groupDomain, .group groupDomain, .group groupDomain,
      .field scalarDomain, .field scalarDomain], [.boolean]⟩

theorem retained_named_calls : helpersProgram.payload.entry.helpers = [responseHelper, equationHelper] := rfl

theorem retained_helper_count : helpersProgram.payload.definitions.length = 2 := rfl

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Full-table named closure equations quantify over independent actual values. -/
theorem response_equation (nonce challenge secret : F) :
    invoke (helpersProgram.payload.tables F G).closed responseHelper
      (.cons nonce (.cons challenge (.cons secret .nil))) =
        .done (.cons (nonce + challenge * secret) .nil) := rfl

theorem equation_equation (base key commitment : G) (challenge answer : F) :
    invoke (helpersProgram.payload.tables F G).closed equationHelper
      (.cons base (.cons key (.cons commitment (.cons challenge (.cons answer .nil))))) =
        .done (.cons (decide (answer • base = commitment + challenge • key)) .nil) := rfl

theorem response_component_equation (nonce challenge secret : F) :
    invoke (helpersProgram.payload.tables F G).components responseHelper
      (.cons (some nonce) (.cons (some challenge) (.cons (some secret) .nil))) =
        .done (.cons (some (nonce + challenge * secret)) .nil) := rfl

def helpersProcess (base key : G) (service : Nat) :
    PIR.Process (participantInterface F G) (Option Bool) :=
  (helpersProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)

def reorderedProcess (base key : G) (service : Nat) :
    PIR.Process (participantInterface F G) (Option Bool) :=
  (reorderedProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)

def process : Form → G → G → Nat → PIR.Process (participantInterface F G) (Option Bool)
  | .original => SchnorrInteractive.process
  | .helpers => helpersProcess
  | .reordered => reorderedProcess

theorem helpers_equation (base key : G) (service : Nat) :
    process (F := F) .helpers base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := rfl

theorem reordered_equation (base key : G) (service : Nat) :
    process (F := F) .reordered base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := by
  apply PIR.Process.call_congr
  intro commitment
  apply PIR.Process.call_congr
  intro challenge
  change F at challenge
  apply PIR.Process.call_congr
  intro acknowledgement
  apply PIR.Process.call_congr
  intro answer
  change F at answer
  change PIR.Process.done (some (decide (answer • base = challenge • key + commitment))) =
    PIR.Process.done (some (decide (answer • base = commitment + challenge • key)))
  rw [add_comm (challenge • key) commitment]

def verifier (form : Form) : Zkc.Protocols.Schnorr.Common.Verifier F G := fun base key service =>
  (process form base key service).interpret CommonAdapter.project

theorem correspondence (form : Form) (base key : G) (service : Nat) :
    verifier (F := F) form base key service = Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  have equation : process (F := F) form base key service =
      (Zkc.Protocols.Schnorr.Common.experiment wiring base key service).interpret CommonAdapter.embed := by
    cases form with
    | original => exact SchnorrInteractive.process_equation base key service
    | helpers => exact helpers_equation base key service
    | reordered => exact reordered_equation base key service
  rw [verifier, equation, CommonAdapter.project_embed]

theorem contract (form : Form) :
    Zkc.Protocols.Schnorr.Common.VerifierContract wiring (verifier (F := F) (G := G) form) :=
  ⟨fun base key service => ⟨correspondence form base key service⟩⟩

abbrev run (form : Form) := Zkc.Protocols.Schnorr.Common.run (verifier (F := F) (G := G) form)

theorem perfect_completeness (form : Form) (base : G) (secret nonce challenge : F) (service : Nat) :
    (run form base (secret • base) service ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome =
      .returned (some true) :=
  (contract form).perfect_completeness base secret nonce challenge service

theorem special_soundness (form : Form) (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F) (distinct : first ≠ second)
    (acceptFirst : (run form base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run form base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key :=
  (contract form).special_soundness base key service prover first second distinct acceptFirst acceptSecond

def earlyVerifier (base key : G) (service : Nat) :
    PIR.Process (CommonAdapter.commonInterface F G) (Option Bool) :=
  ((earlyProgram.participant F G 1 (SchnorrInteractive.verifierInputs base key service)).bind
    fun values => .done (values.get .here)).interpret CommonAdapter.project

/-- The actual counterexample's query is reached before the commitment receive. -/
theorem early_equation (base key : G) (service : Nat) :
    earlyVerifier (F := F) base key service =
      .call (.query wiring.challengeSite scalarDomain (.cons service .nil)) fun (challenge : F) =>
      .call (.receive (.group groupDomain) wiring.commitmentSite 0) fun (commitment : G) =>
      .call (.send (ty := .field scalarDomain) wiring.deliverySite 0 challenge) fun _ =>
      .call (.receive (.field scalarDomain) wiring.responseSite 0) fun (answer : F) =>
      .done (some (decide (answer • base = commitment + challenge • key))) := rfl

private def beginsWithReceive {A : Type} : PIR.Process (CommonAdapter.commonInterface F G) A → Bool
  | .call (.receive ..) _ => true
  | _ => false

theorem early_not_corresponding (base key : G) (service : Nat) :
    earlyVerifier (F := F) base key service ≠ Zkc.Protocols.Schnorr.Common.experiment wiring base key service := by
  intro same
  have first := congrArg beginsWithReceive same
  change false = true at first
  exact Bool.noConfusion first

theorem early_no_contract :
    ¬ Zkc.Protocols.Schnorr.Common.VerifierContract wiring (earlyVerifier (F := F) (G := G)) := by
  intro claimed
  exact early_not_corresponding (F := F) (0 : G) 0 0 (claimed.realizes 0 0 0).process_eq

end ZkcExamples.Structured.SchnorrVariants

/-! One reusable installation on three actual admitted sources. The generated
root certificates remain the owners of constructed source correspondence. -/
namespace ZkcExamples.Structured.SchnorrVariants.Installations
open Zkc.Source Zkc.Source.Structured Zkc.Protocols.Sigma.Source
open ZkcExamples.Structured.Generated.Bindings
set_option maxRecDepth 10000
noncomputable section

def domains : Domains := ⟨"bls12-381.g1", "bls12-381.fr"⟩

def singleSites : Sites :=
  ⟨"s0", "s2", "label_636f6d6d69746d656e74_0", "",
    "label_6368616c6c656e6765", "label_64656c6976657279_0", "label_726573706f6e7365_0", ""⟩

def independentSites : Sites :=
  ⟨"s0", "s2", "label_66697273745f636f6d6d69746d656e74_0", "label_7365636f6e645f636f6d6d69746d656e74_0",
    "label_6368616c6c656e6765", "label_64656c6976657279_0",
    "label_66697273745f726573706f6e7365_0", "label_7365636f6e645f726573706f6e7365_0"⟩

def sharedSites : Sites := { independentSites with response := "label_726573706f6e7365_0" }

def randomizedMetadata : Metadata :=
  ⟨SchnorrRandomizedInputs.protocol0Signature.name,
    "role00000000", "role00000001", (some "zkl_dcbf81f97f37c181fef011e003f8b5e033842ddeccb04c1dea551fb7bf94978f")⟩

/-- Body inference chooses names only after the complete nominal signature and
mathematical body have been fixed. -/
def randomizedRelation : {name : String //
    BodyIn SchnorrRandomizedInputs.program.payload.definitions
      (relationHelper domains name) (relationBody domains)} := by
  infer_reference_installation

/-- Exact source identity and the full typed tree authorize this installation. -/
def randomizedAssociation : Template.Association SchnorrRandomizedInputs.program.payload
    (singleSignature domains randomizedMetadata) (singleBody domains randomizedMetadata singleSites) :=
  ⟨SchnorrRandomizedInputs.protocol0Definition, by structured_mem, rfl, rfl⟩

/-- The same source equation serves arbitrary optional inputs and every reply.
Hidden inputs remain arbitrary at the call boundary and are masked by scope. -/
theorem randomized_installed (model : DomainModel) (role : Nat) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (singleSignature domains randomizedMetadata).inputs)
    (visible : InputVisibility.patternVisible role pattern
      (singleSignature domains randomizedMetadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model SchnorrRandomizedInputs.program.payload)
      (singleSignature domains randomizedMetadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (singleView model domains randomizedMetadata singleSites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  exact single_install model domains randomizedMetadata singleSites randomizedAssociation
    role ctx distinct pattern visible arguments others

/-- The selected helper computes the separately fixed relation, for any domain
model. This is a full outcome equation, without a security conclusion. -/
theorem randomized_relation (model : DomainModel)
    (arguments : Values model.Value (relationHelper domains randomizedRelation.val).inputs) :
    invoke (SchnorrRandomizedInputs.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (relationHelper domains randomizedRelation.val) arguments =
        primitiveOutcome ((relationLaw model domains).reference arguments) :=
  ReferenceLaw.invoke (helper := relationHelper domains randomizedRelation.val)
    (relationLaw model domains) _ SchnorrRandomizedInputs.program.payload.linked
    randomizedRelation.property arguments trivial

def randomizedAndMetadata : Metadata :=
  ⟨SchnorrAndRandomizedInputs.protocol0Signature.name,
    "role00000000", "role00000001", (some "zkl_c0ba4fcd9fc5cad717b8a516be11f316ea8ea6ce0d721ba5e44a7408e5d76479")⟩

/-- Body inference chooses names only after the complete nominal signature and
mathematical body have been fixed. -/
def randomizedAndRelation : {name : String //
    BodyIn SchnorrAndRandomizedInputs.program.payload.definitions
      (independentHelper domains name) (independentRelationBody domains)} := by
  infer_reference_installation

/-- Exact source identity and the full typed tree authorize this installation. -/
def randomizedAndAssociation : Template.Association SchnorrAndRandomizedInputs.program.payload
    (independentSignature domains randomizedAndMetadata) (independentBody domains randomizedAndMetadata independentSites) :=
  ⟨SchnorrAndRandomizedInputs.protocol0Definition, by structured_mem, rfl, rfl⟩

/-- The same source equation serves arbitrary optional inputs and every reply.
Hidden inputs remain arbitrary at the call boundary and are masked by scope. -/
theorem randomizedAnd_installed (model : DomainModel) (role : Nat) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (independentSignature domains randomizedAndMetadata).inputs)
    (visible : InputVisibility.patternVisible role pattern
      (independentSignature domains randomizedAndMetadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model SchnorrAndRandomizedInputs.program.payload)
      (independentSignature domains randomizedAndMetadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (independentView model domains randomizedAndMetadata independentSites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  exact independent_install model domains randomizedAndMetadata independentSites randomizedAndAssociation
    role ctx distinct pattern visible arguments others

/-- The selected helper computes the separately fixed relation, for any domain
model. This is a full outcome equation, without a security conclusion. -/
theorem randomizedAnd_relation (model : DomainModel)
    (arguments : Values model.Value (independentHelper domains randomizedAndRelation.val).inputs) :
    invoke (SchnorrAndRandomizedInputs.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (independentHelper domains randomizedAndRelation.val) arguments =
        primitiveOutcome ((independentLaw model domains).reference arguments) :=
  ReferenceLaw.invoke (helper := independentHelper domains randomizedAndRelation.val)
    (independentLaw model domains) _ SchnorrAndRandomizedInputs.program.payload.linked
    randomizedAndRelation.property arguments trivial

def chaumPedersenMetadata : Metadata :=
  ⟨ChaumPedersenViews.program.payload.entry.signature.name,
    "role00000000", "role00000001", none⟩

/-- Body inference chooses names only after the complete nominal signature and
mathematical body have been fixed. -/
def chaumPedersenRelation : {name : String //
    BodyIn ChaumPedersenViews.program.payload.definitions
      (sharedHelper domains name) (sharedRelationBody domains)} := by
  infer_reference_installation

/-- Exact source identity and the full typed tree authorize this installation. -/
def chaumPedersenAssociation : Template.Association ChaumPedersenViews.program.payload
    (sharedSignature domains chaumPedersenMetadata) (sharedBody domains chaumPedersenMetadata sharedSites) :=
  ⟨ChaumPedersenViews.interactiveDefinition, by structured_mem, rfl, rfl⟩

/-- The same source equation serves arbitrary optional inputs and every reply.
Hidden inputs remain arbitrary at the call boundary and are masked by scope. -/
theorem chaumPedersen_installed (model : DomainModel) (role : Nat) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (sharedSignature domains chaumPedersenMetadata).inputs)
    (visible : InputVisibility.patternVisible role pattern
      (sharedSignature domains chaumPedersenMetadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model ChaumPedersenViews.program.payload)
      (sharedSignature domains chaumPedersenMetadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (sharedView model domains chaumPedersenMetadata sharedSites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  exact shared_install model domains chaumPedersenMetadata sharedSites chaumPedersenAssociation
    role ctx distinct pattern visible arguments others

/-- The selected helper computes the separately fixed relation, for any domain
model. This is a full outcome equation, without a security conclusion. -/
theorem chaumPedersen_relation (model : DomainModel)
    (arguments : Values model.Value (sharedHelper domains chaumPedersenRelation.val).inputs) :
    invoke (ChaumPedersenViews.program.payload.definitions.foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (sharedHelper domains chaumPedersenRelation.val) arguments =
        primitiveOutcome ((sharedLaw model domains).reference arguments) :=
  ReferenceLaw.invoke (helper := sharedHelper domains chaumPedersenRelation.val)
    (sharedLaw model domains) _ ChaumPedersenViews.program.payload.linked
    chaumPedersenRelation.property arguments trivial

end
end ZkcExamples.Structured.SchnorrVariants.Installations
