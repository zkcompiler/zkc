module

public import ZkcSecurity.Endpoint.Compiled
public import ZkcSecurity.FiatShamir.Soundness
public import ZkcSecurity.FiatShamir.Binding
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Installed

@[expose] public section

/-! # Artifact-indexed evidence

A security claim about a compiled Proof Entry is the application of a
registered endpoint theorem to evidence. The evidence is indexed by what the
claim is about:

- the **artifacts** (`Artifacts`): the original export, the constructed
  validator export, the published input types and, for program bytes, the
  executable validator;
- the **covered semantic endpoint** (`Semantics`): the compiled verifier's ideal
  meaning, or host validation of program bytes;
- the **statement form** (`Form`): a statement fixed before the prover runs, or
  chosen by the prover after its oracle queries;
- the **statement relation** (`StatementRelation`): the policy statements (the
  values a host binds), the model statements the family's mathematics is about,
  the functional relation between them, which model statements are false, and
  which policy statements the application counts as false;
- the **parameter regime** (`Regime`): how a challenge is derived from the
  oracle's answer, exactly uniform field elements (`Regime.exact`, the model
  `model.exact-uniform-challenges`) or a decoding of another answer type.

The property is fixed by the evidence structure: ordinary soundness here
(`SoundnessEvidence`), knowledge soundness with a Sigma family
(`ZkcSecurity.Endpoint.KnowledgeEvidence`).

Evidence of ordinary soundness carries the checked compilation (`Compiled`), a
model equation (the admitted original validator on a policy statement is the
family's model validator of every model statement it denotes, proved by `rfl`
or a generated normal form), the family evidence (`CertificateFamily`: a charged
certificate over the checked context's transcript interface, dooming the model
validator of every false model statement), a cost bound of the original
validator on every statement, and two requirements selected by the indices:

- **binding**, required when the form is adaptive (`BindingRequirement`): a
  binding codec of policy statements, which discharges statement determination,
  and coverage of the application's false statements (`Coverage`): either every
  application-false statement is false in the model or unmapped, with the
  validators of unmapped statements doomed, or the application's false-acceptance
  event implies the modeled one;
- **lowering**, required when the endpoint covers program bytes
  (`LoweringRequirement`): the artifacts' executable validator, accepted by the
  lowering rule against the constructed validator, with prepared helpers, sorted
  helper results and admitted published values.

Named hypotheses (`Hypothesis`) are instantiated propositions with their status:
a proof, or a reported assumption citing a registry entry of the hypothesis's
category (`ZkcSecurity.FiatShamir.ObligationStatus`). The endpoints of this
package need none of the collision-bounded identity, authenticated configuration
or verification-key obligations: their statements fix the artifacts and the
configuration before quantifying the adversary, and no current subject has a
verification key; a claim that needs one records it here.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

/-- The semantic endpoint a claim covers. -/
inductive Semantics where
  /-- The compiled verifier's ideal meaning. -/
  | idealMeaning
  /-- Host validation of the deployed program's proof bytes. -/
  | executableBytes
  deriving DecidableEq, Repr

/-- When the statement is chosen. -/
inductive Form where
  /-- Fixed before the prover runs. -/
  | fixed
  /-- Chosen by the prover after its oracle queries. -/
  | adaptive
  deriving DecidableEq, Repr

/-- The claimed property. -/
inductive Property where
  | soundness
  | knowledgeSoundness
  deriving DecidableEq, Repr

def Semantics.label : Semantics → String
  | .idealMeaning => "ideal-meaning"
  | .executableBytes => "executable-bytes"

def Form.label : Form → String
  | .fixed => "fixed"
  | .adaptive => "adaptive"

def Property.label : Property → String
  | .soundness => "soundness"
  | .knowledgeSoundness => "knowledge-soundness"

/-- The parameter regime of challenges: the oracle answers in `Answer`, and a
challenge is the decoding of the answer. -/
structure Regime (F : Type) where
  Answer : Type
  sampleable : SampleableType Answer
  decode : Answer → F

attribute [instance] Regime.sampleable

/-- Exactly uniform field challenges: the oracle answers field elements. -/
def Regime.exact (F : Type) [SampleableType F] : Regime F := ⟨F, inferInstance, id⟩

/-- What a claim's statements are: policy statements (values of the published
types), the model statements the family's mathematics is about, the functional
relation from policy to model statements, the false model statements, and the
policy statements the application counts as false. -/
structure StatementRelation (F G : Type) (publics : List Ty) where
  Model : Type
  models : Values (assignment F G) publics → Model → Prop
  functional : ∀ statement model other, models statement model → models statement other → model = other
  falseModel : Model → Prop
  applicationFalse : Values (assignment F G) publics → Prop

namespace StatementRelation
variable {F G : Type} {publics : List Ty} (relation : StatementRelation F G publics)

/-- A policy statement that denotes a false model statement. -/
def FalseStatement (statement : Values (assignment F G) publics) : Prop :=
  ∃ model, relation.models statement model ∧ relation.falseModel model

end StatementRelation

/-- A named hypothesis of a claim: an instantiated proposition of a registry
category and its status, a proof or a reported assumption citing a registry
entry of that category. -/
structure Hypothesis where
  category : Registry.Category
  claim : Prop
  status : ObligationStatus category claim

section Evidence
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The executable validator of the artifacts, accepted by the lowering rule
against the constructed validator, with its helpers prepared and sorted for the
admitted original's checked helpers, and admitting every statement's published
values. -/
structure LoweringEvidence (art : Artifacts) (c : Compiled art) (F G : Type) [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] where
  validator : Zkc.Executable.Validator
  program : art.program = some validator
  lowered : Zkc.Executable.Lowered
  accepted : Zkc.Executable.checkLowering Zkc.Executable.installed art.participant validator = .ok lowered
  prepared : ∀ name ∈ Zkc.Executable.Instruction.helpers art.participant.instructions,
    Zkc.Executable.Prepared Zkc.Executable.installed validator (helperTable c.imported.program F G) name
  sorted : ∀ call ∈ Zkc.Executable.Instruction.callList art.participant.instructions,
    Zkc.Executable.HelperSorted (helperTable c.imported.program F G) call.1 call.2
  admits : ∀ statement : art.Statement F G, validator.admits (encodeValues statement) = true

/-- Lowering evidence, required exactly when the endpoint covers program bytes. -/
def LoweringRequirement (art : Artifacts) (c : Compiled art) (F G : Type) [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] : Semantics → Type
  | .idealMeaning => PUnit
  | .executableBytes => LoweringEvidence art c F G

/-- The family evidence of ordinary soundness: a charged certificate over the
transcript interface of the checked context with the regime's decoding, whose
doomed set contains the model validator of every false model statement after
every initial transcript. -/
structure CertificateFamily (context : Context) (regime : Regime F) {publics : List Ty}
    (relation : StatementRelation F G publics) where
  validator : relation.Model → PIR.Proc (Actions F G) (Option Bool)
  charge : History F G → Event F G → ENNReal
  certificate : Typed.ChargedCertificate (interface (G := G) context regime.decode) (· = some true) charge
  doomed : ∀ model initial, relation.falseModel model → certificate.doomed initial (validator model)

/-- How the application's false statements are covered by the modeled bound. -/
inductive Coverage {publics : List Ty} (relation : StatementRelation F G publics)
    (codec : BindingCodec (Values (assignment F G) publics) (Event F G))
    (doomed : Values (assignment F G) publics → Prop) where
  /-- Every application-false statement is false in the model or unmapped, and
  the validator of every unmapped statement is doomed at its initial
  transcript. -/
  | rejects (covers : (StatementBinding.mk codec relation.models relation.functional).Covers
        relation.falseModel relation.applicationFalse)
      (unmapped : (StatementBinding.mk codec relation.models relation.functional).RejectsUnmapped doomed)
  /-- The application's false-acceptance event implies the modeled event. -/
  | implies (implication : EventImplication
      (fun result : Values (assignment F G) publics × PIR.Outcome (Option Bool) =>
        relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2)
      (fun result => relation.FalseStatement result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2))

/-- Binding evidence of an adaptive claim: a binding codec of every policy
statement, malformed ones included, as the initial transcript, and the coverage
of the application's false statements. -/
structure BindingEvidence {publics : List Ty} (relation : StatementRelation F G publics)
    (doomed : History F G → Values (assignment F G) publics → Prop) where
  codec : BindingCodec (Values (assignment F G) publics) (Event F G)
  coverage : Coverage relation codec fun statement => doomed (codec.encode statement) statement

/-- Binding evidence, required exactly when the statement is adaptive. -/
def BindingRequirement {publics : List Ty} (relation : StatementRelation F G publics)
    (doomed : History F G → Values (assignment F G) publics → Prop) : Form → Type
  | .fixed => PUnit
  | .adaptive => BindingEvidence relation doomed

/-- Evidence of ordinary soundness for artifacts, a covered endpoint, a statement
form, a statement relation and a regime. -/
structure SoundnessEvidence (art : Artifacts) (endpoint : Semantics) (form : Form)
    (relation : StatementRelation F G art.publics) (regime : Regime F) where
  compiled : Compiled art
  /-- The replaced service handle at which the model equation is read. -/
  handle : Nat
  family : CertificateFamily compiled.context regime relation
  /-- The admitted original validator of a statement is the family's model
  validator of every model statement it denotes. -/
  model : ∀ statement model, relation.models statement model →
    compiled.original statement handle = family.validator model
  /-- The charge of the original validator's queries on a statement, from every
  initial transcript. -/
  cost : art.Statement F G → ENNReal
  costBound : ∀ statement initial, Typed.ChargedCostBound (interface (G := G) compiled.context regime.decode)
    family.charge (compiled.original statement handle) initial (cost statement)
  binding : BindingRequirement relation
    (fun initial statement => family.certificate.doomed initial (compiled.original statement handle)) form
  lowering : LoweringRequirement art compiled F G endpoint
  hypotheses : List Hypothesis

end Evidence

end ZkcSecurity.Endpoint
