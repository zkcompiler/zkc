module

public import ZkcSecurity.Endpoint.Compiled
public import ZkcSecurity.Endpoint.Contract
public import ZkcSecurity.Endpoint.Binding
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
- the **covered semantic endpoint** (`Semantics`): the compiled verifier's resource-free actual Domain
  execution, or host validation of program bytes;
- the **statement form** (`Form`): a statement fixed before the prover runs, or
  chosen by the prover after its oracle queries;
- the **application claim**: for ordinary soundness, which policy statements
  (the values a host binds, malformed ones included) the application counts as
  false; for knowledge soundness, the application's witness relation. A
  registered claim takes it from the admitted original's retained contract, read
  at the policy's published inputs, so the evidence cannot choose it: the claim's
  application declaration states the evidence's type with the contract's
  constant, and the kernel checks the evidence against that type. The generic
  endpoints are parametric in it, and no false statement is required to exist;
- the **parameter regime** (`Regime`): how a challenge is derived from the
  oracle's answer, exactly uniform field elements (`Regime.exact`, the model
  `model.exact-uniform-challenges`) or a decoding of another answer type.

The property is fixed by the evidence structure: ordinary soundness here
(`SoundnessEvidence`), knowledge soundness with a Sigma family
(`ZkcSecurity.Endpoint.KnowledgeEvidence`).

Evidence of ordinary soundness carries the checked compilation (`Compiled`), the
family's model relation (`ModelRelation`: model statements, the functional
relation from policy statements to them and the false model statements), a
model equation (the admitted original validator on a policy statement is the
family's model validator of every model statement it denotes, proved by `rfl`
or a generated normal form), the family evidence (`CertificateFamily`: a charged
certificate over the checked context's transcript interface, dooming the model
validator of every false model statement), the **coverage** of the application
claim by the family (every application-false statement is false in the model
or denotes no model statement, and the original validator of a statement that
denotes none is doomed after every initial transcript), a cost bound of the
original validator on every statement, and two requirements selected by the
indices:

- **binding**, required when the form is adaptive (`BindingRequirement`): the
  application context the host binds, so that every policy statement's initial
  transcript is its policy-derived binding event, which discharges statement
  determination (`policyCodec`);
- **lowering**, required when the endpoint covers program bytes
  (`LoweringRequirement`): the artifacts' executable validator, accepted by the
  lowering rule against the constructed validator, with prepared helpers, sorted
  helper results and admitted published values.

Coverage is required at both forms, after every initial transcript; a fixed
statement needs it only at the transcript it is run from.

Named hypotheses (`Hypothesis`) cite a registry entry by identifier, with the
proposition its schema instantiates to and its status: a proof, or a reported
assumption citing a registry entry of the hypothesis's category
(`ZkcSecurity.FiatShamir.ObligationStatus`). That the proposition is an
instantiation of the cited entry's schema is checked by the declaration-record
emitter, which records the instantiation's arguments. The endpoints of this
package need none of the collision-bounded identity, authenticated configuration
or verification-key obligations: their statements fix the artifacts and the
configuration before quantifying the adversary, and no current subject has a
verification key; a claim that needs one records it here.

This record covers the current compiled path: one field and group, a total
decoder of one answer type into the field, the common participant interface,
and the ordinary random-oracle experiment. Domain-indexed carriers,
request-dependent decoding with refusal, separately identified decoder and
proximity laws with admissible parameters, and provider or joint-stage evidence
with event and budget transport are later extensions of this path.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

/-- The semantic endpoint a claim covers. -/
inductive Semantics where
  /-- Resource-free actual Domain execution (retained request spelling). -/
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

/-- A policy statement the application claim counts as false. -/
def ApplicationFalse {Statement : Type} (claim : Statement → Prop) (statement : Statement) : Prop :=
  claim statement

/-- The family's model relation: model statements, the functional relation from
policy statements to the model statements they denote, and the false model
statements. -/
structure ModelRelation (F G : Type) (publics : List Ty) where
  Model : Type
  models : Values (assignment F G) publics → Model → Prop
  functional : ∀ statement model other, models statement model → models statement other → model = other
  falseModel : Model → Prop

namespace ModelRelation
variable {F G : Type} {publics : List Ty} (relation : ModelRelation F G publics)

/-- A policy statement that denotes a false model statement. -/
def FalseStatement (statement : Values (assignment F G) publics) : Prop :=
  ∃ model, relation.models statement model ∧ relation.falseModel model

/-- A policy statement that denotes no model statement. -/
def Unmapped (statement : Values (assignment F G) publics) : Prop :=
  ∀ model, ¬ relation.models statement model

end ModelRelation

/-- A named hypothesis of a claim: the registry identifier it cites, an
instantiated proposition of that entry's category and its status, a proof or a
reported assumption citing a registry entry of that category. The declaration
record emitter checks that the proposition's head is the cited entry's schema
and records its arguments. -/
structure Hypothesis where
  identifier : String
  category : Registry.Category
  claim : Prop
  status : ObligationStatus category claim

section Evidence
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Fixed byte/Domain transport at every resource budget. Static lowering
admission alone cannot produce this semantic connection. -/
def BytePruning (art : Artifacts) (c : Compiled art) (F G : Type) [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (validator : Zkc.Executable.Validator) (lowered : Zkc.Executable.Lowered) : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : art.Statement F G) (initial : History F G) (bytes : List UInt8),
    Zkc.Executable.Prunes (fun accepted => accepted = false)
      (Zkc.Executable.validate Zkc.Executable.installed validator c.context challenge codec budget binding
        c.position (encodeValues statement) initial bytes)
      (verdict <$> c.verifier challenge statement initial
        (Zkc.Executable.decodeProof codec (Zkc.Executable.Plan.types (encodeValues statement) lowered.plan)
          (bytes.drop 40)))

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
  /-- Actual all-budget byte/Domain transport, separately proved from the static
  lowering check. Its validator, decoder, input policy and target are fixed. -/
  pruning : BytePruning art c F G validator lowered

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
    (relation : ModelRelation F G publics) where
  validator : relation.Model → PIR.Process (Actions F G) (Option Bool)
  charge : History F G → Event F G → ENNReal
  certificate : Typed.ChargedCertificate (interface (G := G) context regime.decode) (· = some true) charge
  doomed : ∀ model initial, relation.falseModel model → certificate.doomed initial (validator model)

end Evidence

/-- Binding evidence of an adaptive claim: the application context the host
binds, so that the initial transcript of every policy statement, malformed ones
included, is its policy-derived binding event (`policyCodec`). -/
structure BindingEvidence where
  application : String

/-- Binding evidence, required exactly when the statement is adaptive. -/
def BindingRequirement : Form → Type
  | .fixed => PUnit
  | .adaptive => BindingEvidence

section Evidence
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Evidence of ordinary soundness for artifacts, a covered endpoint, a statement
form, the application claim (the policy statements it counts as false) and a
regime. -/
structure SoundnessEvidence (art : Artifacts) (endpoint : Semantics) (form : Form)
    (claim : art.Statement F G → Prop) (regime : Regime F) where
  compiled : Compiled art
  connection : compiled.SourceConnection (F := F) (G := G)
  /-- The retained target or the explicitly declared imported-language fixture. -/
  target : SoundnessTarget compiled F G
  /-- A compatibility name for exactly the derived false set. No independently
  chosen predicate can discharge this field. -/
  claimPinned : ∀ statement, claim statement ↔ target.FalseStatement statement
  /-- The replaced service handle at which the model equation is read. -/
  handle : Nat
  relation : ModelRelation F G art.publics
  family : CertificateFamily compiled.context regime relation
  /-- The admitted original validator of a statement is the family's model
  validator of every model statement it denotes. -/
  model : ∀ statement model, relation.models statement model →
    compiled.original statement handle = family.validator model
  /-- Every statement the application counts as false is false in the model or
  denotes no model statement. -/
  covers : ∀ statement, claim statement → relation.FalseStatement statement ∨ relation.Unmapped statement
  /-- The original validator of a statement that denotes no model statement is
  doomed after every initial transcript. -/
  unmapped : ∀ statement, relation.Unmapped statement → ∀ initial,
    family.certificate.doomed initial (compiled.original statement handle)
  /-- The charge of the original validator's queries on a statement, from every
  initial transcript. -/
  cost : art.Statement F G → ENNReal
  costBound : ∀ statement initial, Typed.ChargedCostBound (interface (G := G) compiled.context regime.decode)
    family.charge (compiled.original statement handle) initial (cost statement)
  binding : BindingRequirement form
  lowering : LoweringRequirement art compiled F G endpoint
  hypotheses : List Hypothesis

end Evidence

end ZkcSecurity.Endpoint
