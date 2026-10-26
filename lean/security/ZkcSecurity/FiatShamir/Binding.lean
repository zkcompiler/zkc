module

public import ZkcSecurity.FiatShamir.Interface
public import ZkcSecurity.Stage.Relation
public import ZkcSecurity.Registry
public import Zkc.Construction.Binding

@[expose] public section

/-! Binding codecs and the typed public-value binding event.

Exact statement determination (`Typed.Determined`) asks that the initial
transcript of a statement, followed by any events, identify the statement. It
quantifies over every statement the prover can output, malformed ones included
(for example a raw vector whose length is not `2 ^ count`), so a codec that
discharges it must be injective and prefix-free on the whole statement type,
not only on well-formed statements.

- The typed public-value binding event `Zkc.Construction.PublicBinding Scalar`
  is the application context with a row (`Zkc.Construction.Row`) of the
  statement's typed public values (`Zkc.Construction.PublicValue`): scalars,
  vectors whose length is part of the value, indices with their bounds, and
  counts. Equal events have equal rows by constructor injectivity. These are
  binding representations; validity and canonical order are established
  separately, which keeps malformed values representable.
- `BindingCodec Stmt E` is an injective, prefix-free encoding of statements
  as initial histories of events `E`; it discharges `Typed.Determined`
  (`BindingCodec.determined`).
- `BindingCodec.single` binds a statement as one typed public-value binding
  event, through any injective embedding of binding events into the transcript
  events; it is prefix-free because every statement's history has one event.
  `determined_single` is the resulting determination lemma: it needs only that
  the embedding and the statement's row are injective.
- `StatementBinding Policy Model E` pairs a binding codec of the policy's
  statements, the public inputs the host binds, with the relation between policy
  statements and the model's statements, the statements the library's theorem
  is about. The relation is functional: a policy statement relates to at most
  one model statement. Determination then transfers: the initial history of a
  policy statement, followed by any events, determines its model statement
  (`StatementBinding.determines`), and a choice of policy statement for each
  model statement gives determined model histories
  (`StatementBinding.determined_represent`). That the serialization of the
  typed representation is injective, and that the native transcript absorbs
  that serialization, are separate obligations; a typed public-value binding
  discharges statement determination only.
- Determination says nothing about policy statements that denote no model
  statement (`StatementBinding.Unmapped`): with the empty relation every policy
  statement is unmapped and none is false in the model. An adaptive endpoint
  therefore needs coverage of the application's false statements, in one of two
  forms. Either every application-false policy statement is false in the model
  or unmapped (`StatementBinding.Covers`), and, as a separate obligation, the
  validators of unmapped statements are doomed
  (`StatementBinding.RejectsUnmapped`): then the validators of all
  application-false statements are doomed whenever those of model-false
  statements are (`StatementBinding.doomed_of_covers`). Coverage alone does not
  reject anything: under the empty relation it holds while every statement is
  accepted. Or
  the application's false-acceptance event implies the modeled event
  (`EventImplication`), which transfers the bound
  (`EventImplication.prEvent_le`).

**The other binding obligations.** Besides statement determination, a claim may
need three obligations, recorded as typed fields of its evidence with their
status (`ObligationStatus`: a proof, or a reported assumption that cites a
registry entry of the obligation's own category, `ZkcSecurity.Registry`):

- collision-bounded identity (`CollisionBoundedIdentity`): a collision game
  over every digest in scope, those computed at setup, those the verifier
  recomputes and those given before the protocol, bounded at every budget;
- authenticated configuration (`AuthenticatedConfiguration`): the
  configuration is fixed before the adversary is quantified, each configuration
  value comes from a compile-time constant or a pinned asset, and every
  parameter the attacker selects lies in its admissible range before a security
  level is claimed;
- verification-key correctness (`VerificationKeyCorrectness`): the key is the
  intended one, by checked recomputation, a certificate or a realization
  theorem.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open Zkc.Construction (PublicValue Row PublicBinding)

/-- A binding codec: an encoding of every statement, malformed ones included,
as an initial transcript history, injective and prefix-free. -/
structure BindingCodec (Stmt E : Type) where
  encode : Stmt → List E
  injective : Function.Injective encode
  /-- No statement's history is a proper prefix of another's. -/
  prefixFree : ∀ statement other (rest : List E), encode statement ++ rest = encode other → rest = []

variable {Stmt E Scalar : Type}

/-- An injective, prefix-free codec determines the statement from its initial
history followed by any events. -/
theorem BindingCodec.determined (codec : BindingCodec Stmt E) : Typed.Determined codec.encode := by
  intro statement other rest otherRest same
  rcases List.append_eq_append_iff.mp same with ⟨middle, longer, -⟩ | ⟨middle, longer, -⟩
  · have empty := codec.prefixFree statement other middle longer.symm
    subst empty
    exact codec.injective (by simpa using longer.symm)
  · have empty := codec.prefixFree other statement middle longer.symm
    subst empty
    exact codec.injective (by simpa using longer)

/-- Any injective event embedding is a prefix-free singleton history. The
argument need not use a particular recursive public-value representation. -/
def BindingCodec.singleton (event : Stmt → E) (injective : Function.Injective event) :
    BindingCodec Stmt E where
  encode statement := [event statement]
  injective _ _ same := injective (List.cons.inj same).1
  prefixFree _ _ rest same := by
    simpa using congrArg List.length same

/-- The codec that binds a statement as one typed public-value binding event of
the application context and the statement's canonical row. -/
def BindingCodec.single (bind : PublicBinding Scalar → E) (bindInjective : Function.Injective bind)
    (context : String) (row : Stmt → Row Scalar) (rowInjective : Function.Injective row) :
    BindingCodec Stmt E where
  encode statement := [bind ⟨context, row statement⟩]
  injective statement other same := by
    simp only [List.cons.injEq, and_true] at same
    exact rowInjective (congrArg PublicBinding.row (bindInjective same))
  prefixFree statement other rest same := by
    simpa using congrArg List.length same

/-- Exact statement determination from constructor injectivity: when binding
events embed injectively into the transcript events and a statement's canonical
row determines the statement, the one-event initial histories determine the
statement. -/
theorem determined_single (bind : PublicBinding Scalar → E)
    (bindInjective : Function.Injective bind) (context : String) (row : Stmt → Row Scalar)
    (rowInjective : Function.Injective row) :
    Typed.Determined fun statement : Stmt => [bind ⟨context, row statement⟩] :=
  (BindingCodec.single bind bindInjective context row rowInjective).determined

/-- A statement binding: a binding codec of the policy's statements, and a functional relation
from policy statements to the model's statements. -/
structure StatementBinding (Policy Model E : Type) where
  codec : BindingCodec Policy E
  /-- The model statement a policy statement denotes. -/
  models : Policy → Model → Prop
  /-- A policy statement denotes at most one model statement. -/
  functional : ∀ policy model other, models policy model → models policy other → model = other

namespace StatementBinding
variable {Policy Model : Type} (binding : StatementBinding Policy Model E)

/-- The initial history of a policy statement, followed by any events, determines the model
statement it denotes. -/
theorem determines (policy other : Policy) (model otherModel : Model) (rest otherRest : List E)
    (denotes : binding.models policy model) (otherDenotes : binding.models other otherModel)
    (same : binding.codec.encode policy ++ rest = binding.codec.encode other ++ otherRest) :
    model = otherModel := by
  obtain rfl := binding.codec.determined policy other rest otherRest same
  exact binding.functional policy model otherModel denotes otherDenotes

/-- Choosing, for each model statement, a policy statement that denotes it gives model
histories that determine the model statement. -/
theorem determined_represent (represent : Model → Policy)
    (represents : ∀ model, binding.models (represent model) model) :
    Typed.Determined fun model => binding.codec.encode (represent model) :=
  fun model other rest otherRest same =>
    binding.determines (represent model) (represent other) model other rest otherRest
      (represents model) (represents other) same

/-- A policy statement is false when the model statement it denotes is false. -/
def falsePolicy (falseModel : Model → Prop) (policy : Policy) : Prop :=
  ∃ model, binding.models policy model ∧ falseModel model

theorem falsePolicy_iff (falseModel : Model → Prop) (policy : Policy) (model : Model)
    (denotes : binding.models policy model) :
    binding.falsePolicy falseModel policy ↔ falseModel model := by
  constructor
  · rintro ⟨other, otherDenotes, falseOther⟩
    rwa [binding.functional policy model other denotes otherDenotes]
  · exact fun falseModel => ⟨model, denotes, falseModel⟩

/-- A policy statement that denotes no model statement. -/
def Unmapped (policy : Policy) : Prop :=
  ∀ model, ¬ binding.models policy model

/-- An unmapped policy statement is never false in the model. -/
theorem not_falsePolicy_of_unmapped (falseModel : Model → Prop) (policy : Policy)
    (unmapped : binding.Unmapped policy) : ¬ binding.falsePolicy falseModel policy :=
  fun ⟨model, denotes, _⟩ => unmapped model denotes

/-- Coverage of the application's false statements: every policy statement false for the
application is false in the model or unmapped. Coverage says nothing about how unmapped statements
are treated; their rejection is `RejectsUnmapped`. -/
def Covers (falseModel : Model → Prop) (applicationFalse : Policy → Prop) : Prop :=
  ∀ policy, applicationFalse policy →
    binding.falsePolicy falseModel policy ∨ binding.Unmapped policy

/-- Rejection of unmapped statements: the validator of every policy statement that denotes no
model statement is doomed. -/
def RejectsUnmapped (doomed : Policy → Prop) : Prop :=
  ∀ policy, binding.Unmapped policy → doomed policy

/-- With coverage and the rejection of unmapped statements, the application's false statements are
doomed whenever the model's false statements are. -/
theorem doomed_of_covers {falseModel : Model → Prop} {applicationFalse : Policy → Prop}
    {doomed : Policy → Prop} (covers : binding.Covers falseModel applicationFalse)
    (modelDoomed : ∀ policy model, binding.models policy model → falseModel model → doomed policy)
    (unmappedDoomed : binding.RejectsUnmapped doomed) :
    ∀ policy, applicationFalse policy → doomed policy := by
  intro policy falseForApplication
  rcases covers policy falseForApplication with ⟨model, denotes, falseAt⟩ | unmapped
  · exact modelDoomed policy model denotes falseAt
  · exact unmappedDoomed policy unmapped

end StatementBinding

/-- The application's false-acceptance event implies the modeled event. -/
def EventImplication {Result : Type} (applicationEvent modeledEvent : Result → Prop) : Prop :=
  ∀ result, applicationEvent result → modeledEvent result

/-- An event implication transfers a bound on the modeled event to the application's event. -/
theorem EventImplication.prEvent_le {Result : Type} {applicationEvent modeledEvent : Result → Prop}
    (implies : EventImplication applicationEvent modeledEvent) (experiment : ProbComp Result) :
    Pr{let result ← experiment}[applicationEvent result] ≤
      Pr{let result ← experiment}[modeledEvent result] :=
  prEvent_mono _ _ _ implies

/-! ### The other binding obligations -/

/-- How an obligation of a registry category stands: discharged by a proof, or a reported
assumption citing a registry entry of that category. -/
inductive ObligationStatus (category : Registry.Category) (claim : Prop) where
  | proved (proof : claim)
  | assumed (entry : Registry.Entry) (registered : entry ∈ Registry.entries)
      (categorized : entry.category = category)

/-- The registry entry with an identifier. -/
def registryEntry (identifier : String) : Option Registry.Entry :=
  Registry.entries.find? fun entry => entry.identifier == identifier

/-- A reported assumption citing the registry entry with an identifier, when that entry exists
and has the obligation's category. -/
def ObligationStatus.cite {category : Registry.Category} {claim : Prop} (identifier : String)
    (entry : Registry.Entry) (found : registryEntry identifier = some entry)
    (categorized : entry.category = category) : ObligationStatus category claim :=
  .assumed entry (List.mem_of_find?_eq_some found) categorized

/-- The obligation is discharged by a proof. -/
def ObligationStatus.Discharged {category : Registry.Category} {claim : Prop} :
    ObligationStatus category claim → Prop
  | .proved _ => True
  | .assumed _ _ _ => False

theorem ObligationStatus.holds {category : Registry.Category} {claim : Prop} :
    (status : ObligationStatus category claim) → status.Discharged → claim
  | .proved proof, _ => proof

/-- Where a digest in scope comes from. -/
inductive DigestOrigin where
  /-- Computed when the scheme is set up. -/
  | setup
  /-- Recomputed by the verifier. -/
  | recomputation
  /-- Given before the protocol, such as the digest of a pinned asset. -/
  | preexisting
  deriving DecidableEq

/-- Collision-bounded identity: a collision game over every digest in scope, whatever its
origin, and its bound at every budget. -/
structure CollisionBoundedIdentity where
  /-- Adversaries that output two distinct inputs in scope with one digest. -/
  collisions : Stage.Game
  /-- The origins of the digests the collision game covers. -/
  origins : List DigestOrigin
  complete : ∀ origin, origin ∈ origins
  bound : collisions.Budget → ENNReal
  status : ObligationStatus (.binding .collisionBoundedIdentity) (collisions.Bounded bound)

/-- Where a configuration value comes from. -/
inductive Provenance where
  /-- A compile-time constant of the compiled artifact. -/
  | constant
  /-- A pinned asset, identified by its digest. -/
  | pinned (digest : String)

/-- Authenticated configuration: the configuration and its provenance are fixed before the
adversary is quantified, and the security claim holds at every attacker-selected parameter in
its admissible range. -/
structure AuthenticatedConfiguration (Config Parameter : Type) where
  configuration : Config
  provenance : Provenance
  admissible : Parameter → Prop
  /-- The security claim at a configuration and a parameter; it quantifies the adversary
  after both. -/
  claim : Config → Parameter → Prop
  status : ObligationStatus (.binding .authenticatedConfiguration)
    (∀ parameter, admissible parameter → claim configuration parameter)

/-- How a verification key is shown to be the intended one. -/
inductive KeyEvidence where
  /-- Checked recomputation of the key. -/
  | recomputation
  /-- A certificate checked against the key. -/
  | certificate
  /-- A realization theorem. -/
  | realization

/-- Verification-key correctness: the key used is the intended one, with the kind of evidence
that shows it. -/
structure VerificationKeyCorrectness (Key : Type) where
  key : Key
  intended : Key
  evidence : KeyEvidence
  status : ObligationStatus (.binding .verificationKey) (key = intended)

end ZkcSecurity.FiatShamir
