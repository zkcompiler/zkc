module

public import ZkcSecurity.FiatShamir.Interface
public import ZkcSecurity.Stage.Relation
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

**The other binding obligations.** Besides statement determination, a claim may
need three obligations, recorded as typed fields of its evidence with their
status (`ObligationStatus`: a proof, or a reported assumption named by its
registry identifier):

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

end StatementBinding

/-! ### The other binding obligations -/

/-- How an obligation stands: discharged by a proof, or a reported assumption named by its
registry identifier. -/
inductive ObligationStatus (claim : Prop) where
  | proved (proof : claim)
  | assumed (identifier : String)

/-- The obligation is discharged by a proof. -/
def ObligationStatus.Discharged {claim : Prop} : ObligationStatus claim → Prop
  | .proved _ => True
  | .assumed _ => False

theorem ObligationStatus.holds {claim : Prop} :
    (status : ObligationStatus claim) → status.Discharged → claim
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
  status : ObligationStatus (collisions.Bounded bound)

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
  status : ObligationStatus (∀ parameter, admissible parameter → claim configuration parameter)

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
  status : ObligationStatus (key = intended)

end ZkcSecurity.FiatShamir
