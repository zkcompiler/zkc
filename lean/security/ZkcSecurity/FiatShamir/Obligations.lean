module

public import ZkcSecurity.FiatShamir.Sampling

@[expose] public section

/-! Formal readings of Fiat–Shamir construction obligations.

The [construction obligations](../../../../../docs/spec/ir/construction-obligations.md)
constrain where the values a verifier depends on come from, how a provider maps
transcript queries to primitive inputs, which laws realized answers and hash
handlers satisfy, and how a re-encoding of oracle keys may depend on the oracle.
Each definition below reads one obligation over abstract carriers. A context
`C` is the data present at one point of an execution: the absorbed history,
earlier challenge answers, bound statement inputs and authenticated
configuration, but also data an obligation does not admit, such as the received
message itself, an unbound public parameter or an adversary's output. A
projection `scope : C → K` keeps the admitted part.

- `Determines scope value`: `value` is a function of the admitted part. The
  observation obligations are its instances: an omitted value is reconstructible
  from the absorbed history (`Reconstructible`), the metadata of a certified
  opening is fixed at its receive point (`FixedAtReceivePoint`), an
  explicit-input challenge covers what its check reads (`CoveredByInput`), and
  an explicit-input construction shares the primitive query of equal declared
  inputs (`SharesEqualInputs`).
- `Omission.Classified`: an omitted producer value is reconstructible, a
  certified opening, or followed by no selected request.
- `CausalReencoding` and `PreservesQueryEquality`: the causality and
  equality-preservation conditions of a causal replay coupling.
- `DistinctPrimitiveInputs`: the history-to-primitive correspondence of a
  history provider; `PrefixFreeEncoding`: injective, prefix-free serialization.
- `ExactWithRefusal`: the law of a decoder whose realized subdistribution is its
  success probability times the ideal law.
- `HashLaws`: the hash-consistency and failure laws of a handler, with
  `TotalConsistentHandler` as a stronger specialization that never stops.
- `ConstructionCorrect`: a constructed meaning is the transform of the original
  for every challenge function.
- `AuthenticatedOperand`, `ProductionRange` and `AuthenticatedConfiguration`:
  provenance of security operands and of configuration.
- `GateSite.Placement` (no event absorbed between the gate step and the
  request), `GateSite.ReadsState` and `GateSite.AbsorbsWitness`: the admission
  conditions of a proof-of-work gate; `GateSite.GateDetermines` is a weaker,
  necessary dependency condition of placement.

Exact statement determination is `ZkcSecurity.FiatShamir.Typed.Determined`, a
realized law with a factor and slack is `ZkcSecurity.FiatShamir.Realized`, and
the per-prefix local obligation of a certificate is
`ZkcSecurity.FiatShamir.Typed.Step`.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Obligations
open OracleComp

section Determination
variable {C K V : Type}

/-- `value` is determined by the admitted part `scope` of the context: two
contexts with the same admitted part have the same value. -/
def Determines (scope : C → K) (value : C → V) : Prop :=
  ∀ first second, scope first = scope second → value first = value second

/-- A value read through the admitted part is determined by it. -/
theorem determines_of_factor {scope : C → K} {value : C → V} (read : K → V)
    (factors : ∀ context, value context = read (scope context)) : Determines scope value :=
  fun first second same => by rw [factors, factors, same]

/-- Two contexts with the same admitted part and different values refute
determination. -/
theorem not_determines {scope : C → K} {value : C → V} {first second : C}
    (same : scope first = scope second) (different : value first ≠ value second) :
    ¬ Determines scope value :=
  fun determined => different (determined first second same)

/-- A value omitted from the transcript is reconstructible when the absorbed
history, together with earlier challenge answers, determines it. -/
abbrev Reconstructible (absorbed : C → K) (value : C → V) : Prop :=
  Determines absorbed value

/-- An opening's metadata (root, positions, dimensions and interpretation) is
fixed at its receive point when the admissible sources determine it: absorbed
messages, bound statement inputs, authenticated configuration and earlier
challenge answers. Values merely visible to both roles are not admissible. -/
abbrev FixedAtReceivePoint (sources : C → K) (metadata : C → V) : Prop :=
  Determines sources metadata

/-- A value that a check using an explicit-input challenge reads, and that the
producer controls or that is a statement input, is covered when the challenge's
encoded input determines it. -/
abbrev CoveredByInput (input : C → K) (value : C → V) : Prop :=
  Determines input value

/-- Exact primitive-query sharing: positions with equal declared inputs issue
the same primitive query, so they share one oracle cell. -/
abbrev SharesEqualInputs (input : C → K) (query : C → V) : Prop :=
  Determines input query

end Determination

section Omission

/-- A producer value that a construction leaves out of its transcript at one
point: the absorbed history there (with earlier answers), the omitted value,
whether a selected request is reachable after it, and whether it is an opening
meeting the certified-opening conditions. A value that is not an opening of a
committed table has `certifiedOpening := False`. -/
structure Omission (C K V : Type) where
  absorbed : C → K
  value : C → V
  laterRequest : Prop
  certifiedOpening : Prop

/-- Certified omission: the omitted value is reconstructible from the absorbed
history, a certified opening, or terminal (no selected request follows it). -/
def Omission.Classified {C K V : Type} (omission : Omission C K V) : Prop :=
  Reconstructible omission.absorbed omission.value ∨ omission.certifiedOpening ∨
    ¬ omission.laterRequest

/-- A value that is neither reconstructible, nor an opening, nor terminal
belongs to no omission class. -/
theorem Omission.not_classified {C K V : Type} {omission : Omission C K V}
    (unreconstructible : ¬ Reconstructible omission.absorbed omission.value)
    (notOpening : ¬ omission.certifiedOpening) (later : omission.laterRequest) :
    ¬ omission.Classified := by
  rintro (reconstructible | opening | terminal)
  · exact unreconstructible reconstructible
  · exact notOpening opening
  · exact terminal later

end Omission

section Reencoding
variable {D R : Type}

/-- A re-encoding of oracle keys that may read the oracle table is causal when
each mapped key is computed from the key and from answers at strictly earlier
keys only, never from the answer being selected. -/
def CausalReencoding (earlier : D → D → Prop) (reencode : (D → R) → D → D) : Prop :=
  ∀ table other key, (∀ previous, earlier previous key → table previous = other previous) →
    reencode table key = reencode other key

/-- A re-encoding preserves query equality in both directions: under every
table, equal keys map to equal keys and distinct keys to distinct keys. -/
def PreservesQueryEquality (reencode : (D → R) → D → D) : Prop :=
  ∀ table, Function.Injective (reencode table)

end Reencoding

section Providers

/-- The history-to-primitive correspondence of a history provider: distinct
reachable transcript queries reach distinct primitive inputs. -/
def DistinctPrimitiveInputs {Q X : Type} (reachable : Q → Prop) (input : Q → X) : Prop :=
  ∀ first second, reachable first → reachable second → input first = input second →
    first = second

/-- An injective, prefix-free serialization: no encoding followed by more data
is another encoding, unless the two values and encodings are equal. -/
def PrefixFreeEncoding {H B : Type} (encode : H → List B) : Prop :=
  ∀ first second rest, encode first ++ rest = encode second → first = second ∧ rest = []

theorem PrefixFreeEncoding.injective {H B : Type} {encode : H → List B}
    (prefixFree : PrefixFreeEncoding encode) : Function.Injective encode :=
  fun first second same => (prefixFree first second [] (by rw [List.append_nil, same])).1

end Providers

section Laws
variable {B R : Type} [SampleableType B] [SampleableType R]

/-- Exact with refusal: for every event, a successful decoding lands in it with
the success probability times the event's ideal probability. -/
def ExactWithRefusal (decode : B → Option R) : Prop :=
  ∀ event : R → Prop,
    Pr{let answer ← $ᵗ B}[∃ value, decode answer = some value ∧ event value] =
      Pr{let answer ← $ᵗ B}[(decode answer).isSome] * Pr{let value ← $ᵗ R}[event value]

/-- An exact decoding with refusal is realized with factor one and no slack:
the success probability is at most one. -/
theorem ExactWithRefusal.realized {decode : B → Option R} (exact : ExactWithRefusal decode) :
    Realized decode 1 0 := by
  intro event
  rw [exact event, add_zero]
  exact mul_le_mul' (prEvent_le_one _) le_rfl

end Laws

section Handlers
variable {I : PIR.Signature} {S E : Type}

/-- The laws of law-conditioned outcome preservation for the operations
`hashing` selects, read as: the outcome of every such call, a reply or a stop,
is a function of the operation and its arguments alone, whatever state the
handler is in. Equal inputs then receive equal answers (hash consistency), and
no stop depends on the number or order of earlier calls (the failure law); a
stop that the input alone determines is allowed. -/
def HashLaws (hashing : I.Op → Prop) (handler : PIR.Handler I S E) : Prop :=
  ∃ outcome : (operation : I.Op) → PIR.Outcome (I.Reply operation), ∀ operation,
    hashing operation → ∀ state, (handler operation state).outcome = outcome operation

/-- A stronger specialization of the hash laws: every selected call returns a
fixed function of the operation, whatever the handler's state, and never
stops. -/
def TotalConsistentHandler (hashing : I.Op → Prop) (handler : PIR.Handler I S E) : Prop :=
  ∃ answer : (operation : I.Op) → I.Reply operation, ∀ operation, hashing operation →
    ∀ state, (handler operation state).outcome = .returned (answer operation)

theorem TotalConsistentHandler.hashLaws {hashing : I.Op → Prop} {handler : PIR.Handler I S E}
    (total : TotalConsistentHandler hashing handler) : HashLaws hashing handler := by
  obtain ⟨answer, answers⟩ := total
  exact ⟨fun operation => .returned (answer operation), answers⟩

end Handlers

section Constructions

/-- Construction correctness for a provider: the constructed meaning equals the
transform of the original for every challenge function. -/
def ConstructionCorrect {Challenge Outcome : Type} (constructed transformed : Challenge → Outcome) :
    Prop :=
  ∀ challenge, constructed challenge = transformed challenge

end Constructions

section Provenance
variable {C K G : Type}

/-- Provenance of an operand that enters a certificate error: either the bound
statement inputs and authenticated configuration `fixed` determine it, or the
validator's check before the request (`checked`) admits only values in the
authenticated admissible range on the side where the error grows. -/
def AuthenticatedOperand (fixed : C → K) (operand : C → ℕ) (checked : C → Prop)
    (admissible : ℕ → Prop) : Prop :=
  Determines fixed operand ∨ ∀ context, checked context → admissible (operand context)

/-- A production claim: every value of the operand that the deployment admits
supports the claimed bound. -/
def ProductionRange (operand : C → ℕ) (admitted : C → Prop) (supports : ℕ → Prop) : Prop :=
  ∀ context, admitted context → supports (operand context)

/-- Authenticated configuration is fixed by the deployment before the
adversary runs: it is the same in every context, whatever the adversary does. -/
def AuthenticatedConfiguration (configuration : C → G) : Prop :=
  ∀ first second, configuration first = configuration second

end Provenance

section Gates

/-- One proof-of-work gate attached to a request: the primitive input of the gate
step, the transcript state before the gate, the producer's witness, the events
absorbed between the gate step and the request, and the input from which the
gated value is derived. -/
structure GateSite (C G S W Ev Q : Type) where
  gateInput : C → G
  state : C → S
  witness : C → W
  between : C → List Ev
  requestInput : C → Q

variable {C G S W Ev Q : Type}

/-- Placement: nothing is absorbed between the gate step and the request. -/
def GateSite.Placement (site : GateSite C G S W Ev Q) : Prop :=
  ∀ context, site.between context = []

/-- A necessary dependency condition of placement, weaker than it: the gate's
input determines the input of the gated value. It also holds when a fixed
constant is absorbed in between, so it does not replace `Placement`. -/
def GateSite.GateDetermines (site : GateSite C G S W Ev Q) : Prop :=
  Determines site.gateInput site.requestInput

/-- The gate step's primitive input includes the full transcript state before
the gate, read as: it determines that state. -/
def GateSite.ReadsState (site : GateSite C G S W Ev Q) : Prop :=
  Determines site.gateInput site.state

/-- The state from which the gated value is derived has absorbed the witness,
read as: its input determines the witness. -/
def GateSite.AbsorbsWitness (site : GateSite C G S W Ev Q) : Prop :=
  Determines site.requestInput site.witness

end Gates

end ZkcSecurity.FiatShamir.Obligations
