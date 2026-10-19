module

@[expose] public section

/-! The interaction pattern of a programmable history provider.

A provider that is not an installed native suite binds its own construction
identity. Its canonical binding is an interaction pattern that the compiler
emits: the ordered steps of the protocol, each with its kind, the sort of the
values it carries, how many it carries (with static maxima) and its label. The
pattern's digest is the binding event for construction identity and a
collision-bounded binding term. It binds configuration that changes the step
sequence (counts, maxima, gate difficulties); it does not replace statement
binding, authenticated configuration that leaves the shape unchanged, or
verification-key correctness. This module defines the data shape only: no
digest, encoding or semantics.

The step kinds are those of Plonky3 0.8.0's pattern vocabulary: a public value
both roles hold before the run, an absorbed producer message, a hint that is
not absorbed, a challenge, a proof-of-work step and a salt. The sort is a
parameter, so a catalogue's sort vocabulary attaches without this module
depending on it. A proof-of-work step carries its difficulty in bits as its
count, as in Plonky3.

**The salt kind is reserved.** Salts absorbed before any challenge are part of
zero-knowledge Fiat–Shamir variants (BCS, Plonky3, Chiesa–Orrù). The kind is
part of the vocabulary now, because adding it later would change request and
transcript identities, but it has no semantics yet: an admissible pattern has
no salt step (`Pattern.Admissible`), and admission refuses any other.
-/

set_option autoImplicit false

namespace Zkc.Construction

/-- The role of one step of an interaction pattern. -/
inductive StepKind where
  /-- A public value both roles hold before the run. -/
  | publicValue
  /-- A producer message, absorbed. -/
  | message
  /-- A producer value that is not absorbed. -/
  | hint
  /-- A value derived from the transcript. -/
  | challenge
  /-- A proof-of-work step: the producer grinds and the validator checks. -/
  | pow
  /-- A salt absorbed before any challenge. Reserved: it has no semantics yet. -/
  | salt
  deriving DecidableEq, Repr

/-- How many values a step carries. -/
inductive StepCount where
  /-- No value. -/
  | none
  /-- Exactly one value. -/
  | one
  /-- A statically known number of values; a proof-of-work step's difficulty in
  bits. -/
  | exactly (count : Nat)
  /-- At most a static maximum of values; the actual count travels with them. -/
  | atMost (maximum : Nat)
  deriving DecidableEq, Repr

/-- One step of an interaction pattern: its kind, the sort of its values, how
many values it carries, and its label. -/
structure PatternStep (ValueSort : Type) where
  kind : StepKind
  sort : ValueSort
  count : StepCount
  label : String
  deriving DecidableEq, Repr

/-- An interaction pattern: the steps of a protocol in order. -/
abbrev Pattern (ValueSort : Type) := List (PatternStep ValueSort)

/-- An admissible pattern has no salt step: the salt kind is reserved and
admission refuses it until it has semantics. -/
def Pattern.Admissible {ValueSort : Type} (pattern : Pattern ValueSort) : Prop :=
  ∀ step ∈ pattern, step.kind ≠ .salt

instance {ValueSort : Type} (pattern : Pattern ValueSort) : Decidable pattern.Admissible :=
  inferInstanceAs (Decidable (∀ step ∈ pattern, step.kind ≠ .salt))

end Zkc.Construction
