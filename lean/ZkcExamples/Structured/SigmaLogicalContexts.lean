module

public import ZkcExamples.Structured.LogicalContextControls
public import ZkcExamples.Structured.SchnorrAndBinding
public import ZkcExamples.Structured.ChaumPedersenBinding

@[expose] public section

/-! Shared and independent witnesses of the imported compositions, in one
logical vocabulary.

Both compositions are read through the component relation they combine: the
`DLog` relation retained by the Schnorr subject, keyed by its declaration. Each
atom observes a base and a key at the actual verifier's input ports of the
composed protocol and reads its witness from a lexical binder. Chaum–Pedersen
uses one binder in both atoms; Schnorr AND uses two. The composed protocols'
own retained formulas (`DLogEquality`, `DLogPair`) have their own identities, so
reusing `DLog` here is a proved equivalence with those formulas, not an
identification of declarations. -/
namespace ZkcExamples.Structured.SigmaLogicalContexts
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical
open LogicalContextControls (relations interpretation scalarSort dlog_meaning)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- `DLog` at a base and key observed at a boundary, with a binder as witness. -/
def dlogAt {snapshot : Snapshot} {imported : Imported snapshot} {owner : ContractBinding imported}
    {context : List (LogicalType relations.Sorts)}
    (base key : BoundarySelector owner.protocol.signature (.group groupDomain))
    (witness : Var context scalarSort) : Atom relations (assignment F G) owner.protocol.signature context :=
  ⟨.inr SchnorrBinding.application.relation.index,
    .cons (.observed base) (.cons (.observed key) (.cons (Term.binder witness) .nil))⟩

/-- An atom holds exactly when both observed ports are present and the key is
the binder's multiple of the base. -/
theorem dlogAt_holds {snapshot : Snapshot} {imported : Imported snapshot}
    {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType relations.Sorts)}
    (base key : BoundarySelector owner.protocol.signature (.group groupDomain))
    (witness : Var context scalarSort)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store (interpretation F G) owner invocation context) (baseValue keyValue : G) (value : F)
    (readBase : base.read {} boundary = some baseValue) (readKey : key.read {} boundary = some keyValue)
    (readWitness : store.get (.binder witness) = some value) :
    (dlogAt (F := F) base key witness).Holds (interpretation F G) {} boundary store ↔
      keyValue = value • baseValue := by
  have read : readTerms (interpretation F G) {} boundary store (dlogAt (F := F) base key witness).arguments =
      some (.cons baseValue (.cons keyValue (.cons value .nil))) := by
    simp only [dlogAt, readTerms, Term.read]
    erw [readBase, readKey, readWitness]
    rfl
  constructor
  · rintro ⟨arguments, present, holds⟩
    rw [read] at present
    cases present
    exact (dlog_meaning baseValue keyValue value).mp holds
  · intro equation
    exact ⟨_, read, (dlog_meaning baseValue keyValue value).mpr equation⟩

/-! ### Chaum–Pedersen: one witness binder -/

section Equality
open ChaumPedersenBinding

abbrev shared : List (LogicalType relations.Sorts) := [scalarSort]

def SharedHolds (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (witness : F) : Prop :=
  (dlogAt (F := F) firstBaseSelector firstKeySelector (context := shared) .here).Holds (interpretation F G)
      {} boundary (Store.ofValues (owner := owner) (invocation := rootInvocation) (.cons witness .nil)) ∧
    (dlogAt (F := F) secondBaseSelector secondKeySelector (context := shared) .here).Holds
      (interpretation F G) {} boundary
      (Store.ofValues (owner := owner) (invocation := rootInvocation) (.cons witness .nil))

/-- At any actual verifier run, the shared context holds exactly when the
retained `DLogEquality` formula holds at the verifier's bases and keys. -/
theorem shared_iff (firstBase firstKey secondBase secondKey : G) (service : Nat) (commitments : G × G)
    (challenge response witness : F) :
    SharedHolds (observedBoundary firstBase firstKey secondBase secondKey service commitments
        challenge response) witness ↔
      Relation firstBase firstKey secondBase secondKey witness := by
  unfold SharedHolds
  rw [dlogAt_holds _ _ _ _ _ firstBase firstKey witness rfl rfl rfl,
    dlogAt_holds _ _ _ _ _ secondBase secondKey witness rfl rfl rfl, relation_iff]

/-- Two accepting transcripts with one pair of commitments yield one binder
value for both atoms at the first run's actual boundary. -/
theorem shared_extraction (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (first second firstResponse secondResponse : F) (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments first firstResponse) = some true)
    (acceptSecond : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments second secondResponse) = some true) :
    SharedHolds (observedBoundary firstBase firstKey secondBase secondKey service commitments first
      firstResponse) ((firstResponse - secondResponse) / (first - second)) :=
  (shared_iff ..).mpr ((observed_target_iff ..).mp
    (extracted_target firstBase firstKey secondBase secondKey service commitments first second
      firstResponse secondResponse distinct acceptFirst acceptSecond))

end Equality

/-! ### Schnorr AND: two witness binders -/

section Pair
open SchnorrAndBinding

abbrev independent : List (LogicalType relations.Sorts) := [scalarSort, scalarSort]

def IndependentHolds
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (firstWitness secondWitness : F) : Prop :=
  (dlogAt (F := F) firstBaseSelector firstKeySelector (context := independent) .here).Holds
      (interpretation F G) {} boundary (Store.ofValues (owner := owner) (invocation := rootInvocation)
        (.cons firstWitness (.cons secondWitness .nil))) ∧
    (dlogAt (F := F) secondBaseSelector secondKeySelector (context := independent) (.there .here)).Holds
      (interpretation F G) {} boundary (Store.ofValues (owner := owner) (invocation := rootInvocation)
        (.cons firstWitness (.cons secondWitness .nil)))

theorem independent_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) (firstWitness secondWitness : F) :
    IndependentHolds (observedBoundary firstBase firstKey secondBase secondKey service commitments
        challenge responses) firstWitness secondWitness ↔
      Relation firstBase firstKey secondBase secondKey firstWitness secondWitness := by
  unfold IndependentHolds
  rw [dlogAt_holds _ _ _ _ _ firstBase firstKey firstWitness rfl rfl rfl,
    dlogAt_holds _ _ _ _ _ secondBase secondKey secondWitness rfl rfl rfl, relation_iff]

theorem independent_extraction (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (first second : F) (firstResponses secondResponses : F × F)
    (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments first firstResponses) = some true)
    (acceptSecond : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments second secondResponses) = some true) :
    IndependentHolds (observedBoundary firstBase firstKey secondBase secondKey service commitments first
        firstResponses) ((firstResponses.1 - secondResponses.1) / (first - second))
      ((firstResponses.2 - secondResponses.2) / (first - second)) :=
  (independent_iff ..).mpr ((observed_target_iff ..).mp
    (extracted_target firstBase firstKey secondBase secondKey service commitments first second
      firstResponses secondResponses distinct acceptFirst acceptSecond))

/-- The shared context read at the AND protocol's own ports: one binder for both
atoms. Nothing in the AND protocol establishes it. -/
def PairShared
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (witness : F) : Prop :=
  (dlogAt (F := F) firstBaseSelector firstKeySelector (context := shared) .here).Holds (interpretation F G)
      {} boundary (Store.ofValues (owner := owner) (invocation := rootInvocation) (.cons witness .nil)) ∧
    (dlogAt (F := F) secondBaseSelector secondKeySelector (context := shared) .here).Holds
      (interpretation F G) {} boundary
      (Store.ofValues (owner := owner) (invocation := rootInvocation) (.cons witness .nil))

theorem pairShared_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge : F) (responses : F × F) (witness : F) :
    PairShared (observedBoundary firstBase firstKey secondBase secondKey service commitments
        challenge responses) witness ↔
      firstKey = witness • firstBase ∧ secondKey = witness • secondBase := by
  unfold PairShared
  rw [dlogAt_holds _ _ _ _ _ firstBase firstKey witness rfl rfl rfl,
    dlogAt_holds _ _ _ _ _ secondBase secondKey witness rfl rfl rfl]

end Pair

end ZkcExamples.Structured.SigmaLogicalContexts
