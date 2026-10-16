module

public import Zkc.Source.Structured.LogicalChecking
public import Zkc.Source.Structured.LogicalTranslation
public import ZkcExamples.Structured.SchnorrBinding
public import ZkcExamples.Structured.SchnorrSharedWitness
public import ZkcExamples.Structured.SumcheckContractBindings

@[expose] public section

/-! Controls for logical identity: a static bound that changes no carrier, and
one shared witness versus two independent witnesses for a conjunction of the
actual retained Schnorr `DLog` relation. -/
namespace ZkcExamples.Structured.LogicalContextControls
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical

/-! ### A static bound that changes no carrier -/

inductive BoundedSort where
  | polynomial (bound : Nat)
  deriving DecidableEq

inductive BoundedPredicate where
  | degreeAtMost (bound : Nat)
  deriving DecidableEq

def boundedVocabulary : Vocabulary where
  Sorts := BoundedSort
  Predicates := BoundedPredicate
  Views := Empty
  sortIdentity
    | .polynomial bound => ⟨"polynomial::Bounded", [.domain "bls12-381.fr", .nat bound]⟩
  predicateIdentity
    | .degreeAtMost bound => ⟨"polynomial::DegreeAtMost", [.domain "bls12-381.fr", .nat bound]⟩
  viewIdentity := fun view => nomatch view
  arguments
    | .degreeAtMost bound => [.sort (.polynomial bound)]
  viewInput := fun view => nomatch view
  viewOutput := fun view => nomatch view

instance : DecidableEq boundedVocabulary.Sorts := inferInstanceAs (DecidableEq BoundedSort)

/-- Every bound has the same carrier, a coefficient list. -/
def boundedInterpretation : Interpretation boundedVocabulary (assignment Int Int) where
  sorts _ := List Int
  holds
    | .degreeAtMost bound, .cons coefficients .nil => coefficients.length ≤ bound + 1
  view := fun view => nomatch view

abbrev owner := SumcheckContractBindings.reductionRoot

def boundedAtom (bound : Nat) :
    Atom boundedVocabulary (assignment Int Int) owner.protocol.signature [.sort (.polynomial bound)] :=
  ⟨.degreeAtMost bound, .cons (Term.binder .here) .nil⟩

/-- Equal carriers, distinct identities, distinct meanings: the bound is part
of the instance although no native type or Lean carrier records it. -/
theorem phantom_bound :
    boundedInterpretation.sorts (.polynomial 1) = boundedInterpretation.sorts (.polynomial 2) ∧
    boundedVocabulary.sortIdentity (.polynomial 1) ≠ boundedVocabulary.sortIdentity (.polynomial 2) ∧
    (boundedAtom 2).Holds boundedInterpretation {} ⟨fun _ => .absent _ _, fun _ => .absent _ _⟩
      (Store.ofValues (owner := owner) (invocation := ⟨0, []⟩) (.cons ([0, 0, 1] : List Int) .nil)) ∧
    ¬ (boundedAtom 1).Holds boundedInterpretation {} ⟨fun _ => .absent _ _, fun _ => .absent _ _⟩
      (Store.ofValues (owner := owner) (invocation := ⟨0, []⟩) (.cons ([0, 0, 1] : List Int) .nil)) := by
  refine ⟨rfl, by decide, ⟨_, rfl, ?_⟩, ?_⟩
  · change ([0, 0, 1] : List Int).length ≤ 2 + 1
    decide
  · rintro ⟨arguments, read, holds⟩
    cases read
    change ([0, 0, 1] : List Int).length ≤ 1 + 1 at holds
    exact absurd holds (by decide)

def boundedResolution : Resolution boundedVocabulary :=
  .ofCandidates boundedVocabulary
    (fun identity => match identity.statics with
      | [_, .nat bound] => some (.polynomial bound) | _ => none)
    (fun identity => match identity.statics with
      | [_, .nat bound] => some (.degreeAtMost bound) | _ => none)

/-- The checker refuses a binder bounded by two where the predicate's instance
is bounded by one, although both carriers are coefficient lists. -/
theorem phantom_bound_refused :
    checkContext (Value := assignment Int Int) boundedResolution owner.protocol.signature
      ⟨[.library ⟨"polynomial::Bounded", [.domain "bls12-381.fr", .nat 2]⟩],
        [⟨⟨"polynomial::DegreeAtMost", [.domain "bls12-381.fr", .nat 1]⟩, [.binder 0]⟩]⟩ =
      .error (.sortMismatch 0) := by
  rfl

theorem matching_bound_checks :
    checkContext (Value := assignment Int Int) boundedResolution owner.protocol.signature
      ⟨[.library ⟨"polynomial::Bounded", [.domain "bls12-381.fr", .nat 1]⟩],
        [⟨⟨"polynomial::DegreeAtMost", [.domain "bls12-381.fr", .nat 1]⟩, [.binder 0]⟩]⟩ =
      .ok ⟨[.sort (.polynomial 1)], [boundedAtom 1]⟩ := by
  rfl

/-! ### Shared versus independent witness for a Schnorr conjunction -/

/-- A vocabulary with no library codes; retained relations are added to it. -/
def emptyVocabulary : Vocabulary where
  Sorts := Empty
  Predicates := Empty
  Views := Empty
  sortIdentity := fun code => nomatch code
  predicateIdentity := fun code => nomatch code
  viewIdentity := fun code => nomatch code
  arguments := fun code => nomatch code
  viewInput := fun code => nomatch code
  viewOutput := fun code => nomatch code

def emptyInterpretation (Value : Ty → Type) : Interpretation emptyVocabulary Value where
  sorts := fun code => nomatch code
  holds := fun code => nomatch code
  view := fun code => nomatch code

open SchnorrInteractive SchnorrBinding

abbrev relations := emptyVocabulary.withRelations SchnorrInteractiveData.snapshot

abbrev scalarSort : LogicalType relations.Sorts := .native (.field scalarDomain)
abbrev shared : List (LogicalType relations.Sorts) := [scalarSort]
abbrev independent : List (LogicalType relations.Sorts) := [scalarSort, scalarSort]

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The meaning of every retained relation of the imported Schnorr subject. -/
abbrev interpretation (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] : Interpretation relations (assignment F G) :=
  (emptyInterpretation (assignment F G)).withRelations (relationMeaning (environment (F := F) (G := G)))

/-- One application of the actual retained `DLog` relation with supplied public
values and a logical witness. -/
def dlog {context : List (LogicalType relations.Sorts)} (base key : G) (witness : Var context scalarSort) :
    Atom relations (assignment F G) SchnorrBinding.owner.protocol.signature context :=
  ⟨.inr application.relation.index,
    .cons (.supplied base) (.cons (.supplied key) (.cons (Term.binder witness) .nil))⟩

/-- The retained formula's one meaning: the key is the witness times the base. -/
theorem dlog_meaning (base key : G) (witness : F) :
    relationMeaning (environment (F := F) (G := G)) application.relation.index
      (.cons base (.cons key (.cons witness .nil))) ↔ key = witness • base :=
  ((target (F := F) (G := G)).interpretation.holds_iff_relationMeaning _).symm.trans
    (target.interpretation.holds_iff_predicate target_formula_law _ trivial)

abbrev boundary : BoundaryValuation (assignment F G) SchnorrBinding.owner.protocol.inputs
    SchnorrBinding.owner.protocol.outputs :=
  ⟨fun _ => .absent _ _, fun _ => .absent _ _⟩

/-- The conjunction with one witness binder used by both applications. -/
def SharedHolds (firstBase secondBase firstKey secondKey : G) (witness : F) : Prop :=
  (dlog (F := F) firstBase firstKey (context := shared) .here).Holds (interpretation F G) {} boundary
      (Store.ofValues (owner := SchnorrBinding.owner) (invocation := rootInvocation) (.cons witness .nil)) ∧
    (dlog (F := F) secondBase secondKey (context := shared) .here).Holds (interpretation F G) {} boundary
      (Store.ofValues (owner := SchnorrBinding.owner) (invocation := rootInvocation) (.cons witness .nil))

/-- The conjunction with two witness binders of the same sort. -/
def IndependentHolds (firstBase secondBase firstKey secondKey : G) (first second : F) : Prop :=
  (dlog (F := F) firstBase firstKey (context := independent) .here).Holds (interpretation F G) {} boundary
      (Store.ofValues (owner := SchnorrBinding.owner) (invocation := rootInvocation)
        (.cons first (.cons second .nil))) ∧
    (dlog (F := F) secondBase secondKey (context := independent) (.there .here)).Holds (interpretation F G) {}
      boundary (Store.ofValues (owner := SchnorrBinding.owner) (invocation := rootInvocation)
        (.cons first (.cons second .nil)))

theorem shared_iff (firstBase secondBase firstKey secondKey : G) (witness : F) :
    SharedHolds firstBase secondBase firstKey secondKey witness ↔
      SchnorrSharedWitness.Relation firstBase secondBase firstKey secondKey witness := by
  unfold SharedHolds SchnorrSharedWitness.Relation
  constructor
  · rintro ⟨⟨_, firstRead, firstHolds⟩, ⟨_, secondRead, secondHolds⟩⟩
    cases firstRead
    cases secondRead
    exact ⟨(dlog_meaning _ _ _).mp firstHolds, (dlog_meaning _ _ _).mp secondHolds⟩
  · rintro ⟨first, second⟩
    exact ⟨⟨_, rfl, (dlog_meaning _ _ _).mpr first⟩, ⟨_, rfl, (dlog_meaning _ _ _).mpr second⟩⟩

theorem independent_iff (firstBase secondBase firstKey secondKey : G) (first second : F) :
    IndependentHolds firstBase secondBase firstKey secondKey first second ↔
      firstKey = first • firstBase ∧ secondKey = second • secondBase := by
  unfold IndependentHolds
  constructor
  · rintro ⟨⟨_, firstRead, firstHolds⟩, ⟨_, secondRead, secondHolds⟩⟩
    cases firstRead
    cases secondRead
    exact ⟨(dlog_meaning _ _ _).mp firstHolds, (dlog_meaning _ _ _).mp secondHolds⟩
  · rintro ⟨firstEquation, secondEquation⟩
    exact ⟨⟨_, rfl, (dlog_meaning _ _ _).mpr firstEquation⟩,
      ⟨_, rfl, (dlog_meaning _ _ _).mpr secondEquation⟩⟩

/-- Sharing is a contraction: a shared witness gives an independent pair. -/
theorem shared_gives_independent (firstBase secondBase firstKey secondKey : G) (witness : F)
    (holds : SharedHolds firstBase secondBase firstKey secondKey witness) :
    IndependentHolds firstBase secondBase firstKey secondKey witness witness :=
  (independent_iff _ _ _ _ _ _).mpr ((shared_iff _ _ _ _ _).mp holds)

/-- Joint extraction: two accepting Chaum–Pedersen transcripts with one pair of
commitments, one response per challenge and distinct challenges yield a single
witness for the shared context. The witness is new; it is not a prover input. -/
theorem shared_extraction (firstBase secondBase firstKey secondKey firstCommit secondCommit : G)
    (firstChallenge secondChallenge firstResponse secondResponse : F)
    (distinct : firstChallenge ≠ secondChallenge)
    (firstAccept : firstResponse • firstBase = firstCommit + firstChallenge • firstKey ∧
      firstResponse • secondBase = secondCommit + firstChallenge • secondKey)
    (secondAccept : secondResponse • firstBase = firstCommit + secondChallenge • firstKey ∧
      secondResponse • secondBase = secondCommit + secondChallenge • secondKey) :
    SharedHolds firstBase secondBase firstKey secondKey
      ((firstResponse - secondResponse) / (firstChallenge - secondChallenge)) :=
  (shared_iff _ _ _ _ _).mpr (SchnorrSharedWitness.extract firstBase secondBase firstKey secondKey
    firstCommit secondCommit firstChallenge secondChallenge firstResponse secondResponse distinct
    firstAccept secondAccept)

/-- Two separate Schnorr extractions fill the independent context only. -/
theorem independent_extraction (firstBase secondBase firstKey secondKey firstCommit secondCommit : G)
    (firstChallenge secondChallenge : F) (firstResponses secondResponses : F × F)
    (distinct : firstChallenge ≠ secondChallenge)
    (firstAccept : firstResponses.1 • firstBase = firstCommit + firstChallenge • firstKey ∧
      firstResponses.2 • firstBase = firstCommit + secondChallenge • firstKey)
    (secondAccept : secondResponses.1 • secondBase = secondCommit + firstChallenge • secondKey ∧
      secondResponses.2 • secondBase = secondCommit + secondChallenge • secondKey) :
    IndependentHolds firstBase secondBase firstKey secondKey
      ((firstResponses.1 - firstResponses.2) / (firstChallenge - secondChallenge))
      ((secondResponses.1 - secondResponses.2) / (firstChallenge - secondChallenge)) :=
  (independent_iff _ _ _ _ _ _).mpr
    ⟨(Zkc.Protocols.Schnorr.extract_public_key firstBase firstKey firstCommit firstChallenge
        secondChallenge firstResponses.1 firstResponses.2 distinct firstAccept.1 firstAccept.2).symm,
      (Zkc.Protocols.Schnorr.extract_public_key secondBase secondKey secondCommit firstChallenge
        secondChallenge secondResponses.1 secondResponses.2 distinct secondAccept.1 secondAccept.2).symm⟩

/-- Over the rationals, the independent context is satisfiable for keys zero
and one at base one, while no single witness satisfies the shared context. -/
theorem independent_not_shared :
    IndependentHolds (F := ℚ) (G := ℚ) 1 1 0 1 0 1 ∧
      ¬ ∃ witness : ℚ, SharedHolds (F := ℚ) (G := ℚ) 1 1 0 1 witness := by
  constructor
  · exact (independent_iff _ _ _ _ _ _).mpr ⟨by simp, by simp⟩
  · rintro ⟨witness, holds⟩
    have relation := (shared_iff _ _ _ _ _).mp holds
    have zero : (0 : ℚ) = witness := by simpa using relation.1
    have one : (1 : ℚ) = witness := by simpa using relation.2
    exact zero_ne_one (zero.trans one.symm)

end ZkcExamples.Structured.LogicalContextControls
