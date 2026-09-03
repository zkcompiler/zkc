import M0.Eval

/-!
# First-active execution and the Terminal contract

This file is experimental proof text for the closed laws in Interactive Core
Section 10.  Guard atoms retain structural identity but have no denotation in
the syntax.  A valuation supplies that denotation only to state the universal
first-active theorem.  Scope openings are explicit schedule metadata and do
not participate in the attempt predicate: they are deterministic, unguarded
boundaries.

The must-fact analysis is defined over the complete portable `Term` carrier.
The owner text supplies transfer clauses for Boolean literals, variables,
lets, conditionals, and primitive calls, and now closes every remaining
constructor as contributing no literal.  The forward state is the closed
`Region`, `Implies`, `Disjoint`, `ClaimStatus`, and `LiveClaims` algebra.
-/

namespace M0

/-! ## First-active execution -/

/-- Opaque identity of a complete structurally authenticated guard body. -/
abbrev GuardAtom := Nat

inductive AttemptGuard where
  | always
  | evaluate (atom : GuardAtom)
  deriving Repr, DecidableEq

/-- One occurrence in total order.  `openingsBefore` records the deterministic,
unguarded scope boundaries processed immediately before the occurrence. -/
structure ScheduledOccurrence where
  openingsBefore : List Nat
  guard : AttemptGuard
  isTerminal : Bool
  deriving Repr, DecidableEq

def AttemptGuards : AttemptGuard → List GuardAtom
  | .always => []
  | .evaluate atom => [atom]

def AttemptGuard.Holds (valuation : GuardAtom → Bool) : AttemptGuard → Prop
  | .always => True
  | .evaluate atom => valuation atom = true

instance (valuation : GuardAtom → Bool) (guard : AttemptGuard) :
    Decidable (guard.Holds valuation) := by
  cases guard <;> unfold AttemptGuard.Holds <;> infer_instance

/-- The occurrence exists, its guard is true, and no earlier active terminal
has stopped the run. -/
def Attempted (schedule : List ScheduledOccurrence)
    (valuation : GuardAtom → Bool) (index : Nat) : Prop :=
  ∃ occurrence,
    schedule[index]? = some occurrence ∧
    occurrence.guard.Holds valuation ∧
    ∀ priorIndex prior,
      schedule[priorIndex]? = some prior →
      priorIndex < index →
      prior.isTerminal = true →
      ¬ prior.guard.Holds valuation

/-- The syntactic Section 10 law, retaining both occurrence lookups so the
predicate is executable on a finite carrier. -/
def AttemptedWhenever (schedule : List ScheduledOccurrence)
    (later earlier : Nat) : Prop :=
  match schedule[later]?, schedule[earlier]? with
  | some laterOccurrence, some earlierOccurrence =>
      earlier < later ∧
      ∀ atom, atom ∈ AttemptGuards earlierOccurrence.guard →
        atom ∈ AttemptGuards laterOccurrence.guard
  | _, _ => False

instance (schedule : List ScheduledOccurrence) (later earlier : Nat) :
    Decidable (AttemptedWhenever schedule later earlier) := by
  unfold AttemptedWhenever
  split <;> infer_instance

theorem guard_holds_of_attempt_guards_subset
    (valuation : GuardAtom → Bool) (earlier later : AttemptGuard)
    (laterHolds : later.Holds valuation)
    (subset : ∀ atom, atom ∈ AttemptGuards earlier → atom ∈ AttemptGuards later) :
    earlier.Holds valuation := by
  cases earlier with
  | always => trivial
  | evaluate atom =>
      have member := subset atom (by simp [AttemptGuards])
      cases later with
      | always => simp [AttemptGuards] at member
      | evaluate laterAtom =>
          simp [AttemptGuards] at member
          subst laterAtom
          exact laterHolds

/-- Universal soundness of the syntactic attempt law.  The quantification is
over every valuation; no finite truth-table oracle occurs in the statement or
proof. -/
theorem attemptedWhenever_sound
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (later earlier : Nat)
    (law : AttemptedWhenever schedule later earlier)
    (laterAttempted : Attempted schedule valuation later) :
    Attempted schedule valuation earlier := by
  rcases laterAttempted with
    ⟨actualLater, actualLaterAt, laterHolds, noEarlierTerminal⟩
  cases lawLaterAt : schedule[later]? with
  | none => simp [AttemptedWhenever, lawLaterAt] at law
  | some lawLater =>
      cases lawEarlierAt : schedule[earlier]? with
      | none => simp [AttemptedWhenever, lawLaterAt, lawEarlierAt] at law
      | some lawEarlier =>
          simp only [AttemptedWhenever, lawLaterAt, lawEarlierAt] at law
          have sameLater : lawLater = actualLater := by
            rw [lawLaterAt] at actualLaterAt
            exact Option.some.inj actualLaterAt
          subst lawLater
          have earlierBefore := law.1
          have subset := law.2
          refine ⟨lawEarlier, lawEarlierAt, ?_, ?_⟩
          · exact guard_holds_of_attempt_guards_subset valuation lawEarlier.guard
              actualLater.guard laterHolds subset
          · intro priorIndex prior priorAt priorBefore terminal
            exact noEarlierTerminal priorIndex prior priorAt
              (Nat.lt_trans priorBefore earlierBefore) terminal

/-- Scope-opening membership is schedule data alone and is therefore
independent of a guard valuation. -/
def OpeningBefore (schedule : List ScheduledOccurrence) (index scope : Nat) : Prop :=
  ∃ occurrence, schedule[index]? = some occurrence ∧ scope ∈ occurrence.openingsBefore

theorem opening_before_valuation_independent
    (schedule : List ScheduledOccurrence) (index scope : Nat)
    (_left _right : GuardAtom → Bool) :
    OpeningBefore schedule index scope ↔ OpeningBefore schedule index scope := by
  rfl

/-! ## Closed occurrence regions -/

def earlierTerminalFalseAtoms (schedule : List ScheduledOccurrence) (index : Nat) :
    List GuardAtom :=
  (List.range index).filterMap fun priorIndex =>
    match schedule[priorIndex]? with
    | some prior =>
        if prior.isTerminal then
          match prior.guard with
          | .always => none
          | .evaluate atom => some atom
        else none
    | none => none

def hasEarlierAlways (schedule : List ScheduledOccurrence) (index : Nat) : Bool :=
  (List.range index).any fun priorIndex =>
    match schedule[priorIndex]? with
    | some prior => prior.isTerminal && prior.guard == .always
    | none => false

theorem mem_earlierTerminalFalseAtoms_iff
    (schedule : List ScheduledOccurrence) (index atom : Nat) :
    atom ∈ earlierTerminalFalseAtoms schedule index ↔
      ∃ priorIndex prior,
        schedule[priorIndex]? = some prior ∧ priorIndex < index ∧
        prior.isTerminal = true ∧ prior.guard = .evaluate atom := by
  simp only [earlierTerminalFalseAtoms, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨priorIndex, before, found⟩
    cases priorAt : schedule[priorIndex]? with
    | none => simp [priorAt] at found
    | some prior =>
      cases terminal : prior.isTerminal <;> simp [priorAt, terminal] at found
      cases guard : prior.guard <;> simp [guard] at found
      case evaluate actual =>
        subst actual
        exact ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
  · rintro ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
    refine ⟨priorIndex, before, ?_⟩
    simp [priorAt, terminal, guard]

theorem hasEarlierAlways_eq_true_iff
    (schedule : List ScheduledOccurrence) (index : Nat) :
    hasEarlierAlways schedule index = true ↔
      ∃ priorIndex prior,
        schedule[priorIndex]? = some prior ∧ priorIndex < index ∧
        prior.isTerminal = true ∧ prior.guard = .always := by
  simp only [hasEarlierAlways, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨priorIndex, before, active⟩
    cases priorAt : schedule[priorIndex]? with
    | none => simp [priorAt] at active
    | some prior =>
      cases terminal : prior.isTerminal <;> simp [priorAt, terminal] at active
      cases guard : prior.guard <;> simp [guard] at active
      exact ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
  · rintro ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
    refine ⟨priorIndex, before, ?_⟩
    simp [priorAt, terminal, guard]

def regionOverlap (left right : List GuardAtom) : Bool :=
  left.any fun atom => right.contains atom

theorem regionOverlap_eq_true_iff (left right : List GuardAtom) :
    regionOverlap left right = true ↔ ∃ atom, atom ∈ left ∧ atom ∈ right := by
  simp [regionOverlap, List.any_eq_true]

structure AttemptRegion where
  requiredTrue : List GuardAtom
  requiredFalse : List GuardAtom
  impossible : Bool
  deriving Repr, DecidableEq

/-- The closed region of one occurrence.  An absent occurrence is unreachable;
an in-range occurrence carries its own positive guard and every earlier
terminal guard negatively. -/
def Region (schedule : List ScheduledOccurrence) (index : Nat) : AttemptRegion :=
  match schedule[index]? with
  | none => { requiredTrue := [], requiredFalse := [], impossible := true }
  | some occurrence =>
      let requiredTrue := AttemptGuards occurrence.guard
      let requiredFalse := earlierTerminalFalseAtoms schedule index
      { requiredTrue
        requiredFalse
        impossible := hasEarlierAlways schedule index ||
          regionOverlap requiredTrue requiredFalse }

def AttemptRegion.LiteralsHold (region : AttemptRegion)
    (valuation : GuardAtom → Bool) : Prop :=
  (∀ atom, atom ∈ region.requiredTrue → valuation atom = true) ∧
  (∀ atom, atom ∈ region.requiredFalse → valuation atom = false)

def AttemptRegion.Holds (region : AttemptRegion)
    (valuation : GuardAtom → Bool) : Prop :=
  region.impossible = false ∧ region.LiteralsHold valuation

theorem guard_holds_iff_required_true (valuation : GuardAtom → Bool)
    (guard : AttemptGuard) :
    guard.Holds valuation ↔
      ∀ atom, atom ∈ AttemptGuards guard → valuation atom = true := by
  cases guard <;> simp [AttemptGuard.Holds, AttemptGuards]

def EarlierTerminalsInactive (schedule : List ScheduledOccurrence)
    (valuation : GuardAtom → Bool) (index : Nat) : Prop :=
  ∀ priorIndex prior,
    schedule[priorIndex]? = some prior →
    priorIndex < index →
    prior.isTerminal = true →
    ¬ prior.guard.Holds valuation

theorem earlierTerminalsInactive_iff
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (index : Nat) :
    EarlierTerminalsInactive schedule valuation index ↔
      hasEarlierAlways schedule index = false ∧
      ∀ atom, atom ∈ earlierTerminalFalseAtoms schedule index →
        valuation atom = false := by
  constructor
  · intro inactive
    constructor
    · apply Bool.eq_false_iff.mpr
      intro hasAlways
      obtain ⟨priorIndex, prior, priorAt, before, terminal, guard⟩ :=
        (hasEarlierAlways_eq_true_iff schedule index).mp hasAlways
      have stopped := inactive priorIndex prior priorAt before terminal
      rw [guard] at stopped
      exact stopped trivial
    · intro atom member
      obtain ⟨priorIndex, prior, priorAt, before, terminal, guard⟩ :=
        (mem_earlierTerminalFalseAtoms_iff schedule index atom).mp member
      have stopped := inactive priorIndex prior priorAt before terminal
      rw [guard] at stopped
      cases value : valuation atom with
      | false => rfl
      | true =>
          exact False.elim (stopped (by simp [AttemptGuard.Holds, value]))
  · rintro ⟨noAlways, falseAtoms⟩
    intro priorIndex prior priorAt before terminal
    cases guard : prior.guard with
    | always =>
        have present : hasEarlierAlways schedule index = true :=
          (hasEarlierAlways_eq_true_iff schedule index).mpr
            ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
        rw [noAlways] at present
        contradiction
    | evaluate atom =>
        have member : atom ∈ earlierTerminalFalseAtoms schedule index :=
          (mem_earlierTerminalFalseAtoms_iff schedule index atom).mpr
            ⟨priorIndex, prior, priorAt, before, terminal, guard⟩
        have value := falseAtoms atom member
        simp [AttemptGuard.Holds, value]

theorem attempted_iff_guard_and_earlier_inactive
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (index : Nat) (occurrence : ScheduledOccurrence)
    (atIndex : schedule[index]? = some occurrence) :
    Attempted schedule valuation index ↔
      occurrence.guard.Holds valuation ∧
      EarlierTerminalsInactive schedule valuation index := by
  constructor
  · rintro ⟨actual, actualAt, holds, inactive⟩
    have same : actual = occurrence := by
      rw [atIndex] at actualAt
      exact Option.some.inj actualAt.symm
    subst actual
    exact ⟨holds, inactive⟩
  · rintro ⟨holds, inactive⟩
    exact ⟨occurrence, atIndex, holds, inactive⟩

theorem overlap_false_of_literals_hold (left right : List GuardAtom)
    (valuation : GuardAtom → Bool)
    (trueAtoms : ∀ atom, atom ∈ left → valuation atom = true)
    (falseAtoms : ∀ atom, atom ∈ right → valuation atom = false) :
    regionOverlap left right = false := by
  apply Bool.eq_false_iff.mpr
  intro overlap
  obtain ⟨atom, inLeft, inRight⟩ :=
    (regionOverlap_eq_true_iff left right).mp overlap
  have isTrue := trueAtoms atom inLeft
  have isFalse := falseAtoms atom inRight
  rw [isTrue] at isFalse
  contradiction

/-- Exact attemptedness: the occurrence is attempted on a valuation exactly
when its positive atoms are true, its negative atoms are false, and the region
is not structurally impossible. -/
theorem attempted_iff_region_holds
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (index : Nat) (occurrence : ScheduledOccurrence)
    (atIndex : schedule[index]? = some occurrence) :
    Attempted schedule valuation index ↔ (Region schedule index).Holds valuation := by
  rw [attempted_iff_guard_and_earlier_inactive schedule valuation index occurrence atIndex]
  rw [earlierTerminalsInactive_iff schedule valuation index]
  simp only [Region, atIndex, AttemptRegion.Holds, AttemptRegion.LiteralsHold]
  constructor
  · rintro ⟨guardHolds, noAlways, falseAtoms⟩
    have trueAtoms := (guard_holds_iff_required_true valuation occurrence.guard).mp guardHolds
    have noOverlap := overlap_false_of_literals_hold
      (AttemptGuards occurrence.guard) (earlierTerminalFalseAtoms schedule index)
      valuation trueAtoms falseAtoms
    exact ⟨by simp [noAlways, noOverlap], trueAtoms, falseAtoms⟩
  · rintro ⟨possible, trueAtoms, falseAtoms⟩
    have noAlways : hasEarlierAlways schedule index = false := by
      cases value : hasEarlierAlways schedule index <;> simp_all
    exact ⟨(guard_holds_iff_required_true valuation occurrence.guard).mpr trueAtoms,
      noAlways, falseAtoms⟩

def AttemptRegion.canonicalValuation (region : AttemptRegion) : GuardAtom → Bool :=
  fun atom => region.requiredTrue.contains atom

theorem region_possible_has_valuation
    (schedule : List ScheduledOccurrence) (index : Nat)
    (occurrence : ScheduledOccurrence)
    (atIndex : schedule[index]? = some occurrence)
    (possible : (Region schedule index).impossible = false) :
    ∃ valuation, (Region schedule index).Holds valuation := by
  let valuation := (Region schedule index).canonicalValuation
  refine ⟨valuation, possible, ?_, ?_⟩
  · intro atom member
    exact List.contains_iff_mem.mpr member
  · intro atom member
    simp only [Region, atIndex] at possible member ⊢
    cases value : (AttemptGuards occurrence.guard).contains atom with
    | false =>
        simpa [valuation, AttemptRegion.canonicalValuation, Region, atIndex] using value
    | true =>
        have inTrue : atom ∈ AttemptGuards occurrence.guard :=
          List.contains_iff_mem.mp value
        have overlap : regionOverlap (AttemptGuards occurrence.guard)
            (earlierTerminalFalseAtoms schedule index) = true :=
          (regionOverlap_eq_true_iff _ _).mpr ⟨atom, inTrue, member⟩
        simp [overlap] at possible

/-- Structural impossibility is exact unreachability over all valuations. -/
theorem region_impossible_iff_unreachable
    (schedule : List ScheduledOccurrence) (index : Nat)
    (occurrence : ScheduledOccurrence)
    (atIndex : schedule[index]? = some occurrence) :
    (Region schedule index).impossible = true ↔
      ∀ valuation, ¬ Attempted schedule valuation index := by
  constructor
  · intro impossible valuation attempted
    have holds :=
      (attempted_iff_region_holds schedule valuation index occurrence atIndex).mp attempted
    have possible := holds.1
    rw [impossible] at possible
    contradiction
  · intro unreachable
    cases possible : (Region schedule index).impossible with
    | true => rfl
    | false =>
        obtain ⟨valuation, holds⟩ :=
          region_possible_has_valuation schedule index occurrence atIndex possible
        have attempted :=
          (attempted_iff_region_holds schedule valuation index occurrence atIndex).mpr holds
        exact False.elim (unreachable valuation attempted)

/-! ## Must-fact analysis -/

inductive MustLiteral where
  | positive (input : Nat)
  | negative (input : Nat)
  deriving Repr, DecidableEq

inductive FactSet where
  | impossible
  | possible (facts : List MustLiteral)
  deriving Repr, DecidableEq

structure MustResult where
  whenTrue : FactSet
  whenFalse : FactSet
  deriving Repr, DecidableEq

def MustResult.unknown : MustResult :=
  { whenTrue := .possible [], whenFalse := .possible [] }

def InputMust (input : Nat) (isBoolean : Bool) : MustResult :=
  if isBoolean then
    { whenTrue := .possible [.positive input],
      whenFalse := .possible [.negative input] }
  else .unknown

def MustLiteral.opposite : MustLiteral → MustLiteral
  | .positive input => .negative input
  | .negative input => .positive input

def FactSet.hasContradiction (facts : List MustLiteral) : Bool :=
  facts.any fun literal => facts.contains literal.opposite

/-- Owner-text union, including normalization to `Impossible` when the merged
set contains both polarities of one input. -/
def FactSet.union : FactSet → FactSet → FactSet
  | .impossible, _ => .impossible
  | _, .impossible => .impossible
  | .possible left, .possible right =>
      let merged := left ++ right
      if FactSet.hasContradiction merged then .impossible else .possible merged

def FactSet.meet : FactSet → FactSet → FactSet
  | .impossible, right => right
  | left, .impossible => left
  | .possible left, .possible right =>
      .possible (left.filter fun literal => decide (literal ∈ right))

def conditionalMust (condition whenTrue whenFalse : MustResult) : MustResult :=
  { whenTrue := FactSet.meet
      (FactSet.union condition.whenTrue whenTrue.whenTrue)
      (FactSet.union condition.whenFalse whenFalse.whenTrue),
    whenFalse := FactSet.meet
      (FactSet.union condition.whenTrue whenTrue.whenFalse)
      (FactSet.union condition.whenFalse whenFalse.whenFalse) }

def literalMust (value : TypedValue) : MustResult :=
  match value.datum with
  | .bool true => { whenTrue := .possible [], whenFalse := .impossible }
  | .bool false => { whenTrue := .impossible, whenFalse := .possible [] }
  | _ => .unknown

/-- The exact authored clauses, including the closed empty-fact rule for every
remaining portable constructor. -/
def MustEnv : Term → List MustResult → MustResult
  | .literal value, _ => literalMust value
  | .variable index _, environment => environment[index]?.getD .unknown
  | .letE bound body, environment =>
      MustEnv body (MustEnv bound environment :: environment)
  | .conditional condition whenTrue whenFalse, environment =>
      conditionalMust (MustEnv condition environment)
        (MustEnv whenTrue environment) (MustEnv whenFalse environment)
  | .primitiveCall _ _, _ => .unknown
  | _, _ => .unknown

def inputMustFrom : Nat → List Bool → List MustResult
  | _, [] => []
  | first, isBoolean :: rest =>
      InputMust first isBoolean :: inputMustFrom (first + 1) rest

def inputMustEnvironment (inputIsBoolean : List Bool) : List MustResult :=
  inputMustFrom 0 inputIsBoolean

def Must (term : Term) (inputIsBoolean : List Bool) : MustResult :=
  MustEnv term (inputMustEnvironment inputIsBoolean)

def MustWhenTrue (term : Term) (inputIsBoolean : List Bool) : FactSet :=
  (Must term inputIsBoolean).whenTrue

def MustLiteral.Holds (valuation : Nat → Bool) : MustLiteral → Prop
  | .positive input => valuation input = true
  | .negative input => valuation input = false

def FactSet.Holds (valuation : Nat → Bool) : FactSet → Prop
  | .impossible => False
  | .possible facts => ∀ literal, literal ∈ facts → literal.Holds valuation

def MustResult.SoundFor (valuation : Nat → Bool)
    (result : MustResult) (value : TypedValue) : Prop :=
  match value.datum with
  | .bool true => result.whenTrue.Holds valuation
  | .bool false => result.whenFalse.Holds valuation
  | _ => True

def MustEnvironment.SoundFor (valuation : Nat → Bool)
    (abstract : List MustResult) (concrete : List TypedValue) : Prop :=
  ∀ (index : Nat) (facts : MustResult) (value : TypedValue),
    abstract[index]? = some facts →
    concrete[index]? = some value →
    facts.SoundFor valuation value

theorem MustLiteral.opposite_cannot_both_hold (valuation : Nat → Bool)
    (literal : MustLiteral) (holds : literal.Holds valuation) :
    ¬ literal.opposite.Holds valuation := by
  cases literal <;> simp_all [MustLiteral.Holds, MustLiteral.opposite]

theorem FactSet.no_contradiction_of_holds (valuation : Nat → Bool)
    (facts : List MustLiteral)
    (holds : ∀ literal, literal ∈ facts → literal.Holds valuation) :
    FactSet.hasContradiction facts = false := by
  apply Bool.eq_false_iff.mpr
  intro contradiction
  obtain ⟨literal, member, oppositeMember⟩ :=
    List.any_eq_true.mp contradiction
  have oppositeIn : MustLiteral.opposite literal ∈ facts :=
    List.contains_iff_mem.mp oppositeMember
  exact MustLiteral.opposite_cannot_both_hold valuation literal
    (holds literal member) (holds (MustLiteral.opposite literal) oppositeIn)

theorem FactSet.union_holds (valuation : Nat → Bool) {left right : FactSet}
    (leftHolds : left.Holds valuation) (rightHolds : right.Holds valuation) :
    (left.union right).Holds valuation := by
  cases left with
  | impossible => exact False.elim leftHolds
  | possible leftFacts =>
      cases right with
      | impossible => exact False.elim rightHolds
      | possible rightFacts =>
          let merged := leftFacts ++ rightFacts
          have mergedHolds : ∀ literal, literal ∈ merged →
              literal.Holds valuation := by
            intro literal member
            simp [merged] at member
            cases member with
            | inl inLeft => exact leftHolds literal inLeft
            | inr inRight => exact rightHolds literal inRight
          have consistent := FactSet.no_contradiction_of_holds
            valuation merged mergedHolds
          simpa [FactSet.union, FactSet.Holds, merged, consistent] using mergedHolds

theorem FactSet.meet_holds_left (valuation : Nat → Bool) {left right : FactSet}
    (leftHolds : left.Holds valuation) :
    (left.meet right).Holds valuation := by
  cases left with
  | impossible => exact False.elim leftHolds
  | possible leftFacts =>
      cases right with
      | impossible => exact leftHolds
      | possible rightFacts =>
          intro literal member
          have both : literal ∈ leftFacts ∧ literal ∈ rightFacts := by
            simpa [FactSet.meet] using member
          have inLeft : literal ∈ leftFacts := by
            exact both.1
          exact leftHolds literal inLeft

theorem FactSet.meet_holds_right (valuation : Nat → Bool) {left right : FactSet}
    (rightHolds : right.Holds valuation) :
    (left.meet right).Holds valuation := by
  cases left with
  | impossible => exact rightHolds
  | possible leftFacts =>
      cases right with
      | impossible => exact False.elim rightHolds
      | possible rightFacts =>
          intro literal member
          have both : literal ∈ leftFacts ∧ literal ∈ rightFacts := by
            simpa [FactSet.meet] using member
          have inRight : literal ∈ rightFacts := by
            exact both.2
          exact rightHolds literal inRight

theorem MustResult.unknown_sound (valuation : Nat → Bool) (value : TypedValue) :
    MustResult.unknown.SoundFor valuation value := by
  cases value with
  | mk valueType datum =>
      cases datum <;> simp [MustResult.unknown, MustResult.SoundFor, FactSet.Holds]
      case bool discriminator => cases discriminator <;> simp

theorem MustEnvironment.SoundFor.cons (valuation : Nat → Bool)
    {headFacts : MustResult} {headValue : TypedValue}
    {abstract : List MustResult} {concrete : List TypedValue}
    (headSound : headFacts.SoundFor valuation headValue)
    (tailSound : MustEnvironment.SoundFor valuation abstract concrete) :
    MustEnvironment.SoundFor valuation (headFacts :: abstract) (headValue :: concrete) := by
  unfold MustEnvironment.SoundFor
  intro index facts value abstractAt concreteAt
  cases index with
  | zero =>
      simp at abstractAt concreteAt
      subst facts
      subst value
      exact headSound
  | succ index =>
      simp at abstractAt concreteAt
      exact tailSound index facts value abstractAt concreteAt

theorem conditional_true_branch_sound (valuation : Nat → Bool)
    (condition whenTrue whenFalse : MustResult) (value : TypedValue)
    (conditionSound : condition.whenTrue.Holds valuation)
    (branchSound : whenTrue.SoundFor valuation value) :
    (conditionalMust condition whenTrue whenFalse).SoundFor valuation value := by
  cases value with
  | mk valueType datum =>
      cases datum with
      | bool discriminator =>
          cases discriminator <;>
            simp only [MustResult.SoundFor, conditionalMust] at branchSound ⊢
          · exact FactSet.meet_holds_left valuation
              (FactSet.union_holds valuation conditionSound branchSound)
          · exact FactSet.meet_holds_left valuation
              (FactSet.union_holds valuation conditionSound branchSound)
      | unit => trivial
      | nat value => trivial
      | int value => trivial
      | bytes value => trivial
      | symbol value => trivial
      | seq values => trivial
      | record fields => trivial
      | variant case payload => trivial

theorem conditional_false_branch_sound (valuation : Nat → Bool)
    (condition whenTrue whenFalse : MustResult) (value : TypedValue)
    (conditionSound : condition.whenFalse.Holds valuation)
    (branchSound : whenFalse.SoundFor valuation value) :
    (conditionalMust condition whenTrue whenFalse).SoundFor valuation value := by
  cases value with
  | mk valueType datum =>
      cases datum with
      | bool discriminator =>
          cases discriminator <;>
            simp only [MustResult.SoundFor, conditionalMust] at branchSound ⊢
          · exact FactSet.meet_holds_right valuation
              (FactSet.union_holds valuation conditionSound branchSound)
          · exact FactSet.meet_holds_right valuation
              (FactSet.union_holds valuation conditionSound branchSound)
      | unit => trivial
      | nat value => trivial
      | int value => trivial
      | bytes value => trivial
      | symbol value => trivial
      | seq values => trivial
      | record fields => trivial
      | variant case payload => trivial

def CoreResult.successValue? : CoreResult → Option TypedValue
  | .success value _ => some value
  | _ => none

@[simp] theorem CoreResult.successValue?_addCharge (before : Charge) (result : CoreResult) :
    (result.addCharge before).successValue? = result.successValue? := by
  cases result <;> rfl

@[simp] theorem CoreResult.successValue?_addStep (result : CoreResult) :
    result.addStep.successValue? = result.successValue? := by
  cases result <;> rfl

/-- Soundness against the actual M2 evaluator, for every term, fuel, primitive
denotation, abstract environment, and successful result. -/
theorem mustEnv_sound_evalCore (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) :
    ∀ fuel term concrete abstract value,
      MustEnvironment.SoundFor valuation abstract concrete →
      (evalCore primitive fuel term concrete).successValue? = some value →
      (MustEnv term abstract).SoundFor valuation value := by
  intro fuel
  induction fuel with
  | zero =>
      intro term concrete abstract value environmentSound evaluated
      simp [evalCore, CoreResult.successValue?] at evaluated
  | succ fuel inductionHypothesis =>
      intro term concrete abstract value environmentSound evaluated
      cases term with
      | literal literal =>
          simp [evalCore, CoreResult.successValue?, CoreResult.addStep] at evaluated
          subst value
          cases literal with
          | mk valueType datum =>
              cases datum <;>
                simp [MustEnv, literalMust, MustResult.SoundFor,
                  MustResult.unknown, FactSet.Holds]
              case bool discriminator => cases discriminator <;> simp
      | «variable» index valueType =>
          cases concreteAt : concrete[index]? with
          | none =>
              simp [evalCore, concreteAt, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
          | some concreteValue =>
              simp [evalCore, concreteAt, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
              subst value
              cases abstractAt : abstract[index]? with
              | none =>
                  simpa [MustEnv, abstractAt] using
                    MustResult.unknown_sound valuation concreteValue
              | some abstractValue =>
                  simpa [MustEnv, abstractAt] using
                    environmentSound index abstractValue concreteValue abstractAt concreteAt
      | letE bound body =>
          cases boundRun : evalCore primitive fuel bound concrete with
          | domainFailure failure payload charge =>
              simp [evalCore, boundRun, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
          | checkerFailure code charge =>
              simp [evalCore, boundRun, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
          | success boundValue boundCharge =>
              cases bodyRun : evalCore primitive fuel body (boundValue :: concrete) with
              | domainFailure failure payload charge =>
                  simp [evalCore, boundRun, bodyRun, CoreResult.successValue?,
                    CoreResult.addStep, CoreResult.addCharge] at evaluated
              | checkerFailure code charge =>
                  simp [evalCore, boundRun, bodyRun, CoreResult.successValue?,
                    CoreResult.addStep, CoreResult.addCharge] at evaluated
              | success bodyValue bodyCharge =>
                  simp [evalCore, boundRun, bodyRun, CoreResult.successValue?,
                    CoreResult.addStep, CoreResult.addCharge] at evaluated
                  subst value
                  have boundSound := inductionHypothesis bound concrete abstract boundValue
                    environmentSound (by simp [boundRun, CoreResult.successValue?])
                  have extendedSound := MustEnvironment.SoundFor.cons valuation
                    boundSound environmentSound
                  exact inductionHypothesis body (boundValue :: concrete)
                    (MustEnv bound abstract :: abstract) bodyValue extendedSound
                    (by simp [bodyRun, CoreResult.successValue?])
      | conditional condition whenTrue whenFalse =>
          cases conditionRun : evalCore primitive fuel condition concrete with
          | domainFailure failure payload charge =>
              simp [evalCore, conditionRun, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
          | checkerFailure code charge =>
              simp [evalCore, conditionRun, CoreResult.successValue?,
                CoreResult.addStep] at evaluated
          | success conditionValue conditionCharge =>
              cases conditionValue with
              | mk conditionType conditionDatum =>
                  cases conditionDatum with
                  | bool discriminator =>
                      cases discriminator with
                      | false =>
                          cases branchRun : evalCore primitive fuel whenFalse concrete with
                          | domainFailure failure payload charge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                          | checkerFailure code charge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                          | success branchValue branchCharge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                              subst value
                              have conditionSound := inductionHypothesis condition concrete abstract
                                ⟨conditionType, .bool false⟩ environmentSound
                                (by simp [conditionRun, CoreResult.successValue?])
                              have branchSound := inductionHypothesis whenFalse concrete abstract
                                branchValue environmentSound
                                (by simp [branchRun, CoreResult.successValue?])
                              exact conditional_false_branch_sound valuation
                                (MustEnv condition abstract) (MustEnv whenTrue abstract)
                                (MustEnv whenFalse abstract) branchValue
                                (by simpa [MustResult.SoundFor] using conditionSound) branchSound
                      | true =>
                          cases branchRun : evalCore primitive fuel whenTrue concrete with
                          | domainFailure failure payload charge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                          | checkerFailure code charge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                          | success branchValue branchCharge =>
                              simp [evalCore, conditionRun, branchRun,
                                CoreResult.successValue?, CoreResult.addStep,
                                CoreResult.addCharge] at evaluated
                              subst value
                              have conditionSound := inductionHypothesis condition concrete abstract
                                ⟨conditionType, .bool true⟩ environmentSound
                                (by simp [conditionRun, CoreResult.successValue?])
                              have branchSound := inductionHypothesis whenTrue concrete abstract
                                branchValue environmentSound
                                (by simp [branchRun, CoreResult.successValue?])
                              exact conditional_true_branch_sound valuation
                                (MustEnv condition abstract) (MustEnv whenTrue abstract)
                                (MustEnv whenFalse abstract) branchValue
                                (by simpa [MustResult.SoundFor] using conditionSound) branchSound
                  | unit =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | nat n =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | int n =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | bytes bytes =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | symbol symbol =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | seq values =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | record fields =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
                  | variant case payload =>
                      simp [evalCore, conditionRun, CoreResult.successValue?,
                        CoreResult.addStep] at evaluated
      | recordConstruct fields => exact MustResult.unknown_sound valuation value
      | project record ordinal => exact MustResult.unknown_sound valuation value
      | inject case payload sumType => exact MustResult.unknown_sound valuation value
      | caseE scrutinee branches => exact MustResult.unknown_sound valuation value
      | sequenceConstruct elementType elements maximumLength =>
          exact MustResult.unknown_sound valuation value
      | sequenceLength source => exact MustResult.unknown_sound valuation value
      | fail failureType payload successType => exact MustResult.unknown_sound valuation value
      | strictIndex source index failureType => exact MustResult.unknown_sound valuation value
      | boundedAppend source element failureType => exact MustResult.unknown_sound valuation value
      | primitiveCall primitiveRef arguments => exact MustResult.unknown_sound valuation value
      | boundedIterate source initialState body => exact MustResult.unknown_sound valuation value

def InputEnvironmentMatches (valuation : Nat → Bool) :
    Nat → List Bool → List TypedValue → Prop
  | _, [], [] => True
  | first, true :: kinds, value :: values =>
      value.datum = .bool (valuation first) ∧
        InputEnvironmentMatches valuation (first + 1) kinds values
  | first, false :: kinds, _value :: values =>
      InputEnvironmentMatches valuation (first + 1) kinds values
  | _, _, _ => False

theorem booleanInputMust_sound (valuation : Nat → Bool)
    (input : Nat) (value : TypedValue)
    (alignment : value.datum = .bool (valuation input)) :
    (InputMust input true).SoundFor valuation value := by
  cases value with
  | mk valueType datum =>
      change datum = .bool (valuation input) at alignment
      subst datum
      cases bit : valuation input <;>
        simp [InputMust, MustResult.SoundFor, FactSet.Holds,
          MustLiteral.Holds, bit]

theorem nonBooleanInputMust_sound (valuation : Nat → Bool)
    (input : Nat) (value : TypedValue) :
    (InputMust input false).SoundFor valuation value := by
  simpa [InputMust] using MustResult.unknown_sound valuation value

theorem input_environments_sound_from (valuation : Nat → Bool) :
    ∀ first kinds concrete,
      InputEnvironmentMatches valuation first kinds concrete →
      MustEnvironment.SoundFor valuation (inputMustFrom first kinds) concrete := by
  intro first kinds
  induction kinds generalizing first with
  | nil =>
      intro concrete alignment
      cases concrete with
      | nil =>
          unfold MustEnvironment.SoundFor
          intro index facts value abstractAt concreteAt
          simp [inputMustFrom] at abstractAt
      | cons value values => simp [InputEnvironmentMatches] at alignment
  | cons isBoolean kinds inductionHypothesis =>
      intro concrete alignment
      cases concrete with
      | nil => simp [InputEnvironmentMatches] at alignment
      | cons value values =>
          cases isBoolean with
          | false =>
              exact MustEnvironment.SoundFor.cons valuation
                (nonBooleanInputMust_sound valuation first value)
                (inductionHypothesis (first + 1) values
                  (by simpa [InputEnvironmentMatches] using alignment))
          | true =>
              have parts : value.datum = .bool (valuation first) ∧
                  InputEnvironmentMatches valuation (first + 1) kinds values := by
                simpa [InputEnvironmentMatches] using alignment
              exact MustEnvironment.SoundFor.cons valuation
                (booleanInputMust_sound valuation first value parts.1)
                (inductionHypothesis (first + 1) values parts.2)

theorem input_environments_sound (valuation : Nat → Bool)
    (kinds : List Bool) (concrete : List TypedValue)
    (alignment : InputEnvironmentMatches valuation 0 kinds concrete) :
    MustEnvironment.SoundFor valuation (inputMustEnvironment kinds) concrete := by
  exact input_environments_sound_from valuation 0 kinds concrete alignment

/-- Every true-region fact holds for every mixed Boolean/non-Boolean input
environment on which the evaluator successfully returns true. -/
theorem must_when_true_sound (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (inputIsBoolean : List Bool)
    (concrete : List TypedValue) (fuel : Nat) (term : Term)
    (valueType : ValueType)
    (alignment : InputEnvironmentMatches valuation 0 inputIsBoolean concrete)
    (evaluated : (evalCore primitive fuel term concrete).successValue? =
      some ⟨valueType, .bool true⟩) :
    (MustWhenTrue term inputIsBoolean).Holds valuation := by
  exact mustEnv_sound_evalCore primitive valuation fuel term
    concrete (inputMustEnvironment inputIsBoolean) ⟨valueType, .bool true⟩
    (input_environments_sound valuation inputIsBoolean concrete alignment) evaluated

/-- Symmetric soundness for the false region. -/
theorem must_when_false_sound (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (inputIsBoolean : List Bool)
    (concrete : List TypedValue) (fuel : Nat) (term : Term)
    (valueType : ValueType)
    (alignment : InputEnvironmentMatches valuation 0 inputIsBoolean concrete)
    (evaluated : (evalCore primitive fuel term concrete).successValue? =
      some ⟨valueType, .bool false⟩) :
    (Must term inputIsBoolean).whenFalse.Holds valuation := by
  exact mustEnv_sound_evalCore primitive valuation fuel term
    concrete (inputMustEnvironment inputIsBoolean) ⟨valueType, .bool false⟩
    (input_environments_sound valuation inputIsBoolean concrete alignment) evaluated

theorem impossible_when_true_cannot_evaluate_true (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (inputIsBoolean : List Bool)
    (concrete : List TypedValue) (fuel : Nat) (term : Term)
    (valueType : ValueType)
    (alignment : InputEnvironmentMatches valuation 0 inputIsBoolean concrete)
    (impossible : MustWhenTrue term inputIsBoolean = .impossible) :
    (evalCore primitive fuel term concrete).successValue? ≠
      some ⟨valueType, .bool true⟩ := by
  intro evaluated
  have sound := must_when_true_sound primitive valuation inputIsBoolean concrete fuel
    term valueType alignment evaluated
  rw [impossible] at sound
  exact sound

theorem impossible_when_false_cannot_evaluate_false (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (inputIsBoolean : List Bool)
    (concrete : List TypedValue) (fuel : Nat) (term : Term)
    (valueType : ValueType)
    (alignment : InputEnvironmentMatches valuation 0 inputIsBoolean concrete)
    (impossible : (Must term inputIsBoolean).whenFalse = .impossible) :
    (evalCore primitive fuel term concrete).successValue? ≠
      some ⟨valueType, .bool false⟩ := by
  intro evaluated
  have sound := must_when_false_sound primitive valuation inputIsBoolean concrete fuel
    term valueType alignment evaluated
  rw [impossible] at sound
  exact sound

/-! ## Closed claim-state algebra -/

def atomSetSubset (small large : List GuardAtom) : Bool :=
  small.all fun atom => large.contains atom

theorem atomSetSubset_eq_true_iff (small large : List GuardAtom) :
    atomSetSubset small large = true ↔ ∀ atom, atom ∈ small → atom ∈ large := by
  simp [atomSetSubset, List.all_eq_true]

def Implies (left right : AttemptRegion) : Bool :=
  atomSetSubset right.requiredTrue left.requiredTrue &&
    atomSetSubset right.requiredFalse left.requiredFalse

def Disjoint (left right : AttemptRegion) : Bool :=
  regionOverlap left.requiredTrue right.requiredFalse ||
    regionOverlap right.requiredTrue left.requiredFalse

theorem implies_literals_hold {left right : AttemptRegion}
    (valuation : GuardAtom → Bool) (implies : Implies left right = true)
    (leftHolds : left.LiteralsHold valuation) :
    right.LiteralsHold valuation := by
  have parts : atomSetSubset right.requiredTrue left.requiredTrue = true ∧
      atomSetSubset right.requiredFalse left.requiredFalse = true := by
    simpa [Implies] using implies
  constructor
  · intro atom member
    exact leftHolds.1 atom ((atomSetSubset_eq_true_iff _ _).mp parts.1 atom member)
  · intro atom member
    exact leftHolds.2 atom ((atomSetSubset_eq_true_iff _ _).mp parts.2 atom member)

theorem disjoint_literals_cannot_both_hold {left right : AttemptRegion}
    (valuation : GuardAtom → Bool) (disjoint : Disjoint left right = true)
    (leftHolds : left.LiteralsHold valuation)
    (rightHolds : right.LiteralsHold valuation) : False := by
  have alternatives : regionOverlap left.requiredTrue right.requiredFalse = true ∨
      regionOverlap right.requiredTrue left.requiredFalse = true := by
    simpa [Disjoint] using disjoint
  cases alternatives with
  | inl overlap =>
      obtain ⟨atom, inTrue, inFalse⟩ :=
        (regionOverlap_eq_true_iff _ _).mp overlap
      have isTrue := leftHolds.1 atom inTrue
      have isFalse := rightHolds.2 atom inFalse
      rw [isTrue] at isFalse
      contradiction
  | inr overlap =>
      obtain ⟨atom, inTrue, inFalse⟩ :=
        (regionOverlap_eq_true_iff _ _).mp overlap
      have isTrue := rightHolds.1 atom inTrue
      have isFalse := leftHolds.2 atom inFalse
      rw [isTrue] at isFalse
      contradiction

theorem attempted_of_implies_region
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (later earlier : Nat) (laterOccurrence earlierOccurrence : ScheduledOccurrence)
    (laterAt : schedule[later]? = some laterOccurrence)
    (earlierAt : schedule[earlier]? = some earlierOccurrence)
    (before : earlier < later)
    (implies : Implies (Region schedule later) (Region schedule earlier) = true)
    (laterAttempted : Attempted schedule valuation later) :
    Attempted schedule valuation earlier := by
  have implicationParts :
      atomSetSubset (Region schedule earlier).requiredTrue
          (Region schedule later).requiredTrue = true ∧
      atomSetSubset (Region schedule earlier).requiredFalse
          (Region schedule later).requiredFalse = true := by
    simpa [Implies] using implies
  have subsets : atomSetSubset (AttemptGuards earlierOccurrence.guard)
      (AttemptGuards laterOccurrence.guard) = true := by
    simpa [Region, laterAt, earlierAt] using implicationParts.1
  have law : AttemptedWhenever schedule later earlier := by
    simp only [AttemptedWhenever, laterAt, earlierAt]
    exact ⟨before, (atomSetSubset_eq_true_iff _ _).mp subsets⟩
  exact attemptedWhenever_sound schedule valuation later earlier law laterAttempted

theorem disjoint_regions_cannot_both_be_attempted
    (schedule : List ScheduledOccurrence) (valuation : GuardAtom → Bool)
    (leftIndex rightIndex : Nat)
    (leftOccurrence rightOccurrence : ScheduledOccurrence)
    (leftAt : schedule[leftIndex]? = some leftOccurrence)
    (rightAt : schedule[rightIndex]? = some rightOccurrence)
    (disjoint : Disjoint (Region schedule leftIndex) (Region schedule rightIndex) = true)
    (leftAttempted : Attempted schedule valuation leftIndex)
    (rightAttempted : Attempted schedule valuation rightIndex) : False := by
  have leftHolds :=
    (attempted_iff_region_holds schedule valuation leftIndex leftOccurrence leftAt).mp
      leftAttempted
  have rightHolds :=
    (attempted_iff_region_holds schedule valuation rightIndex rightOccurrence rightAt).mp
      rightAttempted
  exact disjoint_literals_cannot_both_hold valuation disjoint leftHolds.2 rightHolds.2

inductive AbstractClaimSource where
  | initial
  | occurrence (index : Nat)
  deriving Repr, DecidableEq

structure AbstractClaim where
  reference : Nat
  source : AbstractClaimSource
  linearConsumers : List Nat
  deriving Repr, DecidableEq

def AbstractClaimSource.RegionOf (schedule : List ScheduledOccurrence) :
    AbstractClaimSource → AttemptRegion
  | .initial => { requiredTrue := [], requiredFalse := [], impossible := false }
  | .occurrence index => Region schedule index

def earlierLinearConsumers (claim : AbstractClaim) (occurrence : Nat) : List Nat :=
  claim.linearConsumers.filter fun consumer => decide (consumer < occurrence)

inductive ClaimJudgment where
  | live
  | dead
  | unknown
  deriving Repr, DecidableEq

def claimLiveCondition (schedule : List ScheduledOccurrence)
    (claim : AbstractClaim) (occurrence : Nat) : Bool :=
  Implies (Region schedule occurrence) (claim.source.RegionOf schedule) &&
    (earlierLinearConsumers claim occurrence).all fun consumer =>
      Disjoint (Region schedule occurrence) (Region schedule consumer)

def claimDeadCondition (schedule : List ScheduledOccurrence)
    (claim : AbstractClaim) (occurrence : Nat) : Bool :=
  Disjoint (Region schedule occurrence) (claim.source.RegionOf schedule) ||
    (earlierLinearConsumers claim occurrence).any fun consumer =>
      Implies (Region schedule occurrence) (Region schedule consumer)

def ClaimStatus (schedule : List ScheduledOccurrence)
    (claim : AbstractClaim) (occurrence : Nat) : ClaimJudgment :=
  if claimLiveCondition schedule claim occurrence then .live
  else if claimDeadCondition schedule claim occurrence then .dead
  else .unknown

def LiveClaims (schedule : List ScheduledOccurrence)
    (claims : List AbstractClaim) (occurrence : Nat) : List Nat :=
  claims.filterMap fun claim =>
    if ClaimStatus schedule claim occurrence == .live then some claim.reference else none

def AbstractClaimSource.ExistsOn (schedule : List ScheduledOccurrence)
    (valuation : GuardAtom → Bool) : AbstractClaimSource → Prop
  | .initial => True
  | .occurrence index => Attempted schedule valuation index

def AbstractClaim.LiveAt (schedule : List ScheduledOccurrence)
    (valuation : GuardAtom → Bool) (claim : AbstractClaim) (occurrence : Nat) : Prop :=
  claim.source.ExistsOn schedule valuation ∧
    ∀ consumer, consumer ∈ earlierLinearConsumers claim occurrence →
      ¬ Attempted schedule valuation consumer

def AbstractClaim.WellFormedAt (schedule : List ScheduledOccurrence)
    (claim : AbstractClaim) (occurrence : Nat) : Prop :=
  (match claim.source with
   | .initial => True
   | .occurrence source => source < occurrence ∧ ∃ row, schedule[source]? = some row) ∧
  ∀ consumer, consumer ∈ earlierLinearConsumers claim occurrence →
    ∃ row, schedule[consumer]? = some row

theorem claimStatus_live_conditions
    (schedule : List ScheduledOccurrence) (claim : AbstractClaim) (occurrence : Nat)
    (status : ClaimStatus schedule claim occurrence = .live) :
    claimLiveCondition schedule claim occurrence = true := by
  cases live : claimLiveCondition schedule claim occurrence with
  | false =>
      cases dead : claimDeadCondition schedule claim occurrence <;>
        simp [ClaimStatus, live, dead] at status
  | true => rfl

theorem claimStatus_dead_conditions
    (schedule : List ScheduledOccurrence) (claim : AbstractClaim) (occurrence : Nat)
    (status : ClaimStatus schedule claim occurrence = .dead) :
    claimLiveCondition schedule claim occurrence = false ∧
      claimDeadCondition schedule claim occurrence = true := by
  cases live : claimLiveCondition schedule claim occurrence with
  | true => simp [ClaimStatus, live] at status
  | false =>
      cases dead : claimDeadCondition schedule claim occurrence with
      | false => simp [ClaimStatus, live, dead] at status
      | true => exact ⟨rfl, rfl⟩

/-- A `live` result is universally sound for every attempted valuation. -/
theorem claimStatus_live_sound
    (schedule : List ScheduledOccurrence) (claim : AbstractClaim) (occurrence : Nat)
    (occurrenceRow : ScheduledOccurrence)
    (occurrenceAt : schedule[occurrence]? = some occurrenceRow)
    (wellFormed : claim.WellFormedAt schedule occurrence)
    (status : ClaimStatus schedule claim occurrence = .live)
    (valuation : GuardAtom → Bool)
    (attempted : Attempted schedule valuation occurrence) :
    claim.LiveAt schedule valuation occurrence := by
  have live := claimStatus_live_conditions schedule claim occurrence status
  have parts :
      Implies (Region schedule occurrence) (claim.source.RegionOf schedule) = true ∧
      (earlierLinearConsumers claim occurrence).all (fun consumer =>
        Disjoint (Region schedule occurrence) (Region schedule consumer)) = true := by
    simpa [claimLiveCondition] using live
  constructor
  · cases source : claim.source with
    | initial => trivial
    | occurrence sourceIndex =>
        obtain ⟨before, sourceRow, sourceAt⟩ := by
          simpa [AbstractClaim.WellFormedAt, source] using wellFormed.1
        exact attempted_of_implies_region schedule valuation occurrence sourceIndex
          occurrenceRow sourceRow occurrenceAt sourceAt before
          (by simpa [AbstractClaimSource.RegionOf, source] using parts.1) attempted
  · intro consumer member consumerAttempted
    obtain ⟨consumerRow, consumerAt⟩ := wellFormed.2 consumer member
    have disjoint : Disjoint (Region schedule occurrence)
        (Region schedule consumer) = true :=
      (List.all_eq_true.mp parts.2) consumer member
    exact disjoint_regions_cannot_both_be_attempted schedule valuation
      occurrence consumer occurrenceRow consumerRow occurrenceAt consumerAt
      disjoint attempted consumerAttempted

/-- A `dead` result is universally sound for every attempted valuation. -/
theorem claimStatus_dead_sound
    (schedule : List ScheduledOccurrence) (claim : AbstractClaim) (occurrence : Nat)
    (occurrenceRow : ScheduledOccurrence)
    (occurrenceAt : schedule[occurrence]? = some occurrenceRow)
    (wellFormed : claim.WellFormedAt schedule occurrence)
    (status : ClaimStatus schedule claim occurrence = .dead)
    (valuation : GuardAtom → Bool)
    (attempted : Attempted schedule valuation occurrence) :
    ¬ claim.LiveAt schedule valuation occurrence := by
  have conditions := claimStatus_dead_conditions schedule claim occurrence status
  have alternatives :
      Disjoint (Region schedule occurrence) (claim.source.RegionOf schedule) = true ∨
      (earlierLinearConsumers claim occurrence).any (fun consumer =>
        Implies (Region schedule occurrence) (Region schedule consumer)) = true := by
    simpa [claimDeadCondition] using conditions.2
  intro live
  cases alternatives with
  | inl sourceDisjoint =>
      cases source : claim.source with
      | initial =>
          rw [source] at sourceDisjoint
          simp [AbstractClaimSource.RegionOf, Disjoint, regionOverlap] at sourceDisjoint
      | occurrence sourceIndex =>
          obtain ⟨before, sourceRow, sourceAt⟩ := by
            simpa [AbstractClaim.WellFormedAt, source] using wellFormed.1
          exact disjoint_regions_cannot_both_be_attempted schedule valuation
            occurrence sourceIndex occurrenceRow sourceRow occurrenceAt sourceAt
            (by simpa [AbstractClaimSource.RegionOf, source] using sourceDisjoint)
            attempted (by simpa [AbstractClaim.LiveAt,
              AbstractClaimSource.ExistsOn, source] using live.1)
  | inr consumerImplied =>
      obtain ⟨consumer, member, implied⟩ := List.any_eq_true.mp consumerImplied
      obtain ⟨consumerRow, consumerAt⟩ := wellFormed.2 consumer member
      have consumerAttempted := attempted_of_implies_region schedule valuation
        occurrence consumer occurrenceRow consumerRow occurrenceAt consumerAt
        (by
          have : consumer < occurrence := by
            simpa [earlierLinearConsumers] using (List.mem_filter.mp member).2
          exact this)
        implied attempted
      exact (live.2 consumer member) consumerAttempted

/-! ## Executable Terminal-contract decision -/

inductive GuardInput where
  | occurrenceOutput (occurrence output : Nat)
  | other (coordinate : Nat)
  deriving Repr, DecidableEq

structure TerminalView where
  terminal : Nat
  occurrence : Nat
  guardTerm : Option Term
  guardInputs : List GuardInput
  guardInputIsBoolean : List Bool
  requiredChecks : List Nat
  requiredReductions : List Nat
  terminalClaims : List Nat
  deriving Repr

def directPositiveUseFrom (facts : List MustLiteral) (checkOccurrence : Nat) :
    Nat → List GuardInput → Bool
  | _, [] => false
  | input, source :: rest =>
      (source == .occurrenceOutput checkOccurrence 0 &&
        facts.contains (.positive input)) ||
      directPositiveUseFrom facts checkOccurrence (input + 1) rest

def directPositiveUse : FactSet → List GuardInput → Nat → Bool
  | .impossible, _, _ => false
  | .possible facts, inputs, checkOccurrence =>
      directPositiveUseFrom facts checkOccurrence 0 inputs

def CheckTerminalClause (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) (checkOccurrence : Nat) : Prop :=
  AttemptedWhenever schedule terminal.occurrence checkOccurrence ∧
  match terminal.guardTerm with
  | none => False
  | some term =>
      directPositiveUse (MustWhenTrue term terminal.guardInputIsBoolean)
        terminal.guardInputs checkOccurrence = true

def checkTerminalClauseDecision (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) (checkOccurrence : Nat) : Bool :=
  decide (AttemptedWhenever schedule terminal.occurrence checkOccurrence) &&
  match terminal.guardTerm with
  | none => false
  | some term =>
      directPositiveUse (MustWhenTrue term terminal.guardInputIsBoolean)
        terminal.guardInputs checkOccurrence

theorem checkTerminalClauseDecision_correct (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) (checkOccurrence : Nat) :
    checkTerminalClauseDecision schedule terminal checkOccurrence = true ↔
      CheckTerminalClause schedule terminal checkOccurrence := by
  cases guardTermAt : terminal.guardTerm <;>
    simp [checkTerminalClauseDecision, CheckTerminalClause, guardTermAt]

def TerminalGuardPossible (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) : Prop :=
  (Region schedule terminal.occurrence).impossible = false ∧
  match terminal.guardTerm with
  | none => True
  | some term => MustWhenTrue term terminal.guardInputIsBoolean ≠ .impossible

def terminalGuardPossibleDecision (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) : Bool :=
  !(Region schedule terminal.occurrence).impossible &&
  match terminal.guardTerm with
  | none => true
  | some term => decide (MustWhenTrue term terminal.guardInputIsBoolean ≠ .impossible)

theorem terminalGuardPossibleDecision_correct (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) :
    terminalGuardPossibleDecision schedule terminal = true ↔
      TerminalGuardPossible schedule terminal := by
  cases guardTermAt : terminal.guardTerm <;>
    simp [terminalGuardPossibleDecision, TerminalGuardPossible, guardTermAt]

def TerminalContract (schedule : List ScheduledOccurrence)
    (claims : List AbstractClaim) (terminal : TerminalView) : Prop :=
  TerminalGuardPossible schedule terminal ∧
  (∀ checkOccurrence, checkOccurrence ∈ terminal.requiredChecks →
      CheckTerminalClause schedule terminal checkOccurrence) ∧
  (∀ reductionOccurrence, reductionOccurrence ∈ terminal.requiredReductions →
      AttemptedWhenever schedule terminal.occurrence reductionOccurrence) ∧
  (∀ claim, claim ∈ claims →
      ClaimStatus schedule claim terminal.occurrence ≠ .unknown) ∧
  LiveClaims schedule claims terminal.occurrence = terminal.terminalClaims

def terminalContractDecision (schedule : List ScheduledOccurrence)
    (claims : List AbstractClaim) (terminal : TerminalView) : Bool :=
  terminalGuardPossibleDecision schedule terminal &&
  (terminal.requiredChecks.all fun checkOccurrence =>
      checkTerminalClauseDecision schedule terminal checkOccurrence) &&
  (terminal.requiredReductions.all fun reductionOccurrence =>
      decide (AttemptedWhenever schedule terminal.occurrence reductionOccurrence)) &&
  (claims.all fun claim =>
      decide (ClaimStatus schedule claim terminal.occurrence ≠ .unknown)) &&
  (LiveClaims schedule claims terminal.occurrence == terminal.terminalClaims)

theorem terminalContractDecision_correct (schedule : List ScheduledOccurrence)
    (claims : List AbstractClaim) (terminal : TerminalView) :
    terminalContractDecision schedule claims terminal = true ↔
      TerminalContract schedule claims terminal := by
  simp [terminalContractDecision, TerminalContract,
    terminalGuardPossibleDecision_correct, checkTerminalClauseDecision_correct, and_assoc]

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first < second) && strictlyIncreasing (second :: rest)

/-- Admission-boundary wrapper used for comparison with predecessor packages.
Sorted-unique carrier checks belong to admission step 2, not to
`TerminalContract` itself. -/
def terminalAdmissionDecision (schedule : List ScheduledOccurrence)
    (claims : List AbstractClaim) (terminal : TerminalView) : Bool :=
  decide (terminal.guardInputs.length = terminal.guardInputIsBoolean.length) &&
    strictlyIncreasing terminal.requiredChecks &&
    strictlyIncreasing terminal.requiredReductions &&
    strictlyIncreasing (claims.map (·.reference)) &&
    claims.all (strictlyIncreasing ·.linearConsumers) &&
    strictlyIncreasing terminal.terminalClaims &&
    terminalContractDecision schedule claims terminal

end M0
