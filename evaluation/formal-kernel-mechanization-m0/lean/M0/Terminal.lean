import M0.Eval

/-!
# First-active execution and the Terminal contract

This file is experimental proof text for the closed laws in Interactive Core
Section 10.  Guard atoms retain structural identity but have no denotation in
the syntax.  A valuation supplies that denotation only to state the universal
first-active theorem.  Scope openings are explicit schedule metadata and do
not participate in the attempt predicate: they are deterministic, unguarded
boundaries.

The must-fact analysis is defined over the complete M2 `Term` carrier.  The
owner text supplies transfer clauses for Boolean literals, variables, lets,
conditionals, and primitive calls.  Constructors without an authored clause
conservatively return no facts here; that fallback is package-local and is not
an owner law.
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

def InputMust (input : Nat) : MustResult :=
  { whenTrue := .possible [.positive input],
    whenFalse := .possible [.negative input] }

/-- Literal transcription of owner-text union.  In particular, this function
does not add an unauthored contradiction-normalization rule. -/
def FactSet.union : FactSet → FactSet → FactSet
  | .impossible, _ => .impossible
  | _, .impossible => .impossible
  | .possible left, .possible right => .possible (left ++ right)

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

/-- The exact authored clauses plus a conservative package-local fallback for
the M2 constructors for which Section 10 gives no clause. -/
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

def inputMustFrom : Nat → Nat → List MustResult
  | _, 0 => []
  | first, count + 1 => InputMust first :: inputMustFrom (first + 1) count

def inputMustEnvironment (count : Nat) : List MustResult :=
  inputMustFrom 0 count

def Must (term : Term) (inputCount : Nat) : MustResult :=
  MustEnv term (inputMustEnvironment inputCount)

def MustWhenTrue (term : Term) (inputCount : Nat) : FactSet :=
  (Must term inputCount).whenTrue

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

theorem FactSet.union_holds (valuation : Nat → Bool) {left right : FactSet}
    (leftHolds : left.Holds valuation) (rightHolds : right.Holds valuation) :
    (left.union right).Holds valuation := by
  cases left with
  | impossible => exact False.elim leftHolds
  | possible leftFacts =>
      cases right with
      | impossible => exact False.elim rightHolds
      | possible rightFacts =>
          intro literal member
          simp at member
          cases member with
          | inl inLeft => exact leftHolds literal inLeft
          | inr inRight => exact rightHolds literal inRight

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

def booleanInputsFrom (domain : Datum) (valuation : Nat → Bool) :
    Nat → Nat → List TypedValue
  | _, 0 => []
  | first, count + 1 =>
      ⟨.mk domain .bool, .bool (valuation first)⟩ ::
        booleanInputsFrom domain valuation (first + 1) count

def booleanInputEnvironment (domain : Datum) (valuation : Nat → Bool)
    (count : Nat) : List TypedValue :=
  booleanInputsFrom domain valuation 0 count

theorem inputMust_sound (valuation : Nat → Bool) (domain : Datum) (input : Nat) :
    (InputMust input).SoundFor valuation
      ⟨.mk domain .bool, .bool (valuation input)⟩ := by
  cases value : valuation input <;>
    simp [InputMust, MustResult.SoundFor, FactSet.Holds,
      MustLiteral.Holds, value]

theorem input_environments_sound_from (valuation : Nat → Bool) (domain : Datum) :
    ∀ first count,
      MustEnvironment.SoundFor valuation (inputMustFrom first count)
        (booleanInputsFrom domain valuation first count) := by
  intro first count
  induction count generalizing first with
  | zero =>
      unfold MustEnvironment.SoundFor
      intro index facts value abstractAt concreteAt
      simp [inputMustFrom] at abstractAt
  | succ count inductionHypothesis =>
      exact MustEnvironment.SoundFor.cons valuation
        (inputMust_sound valuation domain first)
        (inductionHypothesis (first + 1))

theorem input_environments_sound (valuation : Nat → Bool) (domain : Datum)
    (count : Nat) :
    MustEnvironment.SoundFor valuation (inputMustEnvironment count)
      (booleanInputEnvironment domain valuation count) := by
  exact input_environments_sound_from valuation domain 0 count

/-- Every positive must-fact holds for every Boolean input assignment on which
the M2 evaluator successfully returns true. -/
theorem must_when_true_sound (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (domain : Datum) (inputCount fuel : Nat)
    (term : Term) (valueType : ValueType)
    (evaluated : (evalCore primitive fuel term
      (booleanInputEnvironment domain valuation inputCount)).successValue? =
      some ⟨valueType, .bool true⟩) :
    (MustWhenTrue term inputCount).Holds valuation := by
  exact mustEnv_sound_evalCore primitive valuation fuel term
    (booleanInputEnvironment domain valuation inputCount)
    (inputMustEnvironment inputCount) ⟨valueType, .bool true⟩
    (input_environments_sound valuation domain inputCount) evaluated

/-- Symmetric soundness for the false region. -/
theorem must_when_false_sound (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (domain : Datum) (inputCount fuel : Nat)
    (term : Term) (valueType : ValueType)
    (evaluated : (evalCore primitive fuel term
      (booleanInputEnvironment domain valuation inputCount)).successValue? =
      some ⟨valueType, .bool false⟩) :
    (Must term inputCount).whenFalse.Holds valuation := by
  exact mustEnv_sound_evalCore primitive valuation fuel term
    (booleanInputEnvironment domain valuation inputCount)
    (inputMustEnvironment inputCount) ⟨valueType, .bool false⟩
    (input_environments_sound valuation domain inputCount) evaluated

theorem impossible_when_true_cannot_evaluate_true (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (domain : Datum) (inputCount fuel : Nat)
    (term : Term) (valueType : ValueType)
    (impossible : MustWhenTrue term inputCount = .impossible) :
    (evalCore primitive fuel term
      (booleanInputEnvironment domain valuation inputCount)).successValue? ≠
      some ⟨valueType, .bool true⟩ := by
  intro evaluated
  have sound := must_when_true_sound primitive valuation domain inputCount fuel
    term valueType evaluated
  rw [impossible] at sound
  exact sound

theorem impossible_when_false_cannot_evaluate_false (primitive : PrimitiveDenotation)
    (valuation : Nat → Bool) (domain : Datum) (inputCount fuel : Nat)
    (term : Term) (valueType : ValueType)
    (impossible : (Must term inputCount).whenFalse = .impossible) :
    (evalCore primitive fuel term
      (booleanInputEnvironment domain valuation inputCount)).successValue? ≠
      some ⟨valueType, .bool false⟩ := by
  intro evaluated
  have sound := must_when_false_sound primitive valuation domain inputCount fuel
    term valueType evaluated
  rw [impossible] at sound
  exact sound

/-! ## Executable Terminal-contract decision -/

inductive GuardInput where
  | occurrenceOutput (occurrence output : Nat)
  | other (coordinate : Nat)
  deriving Repr, DecidableEq

structure ClaimTransfer where
  inputs : List Nat
  outputs : List Nat
  deriving Repr, DecidableEq

inductive ClaimEffect where
  | other
  | reduction (transfer : ClaimTransfer)
  | terminal (terminal : Nat)
  deriving Repr, DecidableEq

structure AbstractClaimPath where
  decisions : List (GuardAtom × Bool)
  liveClaims : List Nat
  valid : Bool := true
  deriving Repr, DecidableEq

structure TerminalVisit where
  terminal : Nat
  liveClaims : List Nat
  valid : Bool
  deriving Repr, DecidableEq

structure ForwardClaimState where
  running : List AbstractClaimPath
  visits : List TerminalVisit
  deriving Repr, DecidableEq

def AbstractClaimPath.decision? (path : AbstractClaimPath)
    (atom : GuardAtom) : Option Bool :=
  (path.decisions.find? fun item => item.1 == atom).map Prod.snd

/-- Split only when an opaque guard atom has not appeared on the path.  A
repeated structurally identical atom reuses its prior truth value. -/
def guardBranches (guard : AttemptGuard) (path : AbstractClaimPath) :
    List (Bool × AbstractClaimPath) :=
  match guard with
  | .always => [(true, path)]
  | .evaluate atom =>
      match path.decision? atom with
      | some active => [(active, path)]
      | none =>
          [(true, { path with decisions := (atom, true) :: path.decisions }),
           (false, { path with decisions := (atom, false) :: path.decisions })]

def applyClaimTransfer (linearClaims : List Nat) (transfer : ClaimTransfer)
    (path : AbstractClaimPath) : AbstractClaimPath :=
  let present := transfer.inputs.all fun claim => path.liveClaims.contains claim
  let remaining := path.liveClaims.filter fun claim =>
    !(linearClaims.contains claim && transfer.inputs.contains claim)
  let fresh := transfer.outputs.filter fun claim => !remaining.contains claim
  { path with
    liveClaims := remaining ++ fresh
    valid := path.valid && present }

def advanceClaimBranch (linearClaims : List Nat) (effect : ClaimEffect)
    (branch : Bool × AbstractClaimPath) (state : ForwardClaimState) :
    ForwardClaimState :=
  if branch.1 then
    match effect with
    | .other => { state with running := state.running ++ [branch.2] }
    | .reduction transfer =>
        { state with running := state.running ++
            [applyClaimTransfer linearClaims transfer branch.2] }
    | .terminal terminal =>
        { state with visits := state.visits ++
            [{ terminal, liveClaims := branch.2.liveClaims, valid := branch.2.valid }] }
  else
    { state with running := state.running ++ [branch.2] }

def advanceClaimOccurrence (linearClaims : List Nat)
    (occurrence : ScheduledOccurrence) (effect : ClaimEffect)
    (paths : List AbstractClaimPath) (visits : List TerminalVisit) :
    ForwardClaimState :=
  paths.foldl (fun state path =>
    (guardBranches occurrence.guard path).foldl
      (fun next branch => advanceClaimBranch linearClaims effect branch next)
      state) { running := [], visits }

def forwardClaimsFrom (linearClaims : List Nat) :
    List ScheduledOccurrence → List ClaimEffect → ForwardClaimState → ForwardClaimState
  | occurrence :: occurrences, effect :: effects, state =>
      forwardClaimsFrom linearClaims occurrences effects
        (advanceClaimOccurrence linearClaims occurrence effect state.running state.visits)
  | _, _, state => state

/-- Finite forward abstract state used by the carrier decisions.  It does not
enumerate complete Boolean assignments: it splits the current state only at a
previously unseen opaque guard atom. -/
def forwardClaims (schedule : List ScheduledOccurrence) (effects : List ClaimEffect)
    (initialClaims linearClaims : List Nat) : ForwardClaimState :=
  forwardClaimsFrom linearClaims schedule effects
    { running := [{ decisions := [], liveClaims := initialClaims }], visits := [] }

def ForwardClaimState.claimsAt (state : ForwardClaimState)
    (terminal : Nat) : List (List Nat) :=
  state.visits.filterMap fun visit =>
    if visit.terminal == terminal then some visit.liveClaims else none

def ForwardClaimState.allValid (state : ForwardClaimState) : Bool :=
  state.running.all (·.valid) && state.visits.all (·.valid)

structure TerminalView where
  terminal : Nat
  occurrence : Nat
  guardTerm : Option Term
  guardInputs : List GuardInput
  requiredChecks : List Nat
  requiredReductions : List Nat
  terminalClaims : List Nat
  activePathLiveClaims : List (List Nat)
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
      MustWhenTrue term terminal.guardInputs.length ≠ .impossible ∧
      directPositiveUse (MustWhenTrue term terminal.guardInputs.length)
        terminal.guardInputs checkOccurrence = true

def checkTerminalClauseDecision (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) (checkOccurrence : Nat) : Bool :=
  decide (AttemptedWhenever schedule terminal.occurrence checkOccurrence) &&
  match terminal.guardTerm with
  | none => false
  | some term =>
      decide (MustWhenTrue term terminal.guardInputs.length ≠ .impossible) &&
      directPositiveUse (MustWhenTrue term terminal.guardInputs.length)
        terminal.guardInputs checkOccurrence

theorem checkTerminalClauseDecision_correct (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) (checkOccurrence : Nat) :
    checkTerminalClauseDecision schedule terminal checkOccurrence = true ↔
      CheckTerminalClause schedule terminal checkOccurrence := by
  cases guardTermAt : terminal.guardTerm <;>
    simp [checkTerminalClauseDecision, CheckTerminalClause, guardTermAt]

def TerminalContract (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) : Prop :=
  (∀ checkOccurrence, checkOccurrence ∈ terminal.requiredChecks →
      CheckTerminalClause schedule terminal checkOccurrence) ∧
  (∀ reductionOccurrence, reductionOccurrence ∈ terminal.requiredReductions →
      AttemptedWhenever schedule terminal.occurrence reductionOccurrence) ∧
  (∀ liveClaims, liveClaims ∈ terminal.activePathLiveClaims →
      liveClaims = terminal.terminalClaims)

def terminalContractDecision (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) : Bool :=
  (terminal.requiredChecks.all fun checkOccurrence =>
      checkTerminalClauseDecision schedule terminal checkOccurrence) &&
  (terminal.requiredReductions.all fun reductionOccurrence =>
      decide (AttemptedWhenever schedule terminal.occurrence reductionOccurrence)) &&
  (terminal.activePathLiveClaims.all fun liveClaims =>
      liveClaims == terminal.terminalClaims)

theorem terminalContractDecision_correct (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) :
    terminalContractDecision schedule terminal = true ↔
      TerminalContract schedule terminal := by
  simp [terminalContractDecision, TerminalContract,
    checkTerminalClauseDecision_correct, and_assoc]

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first < second) && strictlyIncreasing (second :: rest)

/-- Admission-boundary wrapper used for comparison with predecessor packages.
Sorted-unique carrier checks belong to admission step 2, not to
`TerminalContract` itself. -/
def terminalAdmissionDecision (schedule : List ScheduledOccurrence)
    (terminal : TerminalView) : Bool :=
  strictlyIncreasing terminal.requiredChecks &&
    strictlyIncreasing terminal.requiredReductions &&
    strictlyIncreasing terminal.terminalClaims &&
    terminalContractDecision schedule terminal

end M0
