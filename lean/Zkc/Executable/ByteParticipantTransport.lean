module

public import Zkc.Executable.DomainNativeByteTransport
public import Zkc.Executable.StaticSourceTransport
public import Zkc.Construction.ScalarVerifier

@[expose] public section
/-! Small observation laws composing native bytes with actual participants.
These laws inspect returned values and open Processes, never a second
constructed-instruction evaluator. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Executable.ByteParticipantTransport
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
open DomainAdapter DomainVM
variable {F G A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def scalarVerdict (result : PIR.Outcome (Option Bool) × Proof F G) : Bool :=
  match result.1, result.2 with
  | .returned (some decision), [] => decision
  | _, _ => false

def scalarSelected (values : List (Value F G)) : Option Bool :=
  match values with
  | .data (.boolean decision) :: _ => some decision
  | _ => none

def scalarSelection (position : Nat) (values : List (Value F G)) : Option Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

def observedVerdict (result : PIR.Outcome (Option Bool) × Bool) : Bool :=
  match result.1 with
  | .returned (some decision) => result.2 && decision
  | _ => false

theorem observedVerdict_observation (result : PIR.Outcome (Option Bool) × Proof F G) :
    observedVerdict (Executable.observation result.1 result.2.isEmpty) = scalarVerdict result := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped => rfl
  | returned value => cases value <;> cases unread <;> rfl

theorem byteAcceptance_selection (position : Nat)
    (result : PIR.Outcome (List (Value F G)) × Bool) :
    byteAcceptance position result =
      observedVerdict (mapOutcome (scalarSelection position) result.1, result.2) := by
  rcases result with ⟨outcome, complete⟩
  cases outcome with
  | stopped => rfl
  | returned values =>
    cases found : values[position]? with
    | none => simp [byteAcceptance, observedVerdict, mapOutcome, scalarSelection, selectedTrue, found]
    | some value =>
      cases value with
      | data payload =>
        cases payload with
        | boolean decision => cases decision <;> simp [byteAcceptance, observedVerdict, mapOutcome, scalarSelection, selectedTrue, found]
        | field | group => simp [byteAcceptance, observedVerdict, mapOutcome, scalarSelection, selectedTrue, found]
      | index | vector | transcript | indices | unsupported =>
        simp [byteAcceptance, observedVerdict, mapOutcome, scalarSelection, selectedTrue, found]

def selected (position : Nat) (values : Environment F G) : Option Bool :=
  match values[position]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

theorem nominalAcceptance_selected (position : Nat)
    (result : PIR.Outcome (Environment F G) × Proof F G) :
    nominalAcceptance position result = scalarVerdict (mapOutcome (selected position) result.1, result.2) := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped => rfl
  | returned values =>
    cases unread <;> simp only [nominalAcceptance, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and,
      Bool.false_and, scalarVerdict, mapOutcome]
    all_goals try (cases selected position values <;> rfl)
    unfold nominalSelected selected
    cases values[position]? with
    | none => rfl
    | some value =>
      cases value with
      | transcript | indices => rfl
      | data payload =>
        rcases payload with ⟨ty, admissible, contents⟩
        cases ty <;> rfl

theorem run_nominalAcceptance (position : Nat) (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) (Environment F G))
    (proof : Proof F G) :
    nominalAcceptance position <$> run key initial challenge process proof =
      scalarVerdict <$> DomainAdapter.runK key initial challenge process proof
        (fun values unread => pure (.returned (selected position values), unread)) := by
  rw [← run_map key initial challenge process (selected position) proof, Functor.map_map]
  congr 1
  funext result
  exact nominalAcceptance_selected position result

/-- A possibly refusing full-tuple readback can be composed before observing
stops and complete unread status. Every action stays in its original monad. -/
theorem run_observe (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (finish : A → PIR.Outcome B) (proof : Proof F G) :
    (fun result => Executable.observation (postOutcome finish result.1) result.2.isEmpty) <$>
        run key initial challenge process proof =
      (fun result => Executable.observation result.1 result.2.isEmpty) <$>
        DomainAdapter.runK key initial challenge process proof (fun value unread => pure (finish value, unread)) := by
  rw [← run_postOutcome key initial challenge finish process proof, Functor.map_map]

theorem mapOutcome_observation {X Y : Type} (f : X → Y) (outcome : PIR.Outcome X) (complete : Bool) :
    (mapOutcome f (Executable.observation outcome complete).1, (Executable.observation outcome complete).2) =
      Executable.observation (mapOutcome f outcome) complete := by
  cases outcome <;> rfl

/-- Readback of a source view's complete Boolean/transcript return is total
on every reached source suffix. No assertion is made about arbitrary histories. -/
theorem readback_source_return (context : Context) (key : Origin → Origin) (initial : History F G)
    (result : Bool × Domain.History (Structured.uniformCarriers F G))
    (readable : (readbackHistory key result.2).isSome = true) :
    mapOutcome scalarSelected
      (readbackOutcome context.suite key initial (.returned (SourceProcess.returnValues context.suite result))) =
      .returned (some result.1) := by
  cases mapped : readbackHistory key result.2 with
  | none => simp [mapped] at readable
  | some suffix =>
    simp [readbackOutcome, readbackValues, SourceProcess.returnValues, readbackValue,
      readbackData, mapped, mapOutcome, scalarSelected]

/-- The selected scalar observation of a source view, retaining malformed
receives, every stop, complete unread status and all challenge actions. -/
theorem source_observation (context : Context) (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F) (process : PIR.Process (Actions F G) Bool) (proof : Proof F G) :
    (fun result => Executable.observation
      (mapOutcome scalarSelected
        (readbackOutcome context.suite key initial result.1)) result.2.isEmpty) <$>
      run key initial challenge
        ((SourceProcess.sourceView context process []).bind fun result =>
          .done (SourceProcess.returnValues context.suite result)) proof =
    (fun result => Executable.observation result.1 result.2.isEmpty) <$>
      DomainAdapter.runK key initial challenge (SourceProcess.sourceView context process []) proof
        (fun result unread => pure (.returned (some result.1), unread)) := by
  have law := run_observe key initial challenge
    ((SourceProcess.sourceView context process []).bind fun result =>
      .done (SourceProcess.returnValues context.suite result))
    (fun values => mapOutcome scalarSelected
      (readbackOutcome context.suite key initial (.returned values))) proof
  have mapped : ∀ outcome : PIR.Outcome (Environment F G),
      postOutcome (fun values => mapOutcome scalarSelected
        (readbackOutcome context.suite key initial (.returned values))) outcome =
      mapOutcome scalarSelected
        (readbackOutcome context.suite key initial outcome) := by
    intro outcome; cases outcome <;> rfl
  simp only [mapped, runK_bind, DomainAdapter.runK] at law
  rw [law]
  congr 1
  apply runK_congr_yields key initial challenge _ _
    (StaticSourceTransport.sourceView_readable context key process [] rfl)
  intro result unread readable
  rw [readback_source_return context key initial result readable]

/-- Pure result projections need agree only at actual all-reply returns. -/
theorem run_map_yields {X : Type} (key : Origin → Origin) (initial : History F G)
    (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (property : A → Prop) (holds : PIR.Yields property process)
    (f g : PIR.Outcome A × Proof F G → X)
    (stops : ∀ reason unread, f (.stopped reason, unread) = g (.stopped reason, unread))
    (returns : ∀ value unread, property value → f (.returned value, unread) = g (.returned value, unread))
    (proof : Proof F G) :
    f <$> run key initial challenge process proof = g <$> run key initial challenge process proof := by
  simp only [run]
  induction process generalizing proof with
  | done value => simpa only [DomainAdapter.runK, map_pure] using congrArg pure (returns value proof holds)
  | halt => simp [DomainAdapter.runK, stops]
  | call operation continuation ih =>
    cases operation with
    | receive ty site schema peer =>
      cases proof with
      | nil => simp [DomainAdapter.runK, stops]
      | cons payload unread =>
        simp only [DomainAdapter.runK]
        cases Value.decode ty (.data payload) with
        | none => simp [stops]
        | some value => exact ih value (holds value) unread
    | send | observe | checkpoint => exact ih () (holds ()) proof
    | localService => simp [DomainAdapter.runK, stops]
    | query history origin =>
      simp only [DomainAdapter.runK]
      split
      · rw [map_bind, map_bind]
        congr 1
        funext answer
        cases answer with
        | stopped => simp [stops]
        | returned value => exact ih value (holds value) proof
      · simp [stops]

/-- Successful full-tuple ABI readback preserves selected nominal acceptance. -/
theorem byteAcceptance_readable (suite : String) (key : Origin → Origin) (initial : History F G)
    (position : Nat) (values : Environment F G) (unread : Proof F G)
    (readable : (readbackValues suite key initial values).isSome = true) :
    byteAcceptance position (nativeObservation suite key initial (.returned values, unread)) =
      nominalAcceptance position (.returned values, unread) := by
  cases erased : readbackValues suite key initial values with
  | none => simp [erased] at readable
  | some scalar =>
    have selected := (show Erases suite key initial values scalar from erased).get position
    simp only [nativeObservation, readbackOutcome, erased, Executable.observation,
      byteAcceptance, nominalAcceptance]
    congr 1
    unfold selectedTrue nominalSelected
    cases nominal : values[position]? with
    | none => simp [nominal] at selected; simp [selected]
    | some value =>
      simp only [nominal, Option.bind_some] at selected
      rw [selected]
      cases value with
      | indices => rfl
      | transcript actual history =>
        by_cases same : actual = suite
        · cases readbackHistory key history <;> simp [readbackValue, same]
        · simp [readbackValue, same]
      | data payload =>
        rcases payload with ⟨ty, admissible, contents⟩
        cases ty <;> try rfl
        cases contents <;> rfl

end Zkc.Executable.ByteParticipantTransport
